use std::mem;

use fxhash::FxHashMap;

use crate::ast;
use crate::ast::visit::{AstRecurse, Visitor};
use crate::diag::DiagCtx;

use super::{BindingId, BindingKind, DeclId, Module, Namespace, Result, Scope, ScopeId, SemaDiag};

impl Module<'_> {
    pub(super) fn resolve(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }

    pub fn resolve_name(
        &self,
        ns: Namespace,
        mut scope_id: ScopeId,
        name: &str,
    ) -> Option<BindingId> {
        loop {
            let scope = &self.scopes[scope_id];
            let bindings = match ns {
                Namespace::Ty => &scope.tys,
                Namespace::Value => &scope.values,
            };

            if let Some(&binding_id) = bindings.get(name) {
                return Some(binding_id);
            }

            scope_id = scope.visible_parent?;
        }
    }
}

struct Pass<'ast, 'm, D> {
    m: &'m mut Module<'ast>,
    diag: &'m mut D,
}

impl<'ast, 'm, D: DiagCtx> Pass<'ast, 'm, D> {
    fn new(m: &'m mut Module<'ast>, diag: &'m mut D) -> Self {
        Self { m, diag }
    }

    fn run(mut self) -> Result {
        self.init_root_scopes();

        let mut result = Ok(());
        result = result.and(self.resolve_decls());
        result = result.and(self.resolve_defs());
        result = result.and(self.find_main_decl());

        result
    }

    fn init_root_scopes(&mut self) {
        self.m.prelude_scope_id = self.m.scopes.insert(Scope {
            parent: None,
            visible_parent: None,
            tys: Default::default(),
            values: Default::default(),
        });

        self.m.root_scope_id = self.m.scopes.insert(Scope {
            parent: None,
            visible_parent: Some(self.m.prelude_scope_id),
            tys: Default::default(),
            values: Default::default(),
        });
    }

    fn resolve_decls(&mut self) -> Result {
        let mut result = Ok(());
        let mut unprocessed = self.m.root_decl_ids().collect::<Vec<_>>();
        // so that diagnostics refer to declarations in the correct order.
        unprocessed.reverse();

        while let Some(decl_id) = unprocessed.pop() {
            result = result.and(self.resolve_decl(decl_id));
            let start = unprocessed.len();
            self.m.decls[decl_id].for_each_child(|decl_id| unprocessed.push(decl_id));
            unprocessed[start..].reverse();
        }

        result
    }

    fn resolve_decl(&mut self, decl_id: DeclId) -> Result {
        let mut result = Ok(());
        let def = self.m.decls[decl_id].def;

        match &def.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(decl) => {
                let parent_decl_id = self.m.decls[decl_id].parent;
                let parent_scope_id = parent_decl_id
                    .and_then(|decl_id| self.m.fn_decl_scopes.get(decl_id))
                    .copied()
                    .unwrap_or(self.m.root_scope_id);
                let decl_scope_id = self.m.scopes.insert(Scope {
                    // the real values will be set in `resolve_defs`.
                    parent: Some(parent_scope_id),
                    visible_parent: None,
                    tys: Default::default(),
                    values: Default::default(),
                });
                self.m.fn_decl_scopes.insert(decl_id, decl_scope_id);

                self.m.bindings[decl.binding.id].kind = BindingKind::FnDecl(decl_id);
                result = result.and(self.add_binding(
                    Namespace::Value,
                    parent_scope_id,
                    decl.binding.name.as_str().into(),
                    decl.binding.id,
                ));
            }

            ast::DeclKind::TypeAlias(_) => unimplemented!(),
            ast::DeclKind::ExceptionType(_) => unimplemented!(),
            ast::DeclKind::ExceptionVariant(_) => unimplemented!(),
        }

        result
    }

    fn resolve_defs(&mut self) -> Result {
        let mut result = Ok(());
        let decl_ids = self.m.root_decl_ids().collect::<Vec<_>>();

        for decl_id in decl_ids {
            let def = self.m.decls[decl_id].def;
            let mut walker = Walker {
                result: Ok(()),
                current_scope_id: self.m.root_scope_id,
                pass: self,
            };
            walker.visit_decl(def);
            result = result.and(walker.result);
        }

        result
    }

    fn find_main_decl(&mut self) -> Result {
        let Some(&binding_id) = self.m.scopes[self.m.root_scope_id].values.get("main") else {
            self.diag.emit(SemaDiag::MissingMain);

            return Err(());
        };

        match self.m.bindings[binding_id].kind {
            BindingKind::Dummy => panic!("the binding for `main` is a dummy"),

            BindingKind::FnDecl(decl_id) => {
                self.m.main_decl_id = decl_id;

                Ok(())
            }

            BindingKind::DeclFnParam(..) => unreachable!(),
            BindingKind::ExprFnParam(..) => unreachable!(),
            BindingKind::Pat(_) => unreachable!(),
            BindingKind::Ty(_) => unreachable!(),
        }
    }

    fn add_binding(
        &mut self,
        ns: Namespace,
        scope_id: ScopeId,
        name: String,
        binding_id: BindingId,
    ) -> Result {
        let scope = &mut self.m.scopes[scope_id];

        if let Some(&prev_binding_id) = scope.get_bindings(ns).get(&name) {
            let binding = &self.m.bindings[binding_id];
            let prev_binding = &self.m.bindings[prev_binding_id];

            self.diag.emit(match ns {
                Namespace::Ty => SemaDiag::DuplicateTyDef {
                    name,
                    location: binding.location,
                    prev_location: prev_binding.location,
                },

                Namespace::Value => SemaDiag::DuplicateVarDef {
                    name,
                    location: binding.location,
                    prev_location: prev_binding.location,
                },
            });

            return Err(());
        }

        scope.get_bindings_mut(ns).insert(name, binding_id);

        Ok(())
    }
}

struct Walker<'ast, 'm, 'p, D> {
    result: Result,
    current_scope_id: ScopeId,
    pass: &'p mut Pass<'ast, 'm, D>,
}

impl<D: DiagCtx> Walker<'_, '_, '_, D> {
    fn enter_new_scope(&mut self) -> ScopeId {
        let scope_id = self.pass.m.scopes.insert(Scope {
            parent: Some(self.current_scope_id),
            visible_parent: Some(self.current_scope_id),
            tys: Default::default(),
            values: Default::default(),
        });

        mem::replace(&mut self.current_scope_id, scope_id)
    }
}

impl<'ast, D: DiagCtx> Visitor<'ast, 'ast> for Walker<'ast, '_, '_, D> {
    fn visit_decl(&mut self, decl: &'ast ast::Decl<'ast>) {
        match &decl.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(d) => {
                let prev_scope_id = self.enter_new_scope();
                assert!(d.generics.is_empty());

                for (idx, param) in d.params.iter().enumerate() {
                    self.pass.m.bindings[param.binding.id].kind =
                        BindingKind::DeclFnParam(decl.id, idx);
                    self.result = self.result.and(self.pass.add_binding(
                        Namespace::Value,
                        self.current_scope_id,
                        param.binding.name.as_str().into(),
                        param.binding.id,
                    ));

                    self.visit_ty_expr(&param.ty_expr);
                }

                let fn_decl_scope_id = self.pass.m.fn_decl_scopes[decl.id];
                self.pass.m.scopes[fn_decl_scope_id].parent = Some(self.current_scope_id);
                self.pass.m.scopes[fn_decl_scope_id].visible_parent = Some(self.current_scope_id);

                if let Some(ret) = &d.ret {
                    self.visit_ty_expr(ret);
                }

                for ty_expr in &d.throws {
                    self.visit_ty_expr(ty_expr);
                }

                self.current_scope_id = fn_decl_scope_id;

                for decl in &d.decls {
                    self.visit_decl(decl);
                }

                self.enter_new_scope();
                d.body.recurse(self);

                self.current_scope_id = prev_scope_id;

                return;
            }

            ast::DeclKind::TypeAlias(_) => unimplemented!(),
            ast::DeclKind::ExceptionType(_) => unimplemented!(),
            ast::DeclKind::ExceptionVariant(_) => unimplemented!(),
        }

        decl.recurse(self);
    }

    fn visit_ty_expr(&mut self, ty_expr: &'ast ast::TyExpr<'ast>) {
        match &ty_expr.kind {
            ast::TyExprKind::Dummy => {}
            ast::TyExprKind::Bool(_) => {}
            ast::TyExprKind::Nat(_) => {}
            ast::TyExprKind::Ref(_) => {}
            ast::TyExprKind::Sum(_) => {}
            ast::TyExprKind::Fn(_) => {}
            ast::TyExprKind::ForAll(_) => unimplemented!(),
            ast::TyExprKind::Mu(_) => unimplemented!(),
            ast::TyExprKind::Tuple(_) => {}

            ast::TyExprKind::Record(t) => {
                let mut fields = FxHashMap::default();

                for field in &t.fields {
                    if let Some(prev_location) =
                        fields.insert(field.name.as_str(), field.name.location())
                    {
                        self.result = Err(());
                        self.pass.diag.emit(SemaDiag::DuplicateRecordTyField {
                            name: field.name.as_str().into(),
                            location: field.name.location(),
                            prev_location,
                        });
                    }
                }
            }

            ast::TyExprKind::Variant(t) => {
                let mut fields = FxHashMap::default();

                for field in &t.fields {
                    if let Some(prev_location) =
                        fields.insert(field.name.as_str(), field.name.location())
                    {
                        self.result = Err(());
                        self.pass.diag.emit(SemaDiag::DuplicateVariantTyField {
                            name: field.name.as_str().into(),
                            location: field.name.location(),
                            prev_location,
                        });
                    }
                }
            }

            ast::TyExprKind::List(_) => {}
            ast::TyExprKind::Unit(_) => {}
            ast::TyExprKind::Top(_) => {}
            ast::TyExprKind::Bot(_) => {}
            ast::TyExprKind::Auto(_) => {}

            ast::TyExprKind::Name(t) => {
                if let Some(binding_id) =
                    self.pass
                        .m
                        .resolve_name(Namespace::Ty, self.current_scope_id, t.name.as_str())
                {
                    self.pass.m.ty_name_exprs.insert(ty_expr.id, binding_id);
                } else {
                    self.result = Err(());
                    self.pass.diag.emit(SemaDiag::UndefinedTy {
                        name: t.name.as_str().into(),
                        location: t.name.location(),
                    });
                }
            }
        }

        ty_expr.recurse(self);
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr<'ast>) {
        match &expr.kind {
            ast::ExprKind::Dummy => {}
            ast::ExprKind::Bool(_) => {}
            ast::ExprKind::Unit(_) => {}
            ast::ExprKind::Int(_) => {}
            ast::ExprKind::Address(_) => {}

            ast::ExprKind::Name(e) => {
                if let Some(binding_id) = self.pass.m.resolve_name(
                    Namespace::Value,
                    self.current_scope_id,
                    e.name.as_str(),
                ) {
                    self.pass.m.name_exprs.insert(expr.id, binding_id);
                } else {
                    self.result = Err(());
                    self.pass.diag.emit(SemaDiag::UndefinedVar {
                        name: e.name.as_str().into(),
                        location: e.name.location(),
                    });
                }
            }

            ast::ExprKind::Field(_) => {}
            ast::ExprKind::Panic(_) => {}
            ast::ExprKind::Throw(_) => {}

            ast::ExprKind::TryCatch(_) => unimplemented!(),
            ast::ExprKind::TryCast(_) => unimplemented!(),

            ast::ExprKind::Fix(_) => {}
            ast::ExprKind::Fold(_) => {}
            ast::ExprKind::Unfold(_) => {}
            ast::ExprKind::Apply(_) => {}
            ast::ExprKind::TyApply(_) => {}
            ast::ExprKind::Ascription(_) => {}
            ast::ExprKind::Cast(_) => {}

            ast::ExprKind::Fn(e) => {
                let prev_scope_id = self.enter_new_scope();

                for (idx, param) in e.params.iter().enumerate() {
                    self.pass.m.bindings[param.binding.id].kind =
                        BindingKind::ExprFnParam(expr.id, idx);
                    self.result = self.result.and(self.pass.add_binding(
                        Namespace::Value,
                        self.current_scope_id,
                        param.binding.name.as_str().into(),
                        param.binding.id,
                    ));

                    self.visit_ty_expr(&param.ty_expr);
                }

                self.enter_new_scope();
                e.body.recurse(self);

                self.current_scope_id = prev_scope_id;

                return;
            }

            ast::ExprKind::Tuple(_) => {}

            ast::ExprKind::Record(e) => {
                let mut fields = FxHashMap::default();

                for field in &e.fields {
                    if let Some(prev_location) =
                        fields.insert(field.name.as_str(), field.name.location())
                    {
                        self.result = Err(());
                        self.pass.diag.emit(SemaDiag::DuplicateRecordField {
                            name: field.name.as_str().into(),
                            location: field.name.location(),
                            prev_location,
                        });
                    }
                }
            }

            ast::ExprKind::Variant(_) => {}

            ast::ExprKind::Match(e) => {
                self.visit_expr(&e.expr);

                for arm in &e.arms {
                    let prev_scope_id = self.enter_new_scope();
                    self.visit_pat(&arm.pat);
                    self.enter_new_scope();
                    self.visit_expr(&arm.body);

                    self.current_scope_id = prev_scope_id;
                }

                return;
            }

            ast::ExprKind::List(_) => {}
            ast::ExprKind::If(_) => {}
            ast::ExprKind::Seq(_) => {}

            ast::ExprKind::Let(e) => {
                let prev_scope_id = self.enter_new_scope();

                if e.rec {
                    for binding in &e.bindings {
                        self.visit_pat(&binding.pat);
                    }

                    // visit initializers *after* bringing all the bindings into scope!
                    for binding in &e.bindings {
                        self.visit_expr(&binding.expr);
                    }

                    self.enter_new_scope();
                } else {
                    for binding in &e.bindings {
                        // visit the initializer first. this is critically important.
                        self.visit_expr(&binding.expr);
                        self.visit_pat(&binding.pat);
                        self.enter_new_scope();
                    }
                }

                self.visit_expr(&e.body);

                self.current_scope_id = prev_scope_id;

                return;
            }

            ast::ExprKind::Generic(_) => unimplemented!(),

            ast::ExprKind::Unary(_) => {}
            ast::ExprKind::Binary(_) => {}
        }

        expr.recurse(self);
    }

    fn visit_pat(&mut self, pat: &'ast ast::Pat<'ast>) {
        match &pat.kind {
            ast::PatKind::Dummy => {}
            ast::PatKind::Variant(_) => {}
            ast::PatKind::Cons(_) => {}
            ast::PatKind::Tuple(_) => {}

            ast::PatKind::Record(p) => {
                let mut fields = FxHashMap::default();

                for field in &p.fields {
                    if let Some(prev_location) =
                        fields.insert(field.name.as_str(), field.name.location())
                    {
                        self.result = Err(());
                        self.pass
                            .diag
                            .emit(SemaDiag::DuplicateRecordPatField {
                                name: field.name.as_str().into(),
                                location: field.name.location(),
                                prev_location,
                            });
                    }
                }
            }

            ast::PatKind::List(_) => {}
            ast::PatKind::Bool(_) => {}
            ast::PatKind::Unit(_) => {}
            ast::PatKind::Int(_) => {}

            ast::PatKind::Name(p) => {
                self.pass.m.bindings[p.binding.id].kind = BindingKind::Pat(pat.id);
                self.result = self.result.and(self.pass.add_binding(
                    Namespace::Value,
                    self.current_scope_id,
                    p.binding.name.as_str().into(),
                    p.binding.id,
                ));

                return;
            }

            ast::PatKind::Ascription(_) => {}
            ast::PatKind::Cast(_) => {}
        }

        pat.recurse(self);
    }

    fn visit_binding(&mut self, _binding: &'ast ast::Binding<'ast>) {
        // the binding should have been visited by its enclosing type.
    }
}
