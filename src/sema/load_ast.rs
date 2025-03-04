use crate::ast;
use crate::ast::visit::{AstRecurse, Visitor, VisitorMut};

use super::feature::Feature;
use super::{BindingInfo, BindingKind, DeclInfo, ExprInfo, Module, PatInfo, TyExprInfo};

impl<'ast> Module<'ast> {
    pub(super) fn load_ast(&mut self, ast: &'ast mut ast::Program<'ast>) {
        Pass::new(self, ast).run()
    }
}

struct Pass<'ast, 'm> {
    m: &'m mut Module<'ast>,
    ast: Option<&'ast mut ast::Program<'ast>>,
}

impl<'ast, 'm> Pass<'ast, 'm> {
    fn new(m: &'m mut Module<'ast>, ast: &'ast mut ast::Program<'ast>) -> Self {
        Self { m, ast: Some(ast) }
    }

    fn run(mut self) {
        self.m.location = self.ast.as_ref().unwrap().location;

        self.load_features();
        self.assign_ids();
        self.set_defs();
    }

    fn load_features(&mut self) {
        for &(extension, location) in &self.ast.as_ref().unwrap().extensions {
            if let Some(feature) = Feature::from_extension(extension, location) {
                self.m.features.insert(feature.kind, feature);
            }
        }
    }

    fn assign_ids(&mut self) {
        let mut walker = IdAssigner { m: self.m };

        for decl in &mut self.ast.as_mut().unwrap().decls {
            walker.visit_decl(decl);
        }
    }

    fn set_defs(&mut self) {
        let decls: &[ast::Decl<'_>] = &self.ast.take().unwrap().decls;
        let mut walker = DefSetter { m: self.m };

        for decl in decls {
            walker.visit_decl(decl);
        }
    }
}

struct IdAssigner<'ast, 'm> {
    m: &'m mut Module<'ast>,
}

impl<'ast, 'm> VisitorMut<'ast, 'm> for IdAssigner<'ast, 'm> {
    fn visit_decl(&mut self, decl: &'m mut ast::Decl<'ast>) {
        decl.id = self.m.decls.insert(DeclInfo {
            def: &ast::DUMMY_DECL,
            parent: None,
        });

        decl.recurse_mut(self);
    }

    fn visit_ty_expr(&mut self, ty_expr: &'m mut ast::TyExpr<'ast>) {
        ty_expr.id = self.m.ty_exprs.insert(TyExprInfo {
            def: &ast::DUMMY_TY_EXPR,
        });

        ty_expr.recurse_mut(self);
    }

    fn visit_expr(&mut self, expr: &'m mut ast::Expr<'ast>) {
        expr.id = self.m.exprs.insert(ExprInfo {
            def: &ast::DUMMY_EXPR,
        });

        expr.recurse_mut(self);
    }

    fn visit_pat(&mut self, pat: &'m mut ast::Pat<'ast>) {
        pat.id = self.m.pats.insert(PatInfo {
            def: &ast::DUMMY_PAT,
        });

        pat.recurse_mut(self);
    }

    fn visit_binding(&mut self, binding: &'m mut ast::Binding<'ast>) {
        binding.id = self.m.bindings.insert(BindingInfo {
            location: binding.location(),
            name: binding.name.as_str().into(),
            kind: BindingKind::Dummy,
        });
    }
}

struct DefSetter<'ast, 'm> {
    m: &'m mut Module<'ast>,
}

impl<'ast> Visitor<'ast, 'ast> for DefSetter<'ast, '_> {
    fn visit_decl(&mut self, decl: &'ast ast::Decl<'ast>) {
        self.m.decls[decl.id].def = decl;

        match &decl.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(d) => {
                for subdecl in &d.decls {
                    self.m.decls[subdecl.id].parent = Some(decl.id);
                }
            }

            ast::DeclKind::TypeAlias(_) => {}
            ast::DeclKind::ExceptionType(_) => {}
            ast::DeclKind::ExceptionVariant(_) => {}
        }

        decl.recurse(self);
    }

    fn visit_ty_expr(&mut self, ty_expr: &'ast ast::TyExpr<'ast>) {
        self.m.ty_exprs[ty_expr.id].def = ty_expr;
        ty_expr.recurse(self);
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr<'ast>) {
        self.m.exprs[expr.id].def = expr;
        expr.recurse(self);
    }

    fn visit_pat(&mut self, pat: &'ast ast::Pat<'ast>) {
        self.m.pats[pat.id].def = pat;
        pat.recurse(self);
    }

    fn visit_binding(&mut self, _binding: &'ast ast::Binding<'ast>) {}
}
