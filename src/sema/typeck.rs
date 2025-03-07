use std::mem;

use crate::ast;
use crate::diag::DiagCtx;
use crate::util::SliceExt;

use super::ty::{Ty, TyFn, TyKind, TyRecord, TyTuple, TyVariant};
use super::{DeclId, Module, Result, TyId};

#[derive(Debug, Clone)]
pub enum ExpectationSource {
    FnDeclRet(DeclId),
}

type ExpectedTy = (TyId, ExpectationSource);

impl Module<'_> {
    pub(super) fn typeck(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }

    fn add_ty(&mut self, mut ty: Ty) -> TyId {
        *self
            .ty_dedup
            .entry(mem::take(&mut ty.kind))
            .or_insert_with_key(|kind| {
                self.tys.insert(Ty {
                    kind: kind.clone(),
                    ..ty
                })
            })
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
        self.add_well_known_tys();
        self.typeck_decls()?;

        Ok(())
    }

    fn add_well_known_tys(&mut self) {
        self.m.well_known_tys.error = self.m.add_ty(Ty {
            kind: TyKind::Error,
        });
        self.m.well_known_tys.unit = self.m.add_ty(Ty { kind: TyKind::Unit });
        self.m.well_known_tys.bool = self.m.add_ty(Ty { kind: TyKind::Bool });
        self.m.well_known_tys.nat = self.m.add_ty(Ty { kind: TyKind::Nat });
        self.m.well_known_tys.empty_tuple = self.m.add_ty(Ty {
            kind: TyKind::Tuple(TyTuple { elems: vec![] }),
        });
    }

    fn is_error_ty(&self, ty_id: TyId) -> bool {
        ty_id == self.m.well_known_tys.error
    }

    fn ty_conforms_to(&self, ty_id: TyId, expected_ty_id: TyId) -> bool {
        if self.is_error_ty(ty_id) || self.is_error_ty(expected_ty_id) {
            return true;
        }

        if ty_id == expected_ty_id {
            return true;
        }

        match (&self.m.tys[ty_id].kind, &self.m.tys[expected_ty_id].kind) {
            (
                &TyKind::Sum(lhs_ty_id, rhs_ty_id),
                &TyKind::Sum(expected_lhs_ty_id, expected_rhs_ty_id),
            ) => {
                self.ty_conforms_to(lhs_ty_id, expected_lhs_ty_id)
                    && self.ty_conforms_to(rhs_ty_id, expected_rhs_ty_id)
            }

            (TyKind::Fn(lhs), TyKind::Fn(rhs)) => {
                self.all_tys_conform_to(&lhs.params, &rhs.params)
                    && self.ty_conforms_to(lhs.ret, rhs.ret)
            }

            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) => {
                self.all_tys_conform_to(&lhs.elems, &rhs.elems)
            }

            (TyKind::Record(lhs), TyKind::Record(rhs)) => lhs.elems.zip_all(
                &rhs.elems,
                |(lhs_name, lhs_ty_id), (rhs_name, rhs_ty_id)| {
                    lhs_name == rhs_name && self.ty_conforms_to(*lhs_ty_id, *rhs_ty_id)
                },
            ),

            (TyKind::Variant(lhs), TyKind::Variant(rhs)) => lhs.elems.zip_all(
                &rhs.elems,
                |(lhs_name, lhs_ty_id), (rhs_name, rhs_ty_id)| {
                    lhs_name == rhs_name
                        && (match (lhs_ty_id, rhs_ty_id) {
                            (Some(lhs_ty_id), Some(rhs_ty_id)) => {
                                self.ty_conforms_to(*lhs_ty_id, *rhs_ty_id)
                            }

                            (None, None) => true,

                            _ => false,
                        })
                },
            ),

            (&TyKind::List(lhs_ty_id), &TyKind::List(rhs_ty_id)) => {
                self.ty_conforms_to(lhs_ty_id, rhs_ty_id)
            }

            (
                // why not `_`?
                // this makes sure I don't forget to fix this if I add new types.
                TyKind::Error
                | TyKind::Unit
                | TyKind::Bool
                | TyKind::Nat
                | TyKind::Sum(..)
                | TyKind::Fn(..)
                | TyKind::Tuple(..)
                | TyKind::Record(..)
                | TyKind::Variant(..)
                | TyKind::List(..),
                _,
            ) => false,
        }
    }

    fn all_tys_conform_to(&self, ty_ids: &[TyId], expected_ty_ids: &[TyId]) -> bool {
        ty_ids.zip_all(expected_ty_ids, |&ty_id, &expected_ty_id| {
            self.ty_conforms_to(ty_id, expected_ty_id)
        })
    }

    fn typeck_decls(&mut self) -> Result {
        self.typeck_decls_early().and(self.typeck_decls_late())
    }

    fn typeck_decls_early(&mut self) -> Result {
        let mut result = Ok(());

        for decl_id in self.m.root_decl_ids().collect::<Vec<_>>() {
            result = result.and(self.typeck_decl_early(self.m.decls[decl_id].def));
        }

        result
    }

    fn typeck_decls_late(&mut self) -> Result {
        let mut result = Ok(());

        for decl_id in self.m.root_decl_ids().collect::<Vec<_>>() {
            result = result.and(self.typeck_decl_late(self.m.decls[decl_id].def));
        }

        result
    }

    fn typeck_decl_early(&mut self, decl: &ast::Decl<'ast>) -> Result {
        let mut result = Ok(());

        match &decl.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(d) => {
                self.m.bindings[d.binding.id].ty_id = self.m.well_known_tys.error;

                assert!(d.generics.is_empty());

                let mut param_ty_ids = Vec::with_capacity(d.params.len());

                for param in &d.params {
                    result = result.and(self.typeck_ty_expr(&param.ty_expr));
                    let param_ty_id = self.m.ty_exprs[param.ty_expr.id].ty_id;
                    self.m.bindings[param.binding.id].ty_id = param_ty_id;
                    param_ty_ids.push(param_ty_id);
                }

                let ret_ty_id = d
                    .ret
                    .as_ref()
                    .map(|ty_expr| {
                        result = result.and(self.typeck_ty_expr(ty_expr));

                        self.m.ty_exprs[ty_expr.id].ty_id
                    })
                    .expect("inferring return types in early typeck stage is unsupported");

                assert!(d.throws.is_empty());

                self.m.bindings[d.binding.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Fn(TyFn {
                        params: param_ty_ids,
                        ret: ret_ty_id,
                    }),
                });

                for subdecl in &d.decls {
                    result = result.and(self.typeck_decl_early(subdecl));
                }
            }

            ast::DeclKind::TypeAlias(_) => unimplemented!(),
            ast::DeclKind::ExceptionType(_) => unimplemented!(),
            ast::DeclKind::ExceptionVariant(_) => unimplemented!(),
        }

        result
    }

    fn typeck_decl_late(&mut self, decl: &ast::Decl<'ast>) -> Result {
        let mut result = Ok(());

        match &decl.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(d) => {
                for subdecl in &d.decls {
                    result = result.and(self.typeck_decl_late(subdecl));
                }

                let fn_ty_id = self.m.bindings[d.binding.id].ty_id;
                let TyKind::Fn(fn_ty) = &self.m.tys[fn_ty_id].kind else {
                    unreachable!();
                };

                result = result.and(self.typeck_expr(
                    &d.body.ret,
                    Some((fn_ty.ret, ExpectationSource::FnDeclRet(decl.id))),
                ));
            }

            ast::DeclKind::TypeAlias(_) => unimplemented!(),
            ast::DeclKind::ExceptionType(_) => unimplemented!(),
            ast::DeclKind::ExceptionVariant(_) => unimplemented!(),
        }

        result
    }

    fn typeck_ty_expr(&mut self, ty_expr: &ast::TyExpr<'ast>) -> Result {
        let mut result = Ok(());
        self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.error;

        match &ty_expr.kind {
            ast::TyExprKind::Dummy => {}

            ast::TyExprKind::Bool(_) => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.bool;
            }

            ast::TyExprKind::Nat(_) => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.nat;
            }

            ast::TyExprKind::Ref(_) => unimplemented!(),

            ast::TyExprKind::Sum(t) => {
                result = result.and(self.typeck_ty_expr(&t.lhs));
                result = result.and(self.typeck_ty_expr(&t.rhs));

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Sum(
                        self.m.ty_exprs[t.lhs.id].ty_id,
                        self.m.ty_exprs[t.rhs.id].ty_id,
                    ),
                });
            }

            ast::TyExprKind::Fn(t) => {
                let mut param_ty_ids = Vec::with_capacity(t.params.len());

                for param in &t.params {
                    result = result.and(self.typeck_ty_expr(param));
                    param_ty_ids.push(self.m.ty_exprs[param.id].ty_id);
                }

                result = result.and(self.typeck_ty_expr(&t.ret));
                let ret_ty_id = self.m.ty_exprs[t.ret.id].ty_id;

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Fn(TyFn {
                        params: param_ty_ids,
                        ret: ret_ty_id,
                    }),
                });
            }

            ast::TyExprKind::ForAll(_) => unimplemented!(),
            ast::TyExprKind::Mu(_) => unimplemented!(),

            ast::TyExprKind::Tuple(t) => {
                let mut elems = Vec::with_capacity(t.elems.len());

                for elem in &t.elems {
                    result = result.and(self.typeck_ty_expr(elem));
                    elems.push(self.m.ty_exprs[elem.id].ty_id);
                }

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Tuple(TyTuple { elems }),
                });
            }

            ast::TyExprKind::Record(t) if t.fields.is_empty() => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.empty_tuple;
            }

            ast::TyExprKind::Record(t) => {
                let mut elems = Vec::with_capacity(t.fields.len());

                for field in &t.fields {
                    result = result.and(self.typeck_ty_expr(&field.ty_expr));
                    elems.push((
                        field.name.as_str().to_owned(),
                        self.m.ty_exprs[field.ty_expr.id].ty_id,
                    ));
                }

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Record(TyRecord::new(elems)),
                });
            }

            ast::TyExprKind::Variant(t) => {
                let mut elems = Vec::with_capacity(t.fields.len());

                for field in &t.fields {
                    elems.push((
                        field.name.as_str().to_owned(),
                        field.ty_expr.as_ref().map(|field_ty_expr| {
                            result = result.and(self.typeck_ty_expr(field_ty_expr));

                            self.m.ty_exprs[field_ty_expr.id].ty_id
                        }),
                    ));
                }

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Variant(TyVariant::new(elems)),
                });
            }

            ast::TyExprKind::List(t) => {
                result = result.and(self.typeck_ty_expr(&t.ty_expr));

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::List(self.m.ty_exprs[t.ty_expr.id].ty_id),
                });
            }

            ast::TyExprKind::Unit(_) => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.unit;
            }

            ast::TyExprKind::Top(_) => unimplemented!(),
            ast::TyExprKind::Bot(_) => unimplemented!(),
            ast::TyExprKind::Auto(_) => unimplemented!(),

            ast::TyExprKind::Name(_) => {
                if let Some(&binding_id) = self.m.ty_name_exprs.get(ty_expr.id) {
                    self.m.ty_exprs[ty_expr.id].ty_id = self.m.bindings[binding_id].ty_id;
                }
            }
        }

        result
    }

    fn typeck_expr(&mut self, expr: &ast::Expr<'ast>, expected_ty: Option<ExpectedTy>) -> Result {
        todo!()
    }
}
