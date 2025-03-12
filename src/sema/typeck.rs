use std::mem;

use ariadne::{Label, ReportBuilder};
use fxhash::{FxHashMap, FxHashSet};

use crate::ast;
use crate::diag::{DiagCtx, IntoReportBuilder};
use crate::location::Location;
use crate::util::SliceExt;

use super::ty::{Ty, TyFn, TyKind, TyRecord, TyTuple, TyVariant};
use super::{DeclId, ExprId, Module, PatId, Result, SemaError, TyExprId, TyId};

#[derive(Debug, Clone)]
pub enum ExpectationSource {
    FnDeclRet(DeclId),

    FixArg(ExprId),

    InjectionArg {
        expr_id: ExprId,
        is_left: bool,
        sum_ty_id: TyId,
    },

    InjectionPat {
        pat_id: PatId,
        is_left: bool,
        sum_ty_id: TyId,
    },

    ConsArg {
        expr_id: ExprId,
        arg_expr_id: ExprId,
        elem_ty_id: TyId,
    },

    ConsPat {
        pat_id: PatId,
        arg_pat_id: PatId,
        elem_ty_id: TyId,
    },

    BuiltinArg {
        expr_id: ExprId,
        builtin: ast::Builtin,
    },

    BuiltinConsPat {
        pat_id: PatId,
        cons: ast::Cons,
    },

    FnArg {
        expr_id: ExprId,
        arg_idx: usize,
        callee_expr_id: ExprId,
        callee_ty_id: TyId,
    },

    AscriptionExpr {
        expr_id: ExprId,
        ty_expr_id: TyExprId,
    },

    AscriptionPat {
        pat_id: PatId,
        ty_expr_id: TyExprId,
    },

    FnExprRet(ExprId),

    TupleExprElem {
        expr_id: ExprId,
        ty_id: TyId,
    },

    TuplePatElem {
        pat_id: PatId,
        ty_id: TyId,
    },

    RecordExprField {
        expr_id: ExprId,
        ty_id: TyId,
    },

    RecordPatField {
        pat_id: PatId,
        ty_id: TyId,
    },

    VariantExprData {
        expr_id: ExprId,
        ty_id: TyId,
    },

    VariantPatData {
        pat_id: PatId,
        ty_id: TyId,
    },

    Scrutinee {
        scrutinee_expr_id: ExprId,
        scrutinee_ty_id: TyId,
        match_expr_id: ExprId,
    },

    MatchArmBody {
        first_arm_expr_id: ExprId,
        ty_id: TyId,
        match_expr_id: ExprId,
    },

    ListExprElem {
        first_elem_expr_id: ExprId,
        ty_id: TyId,
        list_expr_id: ExprId,
    },

    ListPatElem {
        first_elem_pat_id: PatId,
        ty_id: TyId,
        list_pat_id: PatId,
    },

    IfCond {
        expr_id: ExprId,
    },

    IfBranch {
        then_expr_id: ExprId,
        ty_id: TyId,
        if_expr_id: ExprId,
    },

    Seq {
        semi_location: Location,
        expr_id: ExprId,
    },

    LetRecBinding {
        pat_id: PatId,
        ty_id: TyId,
    },

    LetBinding {
        init_expr_id: ExprId,
        ty_id: TyId,
    },

    BinOp {
        op_location: Location,
    },
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
            .or_insert_with_key(|kind| self.tys.insert(Ty { kind: kind.clone() }))
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
        self.set_all_tys_to_error();
        self.typeck_decls()?;
        self.check_main()?;

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

    fn set_all_tys_to_error(&mut self) {
        let error_ty_id = self.m.well_known_tys.error;

        for expr in self.m.exprs.values_mut() {
            expr.ty_id = error_ty_id;
        }

        for ty_expr in self.m.ty_exprs.values_mut() {
            ty_expr.ty_id = error_ty_id;
        }

        for pat in self.m.pats.values_mut() {
            pat.ty_id = error_ty_id;
        }

        for binding in self.m.bindings.values_mut() {
            binding.ty_id = error_ty_id;
        }
    }

    fn check_main(&mut self) -> Result {
        let ast::DeclKind::Fn(decl) = &self.m.decls[self.m.main_decl_id].def.kind else {
            unreachable!()
        };

        if decl.params.len() == 1 {
            Ok(())
        } else {
            self.diag.emit(SemaError::IncorrectArityOfMain {
                location: decl.binding.location(),
                actual: decl.params.len(),
            });

            Err(())
        }
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

            (TyKind::Record(r), TyKind::Tuple(t)) | (TyKind::Tuple(t), TyKind::Record(r))
                if r.elems.is_empty() && t.elems.is_empty() =>
            {
                true
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

    fn are_tys_equivalent(&self, lhs_ty_id: TyId, rhs_ty_id: TyId) -> bool {
        lhs_ty_id == rhs_ty_id
    }

    fn augment_error_with_expectation(
        &self,
        report: impl IntoReportBuilder,
        source: ExpectationSource,
    ) -> ReportBuilder<'static, Location> {
        let mut report = report.into_report_builder();

        match source {
            ExpectationSource::FnDeclRet(decl_id) => {
                let decl = &self.m.decls[decl_id].def;
                let ast::DeclKind::Fn(decl_fn) = &decl.kind else {
                    unreachable!()
                };

                if let Some(ret_ty_expr) = &decl_fn.ret {
                    if ret_ty_expr.location.has_span() {
                        report.add_label(
                            Label::new(ret_ty_expr.location)
                                .with_message("expected because of the return type here"),
                        );
                    } else if decl.location.has_span() {
                        report.add_label(
                            Label::new(decl.location)
                                .with_message("expected because of this function's return type"),
                        );
                    } else {
                        report.add_note(format!(
                            "expected because of the return type of the function `{}`",
                            decl_fn.binding.name.as_str(),
                        ));
                    }
                }
            }

            ExpectationSource::FixArg(expr_id) => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location)
                            .with_message("the fixpoint combinator requires that the parameter type matches the return type")
                    );
                }
            }

            ExpectationSource::InjectionArg {
                expr_id,
                is_left,
                sum_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(format!(
                        "expected by the {} injection into the sum type `{}`",
                        if is_left { "left" } else { "right" },
                        self.m.display_ty(sum_ty_id),
                    )));
                }
            }

            ExpectationSource::InjectionPat {
                pat_id,
                is_left,
                sum_ty_id,
            } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "expected by the {} injection into the sum type `{}`",
                        if is_left { "left" } else { "right" },
                        self.m.display_ty(sum_ty_id),
                    )));
                }
            }

            ExpectationSource::ConsArg {
                expr_id,
                arg_expr_id,
                elem_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let arg_expr = self.m.exprs[arg_expr_id].def;

                if arg_expr.location.has_span() {
                    report.add_label(Label::new(arg_expr.location).with_message(format!(
                        "expected because this expression has the type `{}`",
                        self.m.display_ty(elem_ty_id),
                    )));
                }

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location).with_message("in this `cons` expression"),
                    );
                }
            }

            ExpectationSource::ConsPat {
                pat_id,
                arg_pat_id,
                elem_ty_id,
            } => {
                let pat = self.m.pats[pat_id].def;
                let arg_pat = self.m.pats[arg_pat_id].def;

                if arg_pat.location.has_span() {
                    report.add_label(Label::new(arg_pat.location).with_message(format!(
                        "expected because this pattern has the type `{}`",
                        self.m.display_ty(elem_ty_id),
                    )));
                }

                if pat.location.has_span() {
                    report
                        .add_label(Label::new(pat.location).with_message("in this `cons` pattern"));
                }
            }

            ExpectationSource::BuiltinArg { expr_id, builtin } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(format!(
                        "expected as an argument to this `{builtin}` expression"
                    )));
                }
            }

            ExpectationSource::BuiltinConsPat { pat_id, cons } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "expected as an argument to this `{cons}` constructor pattern"
                    )));
                }
            }

            ExpectationSource::FnArg {
                expr_id,
                arg_idx,
                callee_expr_id,
                callee_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let callee_expr = self.m.exprs[callee_expr_id].def;

                if callee_expr.location.has_span() {
                    report.add_label(Label::new(callee_expr.location).with_message(format!(
                        "expected as an argument #{} to this function",
                        arg_idx + 1,
                    )));

                    report.add_label(Label::new(callee_expr.location).with_message(format!(
                        "the callee has the type `{}`",
                        self.m.display_ty(callee_ty_id),
                    )));
                }

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location)
                            .with_message("in this function application expression"),
                    );
                }
            }

            ExpectationSource::AscriptionExpr {
                expr_id,
                ty_expr_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let ty_expr = &self.m.ty_exprs[ty_expr_id].def;

                if ty_expr.location.has_span() {
                    report.add_label(
                        Label::new(ty_expr.location)
                            .with_message("expected due to this type ascription"),
                    );
                }

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location)
                            .with_message("in this type ascription expression"),
                    );
                }
            }

            ExpectationSource::AscriptionPat { pat_id, ty_expr_id } => {
                let pat = self.m.pats[pat_id].def;
                let ty_expr = &self.m.ty_exprs[ty_expr_id].def;

                if ty_expr.location.has_span() {
                    report.add_label(
                        Label::new(ty_expr.location)
                            .with_message("expected due to this type ascription"),
                    );
                }

                if pat.location.has_span() {
                    report.add_label(
                        Label::new(pat.location).with_message("in this type ascription pattern"),
                    );
                }
            }

            ExpectationSource::FnExprRet(expr_id) => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location)
                            .with_message("expected as this anonymous function's return type"),
                    );
                }
            }

            ExpectationSource::TupleExprElem { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(format!(
                        "expected for this tuple expression to have the type `{}`",
                        self.m.display_ty(ty_id)
                    )));
                }
            }

            ExpectationSource::TuplePatElem { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "expected for this tuple pattern to have the type `{}`",
                        self.m.display_ty(ty_id)
                    )));
                }
            }

            ExpectationSource::RecordExprField { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(format!(
                        "expected for this record expression to have the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::RecordPatField { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "expected for this record pattern to have the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::VariantExprData { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(format!(
                        "expected for this variant expression to have the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::VariantPatData { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "expected for this variant pattern to have the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::Scrutinee {
                scrutinee_expr_id,
                scrutinee_ty_id,
                match_expr_id,
            } => {
                let scrutinee = self.m.exprs[scrutinee_expr_id].def;
                let match_expr = self.m.exprs[match_expr_id].def;

                if scrutinee.location.has_span() {
                    report.add_label(Label::new(scrutinee.location).with_message(format!(
                        "this expression has the type `{}`",
                        self.m.display_ty(scrutinee_ty_id),
                    )));

                    if match_expr.location.has_span() {
                        report.add_label(
                            Label::new(match_expr.location)
                                .with_message("in this match expression"),
                        );
                    }
                }
            }

            ExpectationSource::MatchArmBody {
                first_arm_expr_id,
                ty_id,
                match_expr_id,
            } => {
                let first_arm = self.m.exprs[first_arm_expr_id].def;
                let match_expr = self.m.exprs[match_expr_id].def;

                if first_arm.location.has_span() {
                    report.add_label(Label::new(first_arm.location).with_message(format!(
                        "this arm has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));

                    if match_expr.location.has_span() {
                        report.add_label(
                            Label::new(match_expr.location)
                                .with_message("in this match expression"),
                        );
                    }
                }
            }

            ExpectationSource::ListExprElem {
                first_elem_expr_id,
                ty_id,
                list_expr_id,
            } => {
                let first_elem = self.m.exprs[first_elem_expr_id].def;
                let list_expr = self.m.exprs[list_expr_id].def;

                if first_elem.location.has_span() {
                    report.add_label(Label::new(first_elem.location).with_message(format!(
                        "this element has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));

                    if list_expr.location.has_span() {
                        report.add_label(
                            Label::new(list_expr.location).with_message("in this list expression"),
                        );
                    }
                }
            }

            ExpectationSource::ListPatElem {
                first_elem_pat_id,
                ty_id,
                list_pat_id,
            } => {
                let first_elem = self.m.pats[first_elem_pat_id].def;
                let list_pat = self.m.pats[list_pat_id].def;

                if first_elem.location.has_span() {
                    report.add_label(Label::new(first_elem.location).with_message(format!(
                        "this element has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));

                    if list_pat.location.has_span() {
                        report.add_label(
                            Label::new(list_pat.location).with_message("in this list pattern"),
                        );
                    }
                }
            }

            ExpectationSource::IfCond { expr_id } => {
                let expr = self.m.exprs[expr_id].def;

                if expr.location.has_span() {
                    report.add_label(Label::new(expr.location).with_message(
                        "expected because this is the condition of this `if` expression",
                    ));
                }
            }

            ExpectationSource::IfBranch {
                then_expr_id,
                ty_id,
                if_expr_id,
            } => {
                let then_expr = self.m.exprs[then_expr_id].def;
                let if_expr = self.m.exprs[if_expr_id].def;

                if then_expr.location.has_span() {
                    report.add_label(Label::new(then_expr.location).with_message(format!(
                        "expected because this branch has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));

                    if if_expr.location.has_span() {
                        report.add_label(
                            Label::new(if_expr.location).with_message("in this `if` expression"),
                        );
                    }
                }
            }

            ExpectationSource::Seq {
                semi_location,
                expr_id,
            } => {
                let expr = self.m.exprs[expr_id].def;

                if semi_location.has_span() {
                    report.add_label(
                        Label::new(semi_location)
                            .with_message("expected because it is followed by a semicolon"),
                    );
                }

                if expr.location.has_span() {
                    report.add_label(
                        Label::new(expr.location).with_message("in this sequence expression"),
                    );
                }
            }

            ExpectationSource::LetRecBinding { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                if pat.location.has_span() {
                    report.add_label(Label::new(pat.location).with_message(format!(
                        "this pattern has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::LetBinding {
                init_expr_id,
                ty_id,
            } => {
                let init_expr = self.m.exprs[init_expr_id].def;

                if init_expr.location.has_span() {
                    report.add_label(Label::new(init_expr.location).with_message(format!(
                        "this expression has the type `{}`",
                        self.m.display_ty(ty_id),
                    )));
                }
            }

            ExpectationSource::BinOp { op_location } => {
                if op_location.has_span() {
                    report.add_label(
                        Label::new(op_location)
                            .with_message("expected because it's an operand to this operator"),
                    );
                }
            }
        }

        report
    }

    fn make_expr_ty_error(
        &self,
        expr_id: ExprId,
        ty_id: TyId,
        expected_ty_id: TyId,
        source: ExpectationSource,
    ) -> ReportBuilder<'static, Location> {
        let report = SemaError::UnexpectedTypeForExpression {
            location: self.m.exprs[expr_id].def.location,
            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
            actual_ty: self.m.display_ty(ty_id).to_string(),
        }
        .into_report_builder();

        self.augment_error_with_expectation(report, source)
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
        match &expr.kind {
            ast::ExprKind::Dummy => Ok(()),
            ast::ExprKind::Bool(e) => self.typeck_expr_bool(expr.id, e, expected_ty),
            ast::ExprKind::Unit(e) => self.typeck_expr_unit(expr.id, e, expected_ty),
            ast::ExprKind::Int(e) => self.typeck_expr_int(expr.id, e, expected_ty),
            ast::ExprKind::Address(_) => unimplemented!(),
            ast::ExprKind::Name(e) => self.typeck_expr_name(expr.id, e, expected_ty),
            ast::ExprKind::Field(e) => self.typeck_expr_field(expr.id, e, expected_ty),
            ast::ExprKind::Panic(_) => unimplemented!(),
            ast::ExprKind::Throw(_) => unimplemented!(),
            ast::ExprKind::TryCatch(_) => unimplemented!(),
            ast::ExprKind::TryCast(_) => unimplemented!(),
            ast::ExprKind::Fix(e) => self.typeck_expr_fix(expr.id, e, expected_ty),
            ast::ExprKind::Fold(_) => unimplemented!(),
            ast::ExprKind::Unfold(_) => unimplemented!(),
            ast::ExprKind::Apply(e) => self.typeck_expr_apply(expr.id, e, expected_ty),
            ast::ExprKind::TyApply(_) => unimplemented!(),
            ast::ExprKind::Ascription(e) => self.typeck_expr_ascription(expr.id, e, expected_ty),
            ast::ExprKind::Cast(_) => unimplemented!(),
            ast::ExprKind::Fn(e) => self.typeck_expr_fn(expr.id, e, expected_ty),
            ast::ExprKind::Tuple(e) => self.typeck_expr_tuple(expr.id, e, expected_ty),
            ast::ExprKind::Record(e) => self.typeck_expr_record(expr.id, e, expected_ty),
            ast::ExprKind::Variant(e) => self.typeck_expr_variant(expr.id, e, expected_ty),
            ast::ExprKind::Match(e) => self.typeck_expr_match(expr.id, e, expected_ty),
            ast::ExprKind::List(e) => self.typeck_expr_list(expr.id, e, expected_ty),
            ast::ExprKind::If(e) => self.typeck_expr_if(expr.id, e, expected_ty),
            ast::ExprKind::Seq(e) => self.typeck_expr_seq(expr.id, e, expected_ty),
            ast::ExprKind::Let(e) => self.typeck_expr_let(expr.id, e, expected_ty),
            ast::ExprKind::Generic(_) => unimplemented!(),
            ast::ExprKind::Unary(e) => self.typeck_expr_unary(expr.id, e, expected_ty),
            ast::ExprKind::Binary(e) => self.typeck_expr_binary(expr.id, e, expected_ty),
        }
    }

    fn typeck_expr_bool(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprBool,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.bool, expected_ty_id) {
                self.diag.emit(self.make_expr_ty_error(
                    expr_id,
                    self.m.well_known_tys.bool,
                    expected_ty_id,
                    source,
                ));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = self.m.well_known_tys.bool;

        Ok(())
    }

    fn typeck_expr_unit(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprUnit,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.unit, expected_ty_id) {
                self.diag.emit(self.make_expr_ty_error(
                    expr_id,
                    self.m.well_known_tys.unit,
                    expected_ty_id,
                    source,
                ));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = self.m.well_known_tys.unit;

        Ok(())
    }

    fn typeck_expr_int(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprInt,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.nat, expected_ty_id) {
                self.diag.emit(self.make_expr_ty_error(
                    expr_id,
                    self.m.well_known_tys.unit,
                    expected_ty_id,
                    source,
                ));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = self.m.well_known_tys.nat;

        Ok(())
    }

    fn typeck_expr_name(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprName<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let binding_id = self.m.name_exprs[expr_id];
        let ty_id = self.m.bindings[binding_id].ty_id;

        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ty_id, expected_ty_id) {
                let mut report = self.make_expr_ty_error(expr_id, ty_id, expected_ty_id, source);

                if self.m.bindings[binding_id].location.has_span() {
                    report.add_label(
                        Label::new(self.m.bindings[binding_id].location).with_message(format!(
                            "the binding `{}` is defined here",
                            self.m.bindings[binding_id].name,
                        )),
                    );
                }

                self.diag.emit(report);

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = ty_id;

        Ok(())
    }

    fn typeck_expr_field(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprField<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        self.typeck_expr(&expr.base, None)?;
        let base_ty_id = self.m.exprs[expr.base.id].ty_id;

        if base_ty_id == self.m.well_known_tys.error {
            return Ok(());
        }

        let ty_id = match &expr.field {
            ast::ExprFieldName::Name(name) => {
                if self.are_tys_equivalent(base_ty_id, self.m.well_known_tys.empty_tuple) {
                    self.diag.emit(SemaError::UnexpectedFieldAccess {
                        location: self.m.exprs[expr_id].def.location,
                        field: name.as_str().into(),
                        record_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: name.location(),
                    });

                    return Err(());
                }

                let TyKind::Record(ty) = &self.m.tys[base_ty_id].kind else {
                    self.diag.emit(SemaError::ExtractingFieldOfNonRecordTy {
                        location: self.m.exprs[expr_id].def.location,
                        field: name.as_str().into(),
                        actual_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: name.location(),
                    });

                    return Err(());
                };

                let Some(&idx) = ty.fields.get(name.as_str()) else {
                    self.diag.emit(SemaError::UnexpectedFieldAccess {
                        location: self.m.exprs[expr_id].def.location,
                        field: name.as_str().into(),
                        record_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: name.location(),
                    });

                    return Err(());
                };

                ty.elems[idx].1
            }

            &ast::ExprFieldName::Index(location, idx) => {
                let TyKind::Tuple(ty) = &self.m.tys[base_ty_id].kind else {
                    self.diag.emit(SemaError::IndexingNonTupleTy {
                        location: self.m.exprs[expr_id].def.location,
                        actual_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: location,
                    });

                    return Err(());
                };

                match idx.checked_sub(1).and_then(|idx| ty.elems.get(idx)) {
                    Some(&elem_ty_id) => elem_ty_id,

                    None => {
                        self.diag.emit(SemaError::TupleIndexOutOfBounds {
                            location: self.m.exprs[expr_id].def.location,
                            idx,
                            tuple_len: ty.elems.len(),
                            actual_ty: self.m.display_ty(base_ty_id).to_string(),
                            base_location: expr.base.location,
                            field_location: location,
                        });

                        return Err(());
                    }
                }
            }
        };

        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ty_id, expected_ty_id) {
                self.diag
                    .emit(self.make_expr_ty_error(expr_id, ty_id, expected_ty_id, source));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = ty_id;

        Ok(())
    }

    fn typeck_expr_fix(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprFix<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        self.typeck_expr(&expr.expr, None)?;
        let inner_ty_id = self.m.exprs[expr.expr.id].ty_id;

        if inner_ty_id == self.m.well_known_tys.error {
            return Ok(());
        }

        let TyKind::Fn(inner_ty) = &self.m.tys[inner_ty_id].kind else {
            self.diag.emit(SemaError::FixNotFunction {
                location: self.m.exprs[expr_id].def.location,
                actual_ty: self.m.display_ty(inner_ty_id).to_string(),
                inner_location: expr.expr.location,
            });

            return Err(());
        };

        if inner_ty.params.len() != 1 {
            self.diag.emit(SemaError::FixWrongFunctionParamCount {
                location: self.m.exprs[expr_id].def.location,
                actual_ty: self.m.display_ty(inner_ty_id).to_string(),
                inner_location: expr.expr.location,
            });

            return Err(());
        }

        if !self.are_tys_equivalent(inner_ty.params[0], inner_ty.ret) {
            let expected_ty = self.m.add_ty(Ty {
                kind: TyKind::Fn(TyFn {
                    params: vec![inner_ty.params[0]],
                    ret: inner_ty.params[0],
                }),
            });

            self.diag.emit(self.make_expr_ty_error(
                expr.expr.id,
                inner_ty_id,
                expected_ty,
                ExpectationSource::FixArg(expr_id),
            ));

            return Err(());
        }

        let ty_id = inner_ty.ret;

        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ty_id, expected_ty_id) {
                self.diag
                    .emit(self.make_expr_ty_error(expr_id, ty_id, expected_ty_id, source));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = ty_id;

        Ok(())
    }

    fn typeck_expr_apply(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprApply<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        match &expr.callee {
            ast::Callee::Builtin { kw: _, builtin } => match builtin {
                ast::Builtin::Inl | ast::Builtin::Inr => {
                    let Some((expected_ty_id, source)) = expected_ty else {
                        self.diag.emit(SemaError::AmbiguousSumTypeInExpr {
                            location: self.m.exprs[expr_id].def.location,
                        });

                        return Err(());
                    };

                    if expected_ty_id == self.m.well_known_tys.error {
                        return Ok(());
                    }

                    let TyKind::Sum(lhs_ty_id, rhs_ty_id) = self.m.tys[expected_ty_id].kind else {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaError::UnexpectedInjection {
                                location: self.m.exprs[expr_id].def.location,
                                expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            },
                            source,
                        ));

                        return Err(());
                    };

                    let (is_left, param_ty_id) = if *builtin == ast::Builtin::Inl {
                        (true, lhs_ty_id)
                    } else {
                        (false, rhs_ty_id)
                    };

                    self.typeck_application(
                        expr_id,
                        vec![Some((
                            param_ty_id,
                            ExpectationSource::InjectionArg {
                                expr_id,
                                is_left,
                                sum_ty_id: expected_ty_id,
                            },
                        ))],
                        expected_ty_id,
                        &expr.args,
                        Some((expected_ty_id, source)),
                    )
                }

                ast::Builtin::Cons => {
                    if let Some((expected_ty_id, source)) = expected_ty {
                        if expected_ty_id == self.m.well_known_tys.error {
                            return Ok(());
                        }

                        let TyKind::List(elem_ty_id) = self.m.tys[expected_ty_id].kind else {
                            self.diag.emit(self.augment_error_with_expectation(
                                SemaError::UnexpectedList {
                                    location: self.m.exprs[expr_id].def.location,
                                    expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                                },
                                source,
                            ));

                            return Err(());
                        };

                        self.typeck_application(
                            expr_id,
                            vec![
                                Some((elem_ty_id, source.clone())),
                                Some((expected_ty_id, source.clone())),
                            ],
                            expected_ty_id,
                            &expr.args,
                            Some((expected_ty_id, source)),
                        )
                    } else {
                        self.check_application_arg_count(expr_id, expr.args.len(), 2)?;
                        let mut result = self.typeck_expr(&expr.args[0], None);
                        let elem_ty_id = self.m.exprs[expr.args[0].id].ty_id;
                        let ty_id = self.m.add_ty(Ty {
                            kind: TyKind::List(elem_ty_id),
                        });

                        result = result.and(self.typeck_expr(
                            &expr.args[1],
                            Some((
                                ty_id,
                                ExpectationSource::ConsArg {
                                    expr_id,
                                    arg_expr_id: expr.args[0].id,
                                    elem_ty_id,
                                },
                            )),
                        ));

                        self.m.exprs[expr_id].ty_id = ty_id;

                        result
                    }
                }

                ast::Builtin::ListHead => {
                    if let Some((expected_ty_id, source)) = expected_ty {
                        if expected_ty_id == self.m.well_known_tys.error {
                            return Ok(());
                        }

                        let list_ty_id = self.m.add_ty(Ty {
                            kind: TyKind::List(expected_ty_id),
                        });

                        self.typeck_application(
                            expr_id,
                            vec![Some((
                                list_ty_id,
                                ExpectationSource::BuiltinArg {
                                    expr_id,
                                    builtin: *builtin,
                                },
                            ))],
                            expected_ty_id,
                            &expr.args,
                            Some((expected_ty_id, source)),
                        )
                    } else {
                        self.check_application_arg_count(expr_id, expr.args.len(), 1)?;
                        self.typeck_expr(&expr.args[0], None)?;
                        let arg_ty_id = self.m.exprs[expr.args[0].id].ty_id;

                        let ty_id = if arg_ty_id == self.m.well_known_tys.error {
                            self.m.well_known_tys.error
                        } else if let TyKind::List(elem_ty_id) = self.m.tys[arg_ty_id].kind {
                            elem_ty_id
                        } else {
                            self.diag.emit(SemaError::ExprTyNotList {
                                location: expr.args[0].location,
                                actual_ty: self.m.display_ty(arg_ty_id).to_string(),
                            });

                            return Err(());
                        };

                        self.m.exprs[expr_id].ty_id = ty_id;

                        Ok(())
                    }
                }

                ast::Builtin::ListIsEmpty => {
                    self.check_application_arg_count(expr_id, expr.args.len(), 1)?;
                    self.typeck_expr(&expr.args[0], None)?;
                    let arg_ty_id = self.m.exprs[expr.args[0].id].ty_id;

                    if arg_ty_id == self.m.well_known_tys.error {
                        // ignore.
                    } else if let TyKind::List(_) = self.m.tys[arg_ty_id].kind {
                        // also good.
                    } else {
                        self.diag.emit(SemaError::ExprTyNotList {
                            location: expr.args[0].location,
                            actual_ty: self.m.display_ty(arg_ty_id).to_string(),
                        });

                        return Err(());
                    };

                    if let Some((expected_ty_id, source)) = expected_ty {
                        if !self.ty_conforms_to(self.m.well_known_tys.bool, expected_ty_id) {
                            self.diag.emit(self.make_expr_ty_error(
                                expr_id,
                                self.m.well_known_tys.bool,
                                expected_ty_id,
                                source,
                            ));

                            return Err(());
                        }
                    }

                    self.m.exprs[expr_id].ty_id = self.m.well_known_tys.bool;

                    Ok(())
                }

                ast::Builtin::ListTail => {
                    self.check_application_arg_count(expr_id, expr.args.len(), 1)?;
                    self.typeck_expr(&expr.args[0], None)?;
                    let arg_ty_id = self.m.exprs[expr.args[0].id].ty_id;

                    if arg_ty_id == self.m.well_known_tys.error {
                        // ignore.
                    } else if let TyKind::List(_) = self.m.tys[arg_ty_id].kind {
                        // also good.
                    } else {
                        self.diag.emit(SemaError::ExprTyNotList {
                            location: expr.args[0].location,
                            actual_ty: self.m.display_ty(arg_ty_id).to_string(),
                        });
                    };

                    if let Some((expected_ty_id, source)) = expected_ty {
                        if !self.ty_conforms_to(arg_ty_id, expected_ty_id) {
                            self.diag.emit(self.make_expr_ty_error(
                                expr_id,
                                arg_ty_id,
                                expected_ty_id,
                                source,
                            ));

                            return Err(());
                        }
                    }

                    self.m.exprs[expr_id].ty_id = arg_ty_id;

                    Ok(())
                }

                ast::Builtin::Succ | ast::Builtin::NatPred => self.typeck_application(
                    expr_id,
                    vec![Some((
                        self.m.well_known_tys.nat,
                        ExpectationSource::BuiltinArg {
                            expr_id,
                            builtin: *builtin,
                        },
                    ))],
                    self.m.well_known_tys.nat,
                    &expr.args,
                    expected_ty,
                ),

                ast::Builtin::Not => self.typeck_application(
                    expr_id,
                    vec![Some((
                        self.m.well_known_tys.bool,
                        ExpectationSource::BuiltinArg {
                            expr_id,
                            builtin: *builtin,
                        },
                    ))],
                    self.m.well_known_tys.bool,
                    &expr.args,
                    expected_ty,
                ),

                ast::Builtin::NatIsZero => self.typeck_application(
                    expr_id,
                    vec![Some((
                        self.m.well_known_tys.nat,
                        ExpectationSource::BuiltinArg {
                            expr_id,
                            builtin: *builtin,
                        },
                    ))],
                    self.m.well_known_tys.bool,
                    &expr.args,
                    expected_ty,
                ),

                ast::Builtin::NatRec => {
                    if let Some((expected_ty_id, source)) = expected_ty {
                        if expected_ty_id == self.m.well_known_tys.error {
                            return Ok(());
                        }

                        let inner_fn_ty_id = self.m.add_ty(Ty {
                            kind: TyKind::Fn(TyFn {
                                params: vec![expected_ty_id],
                                ret: expected_ty_id,
                            }),
                        });
                        let fn_ty_id = self.m.add_ty(Ty {
                            kind: TyKind::Fn(TyFn {
                                params: vec![self.m.well_known_tys.nat],
                                ret: inner_fn_ty_id,
                            }),
                        });

                        let arg_source = ExpectationSource::BuiltinArg {
                            expr_id,
                            builtin: *builtin,
                        };

                        self.typeck_application(
                            expr_id,
                            vec![
                                Some((self.m.well_known_tys.nat, arg_source.clone())),
                                Some((expected_ty_id, arg_source.clone())),
                                Some((fn_ty_id, arg_source)),
                            ],
                            expected_ty_id,
                            &expr.args,
                            Some((expected_ty_id, source)),
                        )
                    } else {
                        self.check_application_arg_count(expr_id, expr.args.len(), 3)?;

                        let mut result = self.typeck_expr(
                            &expr.args[0],
                            Some((
                                self.m.well_known_tys.nat,
                                ExpectationSource::BuiltinArg {
                                    expr_id,
                                    builtin: *builtin,
                                },
                            )),
                        );

                        result = result.and(self.typeck_expr(&expr.args[1], None));

                        let z_ty_id = self.m.exprs[expr.args[1].id].ty_id;
                        let inner_fn_ty_id = self.m.add_ty(Ty {
                            kind: TyKind::Fn(TyFn {
                                params: vec![z_ty_id],
                                ret: z_ty_id,
                            }),
                        });
                        let fn_ty_id = self.m.add_ty(Ty {
                            kind: TyKind::Fn(TyFn {
                                params: vec![self.m.well_known_tys.nat],
                                ret: inner_fn_ty_id,
                            }),
                        });

                        result = result.and(self.typeck_expr(
                            &expr.args[2],
                            Some((
                                fn_ty_id,
                                ExpectationSource::BuiltinArg {
                                    expr_id,
                                    builtin: *builtin,
                                },
                            )),
                        ));

                        self.m.exprs[expr_id].ty_id = z_ty_id;

                        result
                    }
                }
            },

            ast::Callee::Expr(callee) => {
                self.typeck_expr(callee, None)?;
                let callee_ty_id = self.m.exprs[callee.id].ty_id;

                if callee_ty_id == self.m.well_known_tys.error {
                    return Err(());
                }

                let TyKind::Fn(callee_ty) = &self.m.tys[callee_ty_id].kind else {
                    self.diag.emit(SemaError::ApplyNotFunction {
                        location: self.m.exprs[expr_id].def.location,
                        actual_ty: self.m.display_ty(callee_ty_id).to_string(),
                        callee_location: callee.location,
                    });

                    return Err(());
                };

                self.typeck_application(
                    expr_id,
                    callee_ty
                        .params
                        .iter()
                        .enumerate()
                        .map(|(arg_idx, &param_ty_id)| {
                            Some((
                                param_ty_id,
                                ExpectationSource::FnArg {
                                    expr_id,
                                    callee_expr_id: callee.id,
                                    arg_idx,
                                    callee_ty_id,
                                },
                            ))
                        })
                        .collect(),
                    callee_ty.ret,
                    &expr.args,
                    expected_ty,
                )
            }
        }
    }

    fn typeck_application(
        &mut self,
        expr_id: ExprId,
        param_ty_ids: Vec<Option<ExpectedTy>>,
        ret_ty_id: TyId,
        args: &[ast::Expr<'ast>],
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ret_ty_id, expected_ty_id) {
                self.diag
                    .emit(self.make_expr_ty_error(expr_id, ret_ty_id, expected_ty_id, source));

                return Err(());
            }
        }

        let mut result = self.check_application_arg_count(expr_id, args.len(), param_ty_ids.len());
        let mut param_iter = param_ty_ids.into_iter();

        for arg in args {
            result = result.and(self.typeck_expr(arg, param_iter.next().flatten()));
        }

        self.m.exprs[expr_id].ty_id = ret_ty_id;

        result
    }

    fn check_application_arg_count(
        &mut self,
        expr_id: ExprId,
        arg_count: usize,
        expected: usize,
    ) -> Result {
        if arg_count != expected {
            self.diag.emit(SemaError::IncorrectNumberOfArgumentsInExpr {
                location: self.m.exprs[expr_id].def.location,
                expected,
                actual: arg_count,
            });

            Err(())
        } else {
            Ok(())
        }
    }

    fn typeck_expr_ascription(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprAscription<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = self.typeck_ty_expr(&expr.ty_expr);
        let ty_id = self.m.ty_exprs[expr.ty_expr.id].ty_id;

        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ty_id, expected_ty_id) {
                self.diag
                    .emit(self.make_expr_ty_error(expr_id, ty_id, expected_ty_id, source));

                return Err(());
            }
        }

        result = result.and(self.typeck_expr(
            &expr.expr,
            Some((
                ty_id,
                ExpectationSource::AscriptionExpr {
                    expr_id,
                    ty_expr_id: expr.ty_expr.id,
                },
            )),
        ));

        self.m.exprs[expr_id].ty_id = ty_id;

        result
    }

    fn typeck_expr_fn(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprFn<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if expected_ty_id == self.m.well_known_tys.error {
                return Ok(());
            }

            let TyKind::Fn(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedLambda {
                        location: self.m.exprs[expr_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                self.typeck_expr_fn(expr_id, expr, None)?;

                return Err(());
            };

            if ty.params.len() != expr.params.len() {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedNumberOfParametersInLambda {
                        location: self.m.exprs[expr_id].def.location,
                        actual: expr.params.len(),
                        expected: ty.params.len(),
                    },
                    source,
                ));

                self.typeck_expr_fn(expr_id, expr, None)?;

                return Err(());
            }

            let ret_ty_id = ty.ret;
            let mut result = Ok(());

            for (param, expected_param_ty_id) in expr.params.iter().zip(ty.params.clone()) {
                result = result.and(self.typeck_ty_expr(&param.ty_expr));
                let param_ty_id = self.m.ty_exprs[param.ty_expr.id].ty_id;
                self.m.bindings[param.binding.id].ty_id = param_ty_id;

                if !self.ty_conforms_to(expected_param_ty_id, param_ty_id) {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedTypeForParameter {
                            location: param.binding.location(),
                            name: param.binding.name.as_str().into(),
                            expected_ty: self.m.display_ty(expected_param_ty_id).to_string(),
                            actual_ty: self.m.display_ty(param_ty_id).to_string(),
                            expr_location: self.m.exprs[expr_id].def.location,
                        },
                        source.clone(),
                    ));

                    result = Err(());
                }
            }

            result = result.and(self.typeck_expr(
                &expr.body.ret,
                Some((ret_ty_id, ExpectationSource::FnExprRet(expr_id))),
            ));

            self.m.exprs[expr_id].ty_id = expected_ty_id;

            result
        } else {
            let mut result = Ok(());
            let mut param_ty_ids = Vec::with_capacity(expr.params.len());

            for param in &expr.params {
                result = result.and(self.typeck_ty_expr(&param.ty_expr));
                let param_ty_id = self.m.ty_exprs[param.ty_expr.id].ty_id;
                self.m.bindings[param.binding.id].ty_id = param_ty_id;
                param_ty_ids.push(param_ty_id);
            }

            result = result.and(self.typeck_expr(&expr.body.ret, None));
            let ret_ty_id = self.m.exprs[expr.body.ret.id].ty_id;

            self.m.exprs[expr_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::Fn(TyFn {
                    params: param_ty_ids,
                    ret: ret_ty_id,
                }),
            });

            result
        }
    }

    fn typeck_expr_tuple(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprTuple<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if expected_ty_id == self.m.well_known_tys.error {
                return self.typeck_expr_tuple(expr_id, expr, None);
            }

            let TyKind::Tuple(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedTuple {
                        location: self.m.exprs[expr_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));
                self.typeck_expr_tuple(expr_id, expr, None)?;

                return Err(());
            };

            if expr.elems.len() != ty.elems.len() {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedTupleLengthInExpr {
                        location: self.m.exprs[expr_id].def.location,
                        actual: expr.elems.len(),
                        expected: ty.elems.len(),
                    },
                    source,
                ));
                self.typeck_expr_tuple(expr_id, expr, None)?;

                return Err(());
            }

            let mut result = Ok(());

            for (elem, expected_elem_ty_id) in expr.elems.iter().zip(ty.elems.clone()) {
                result = result.and(self.typeck_expr(
                    elem,
                    Some((
                        expected_elem_ty_id,
                        ExpectationSource::TupleExprElem {
                            expr_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }

            self.m.exprs[expr_id].ty_id = expected_ty_id;

            result
        } else {
            let mut result = Ok(());
            let mut elem_ty_ids = Vec::with_capacity(expr.elems.len());

            for elem in &expr.elems {
                result = result.and(self.typeck_expr(elem, None));
                elem_ty_ids.push(self.m.exprs[elem.id].ty_id);
            }

            self.m.exprs[expr_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::Tuple(TyTuple { elems: elem_ty_ids }),
            });

            result
        }
    }

    fn typeck_expr_record(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprRecord<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if expected_ty_id == self.m.well_known_tys.error {
                return self.typeck_expr_record(expr_id, expr, None);
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) if ty.elems.is_empty() => &TyRecord::new(vec![]),
                TyKind::Record(ty) => ty,

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedRecord {
                            location: self.m.exprs[expr_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));
                    self.typeck_expr_record(expr_id, expr, None)?;

                    return Err(());
                }
            };

            let mut result = Ok(());
            let required_fields = ty
                .fields
                .keys()
                .map(|s| s.as_str())
                .collect::<FxHashSet<_>>();
            let provided_fields = expr
                .fields
                .iter()
                .map(|field| field.name.as_str())
                .collect::<FxHashSet<_>>();
            let provided_fields_by_name = expr
                .fields
                .iter()
                .map(|field| (field.name.as_str(), field))
                .collect::<FxHashMap<_, _>>();

            for name in required_fields.difference(&provided_fields).copied() {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::MissingRecordFieldInExpr {
                        location: self.m.exprs[expr_id].def.location,
                        name: name.into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source.clone(),
                ));
            }

            for name in provided_fields.difference(&required_fields).copied() {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedRecordFieldInExpr {
                        location: provided_fields_by_name[name].name.location(),
                        name: name.into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        expr_location: self.m.exprs[expr_id].def.location,
                    },
                    source.clone(),
                ));
            }

            result?;

            let expected_field_ty_ids = ty
                .fields
                .iter()
                .map(|(name, &idx)| {
                    (
                        // so that the name does not depend on `self`
                        provided_fields_by_name[name.as_str()].name.as_str(),
                        ty.elems[idx].1,
                    )
                })
                .collect::<FxHashMap<_, _>>();

            for (name, expected_field_ty_id) in expected_field_ty_ids {
                result = result.and(self.typeck_expr(
                    &provided_fields_by_name[name].expr,
                    Some((
                        expected_field_ty_id,
                        ExpectationSource::RecordExprField {
                            expr_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }

            self.m.exprs[expr_id].ty_id = expected_ty_id;

            result
        } else {
            let mut result = Ok(());
            let mut elems = Vec::with_capacity(expr.fields.len());

            for field in &expr.fields {
                result = result.and(self.typeck_expr(&field.expr, None));
                elems.push((
                    field.name.as_str().to_owned(),
                    self.m.exprs[field.expr.id].ty_id,
                ));
            }

            self.m.exprs[expr_id].ty_id = if elems.is_empty() {
                self.m.well_known_tys.empty_tuple
            } else {
                self.m.add_ty(Ty {
                    kind: TyKind::Record(TyRecord::new(elems)),
                })
            };

            result
        }
    }

    fn typeck_expr_variant(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprVariant<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, source)) = expected_ty else {
            self.diag.emit(SemaError::AmbiguousVariantExprType {
                location: self.m.exprs[expr_id].def.location,
            });

            return Err(());
        };

        if expected_ty_id == self.m.well_known_tys.error {
            return Ok(());
        }

        let TyKind::Variant(ty) = &self.m.tys[expected_ty_id].kind else {
            self.diag.emit(self.augment_error_with_expectation(
                SemaError::UnexpectedVariant {
                    location: self.m.exprs[expr_id].def.location,
                    expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                },
                source,
            ));

            return Err(());
        };

        let Some(&idx) = ty.labels.get(expr.label.as_str()) else {
            self.diag.emit(self.augment_error_with_expectation(
                SemaError::UnexpectedVariantLabelInExpr {
                    location: expr.label.location(),
                    name: expr.label.as_str().into(),
                    expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    expr_location: self.m.exprs[expr_id].def.location,
                },
                source,
            ));

            return Err(());
        };

        let label_ty_id = ty.elems[idx].1;
        let mut result = Ok(());

        match (&expr.expr, label_ty_id) {
            (Some(inner), Some(label_ty_id)) => {
                result = result.and(self.typeck_expr(
                    inner,
                    Some((
                        label_ty_id,
                        ExpectationSource::VariantExprData {
                            expr_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }

            (None, None) => {}

            (Some(_), None) => {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedDataForNullaryLabel {
                        location: expr.label.location(),
                        name: expr.label.as_str().into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        expr_location: self.m.exprs[expr_id].def.location,
                    },
                    source,
                ));
            }

            (None, Some(_)) => {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::MissingDataForLabel {
                        location: expr.label.location(),
                        name: expr.label.as_str().into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        expr_location: self.m.exprs[expr_id].def.location,
                    },
                    source,
                ));
            }
        }

        self.m.exprs[expr_id].ty_id = expected_ty_id;

        result
    }

    fn typeck_expr_match(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprMatch<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = self.typeck_expr(&expr.expr, None);

        // all types are inhabited, so there must be at least one branch.
        if expr.arms.is_empty() {
            self.diag.emit(SemaError::IllegalEmptyMatching {
                location: self.m.exprs[expr_id].def.location,
            });

            return Err(());
        }

        let scrutinee_ty_id = self.m.exprs[expr.expr.id].ty_id;
        result = result.and(self.typeck_pat(
            &expr.arms[0].pat,
            Some((
                scrutinee_ty_id,
                ExpectationSource::Scrutinee {
                    scrutinee_expr_id: expr.expr.id,
                    scrutinee_ty_id,
                    match_expr_id: expr_id,
                },
            )),
        ));
        result = result.and(self.typeck_expr(&expr.arms[0].body, expected_ty.clone()));
        let expected_ty = expected_ty.unwrap_or_else(|| {
            (
                self.m.exprs[expr.arms[0].body.id].ty_id,
                ExpectationSource::MatchArmBody {
                    first_arm_expr_id: expr.arms[0].body.id,
                    ty_id: self.m.exprs[expr.arms[0].body.id].ty_id,
                    match_expr_id: expr_id,
                },
            )
        });

        for arm in expr.arms.iter().skip(1) {
            result = result.and(self.typeck_pat(
                &arm.pat,
                Some((
                    scrutinee_ty_id,
                    ExpectationSource::Scrutinee {
                        scrutinee_expr_id: expr.expr.id,
                        scrutinee_ty_id,
                        match_expr_id: expr_id,
                    },
                )),
            ));

            result = result.and(self.typeck_expr(&arm.body, Some(expected_ty.clone())));
        }

        self.m.exprs[expr_id].ty_id = expected_ty.0;

        result
    }

    fn typeck_expr_list(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprList<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            let elem_ty_id = if expected_ty_id == self.m.well_known_tys.error {
                self.m.well_known_tys.error
            } else {
                let TyKind::List(ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedList {
                            location: self.m.exprs[expr_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));
                    self.typeck_expr_list(expr_id, expr, None)?;

                    return Err(());
                };

                ty_id
            };

            let mut result = Ok(());

            for elem in &expr.elems {
                result = result.and(self.typeck_expr(elem, Some((elem_ty_id, source.clone()))));
            }

            self.m.exprs[expr_id].ty_id = expected_ty_id;

            result
        } else if expr.elems.is_empty() {
            self.diag.emit(SemaError::AmbiguousEmptyListExprTy {
                location: self.m.exprs[expr_id].def.location,
            });

            Err(())
        } else {
            let mut result = Ok(());
            result = result.and(self.typeck_expr(&expr.elems[0], None));
            let elem_ty_id = self.m.exprs[expr.elems[0].id].ty_id;

            for elem in expr.elems.iter().skip(1) {
                result = result.and(self.typeck_expr(
                    elem,
                    Some((
                        elem_ty_id,
                        ExpectationSource::ListExprElem {
                            first_elem_expr_id: expr.elems[0].id,
                            ty_id: elem_ty_id,
                            list_expr_id: expr_id,
                        },
                    )),
                ));
            }

            self.m.exprs[expr_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::List(elem_ty_id),
            });

            result
        }
    }

    fn typeck_expr_if(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprIf<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = self.typeck_expr(
            &expr.cond,
            Some((
                self.m.well_known_tys.bool,
                ExpectationSource::IfCond { expr_id },
            )),
        );
        result = result.and(self.typeck_expr(&expr.then_expr, expected_ty.clone()));

        let expected_ty = expected_ty.unwrap_or_else(|| {
            let ty_id = self.m.exprs[expr.then_expr.id].ty_id;
            (
                ty_id,
                ExpectationSource::IfBranch {
                    then_expr_id: expr.then_expr.id,
                    ty_id,
                    if_expr_id: expr_id,
                },
            )
        });
        let ty_id = expected_ty.0;
        result = result.and(self.typeck_expr(&expr.else_expr, Some(expected_ty)));

        self.m.exprs[expr_id].ty_id = ty_id;

        result
    }

    fn typeck_expr_seq(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprSeq<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let ((last_expr, _), unit_exprs) = expr.exprs.split_last().unwrap();
        let mut result = Ok(());

        for (unit_expr, semi) in unit_exprs {
            result = result.and(self.typeck_expr(
                unit_expr,
                Some((
                    self.m.well_known_tys.unit,
                    ExpectationSource::Seq {
                        semi_location: semi.as_ref().map(|token| token.span).into(),
                        expr_id,
                    },
                )),
            ));
        }

        /*
        // this is how it works in rust. I guess it's not how it works in Stella. weird.
        if last_semi.is_some() {
            if let Some((expected_ty_id, source)) = expected_ty {
                if !self.ty_conforms_to(self.m.well_known_tys.unit, expected_ty_id) {
                    self.diag.emit(self.make_expr_ty_error(
                        expr_id,
                        self.m.well_known_tys.unit,
                        expected_ty_id,
                        source,
                    ));

                    result = Err(());
                }
            }

            result = result.and(self.typeck_expr(
                last_expr,
                Some((
                    self.m.well_known_tys.unit,
                    ExpectationSource::Seq {
                        semi_location: last_semi.as_ref().unwrap().span.into(),
                        expr_id,
                    },
                )),
            ));

            self.m.exprs[expr_id].ty_id = self.m.well_known_tys.unit;

            result
        } else {*/

        result = result.and(self.typeck_expr(last_expr, expected_ty));
        self.m.exprs[expr_id].ty_id = self.m.exprs[last_expr.id].ty_id;

        result

        /*}*/
    }

    fn typeck_expr_let(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprLet<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = Ok(());

        if expr.rec {
            // typeck all the bindings first. they may require ascriptions.
            for binding in &expr.bindings {
                result = result.and(self.typeck_pat(&binding.pat, None));
            }

            // now that all the bindings have known types, we can check the initializers.
            for binding in &expr.bindings {
                let expected_ty_id = self.m.pats[binding.pat.id].ty_id;
                result = result.and(self.typeck_expr(
                    &binding.expr,
                    Some((
                        expected_ty_id,
                        ExpectationSource::LetRecBinding {
                            pat_id: binding.pat.id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }
        } else {
            for binding in &expr.bindings {
                result = result.and(self.typeck_expr(&binding.expr, None));
                let expected_ty_id = self.m.exprs[binding.expr.id].ty_id;
                result = result.and(self.typeck_pat(
                    &binding.pat,
                    Some((
                        expected_ty_id,
                        ExpectationSource::LetBinding {
                            init_expr_id: binding.expr.id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }
        }

        result = result.and(self.typeck_expr(&expr.body, expected_ty));
        self.m.exprs[expr_id].ty_id = self.m.exprs[expr.body.id].ty_id;

        result
    }

    fn typeck_expr_unary(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprUnary<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let _ = expr_id;
        let _ = expected_ty;

        match expr.op {
            ast::UnOp::New => unimplemented!(),
            ast::UnOp::Deref => unimplemented!(),
        }
    }

    fn typeck_expr_binary(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprBinary<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = Ok(());

        match expr.op {
            ast::BinOp::Add | ast::BinOp::Sub | ast::BinOp::Mul | ast::BinOp::Div => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    if !self.ty_conforms_to(self.m.well_known_tys.nat, expected_ty_id) {
                        result = Err(());
                        self.diag.emit(self.make_expr_ty_error(
                            expr_id,
                            self.m.well_known_tys.nat,
                            expected_ty_id,
                            source,
                        ));
                    }
                }

                let operand_source = ExpectationSource::BinOp {
                    op_location: expr.token.as_ref().map(|token| token.span).into(),
                };
                result = result.and(self.typeck_expr(
                    &expr.lhs,
                    Some((self.m.well_known_tys.nat, operand_source.clone())),
                ));
                result = result.and(self.typeck_expr(
                    &expr.rhs,
                    Some((self.m.well_known_tys.nat, operand_source.clone())),
                ));

                self.m.exprs[expr_id].ty_id = self.m.well_known_tys.nat;

                result
            }

            ast::BinOp::And | ast::BinOp::Or => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    if !self.ty_conforms_to(self.m.well_known_tys.bool, expected_ty_id) {
                        result = Err(());
                        self.diag.emit(self.make_expr_ty_error(
                            expr_id,
                            self.m.well_known_tys.bool,
                            expected_ty_id,
                            source,
                        ));
                    }
                }

                let operand_source = ExpectationSource::BinOp {
                    op_location: expr.token.as_ref().map(|token| token.span).into(),
                };
                result = result.and(self.typeck_expr(
                    &expr.lhs,
                    Some((self.m.well_known_tys.bool, operand_source.clone())),
                ));
                result = result.and(self.typeck_expr(
                    &expr.rhs,
                    Some((self.m.well_known_tys.bool, operand_source.clone())),
                ));

                self.m.exprs[expr_id].ty_id = self.m.well_known_tys.bool;

                result
            }

            ast::BinOp::Lt
            | ast::BinOp::Le
            | ast::BinOp::Gt
            | ast::BinOp::Ge
            // equality is only defined for Nat, though I'd expect Bools there as well....
            | ast::BinOp::Eq
            | ast::BinOp::Ne => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    if !self.ty_conforms_to(self.m.well_known_tys.bool, expected_ty_id) {
                        result = Err(());
                        self.diag.emit(self.make_expr_ty_error(
                            expr_id,
                            self.m.well_known_tys.bool,
                            expected_ty_id,
                            source,
                        ));
                    }
                }

                let operand_source = ExpectationSource::BinOp {
                    op_location: expr.token.as_ref().map(|token| token.span).into(),
                };
                result = result.and(self.typeck_expr(
                    &expr.lhs,
                    Some((self.m.well_known_tys.nat, operand_source.clone())),
                ));
                result = result.and(self.typeck_expr(
                    &expr.rhs,
                    Some((self.m.well_known_tys.nat, operand_source.clone())),
                ));

                self.m.exprs[expr_id].ty_id = self.m.well_known_tys.bool;

                result
            }

            ast::BinOp::Assign => unimplemented!(),
        }
    }

    fn typeck_pat(&mut self, pat: &ast::Pat<'ast>, expected_ty: Option<ExpectedTy>) -> Result {
        match &pat.kind {
            ast::PatKind::Dummy => Ok(()),
            ast::PatKind::Variant(p) => self.typeck_pat_variant(pat.id, p, expected_ty),
            ast::PatKind::Cons(p) => self.typeck_pat_cons(pat.id, p, expected_ty),
            ast::PatKind::Tuple(p) => self.typeck_pat_tuple(pat.id, p, expected_ty),
            ast::PatKind::Record(p) => self.typeck_pat_record(pat.id, p, expected_ty),
            ast::PatKind::List(p) => self.typeck_pat_list(pat.id, p, expected_ty),
            ast::PatKind::Bool(p) => self.typeck_pat_bool(pat.id, p, expected_ty),
            ast::PatKind::Unit(p) => self.typeck_pat_unit(pat.id, p, expected_ty),
            ast::PatKind::Int(p) => self.typeck_pat_int(pat.id, p, expected_ty),
            ast::PatKind::Name(p) => self.typeck_pat_name(pat.id, p, expected_ty),
            ast::PatKind::Ascription(p) => self.typeck_pat_ascription(pat.id, p, expected_ty),
            ast::PatKind::Cast(_) => unimplemented!(),
        }
    }

    fn typeck_pat_variant(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatVariant<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, source)) = expected_ty else {
            self.diag.emit(SemaError::AmbiguousVariantPatType {
                location: self.m.pats[pat_id].def.location,
            });

            return Err(());
        };

        if expected_ty_id == self.m.well_known_tys.error {
            return Ok(());
        }

        let TyKind::Variant(ty) = &self.m.tys[expected_ty_id].kind else {
            self.diag.emit(self.augment_error_with_expectation(
                SemaError::UnexpectedPatternForType {
                    location: self.m.pats[pat_id].def.location,
                    expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                },
                source,
            ));

            return Err(());
        };

        let Some(&idx) = ty.labels.get(pat.label.as_str()) else {
            self.diag.emit(self.augment_error_with_expectation(
                SemaError::UnexpectedVariantLabelInPat {
                    location: pat.label.location(),
                    name: pat.label.as_str().into(),
                    expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    pat_location: self.m.pats[pat_id].def.location,
                },
                source,
            ));

            return Err(());
        };

        let label_ty_id = ty.elems[idx].1;

        match (&pat.pat, label_ty_id) {
            (Some(inner), Some(label_ty_id)) => {
                self.typeck_pat(
                    inner,
                    Some((
                        label_ty_id,
                        ExpectationSource::VariantPatData {
                            pat_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                )?;
            }

            (None, None) => {}

            (Some(_), None) => {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedNonNullaryVariantPattern {
                        location: pat.label.location(),
                        name: pat.label.as_str().into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        pat_location: self.m.pats[pat_id].def.location,
                    },
                    source,
                ));

                return Err(());
            }

            (None, Some(_)) => {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedNullaryVariantPattern {
                        location: pat.label.location(),
                        name: pat.label.as_str().into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        pat_location: self.m.pats[pat_id].def.location,
                    },
                    source,
                ));

                return Err(());
            }
        }

        self.m.pats[pat_id].ty_id = expected_ty_id;

        Ok(())
    }

    fn typeck_pat_cons(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatCons<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        match pat.cons {
            ast::Cons::Inl | ast::Cons::Inr => {
                let Some((expected_ty_id, source)) = expected_ty else {
                    self.diag.emit(SemaError::AmbiguousSumTypeInPat {
                        location: self.m.pats[pat_id].def.location,
                    });

                    return Err(());
                };

                if expected_ty_id == self.m.well_known_tys.error {
                    return Ok(());
                }

                let TyKind::Sum(lhs_ty_id, rhs_ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedPatternForType {
                            location: self.m.pats[pat_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));

                    return Err(());
                };

                let (is_left, inner_ty_id) = if pat.cons == ast::Cons::Inl {
                    (true, lhs_ty_id)
                } else {
                    (false, rhs_ty_id)
                };

                self.check_pat_cons_arg_count(pat_id, pat.args.len(), 1)?;

                let result = self.typeck_pat(
                    &pat.args[0],
                    Some((
                        inner_ty_id,
                        ExpectationSource::InjectionPat {
                            pat_id,
                            is_left,
                            sum_ty_id: expected_ty_id,
                        },
                    )),
                );

                self.m.pats[pat_id].ty_id = expected_ty_id;

                result
            }

            ast::Cons::Cons => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    if expected_ty_id == self.m.well_known_tys.error {
                        return Ok(());
                    }

                    let TyKind::List(elem_ty_id) = self.m.tys[expected_ty_id].kind else {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaError::UnexpectedPatternForType {
                                location: self.m.pats[pat_id].def.location,
                                expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            },
                            source,
                        ));

                        return Err(());
                    };

                    self.check_pat_cons_arg_count(pat_id, pat.args.len(), 2)?;

                    let mut result =
                        self.typeck_pat(&pat.args[0], Some((elem_ty_id, source.clone())));
                    result = result
                        .and(self.typeck_pat(&pat.args[1], Some((expected_ty_id, source.clone()))));

                    self.m.pats[pat_id].ty_id = expected_ty_id;

                    result
                } else {
                    self.check_pat_cons_arg_count(pat_id, pat.args.len(), 2)?;
                    let mut result = self.typeck_pat(&pat.args[0], None);
                    let elem_ty_id = self.m.pats[pat.args[0].id].ty_id;
                    let ty_id = self.m.add_ty(Ty {
                        kind: TyKind::List(elem_ty_id),
                    });

                    result = result.and(self.typeck_pat(
                        &pat.args[1],
                        Some((
                            ty_id,
                            ExpectationSource::ConsPat {
                                pat_id,
                                arg_pat_id: pat.args[0].id,
                                elem_ty_id,
                            },
                        )),
                    ));

                    self.m.pats[pat_id].ty_id = ty_id;

                    result
                }
            }

            ast::Cons::Succ => {
                self.check_pat_cons_arg_count(pat_id, pat.args.len(), 1)?;
                let mut result = Ok(());

                if let Some((expected_ty_id, source)) = expected_ty {
                    if !self.ty_conforms_to(self.m.well_known_tys.nat, expected_ty_id) {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaError::UnexpectedPatternForType {
                                location: self.m.pats[pat_id].def.location,
                                expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            },
                            source,
                        ));

                        result = Err(());
                    }
                }

                result = result.and(self.typeck_pat(
                    &pat.args[0],
                    Some((
                        self.m.well_known_tys.nat,
                        ExpectationSource::BuiltinConsPat {
                            pat_id,
                            cons: pat.cons,
                        },
                    )),
                ));

                self.m.pats[pat_id].ty_id = self.m.well_known_tys.nat;

                result
            }
        }
    }

    fn check_pat_cons_arg_count(
        &mut self,
        pat_id: PatId,
        arg_count: usize,
        expected: usize,
    ) -> Result {
        if arg_count != expected {
            self.diag.emit(SemaError::IncorrectNumberOfArgumentsInPat {
                location: self.m.pats[pat_id].def.location,
                expected,
                actual: arg_count,
            });

            Err(())
        } else {
            Ok(())
        }
    }

    fn typeck_pat_tuple(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatTuple<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if expected_ty_id == self.m.well_known_tys.error {
                return Ok(());
            }

            let TyKind::Tuple(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedPatternForType {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            };

            if pat.elems.len() != ty.elems.len() {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedTupleLengthInPat {
                        location: self.m.pats[pat_id].def.location,
                        actual: pat.elems.len(),
                        expected: ty.elems.len(),
                    },
                    source,
                ));

                return Err(());
            }

            let mut result = Ok(());

            for (elem, expected_elem_ty_id) in pat.elems.iter().zip(ty.elems.clone()) {
                result = result.and(self.typeck_pat(
                    elem,
                    Some((
                        expected_elem_ty_id,
                        ExpectationSource::TuplePatElem {
                            pat_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }

            self.m.pats[pat_id].ty_id = expected_ty_id;

            result
        } else {
            let mut result = Ok(());
            let mut elem_ty_ids = Vec::with_capacity(pat.elems.len());

            for elem in &pat.elems {
                result = result.and(self.typeck_pat(elem, None));
                elem_ty_ids.push(self.m.pats[elem.id].ty_id);
            }

            self.m.pats[pat_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::Tuple(TyTuple { elems: elem_ty_ids }),
            });

            result
        }
    }

    fn typeck_pat_record(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatRecord<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if expected_ty_id == self.m.well_known_tys.error {
                return Ok(());
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) if ty.elems.is_empty() => &TyRecord::new(vec![]),
                TyKind::Record(ty) => ty,

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedPatternForType {
                            location: self.m.pats[pat_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));

                    return Err(());
                }
            };

            let mut result = Ok(());
            let required_fields = ty
                .fields
                .keys()
                .map(|s| s.as_str())
                .collect::<FxHashSet<_>>();
            let provided_fields = pat
                .fields
                .iter()
                .map(|field| field.name.as_str())
                .collect::<FxHashSet<_>>();
            let provided_fields_by_name = pat
                .fields
                .iter()
                .map(|field| (field.name.as_str(), field))
                .collect::<FxHashMap<_, _>>();

            for name in required_fields.difference(&provided_fields).copied() {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::MissingRecordFieldInPat {
                        location: self.m.pats[pat_id].def.location,
                        name: name.into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source.clone(),
                ));
            }

            for name in provided_fields.difference(&required_fields).copied() {
                result = Err(());
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedRecordFieldInPat {
                        location: provided_fields_by_name[name].name.location(),
                        name: name.into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        pat_location: self.m.pats[pat_id].def.location,
                    },
                    source.clone(),
                ));
            }

            result?;

            let expected_field_ty_ids = ty
                .fields
                .iter()
                .map(|(name, &idx)| {
                    (
                        provided_fields_by_name[name.as_str()].name.as_str(),
                        ty.elems[idx].1,
                    )
                })
                .collect::<FxHashMap<_, _>>();

            for (name, expected_field_ty_id) in expected_field_ty_ids {
                result = result.and(self.typeck_pat(
                    &provided_fields_by_name[name].pat,
                    Some((
                        expected_field_ty_id,
                        ExpectationSource::RecordPatField {
                            pat_id,
                            ty_id: expected_ty_id,
                        },
                    )),
                ));
            }

            self.m.pats[pat_id].ty_id = expected_ty_id;

            result
        } else {
            let mut result = Ok(());
            let mut elems = Vec::with_capacity(pat.fields.len());

            for field in &pat.fields {
                result = result.and(self.typeck_pat(&field.pat, None));
                elems.push((
                    field.name.as_str().to_owned(),
                    self.m.pats[field.pat.id].ty_id,
                ));
            }

            self.m.pats[pat_id].ty_id = if elems.is_empty() {
                self.m.well_known_tys.empty_tuple
            } else {
                self.m.add_ty(Ty {
                    kind: TyKind::Record(TyRecord::new(elems)),
                })
            };

            result
        }
    }

    fn typeck_pat_list(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatList<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            let elem_ty_id = if expected_ty_id == self.m.well_known_tys.error {
                self.m.well_known_tys.error
            } else {
                let TyKind::List(ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaError::UnexpectedPatternForType {
                            location: self.m.pats[pat_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));

                    return Err(());
                };

                ty_id
            };

            let mut result = Ok(());

            for elem in &pat.elems {
                result = result.and(self.typeck_pat(elem, Some((elem_ty_id, source.clone()))));
            }

            self.m.pats[pat_id].ty_id = expected_ty_id;

            result
        } else if pat.elems.is_empty() {
            self.diag.emit(SemaError::AmbiguousEmptyListPatTy {
                location: self.m.pats[pat_id].def.location,
            });

            Err(())
        } else {
            let mut result = Ok(());
            result = result.and(self.typeck_pat(&pat.elems[0], None));
            let elem_ty_id = self.m.pats[pat.elems[0].id].ty_id;

            for elem in pat.elems.iter().skip(1) {
                result = result.and(self.typeck_pat(
                    elem,
                    Some((
                        elem_ty_id,
                        ExpectationSource::ListPatElem {
                            first_elem_pat_id: pat.elems[0].id,
                            ty_id: elem_ty_id,
                            list_pat_id: pat_id,
                        },
                    )),
                ));
            }

            self.m.pats[pat_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::List(elem_ty_id),
            });

            result
        }
    }

    fn typeck_pat_bool(
        &mut self,
        pat_id: PatId,
        _pat: &ast::PatBool,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.bool, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedPatternForType {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            }
        }

        self.m.pats[pat_id].ty_id = self.m.well_known_tys.bool;

        Ok(())
    }

    fn typeck_pat_unit(
        &mut self,
        pat_id: PatId,
        _pat: &ast::PatUnit,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.unit, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedPatternForType {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            }
        }

        self.m.pats[pat_id].ty_id = self.m.well_known_tys.unit;

        Ok(())
    }

    fn typeck_pat_int(
        &mut self,
        pat_id: PatId,
        _pat: &ast::PatInt,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(self.m.well_known_tys.nat, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedPatternForType {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            }
        }

        self.m.pats[pat_id].ty_id = self.m.well_known_tys.nat;

        Ok(())
    }

    fn typeck_pat_name(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatName<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, _source)) = expected_ty else {
            self.diag.emit(SemaError::AmbiguousBindingPatType {
                location: self.m.pats[pat_id].def.location,
            });

            return Err(());
        };

        self.m.bindings[pat.binding.id].ty_id = expected_ty_id;
        self.m.pats[pat_id].ty_id = expected_ty_id;

        Ok(())
    }

    fn typeck_pat_ascription(
        &mut self,
        pat_id: PatId,
        pat: &ast::PatAscription<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = self.typeck_ty_expr(&pat.ty_expr);
        let ty_id = self.m.ty_exprs[pat.ty_expr.id].ty_id;

        if let Some((expected_ty_id, source)) = expected_ty {
            if !self.ty_conforms_to(ty_id, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaError::UnexpectedPatternForType {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            }
        }

        result = result.and(self.typeck_pat(
            &pat.pat,
            Some((
                ty_id,
                ExpectationSource::AscriptionPat {
                    pat_id,
                    ty_expr_id: pat.ty_expr.id,
                },
            )),
        ));

        self.m.pats[pat_id].ty_id = ty_id;

        result
    }
}
