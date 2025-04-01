use std::cmp::Ordering;
use std::fmt::Write;
use std::mem;

use fxhash::{FxHashMap, FxHashSet};

use crate::ast;
use crate::diag::{Code, DiagCtx, Diagnostic, IntoDiagnostic, Label};
use crate::location::Location;

use super::feature::FeatureKind;
use super::ty::{RefMode, Ty, TyFn, TyKind, TyRecord, TyTuple, TyVariant};
use super::{DeclId, ExcTyDecl, ExprId, Module, PatId, Result, SemaDiag, TyExprId, TyId};

fn tuple_ordering<I>(elems: I) -> Option<Ordering>
where
    I: IntoIterator<Item = Option<Ordering>>,
{
    elems.into_iter().try_fold(Ordering::Equal, |acc, elem| {
        use Ordering::Equal as E;
        use Ordering::Greater as R;
        use Ordering::Less as L;

        Some(match (acc, elem?) {
            (E, E) => E,
            (E | L, E | L) => L,
            (E | R, E | R) => R,
            _ => return None,
        })
    })
}

#[derive(Debug, Clone)]
pub enum ExpectationSource {
    FnDeclRet(DeclId),

    FixArg {
        expr_id: ExprId,
        ty_id: TyId,
    },

    FixArgRet(ExprId),

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

    AssignRhs {
        op_location: Location,
        lhs_expr_id: ExprId,
        ty_id: TyId,
    },

    ExceptionTyDecl,

    TryExpr {
        expr_id: ExprId,
        ty_id: TyId,
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
        self.typeck_exc_ty()?;
        self.typeck_decls()?;
        self.check_main()?;

        if cfg!(debug_assertions) {
            self.check_valid();
        }

        Ok(())
    }

    fn check_valid(&mut self) {
        let mut failed = false;

        for (_, expr) in &self.m.exprs {
            if self.is_untyped(expr.ty_id) {
                failed = true;
                self.diag.emit(
                    Diagnostic::error()
                        .at(expr.def.location)
                        .with_code(Code::INTERNAL_ERROR)
                        .with_msg("the expression is untyped despite the typeck succeeding")
                        .with_label(Label::primary(expr.def.location))
                        .make(),
                );
            }
        }

        for (_, ty_expr) in &self.m.ty_exprs {
            if self.is_untyped(ty_expr.ty_id) {
                failed = true;
                self.diag.emit(
                    Diagnostic::error()
                        .at(ty_expr.def.location)
                        .with_msg("the type expression is untyped despite the typeck succeeding")
                        .with_code(Code::INTERNAL_ERROR)
                        .with_label(Label::primary(ty_expr.def.location))
                        .make(),
                );
            }
        }

        for (_, pat) in &self.m.pats {
            if self.is_untyped(pat.ty_id) {
                failed = true;
                self.diag.emit(
                    Diagnostic::error()
                        .at(pat.def.location)
                        .with_code(Code::INTERNAL_ERROR)
                        .with_msg("the pattern is untyped despite the typeck succeeding")
                        .with_label(Label::primary(pat.def.location))
                        .make(),
                );
            }
        }

        for (_, binding) in &self.m.bindings {
            if self.is_untyped(binding.ty_id) {
                failed = true;
                self.diag.emit(
                    Diagnostic::error()
                        .at(binding.location)
                        .with_code(Code::INTERNAL_ERROR)
                        .with_msg("the binding is untyped despite the typeck succeeding")
                        .with_label(Label::primary(binding.location))
                        .make(),
                );
            }
        }

        assert!(!failed, "detected a typeck bug");
    }

    fn add_well_known_tys(&mut self) {
        self.m.well_known_tys.error = self.m.add_ty(Ty {
            kind: TyKind::Untyped { error: true },
        });
        self.m.well_known_tys.untyped = self.m.add_ty(Ty {
            kind: TyKind::Untyped { error: false },
        });
        self.m.well_known_tys.unit = self.m.add_ty(Ty { kind: TyKind::Unit });
        self.m.well_known_tys.bool = self.m.add_ty(Ty { kind: TyKind::Bool });
        self.m.well_known_tys.nat = self.m.add_ty(Ty { kind: TyKind::Nat });
        self.m.well_known_tys.empty_tuple = self.m.add_ty(Ty {
            kind: TyKind::Tuple(TyTuple { elems: vec![] }),
        });
        self.m.well_known_tys.top = self.m.add_ty(Ty { kind: TyKind::Top });
        self.m.well_known_tys.bot = self.m.add_ty(Ty { kind: TyKind::Bot });
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
            self.diag.emit(SemaDiag::WrongMainParamCount {
                location: decl.binding.location(),
                actual: decl.params.len(),
            });

            Err(())
        }
    }

    fn is_untyped(&self, ty_id: TyId) -> bool {
        matches!(self.m.tys[ty_id].kind, TyKind::Untyped { .. })
    }

    fn cmp_ty_tuple<L, R>(&self, lhs: L, rhs: R) -> Option<Ordering>
    where
        L: IntoIterator<Item = TyId>,
        L::IntoIter: ExactSizeIterator,
        R: IntoIterator<Item = TyId>,
        R::IntoIter: ExactSizeIterator,
    {
        let lhs = lhs.into_iter();
        let rhs = rhs.into_iter();

        if lhs.len() != rhs.len() {
            return None;
        }

        tuple_ordering(lhs.zip(rhs).map(|(l, r)| self.cmp_tys(l, r)))
    }

    /// Returns the ordering between two types induced by the subtype relation.
    fn cmp_tys(&self, lhs_ty_id: TyId, rhs_ty_id: TyId) -> Option<Ordering> {
        if lhs_ty_id == rhs_ty_id {
            return Some(Ordering::Equal);
        }

        Some(
            match (&self.m.tys[lhs_ty_id].kind, &self.m.tys[rhs_ty_id].kind) {
                // ∀T: Untyped <: T ∧ T <: Untyped.
                (TyKind::Untyped { .. }, _) | (_, TyKind::Untyped { .. }) => Ordering::Equal,

                // ∀T: T <: Top.
                (_, TyKind::Top) => Ordering::Less,
                (TyKind::Top, _) => Ordering::Greater,

                // ∀T: Bot <: T.
                (TyKind::Bot, _) => Ordering::Less,
                (_, TyKind::Bot) => Ordering::Greater,

                (&TyKind::Ref(lhs, _), &TyKind::Ref(rhs, RefMode::Source)) => {
                    self.cmp_tys(lhs, rhs)?
                }

                (&TyKind::Ref(lhs, RefMode::Source), &TyKind::Ref(rhs, _)) => {
                    self.cmp_tys(lhs, rhs)?.reverse()
                }

                (&TyKind::Ref(lhs, _), &TyKind::Ref(rhs, _)) => match self.cmp_tys(lhs, rhs)? {
                    Ordering::Equal => Ordering::Equal,

                    // references are invariant.
                    _ => return None,
                },

                (&TyKind::Sum(ll, lr), &TyKind::Sum(rl, rr)) => {
                    tuple_ordering([self.cmp_tys(ll, rl), self.cmp_tys(lr, rr)])?
                }

                (TyKind::Fn(lhs), TyKind::Fn(rhs)) => {
                    tuple_ordering([
                        self.cmp_ty_tuple(lhs.params.iter().copied(), rhs.params.iter().copied())
                            // fn is contravariant in parameters.
                            .map(Ordering::reverse),
                        self.cmp_tys(lhs.ret, rhs.ret),
                    ])?
                }

                (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) => {
                    self.cmp_ty_tuple(lhs.elems.iter().copied(), rhs.elems.iter().copied())?
                }

                // {} means both an empty record type and an empty tuple.
                (TyKind::Record(r), TyKind::Tuple(t)) | (TyKind::Tuple(t), TyKind::Record(r))
                    if r.elems.is_empty() && t.elems.is_empty() =>
                {
                    Ordering::Equal
                }

                // {f₁ : T₁, ..., fₙ : Tₙ} <: {}.
                (TyKind::Record(_), TyKind::Tuple(rhs))
                    if self.m.is_feature_enabled(FeatureKind::Subtyping)
                        && rhs.elems.is_empty() =>
                {
                    Ordering::Less
                }

                // {} >: {f₁ : T₁, ..., fₙ : Tₙ}.
                (TyKind::Tuple(lhs), TyKind::Record(_))
                    if self.m.is_feature_enabled(FeatureKind::Subtyping)
                        && lhs.elems.is_empty() =>
                {
                    Ordering::Greater
                }

                (TyKind::Record(lhs), TyKind::Record(rhs))
                    if self.m.is_feature_enabled(FeatureKind::Subtyping) =>
                {
                    let lhs_fields = lhs.fields.keys().collect::<FxHashSet<_>>();
                    let rhs_fields = rhs.fields.keys().collect::<FxHashSet<_>>();

                    // fields(lhs) ⊆ fields(rhs) ⇒ width_ordering = >:.
                    let (width_ordering, fields) = if lhs_fields == rhs_fields {
                        (Ordering::Equal, &lhs_fields)
                    } else if lhs_fields.is_superset(&rhs_fields) {
                        (Ordering::Less, &rhs_fields)
                    } else if lhs_fields.is_subset(&rhs_fields) {
                        (Ordering::Greater, &lhs_fields)
                    } else {
                        return None;
                    };

                    tuple_ordering([Some(width_ordering)].into_iter().chain(fields.iter().map(
                        |name| {
                            let lhs_idx = lhs.fields[name.as_str()];
                            let rhs_idx = rhs.fields[name.as_str()];

                            self.cmp_tys(lhs.elems[lhs_idx].1, rhs.elems[rhs_idx].1)
                        },
                    )))?
                }

                (TyKind::Record(lhs), TyKind::Record(rhs)) => {
                    if lhs.elems.len() != rhs.elems.len() {
                        return None;
                    }

                    if lhs
                        .elems
                        .iter()
                        .zip(&rhs.elems)
                        .any(|((lhs_name, _), (rhs_name, _))| lhs_name != rhs_name)
                    {
                        return None;
                    }

                    self.cmp_ty_tuple(
                        lhs.elems.iter().map(|&(_, l)| l),
                        rhs.elems.iter().map(|&(_, r)| r),
                    )?
                }

                (TyKind::Variant(lhs), TyKind::Variant(rhs))
                    if self.m.is_feature_enabled(FeatureKind::Subtyping) =>
                {
                    let lhs_labels = lhs.labels.keys().collect::<FxHashSet<_>>();
                    let rhs_labels = rhs.labels.keys().collect::<FxHashSet<_>>();

                    // fields(lhs) ⊆ fields(rhs) ⇒ width_ordering = <:.
                    let (width_ordering, labels) = if lhs_labels == rhs_labels {
                        (Ordering::Equal, &lhs_labels)
                    } else if lhs_labels.is_subset(&rhs_labels) {
                        (Ordering::Less, &lhs_labels)
                    } else if lhs_labels.is_superset(&rhs_labels) {
                        (Ordering::Greater, &rhs_labels)
                    } else {
                        return None;
                    };

                    tuple_ordering([Some(width_ordering)].into_iter().chain(labels.iter().map(
                        |name| {
                            let lhs_idx = lhs.labels[name.as_str()];
                            let rhs_idx = rhs.labels[name.as_str()];

                            match (lhs.elems[lhs_idx].1, rhs.elems[rhs_idx].1) {
                                (Some(l), Some(r)) => self.cmp_tys(l, r),
                                (None, None) => Some(Ordering::Equal),
                                _ => None,
                            }
                        },
                    )))?
                }

                (TyKind::Variant(lhs), TyKind::Variant(rhs)) => {
                    if lhs.elems.len() != rhs.elems.len() {
                        return None;
                    }

                    if lhs
                        .elems
                        .iter()
                        .zip(&rhs.elems)
                        .any(|((lhs_name, _), (rhs_name, _))| lhs_name != rhs_name)
                    {
                        return None;
                    }

                    tuple_ordering(lhs.elems.iter().zip(&rhs.elems).map(
                        |(&(_, l), &(_, r))| match (l, r) {
                            (Some(l), Some(r)) => self.cmp_tys(l, r),
                            (None, None) => Some(Ordering::Equal),
                            _ => None,
                        },
                    ))?
                }

                (&TyKind::List(l), &TyKind::List(r)) => self.cmp_tys(l, r)?,

                (
                    // why not `_`?
                    // this makes sure I don't forget to fix this if I add new types.
                    TyKind::Unit
                    | TyKind::Bool
                    | TyKind::Nat
                    | TyKind::Sum(..)
                    | TyKind::Fn(..)
                    | TyKind::Tuple(..)
                    | TyKind::Record(..)
                    | TyKind::Variant(..)
                    | TyKind::List(..)
                    | TyKind::Ref(..),
                    _,
                ) => return None,
            },
        )
    }

    fn ty_conforms_to(&self, ty_id: TyId, expected_ty_id: TyId) -> bool {
        if self.is_untyped(ty_id) || self.is_untyped(expected_ty_id) {
            return true;
        }

        if ty_id == expected_ty_id {
            return true;
        }

        self.cmp_tys(ty_id, expected_ty_id)
            .is_some_and(|ord| ord <= Ordering::Equal)
    }

    fn are_tys_equivalent(&self, lhs_ty_id: TyId, rhs_ty_id: TyId) -> bool {
        self.cmp_tys(lhs_ty_id, rhs_ty_id) == Some(Ordering::Equal)
    }

    fn augment_error_with_expectation(
        &self,
        diag: impl IntoDiagnostic,
        source: ExpectationSource,
    ) -> Diagnostic {
        let mut diag = diag.into_diagnostic();

        match source {
            ExpectationSource::FnDeclRet(decl_id) => {
                let decl = &self.m.decls[decl_id].def;
                let ast::DeclKind::Fn(decl_fn) = &decl.kind else {
                    unreachable!()
                };

                if let Some(ret_ty_expr) = &decl_fn.ret {
                    if ret_ty_expr.location.has_span() {
                        diag.add_label(
                            Label::secondary(ret_ty_expr.location)
                                .with_msg("expected because of the return type here"),
                        );
                    } else if decl.location.has_span() {
                        diag.add_label(
                            Label::secondary(decl.location)
                                .with_msg("expected because of this function's return type"),
                        );
                    } else {
                        diag.add_note(format!(
                            "expected because of the return type of the function `{}`",
                            decl_fn.binding.name.as_str(),
                        ));
                    }
                }
            }

            ExpectationSource::FixArg { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected so that the `fix` expression has the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::FixArgRet(expr_id) => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(
                    "the fixpoint combinator requires that the parameter type matches the return type"
                ));
            }

            ExpectationSource::InjectionArg {
                expr_id,
                is_left,
                sum_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected by the {} injection into the sum type `{}`",
                    if is_left { "left" } else { "right" },
                    self.m.display_ty(sum_ty_id),
                )));
            }

            ExpectationSource::InjectionPat {
                pat_id,
                is_left,
                sum_ty_id,
            } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "expected by the {} injection into the sum type `{}`",
                    if is_left { "left" } else { "right" },
                    self.m.display_ty(sum_ty_id),
                )));
            }

            ExpectationSource::ConsArg {
                expr_id,
                arg_expr_id,
                elem_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let arg_expr = self.m.exprs[arg_expr_id].def;

                diag.add_label(Label::secondary(arg_expr.location).with_msg(format!(
                    "expected because this expression has the type `{}`",
                    self.m.display_ty(elem_ty_id),
                )));

                diag.add_label(
                    Label::secondary(expr.location).with_msg("in this `cons` expression"),
                );
            }

            ExpectationSource::ConsPat {
                pat_id,
                arg_pat_id,
                elem_ty_id,
            } => {
                let pat = self.m.pats[pat_id].def;
                let arg_pat = self.m.pats[arg_pat_id].def;

                diag.add_label(Label::secondary(arg_pat.location).with_msg(format!(
                    "expected because this pattern has the type `{}`",
                    self.m.display_ty(elem_ty_id),
                )));

                diag.add_label(Label::secondary(pat.location).with_msg("in this `cons` pattern"));
            }

            ExpectationSource::BuiltinArg { expr_id, builtin } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected as an argument to this `{builtin}` expression"
                )));
            }

            ExpectationSource::BuiltinConsPat { pat_id, cons } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "expected as an argument to this `{cons}` constructor pattern"
                )));
            }

            ExpectationSource::FnArg {
                expr_id,
                arg_idx,
                callee_expr_id,
                callee_ty_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let callee_expr = self.m.exprs[callee_expr_id].def;

                diag.add_label(Label::secondary(callee_expr.location).with_msg(format!(
                    "expected as an argument #{} to this function",
                    arg_idx + 1,
                )));

                diag.add_label(Label::secondary(callee_expr.location).with_msg(format!(
                    "the callee has the type `{}`",
                    self.m.display_ty(callee_ty_id),
                )));

                diag.add_label(
                    Label::secondary(expr.location)
                        .with_msg("in this function application expression"),
                );
            }

            ExpectationSource::AscriptionExpr {
                expr_id,
                ty_expr_id,
            } => {
                let expr = self.m.exprs[expr_id].def;
                let ty_expr = &self.m.ty_exprs[ty_expr_id].def;

                diag.add_label(
                    Label::secondary(ty_expr.location)
                        .with_msg("expected due to this type ascription"),
                );

                diag.add_label(
                    Label::secondary(expr.location).with_msg("in this type ascription expression"),
                );
            }

            ExpectationSource::AscriptionPat { pat_id, ty_expr_id } => {
                let pat = self.m.pats[pat_id].def;
                let ty_expr = &self.m.ty_exprs[ty_expr_id].def;

                diag.add_label(
                    Label::secondary(ty_expr.location)
                        .with_msg("expected due to this type ascription"),
                );

                diag.add_label(
                    Label::secondary(pat.location).with_msg("in this type ascription pattern"),
                );
            }

            ExpectationSource::FnExprRet(expr_id) => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(
                    Label::secondary(expr.location)
                        .with_msg("expected as this anonymous function's return type"),
                );
            }

            ExpectationSource::TupleExprElem { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected for this tuple expression to have the type `{}`",
                    self.m.display_ty(ty_id)
                )));
            }

            ExpectationSource::TuplePatElem { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "expected for this tuple pattern to have the type `{}`",
                    self.m.display_ty(ty_id)
                )));
            }

            ExpectationSource::RecordExprField { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected for this record expression to have the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::RecordPatField { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "expected for this record pattern to have the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::VariantExprData { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected for this variant expression to have the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::VariantPatData { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "expected for this variant pattern to have the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::Scrutinee {
                scrutinee_expr_id,
                scrutinee_ty_id,
                match_expr_id,
            } => {
                let scrutinee = self.m.exprs[scrutinee_expr_id].def;
                let match_expr = self.m.exprs[match_expr_id].def;

                diag.add_label(Label::secondary(scrutinee.location).with_msg(format!(
                    "this expression has the type `{}`",
                    self.m.display_ty(scrutinee_ty_id),
                )));

                diag.add_label(
                    Label::secondary(match_expr.location).with_msg("in this match expression"),
                );
            }

            ExpectationSource::MatchArmBody {
                first_arm_expr_id,
                ty_id,
                match_expr_id,
            } => {
                let first_arm = self.m.exprs[first_arm_expr_id].def;
                let match_expr = self.m.exprs[match_expr_id].def;

                diag.add_label(Label::secondary(first_arm.location).with_msg(format!(
                    "this arm has the type `{}`",
                    self.m.display_ty(ty_id),
                )));

                diag.add_label(
                    Label::secondary(match_expr.location).with_msg("in this match expression"),
                );
            }

            ExpectationSource::ListExprElem {
                first_elem_expr_id,
                ty_id,
                list_expr_id,
            } => {
                let first_elem = self.m.exprs[first_elem_expr_id].def;
                let list_expr = self.m.exprs[list_expr_id].def;

                diag.add_label(Label::secondary(first_elem.location).with_msg(format!(
                    "this element has the type `{}`",
                    self.m.display_ty(ty_id),
                )));

                diag.add_label(
                    Label::secondary(list_expr.location).with_msg("in this list expression"),
                );
            }

            ExpectationSource::ListPatElem {
                first_elem_pat_id,
                ty_id,
                list_pat_id,
            } => {
                let first_elem = self.m.pats[first_elem_pat_id].def;
                let list_pat = self.m.pats[list_pat_id].def;

                diag.add_label(Label::secondary(first_elem.location).with_msg(format!(
                    "this element has the type `{}`",
                    self.m.display_ty(ty_id),
                )));

                diag.add_label(
                    Label::secondary(list_pat.location).with_msg("in this list pattern"),
                );
            }

            ExpectationSource::IfCond { expr_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(
                    Label::secondary(expr.location)
                        .with_msg("expected because this is the condition of this `if` expression"),
                );
            }

            ExpectationSource::IfBranch {
                then_expr_id,
                ty_id,
                if_expr_id,
            } => {
                let then_expr = self.m.exprs[then_expr_id].def;
                let if_expr = self.m.exprs[if_expr_id].def;

                diag.add_label(Label::secondary(then_expr.location).with_msg(format!(
                    "expected because this branch has the type `{}`",
                    self.m.display_ty(ty_id),
                )));

                diag.add_label(
                    Label::secondary(if_expr.location).with_msg("in this `if` expression"),
                );
            }

            ExpectationSource::Seq {
                semi_location,
                expr_id,
            } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(
                    Label::secondary(semi_location)
                        .with_msg("expected because it is followed by a semicolon"),
                );

                diag.add_label(
                    Label::secondary(expr.location).with_msg("in this sequence expression"),
                );
            }

            ExpectationSource::LetRecBinding { pat_id, ty_id } => {
                let pat = self.m.pats[pat_id].def;

                diag.add_label(Label::secondary(pat.location).with_msg(format!(
                    "this pattern has the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::LetBinding {
                init_expr_id,
                ty_id,
            } => {
                let init_expr = self.m.exprs[init_expr_id].def;

                diag.add_label(Label::secondary(init_expr.location).with_msg(format!(
                    "this expression has the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::BinOp { op_location } => {
                diag.add_label(
                    Label::secondary(op_location)
                        .with_msg("expected because it's an operand to this operator"),
                );
            }

            ExpectationSource::AssignRhs {
                op_location,
                lhs_expr_id,
                ty_id,
            } => {
                let lhs_expr = self.m.exprs[lhs_expr_id].def;

                diag.add_label(
                    Label::secondary(op_location)
                        .with_msg("expected because it's an operand to an assignment expression"),
                );
                diag.add_label(Label::secondary(lhs_expr.location).with_msg(format!(
                    "this expression has the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }

            ExpectationSource::ExceptionTyDecl => {
                let mut msg =
                    "the exception must conform to the variant exception type declared here"
                        .to_owned();

                match &self.m.exc_ty_decl {
                    ExcTyDecl::None => {
                        panic!("ExpectationSource::ExceptionTyDecl with no exc_ty_decl")
                    }

                    ExcTyDecl::OpenVariantTy { elems, .. } => {
                        if elems.len() > 1 {
                            let _ = write!(
                                msg,
                                " and in {} other declaration{suffix}",
                                elems.len() - 1,
                                suffix = if elems.len() == 2 { "" } else { "s" },
                            );
                        }

                        diag.add_label(
                            Label::secondary(self.m.decls[elems[0]].def.location).with_msg(msg),
                        );
                    }

                    ExcTyDecl::Decl(decl_id) => {
                        diag.add_label(
                            Label::secondary(self.m.decls[*decl_id].def.location).with_msg(msg),
                        );
                    }
                }
            }

            ExpectationSource::TryExpr { expr_id, ty_id } => {
                let expr = self.m.exprs[expr_id].def;

                diag.add_label(Label::secondary(expr.location).with_msg(format!(
                    "expected because this expression has the type `{}`",
                    self.m.display_ty(ty_id),
                )));
            }
        }

        diag
    }

    fn make_expr_ty_error(
        &self,
        expr_id: ExprId,
        ty_id: TyId,
        expected_ty_id: TyId,
        source: ExpectationSource,
    ) -> Diagnostic {
        let location = self.m.exprs[expr_id].def.location;
        let expected_ty = self.m.display_ty(expected_ty_id).to_string();
        let actual_ty = self.m.display_ty(ty_id).to_string();

        self.augment_error_with_expectation(
            if self.m.is_feature_enabled(FeatureKind::Subtyping) {
                SemaDiag::ExprTyMismatchSubtype {
                    location,
                    expected_ty,
                    actual_ty,
                }
            } else {
                SemaDiag::ExprTyMismatch {
                    location,
                    expected_ty,
                    actual_ty,
                }
            },
            source,
        )
    }

    fn make_exception_ty_not_declared_error(&self, location: Location) -> Diagnostic {
        let mut diag = SemaDiag::ExceptionTyNotDeclared { location }.into_diagnostic();

        if self
            .m
            .is_feature_enabled(FeatureKind::OpenVariantExceptions)
        {
            diag.add_note(
                "use an `exception variant` declaration to add a variant to the exception type",
            );
        } else if self
            .m
            .is_feature_enabled(FeatureKind::ExceptionTypeDeclaration)
        {
            diag.add_note("use an `exception type` declaration to specify the exception type");
        } else {
            diag.add_note(format!(
                "enable #{} or #{} to allow specifying the exception type",
                FeatureKind::OpenVariantExceptions.extension().unwrap(),
                FeatureKind::ExceptionTypeDeclaration.extension().unwrap(),
            ));
        }

        diag
    }

    fn typeck_exc_ty(&mut self) -> Result {
        let mut result = Ok(());

        self.m.exc_ty_id = match &self.m.exc_ty_decl {
            ExcTyDecl::None => None,

            ExcTyDecl::OpenVariantTy { elems, .. } => {
                let elems = elems
                    .clone()
                    .into_iter()
                    .map(|decl_id| {
                        let ast::DeclKind::ExceptionVariant(decl) = &self.m.decls[decl_id].def.kind
                        else {
                            unreachable!();
                        };

                        result = result.and(self.typeck_ty_expr(&decl.variant_ty_expr));
                        let ty_id = self.m.ty_exprs[decl.variant_ty_expr.id].ty_id;

                        (decl.name.as_str().to_owned(), Some(ty_id))
                    })
                    .collect();

                Some(self.m.add_ty(Ty {
                    kind: TyKind::Variant(TyVariant::new(elems)),
                }))
            }

            ExcTyDecl::Decl(decl_id) => {
                let ast::DeclKind::ExceptionType(decl) = &self.m.decls[*decl_id].def.kind else {
                    unreachable!();
                };

                result = result.and(self.typeck_ty_expr(&decl.ty_expr));

                Some(self.m.ty_exprs[decl.ty_expr.id].ty_id)
            }
        };

        result
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

            ast::DeclKind::ExceptionType(_) => {}
            ast::DeclKind::ExceptionVariant(_) => {}
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

            ast::DeclKind::ExceptionType(_) => {}
            ast::DeclKind::ExceptionVariant(_) => {}
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

            ast::TyExprKind::Ref(t) => {
                result = result.and(self.typeck_ty_expr(&t.ty_expr));

                self.m.ty_exprs[ty_expr.id].ty_id = self.m.add_ty(Ty {
                    kind: TyKind::Ref(self.m.ty_exprs[t.ty_expr.id].ty_id, RefMode::Ref),
                });
            }

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

            ast::TyExprKind::Top(_) => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.top;
            }

            ast::TyExprKind::Bot(_) => {
                self.m.ty_exprs[ty_expr.id].ty_id = self.m.well_known_tys.bot;
            }

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
            ast::ExprKind::Address(e) => self.typeck_expr_address(expr.id, e, expected_ty),
            ast::ExprKind::Name(e) => self.typeck_expr_name(expr.id, e, expected_ty),
            ast::ExprKind::Field(e) => self.typeck_expr_field(expr.id, e, expected_ty),
            ast::ExprKind::Panic(e) => self.typeck_expr_panic(expr.id, e, expected_ty),
            ast::ExprKind::Throw(e) => self.typeck_expr_throw(expr.id, e, expected_ty),
            ast::ExprKind::Try(e) => self.typeck_expr_try(expr.id, e, expected_ty),
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
                    self.m.well_known_tys.nat,
                    expected_ty_id,
                    source,
                ));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = self.m.well_known_tys.nat;

        Ok(())
    }

    fn typeck_expr_address(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprAddress,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, source)) = expected_ty else {
            self.diag.emit(SemaDiag::AmbiguousAddressExprTy {
                location: self.m.exprs[expr_id].def.location,
            });

            return Err(());
        };

        if self.is_untyped(expected_ty_id) {
            return Ok(());
        }

        match self.m.tys[expected_ty_id].kind {
            TyKind::Ref(_, _) => {}
            TyKind::Top => {}

            _ => {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::UnexpectedAddressExpr {
                        location: self.m.exprs[expr_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            }
        }

        self.m.exprs[expr_id].ty_id = expected_ty_id;

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
                        Label::secondary(self.m.bindings[binding_id].location).with_msg(format!(
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

        if self.is_untyped(base_ty_id) {
            return Ok(());
        }

        let ty_id = match &expr.field {
            ast::ExprFieldName::Name(name) => {
                if self.are_tys_equivalent(base_ty_id, self.m.well_known_tys.empty_tuple) {
                    self.diag.emit(SemaDiag::NoSuchField {
                        location: self.m.exprs[expr_id].def.location,
                        field: name.as_str().into(),
                        record_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: name.location(),
                    });

                    return Err(());
                }

                let TyKind::Record(ty) = &self.m.tys[base_ty_id].kind else {
                    self.diag.emit(SemaDiag::ExtractingFieldOfNonRecordTy {
                        location: self.m.exprs[expr_id].def.location,
                        field: name.as_str().into(),
                        actual_ty: self.m.display_ty(base_ty_id).to_string(),
                        base_location: expr.base.location,
                        field_location: name.location(),
                    });

                    return Err(());
                };

                let Some(&idx) = ty.fields.get(name.as_str()) else {
                    self.diag.emit(SemaDiag::NoSuchField {
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
                    self.diag.emit(SemaDiag::IndexingNonTupleTy {
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
                        self.diag.emit(SemaDiag::NoSuchElement {
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

    fn typeck_expr_panic(
        &mut self,
        expr_id: ExprId,
        _expr: &ast::ExprPanic,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, _source)) = expected_ty else {
            self.diag.emit(SemaDiag::AmbiguousPanicExprTy {
                location: self.m.exprs[expr_id].def.location,
            });

            return Err(());
        };

        self.m.exprs[expr_id].ty_id = expected_ty_id;

        Ok(())
    }

    fn typeck_expr_throw(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprThrow<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let Some((expected_ty_id, _source)) = expected_ty else {
            self.diag.emit(SemaDiag::AmbiguousThrowExprTy {
                location: self.m.exprs[expr_id].def.location,
            });

            return Err(());
        };

        self.m.exprs[expr_id].ty_id = expected_ty_id;

        let Some(exc_ty_id) = self.m.exc_ty_id else {
            self.diag.emit(
                self.make_exception_ty_not_declared_error(self.m.exprs[expr_id].def.location),
            );

            return Err(());
        };

        self.typeck_expr(
            &expr.exc,
            Some((exc_ty_id, ExpectationSource::ExceptionTyDecl)),
        )
    }

    fn typeck_expr_try(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprTry<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = Ok(());
        result = result.and(self.typeck_expr(&expr.try_expr, expected_ty.clone()));

        let expected_ty = expected_ty.unwrap_or_else(|| {
            let ty_id = self.m.exprs[expr.try_expr.id].ty_id;

            (
                ty_id,
                ExpectationSource::TryExpr {
                    expr_id: expr.try_expr.id,
                    ty_id,
                },
            )
        });
        let ty_id = expected_ty.0;

        match &expr.fallback {
            ast::ExprTryFallback::Catch(arm) => {
                let exc_ty_id = self.m.exc_ty_id.unwrap_or_else(|| {
                    self.diag
                        .emit(self.make_exception_ty_not_declared_error(arm.pat.location));

                    self.m.well_known_tys.error
                });

                result = result.and(self.typeck_pat(
                    &arm.pat,
                    Some((exc_ty_id, ExpectationSource::ExceptionTyDecl)),
                ));
                result = result.and(self.typeck_expr(&arm.body, Some(expected_ty)));
            }

            ast::ExprTryFallback::With(expr) => {
                result = result.and(self.typeck_expr(expr, Some(expected_ty)));
            }
        }

        self.m.exprs[expr_id].ty_id = ty_id;

        result
    }

    fn typeck_expr_fix(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprFix<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let inner_expected_ty = expected_ty.as_ref().map(|&(expected_ty_id, _)| {
            (
                self.m.add_ty(Ty {
                    kind: TyKind::Fn(TyFn {
                        // don't check the parameter type because we'll do it later anyway.
                        params: vec![self.m.well_known_tys.untyped],
                        ret: expected_ty_id,
                    }),
                }),
                ExpectationSource::FixArg {
                    expr_id,
                    ty_id: expected_ty_id,
                },
            )
        });
        self.typeck_expr(&expr.expr, inner_expected_ty)?;

        let inner_ty_id = self.m.exprs[expr.expr.id].ty_id;

        if self.is_untyped(inner_ty_id) {
            return Ok(());
        }

        if inner_ty_id == self.m.well_known_tys.bot && expected_ty.is_some() {
            // only allow doing this when checking the type. that's what the reference
            // implementatino does, don't ask me.
            self.m.exprs[expr_id].ty_id = self.m.well_known_tys.bot;

            return Ok(());
        }

        let TyKind::Fn(inner_ty) = &self.m.tys[inner_ty_id].kind else {
            self.diag.emit(SemaDiag::FixNotFn {
                location: self.m.exprs[expr_id].def.location,
                actual_ty: self.m.display_ty(inner_ty_id).to_string(),
                inner_location: expr.expr.location,
            });

            return Err(());
        };

        if inner_ty.params.len() != 1 {
            self.diag.emit(SemaDiag::FixWrongFnParamCount {
                location: self.m.exprs[expr_id].def.location,
                actual_ty: self.m.display_ty(inner_ty_id).to_string(),
                inner_location: expr.expr.location,
            });

            return Err(());
        }

        if !self.ty_conforms_to(inner_ty.ret, inner_ty.params[0]) {
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
                ExpectationSource::FixArgRet(expr_id),
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
                        self.diag.emit(SemaDiag::AmbiguousSumTyInExpr {
                            location: self.m.exprs[expr_id].def.location,
                        });

                        return Err(());
                    };

                    if self.is_untyped(expected_ty_id) {
                        return Ok(());
                    }

                    if expected_ty_id == self.m.well_known_tys.top {
                        return self.typeck_expr_apply(expr_id, expr, None);
                    }

                    let TyKind::Sum(lhs_ty_id, rhs_ty_id) = self.m.tys[expected_ty_id].kind else {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaDiag::UnexpectedInjection {
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
                        if self.is_untyped(expected_ty_id) {
                            return Ok(());
                        }

                        if expected_ty_id == self.m.well_known_tys.top {
                            return self.typeck_expr_apply(expr_id, expr, None);
                        }

                        let TyKind::List(elem_ty_id) = self.m.tys[expected_ty_id].kind else {
                            self.diag.emit(self.augment_error_with_expectation(
                                SemaDiag::UnexpectedList {
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
                        if self.is_untyped(expected_ty_id) {
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

                        let ty_id = if self.is_untyped(arg_ty_id) {
                            self.m.well_known_tys.error
                        } else if let TyKind::List(elem_ty_id) = self.m.tys[arg_ty_id].kind {
                            elem_ty_id
                        } else {
                            self.diag.emit(SemaDiag::ExprTyNotList {
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

                    if self.is_untyped(arg_ty_id) {
                        // ignore.
                    } else if let TyKind::List(_) = self.m.tys[arg_ty_id].kind {
                        // also good.
                    } else {
                        self.diag.emit(SemaDiag::ExprTyNotList {
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
                    let mut result = Ok(());

                    'ty_check: {
                        if let Some((expected_ty_id, ref source)) = expected_ty {
                            if self.is_untyped(expected_ty_id) {
                                return Ok(());
                            }

                            let TyKind::List(_) = self.m.tys[expected_ty_id].kind else {
                                result = Err(());
                                break 'ty_check;
                            };

                            return self.typeck_application(
                                expr_id,
                                vec![Some((expected_ty_id, source.clone()))],
                                expected_ty_id,
                                &expr.args,
                                Some((expected_ty_id, source.clone())),
                            );
                        }
                    }

                    self.check_application_arg_count(expr_id, expr.args.len(), 1)?;
                    self.typeck_expr(&expr.args[0], None)?;
                    let arg_ty_id = self.m.exprs[expr.args[0].id].ty_id;

                    if self.is_untyped(arg_ty_id) {
                        // ignore.
                    } else if let TyKind::List(_) = self.m.tys[arg_ty_id].kind {
                        // also good.
                    } else {
                        self.diag.emit(SemaDiag::ExprTyNotList {
                            location: expr.args[0].location,
                            actual_ty: self.m.display_ty(arg_ty_id).to_string(),
                        });

                        return Err(());
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

                    result
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
                        if self.is_untyped(expected_ty_id) {
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

                if self.is_untyped(callee_ty_id) {
                    return Err(());
                }

                let TyKind::Fn(callee_ty) = &self.m.tys[callee_ty_id].kind else {
                    self.diag.emit(SemaDiag::ApplyNotFn {
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
            self.diag.emit(SemaDiag::WrongArgCountInExpr {
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
            if self.is_untyped(expected_ty_id) {
                return Ok(());
            }

            if expected_ty_id == self.m.well_known_tys.top {
                return self.typeck_expr_fn(expr_id, expr, None);
            }

            let TyKind::Fn(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::UnexpectedFn {
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
                    SemaDiag::WrongFnParamCount {
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
                        SemaDiag::ParamTyMismatch {
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
            if self.is_untyped(expected_ty_id) {
                return self.typeck_expr_tuple(expr_id, expr, None);
            }

            if expected_ty_id == self.m.well_known_tys.top {
                return self.typeck_expr_tuple(expr_id, expr, None);
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) => ty,
                TyKind::Record(ty) if ty.elems.is_empty() => &TyTuple { elems: vec![] },

                TyKind::Record(ty) if expr.elems.is_empty() => {
                    // since `{}` is nominally a tuple, if we expect a non-empty record, we report
                    // all of its fields as missing, pretending that `{}` is actually a record.
                    for (name, _) in &ty.elems {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaDiag::MissingRecordFieldInExpr {
                                location: self.m.exprs[expr_id].def.location,
                                name: name.into(),
                                expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            },
                            source.clone(),
                        ));
                    }

                    return Err(());
                }

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::UnexpectedTuple {
                            location: self.m.exprs[expr_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));
                    self.typeck_expr_tuple(expr_id, expr, None)?;

                    return Err(());
                }
            };

            if expr.elems.len() != ty.elems.len() {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::WrongTupleLengthInExpr {
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
            if self.is_untyped(expected_ty_id) {
                return self.typeck_expr_record(expr_id, expr, None);
            }

            if expected_ty_id == self.m.well_known_tys.top {
                return self.typeck_expr_record(expr_id, expr, None);
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) if ty.elems.is_empty() => &TyRecord::new(vec![]),
                TyKind::Record(ty) => ty,

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::UnexpectedRecord {
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
                    SemaDiag::MissingRecordFieldInExpr {
                        location: self.m.exprs[expr_id].def.location,
                        name: name.into(),
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source.clone(),
                ));
            }

            if !self.m.is_feature_enabled(FeatureKind::Subtyping) {
                for name in provided_fields.difference(&required_fields).copied() {
                    result = Err(());
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::NoSuchRecordFieldInExpr {
                            location: provided_fields_by_name[name].name.location(),
                            name: name.into(),
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            expr_location: self.m.exprs[expr_id].def.location,
                        },
                        source.clone(),
                    ));
                }
            }

            result?;

            let fields = expr
                .fields
                .iter()
                .map(|field| {
                    (
                        &field.expr,
                        ty.fields
                            .get(field.name.as_str())
                            .map(|&idx| ty.elems[idx].1),
                    )
                })
                .collect::<Vec<_>>();

            for (expr, expected_field_ty_id) in fields {
                result = result.and(self.typeck_expr(
                    expr,
                    expected_field_ty_id.map(|expected_field_ty_id| {
                        (
                            expected_field_ty_id,
                            ExpectationSource::RecordExprField {
                                expr_id,
                                ty_id: expected_ty_id,
                            },
                        )
                    }),
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
        if let Some((expected_ty_id, source)) = expected_ty {
            if self.is_untyped(expected_ty_id) {
                return Ok(());
            }

            if expected_ty_id == self.m.well_known_tys.top {
                return self.typeck_expr_variant(expr_id, expr, None);
            }

            let TyKind::Variant(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::UnexpectedVariant {
                        location: self.m.exprs[expr_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            };

            let Some(&idx) = ty.labels.get(expr.label.as_str()) else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::NoSuchVariantLabelInExpr {
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
                        SemaDiag::UnexpectedDataForNullaryLabel {
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
                        SemaDiag::MissingDataForLabel {
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
        } else if self.m.is_feature_enabled(FeatureKind::Subtyping) {
            let result = expr
                .expr
                .as_ref()
                .map(|inner| self.typeck_expr(inner, None))
                .unwrap_or(Ok(()));

            self.m.exprs[expr_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::Variant(TyVariant::new(vec![(
                    expr.label.as_str().into(),
                    expr.expr.as_ref().map(|inner| self.m.exprs[inner.id].ty_id),
                )])),
            });

            result
        } else {
            self.diag.emit(SemaDiag::AmbiguousVariantTyInExpr {
                location: self.m.exprs[expr_id].def.location,
            });

            Err(())
        }
    }

    fn typeck_expr_match(
        &mut self,
        expr_id: ExprId,
        expr: &ast::ExprMatch<'ast>,
        expected_ty: Option<ExpectedTy>,
    ) -> Result {
        let mut result = self.typeck_expr(&expr.expr, None);

        // there must be at least one branch, even for `Bot`.
        // (we treat Bot as an inhabited type when checking pattern exhaustiveness.)
        if expr.arms.is_empty() {
            self.diag.emit(SemaDiag::EmptyMatch {
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
            let elem_ty_id = if self.is_untyped(expected_ty_id) {
                self.m.well_known_tys.error
            } else {
                if expected_ty_id == self.m.well_known_tys.top {
                    return self.typeck_expr_list(expr_id, expr, None);
                }

                let TyKind::List(ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::UnexpectedList {
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
            self.diag.emit(SemaDiag::AmbiguousEmptyListExprTy {
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
        match expr.op {
            ast::UnOp::New => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    let pointee_ty_id = if self.is_untyped(expected_ty_id) {
                        self.m.well_known_tys.error
                    } else {
                        if expected_ty_id == self.m.well_known_tys.top {
                            return self.typeck_expr_unary(expr_id, expr, None);
                        }

                        match self.m.tys[expected_ty_id].kind {
                            TyKind::Ref(ty_id, _) => ty_id,

                            _ => {
                                self.diag.emit(self.augment_error_with_expectation(
                                    SemaDiag::UnexpectedNewExpr {
                                        location: self.m.exprs[expr_id].def.location,
                                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                                    },
                                    source.clone(),
                                ));

                                self.m.well_known_tys.error
                            }
                        }
                    };

                    let result = self.typeck_expr(&expr.rhs, Some((pointee_ty_id, source)));
                    self.m.exprs[expr_id].ty_id = expected_ty_id;

                    result
                } else {
                    let result = self.typeck_expr(&expr.rhs, None);
                    let pointee_ty_id = self.m.exprs[expr.rhs.id].ty_id;

                    self.m.exprs[expr_id].ty_id = self.m.add_ty(Ty {
                        kind: TyKind::Ref(pointee_ty_id, RefMode::Ref),
                    });

                    result
                }
            }

            ast::UnOp::Deref => {
                if let Some((expected_ty_id, source)) = expected_ty {
                    if self.is_untyped(expected_ty_id) {
                        return Ok(());
                    }

                    let arg_ty_id = self.m.add_ty(Ty {
                        kind: TyKind::Ref(expected_ty_id, RefMode::Source),
                    });

                    let result = self.typeck_expr(&expr.rhs, Some((arg_ty_id, source)));
                    self.m.exprs[expr_id].ty_id = expected_ty_id;

                    result
                } else {
                    self.typeck_expr(&expr.rhs, None)?;
                    let arg_ty_id = self.m.exprs[expr.rhs.id].ty_id;

                    // WARN: may need to be changed when Bot is added.
                    let ty_id = if self.is_untyped(arg_ty_id) {
                        self.m.well_known_tys.error
                    } else if let TyKind::Ref(ty_id, RefMode::Ref | RefMode::Source) =
                        self.m.tys[arg_ty_id].kind
                    {
                        ty_id
                    } else {
                        self.diag.emit(SemaDiag::ExprTyNotReference {
                            location: expr.rhs.location,
                            actual_ty: self.m.display_ty(arg_ty_id).to_string(),
                        });

                        return Err(());
                    };

                    self.m.exprs[expr_id].ty_id = ty_id;

                    Ok(())
                }
            }
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

            ast::BinOp::Assign => {
                let mut result = Ok(());
                result = result.and(self.typeck_expr(&expr.lhs, None));
                let ref_ty_id = self.m.exprs[expr.lhs.id].ty_id;

                let pointee_ty_id = if self.is_untyped(ref_ty_id) {
                    self.m.well_known_tys.error
                } else if let TyKind::Ref(pointee_ty_id, RefMode::Ref) = self.m.tys[ref_ty_id].kind {
                    pointee_ty_id
                } else if let TyKind::Ref(pointee_ty_id, RefMode::Source) = self.m.tys[ref_ty_id].kind {
                    let expected_ty_id = self.m.add_ty(Ty {
                        kind: TyKind::Ref(pointee_ty_id, RefMode::Ref),
                    });
                    self.diag.emit(SemaDiag::ExprTyMismatch {
                        location: self.m.exprs[expr.lhs.id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        actual_ty: self.m.display_ty(ref_ty_id).to_string(),
                    });

                    return Err(());
                } else {
                    self.diag.emit(SemaDiag::ExprTyNotReference {
                        location: expr.lhs.location,
                        actual_ty: self.m.display_ty(ref_ty_id).to_string(),
                    });

                    return Err(());
                };

                result = result.and(self.typeck_expr(&expr.rhs, Some((
                    pointee_ty_id,
                    ExpectationSource::AssignRhs {
                        op_location: expr.token.as_ref().map(|token| token.span).into(),
                        lhs_expr_id: expr.lhs.id,
                        ty_id: ref_ty_id,
                    },
                ))));

                self.m.exprs[expr_id].ty_id = self.m.well_known_tys.unit;

                if let Some((expected_ty_id, source)) = expected_ty {
                    if !self.ty_conforms_to(self.m.well_known_tys.unit, expected_ty_id) {
                        result = Err(());
                        self.diag.emit(self.make_expr_ty_error(
                            expr_id,
                            self.m.well_known_tys.unit,
                            expected_ty_id,
                            source,
                        ));
                    }
                }

                result
            }
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
        if let Some((expected_ty_id, source)) = expected_ty {
            if self.is_untyped(expected_ty_id) {
                return Ok(());
            }

            let TyKind::Variant(ty) = &self.m.tys[expected_ty_id].kind else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::IllegalPatForTy {
                        location: self.m.pats[pat_id].def.location,
                        expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                    },
                    source,
                ));

                return Err(());
            };

            let Some(&idx) = ty.labels.get(pat.label.as_str()) else {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::NoSuchVariantLabelInPat {
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
                        SemaDiag::UnexpectedNonNullaryVariantPat {
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
                        SemaDiag::UnexpectedNullaryVariantPat {
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
        } else if self.m.is_feature_enabled(FeatureKind::Subtyping) {
            let result = pat
                .pat
                .as_ref()
                .map(|inner| self.typeck_pat(inner, None))
                .unwrap_or(Ok(()));

            self.m.pats[pat_id].ty_id = self.m.add_ty(Ty {
                kind: TyKind::Variant(TyVariant::new(vec![(
                    pat.label.as_str().into(),
                    pat.pat.as_ref().map(|inner| self.m.pats[inner.id].ty_id),
                )])),
            });

            result
        } else {
            self.diag.emit(SemaDiag::AmbiguousVariantTyInPat {
                location: self.m.pats[pat_id].def.location,
            });

            return Err(());
        }
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
                    self.diag.emit(SemaDiag::AmbiguousSumTyInPat {
                        location: self.m.pats[pat_id].def.location,
                    });

                    return Err(());
                };

                if self.is_untyped(expected_ty_id) {
                    return Ok(());
                }

                let TyKind::Sum(lhs_ty_id, rhs_ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::IllegalPatForTy {
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
                    if self.is_untyped(expected_ty_id) {
                        return Ok(());
                    }

                    let TyKind::List(elem_ty_id) = self.m.tys[expected_ty_id].kind else {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaDiag::IllegalPatForTy {
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
                    if !self.are_tys_equivalent(self.m.well_known_tys.nat, expected_ty_id) {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaDiag::IllegalPatForTy {
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
            self.diag.emit(SemaDiag::WrongArgCountInPat {
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
            if self.is_untyped(expected_ty_id) {
                return Ok(());
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) => ty,
                TyKind::Record(ty) if ty.elems.is_empty() => &TyTuple { elems: vec![] },

                TyKind::Record(ty) if pat.elems.is_empty() => {
                    // pretend `{}` is a record pattern (see `typeck_expr_tuple`).
                    for (name, _) in &ty.elems {
                        self.diag.emit(self.augment_error_with_expectation(
                            SemaDiag::MissingRecordFieldInPat {
                                location: self.m.pats[pat_id].def.location,
                                name: name.into(),
                                expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                            },
                            source.clone(),
                        ));
                    }

                    return Err(());
                }

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::IllegalPatForTy {
                            location: self.m.pats[pat_id].def.location,
                            expected_ty: self.m.display_ty(expected_ty_id).to_string(),
                        },
                        source,
                    ));

                    return Err(());
                }
            };

            if pat.elems.len() != ty.elems.len() {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::WrongTupleLengthInPat {
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
            if self.is_untyped(expected_ty_id) {
                return Ok(());
            }

            let ty = match &self.m.tys[expected_ty_id].kind {
                TyKind::Tuple(ty) if ty.elems.is_empty() => &TyRecord::new(vec![]),
                TyKind::Record(ty) => ty,

                _ => {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::IllegalPatForTy {
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
                    SemaDiag::MissingRecordFieldInPat {
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
                    SemaDiag::NoSuchRecordFieldInPat {
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
            let elem_ty_id = if self.is_untyped(expected_ty_id) {
                self.m.well_known_tys.error
            } else {
                let TyKind::List(ty_id) = self.m.tys[expected_ty_id].kind else {
                    self.diag.emit(self.augment_error_with_expectation(
                        SemaDiag::IllegalPatForTy {
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
            self.diag.emit(SemaDiag::AmbiguousEmptyListPatTy {
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
            if !self.are_tys_equivalent(self.m.well_known_tys.bool, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::IllegalPatForTy {
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
            if !self.are_tys_equivalent(self.m.well_known_tys.unit, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::IllegalPatForTy {
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
            if !self.are_tys_equivalent(self.m.well_known_tys.nat, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::IllegalPatForTy {
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
            self.diag.emit(SemaDiag::AmbiguousBindingPatTy {
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
            if !self.are_tys_equivalent(ty_id, expected_ty_id) {
                self.diag.emit(self.augment_error_with_expectation(
                    SemaDiag::IllegalPatForTy {
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
