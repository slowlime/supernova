use fxhash::FxHashSet;

use crate::ast;
use crate::diag::{DiagCtx, Diagnostic, IntoDiagnostic};
use crate::location::Location;
use crate::util::format_iter;

use super::feature::{EnableReason, Feature, FeatureKind};
use super::{DeclId, ExprId, Module, PatId, Result, SemaDiag, TyExprId};

impl Module<'_> {
    pub(super) fn process_features(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

struct Pass<'ast, 'm, D> {
    m: &'m mut Module<'ast>,
    diag: &'m mut D,
}

fn make_feature_disabled_error(diag: impl IntoDiagnostic, feature: FeatureKind) -> Diagnostic {
    let mut diag = diag
        .into_diagnostic()
        .with_note(format!("feature {feature} is disabled"));

    let extensions = feature
        .extension()
        .map(|extension| vec![extension])
        .unwrap_or_else(|| feature.enabled_by_extensions());

    match &extensions[..] {
        [] => {}

        &[extension] => diag.add_note(format!(
            "you can enable the feature with the #{extension} extension"
        )),

        _ => {
            diag.add_note(format!(
                "you can enable the feature with any of the following extensions: {}",
                format_iter(extensions.iter().map(|ext| format!("#{ext}")), "or", ""),
            ));
        }
    }

    diag
}

impl<'ast, 'm, D: DiagCtx> Pass<'ast, 'm, D> {
    fn new(m: &'m mut Module<'ast>, diag: &'m mut D) -> Self {
        Self { m, diag }
    }

    fn run(mut self) -> Result {
        self.build_trans_closure();
        self.check_feature_conflicts()?;
        self.check_syntactical_features()?;

        Ok(())
    }

    fn build_trans_closure(&mut self) {
        let mut unprocessed = self.m.features.keys().copied().collect::<Vec<_>>();
        let mut discovered = unprocessed.iter().copied().collect::<FxHashSet<_>>();

        while let Some(feature) = unprocessed.pop() {
            for &dep in feature.depends() {
                if !discovered.insert(dep) {
                    continue;
                }

                self.m.features.insert(
                    dep,
                    Feature {
                        kind: dep,
                        reason: EnableReason::Feature(feature),
                    },
                );
                unprocessed.push(dep);
            }
        }
    }

    fn emit_feature_conflict(&mut self, conflicting_features: Vec<(FeatureKind, EnableReason)>) {
        let location = conflicting_features
            .iter()
            .filter_map(|(_, reason)| match reason {
                EnableReason::Extension(location) => Some(*location),
                _ => None,
            })
            .max()
            .unwrap_or(self.m.location);

        self.diag.emit(SemaDiag::ConflictingFeatures {
            location,
            features: conflicting_features,
        });
    }

    fn check_feature_conflicts(&mut self) -> Result {
        let mut result = Ok(());

        for &conflict in Feature::MUTUALLY_EXCLUSIVE_FEATURES {
            if conflict
                .iter()
                .filter(|&&feature| self.m.is_feature_enabled(feature))
                .count()
                <= 1
            {
                continue;
            }

            let mut conflicting_features = vec![];

            for feature in conflict {
                if let Some(f) = self.m.features.get(feature) {
                    conflicting_features.push((*feature, f.reason.clone()));
                }
            }

            result = Err(());
            self.emit_feature_conflict(conflicting_features);
        }

        let mut conflicts = vec![];

        for (&kind, feature) in &self.m.features {
            let mut conflicting_features = vec![];

            for &conflicting_feature in Feature::disallowed_features_for(kind) {
                if let Some(f) = self.m.features.get(&conflicting_feature) {
                    if conflicting_features.is_empty() {
                        conflicting_features.push((kind, feature.reason.clone()));
                    }

                    conflicting_features.push((conflicting_feature, f.reason.clone()));
                }
            }

            if !conflicting_features.is_empty() {
                conflicts.push(conflicting_features);
                result = Err(());
            }
        }

        for conflict in conflicts {
            self.emit_feature_conflict(conflict);
        }

        result
    }

    fn check_syntactical_features(&mut self) -> Result {
        let mut result = Ok(());
        result = result.and(self.check_decls());
        result = result.and(self.check_ty_exprs());
        result = result.and(self.check_exprs());
        result = result.and(self.check_pats());

        result
    }

    fn check_decls(&mut self) -> Result {
        let decl_ids = self.m.decls.keys().collect::<Vec<_>>();
        let mut result = Ok(());

        for decl_id in decl_ids {
            result = result.and(self.check_decl(decl_id));
        }

        result
    }

    fn check_decl(&mut self, decl_id: DeclId) -> Result {
        let mut result = Ok(());
        let def = self.m.decls[decl_id].def;

        match &def.kind {
            ast::DeclKind::Dummy => {}

            ast::DeclKind::Fn(decl) => {
                result = result.and(self.check_fn_param_count(
                    decl.params.len(),
                    decl.fn_kw.as_ref().map(|token| token.span).into(),
                ));

                if decl.generics.is_some()
                    && !self.m.is_feature_enabled(FeatureKind::TypeParameters)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::FnHasTypeParams {
                            location: decl.fn_kw.as_ref().map(|token| token.span).into(),
                            generic_kw_location: decl
                                .generic_kw
                                .as_ref()
                                .map(|token| token.span)
                                .into(),
                        },
                        FeatureKind::TypeParameters,
                    ));
                }

                if decl.ret.is_none() && !self.m.is_feature_enabled(FeatureKind::TypeInference) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::TyInferenceNotAvailable {
                            location: decl.fn_kw.as_ref().map(|token| token.span).into(),
                        },
                        FeatureKind::TypeInference,
                    ));
                }

                if (decl.throws_kw.is_some() || !decl.throws.is_empty())
                    && !self.m.is_feature_enabled(FeatureKind::ThrowsAnnotations)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::FnHasThrows {
                            location: decl.fn_kw.as_ref().map(|token| token.span).into(),
                            throws_kw_location: decl
                                .throws_kw
                                .as_ref()
                                .map(|token| token.span)
                                .into(),
                        },
                        FeatureKind::ThrowsAnnotations,
                    ));
                }

                for subdecl in &decl.decls {
                    match subdecl.kind {
                        ast::DeclKind::Dummy => {}

                        ast::DeclKind::TypeAlias(_)
                        | ast::DeclKind::ExceptionType(_)
                        | ast::DeclKind::ExceptionVariant(_) => {
                            result = Err(());
                            self.diag.emit(SemaDiag::NestedDeclNotAllowed {
                                location: subdecl.location,
                                func_name_location: decl.binding.location(),
                            });
                        }

                        ast::DeclKind::Fn(_) => {
                            if !self
                                .m
                                .is_feature_enabled(FeatureKind::NestedFunctionDeclarations)
                            {
                                result = Err(());
                                self.diag.emit(make_feature_disabled_error(
                                    SemaDiag::NestedDeclNotAllowed {
                                        location: subdecl.location,
                                        func_name_location: decl.binding.location(),
                                    },
                                    FeatureKind::NestedFunctionDeclarations,
                                ));
                            }
                        }
                    }
                }
            }

            ast::DeclKind::TypeAlias(_) => {
                result = Err(());
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::TyAliasNotAllowed {
                        location: def.location,
                    },
                    FeatureKind::TypeAliases,
                ));
            }

            ast::DeclKind::ExceptionType(_) => {
                if !self
                    .m
                    .is_feature_enabled(FeatureKind::ExceptionTypeDeclaration)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ExceptionTyDeclNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::ExceptionTypeDeclaration,
                    ));
                }
            }

            ast::DeclKind::ExceptionVariant(_) => {
                if !self
                    .m
                    .is_feature_enabled(FeatureKind::OpenVariantExceptions)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ExceptionVariantDeclNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::OpenVariantExceptions,
                    ));
                }
            }
        }

        result
    }

    fn check_ty_exprs(&mut self) -> Result {
        let ty_expr_ids = self.m.ty_exprs.keys().collect::<Vec<_>>();
        let mut result = Ok(());

        for ty_expr_id in ty_expr_ids {
            result = result.and(self.check_ty_expr(ty_expr_id));
        }

        result
    }

    fn check_ty_expr(&mut self, ty_expr_id: TyExprId) -> Result {
        let mut result = Ok(());
        let def = self.m.ty_exprs[ty_expr_id].def;

        match &def.kind {
            ast::TyExprKind::Dummy => {}
            ast::TyExprKind::Bool(_) => {}
            ast::TyExprKind::Nat(_) => {}

            ast::TyExprKind::Ref(_) => {
                if !self.m.is_feature_enabled(FeatureKind::References) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ReferenceTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::References,
                    ));
                }
            }

            ast::TyExprKind::Sum(ty_expr) => {
                if !self.m.is_feature_enabled(FeatureKind::SumTypes) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::SumTyNotAllowed {
                            location: def.location,
                            plus_location: ty_expr
                                .plus_token
                                .as_ref()
                                .map(|token| token.span)
                                .into(),
                        },
                        FeatureKind::SumTypes,
                    ));
                }
            }

            ast::TyExprKind::Fn(ty_expr) => {
                result = result.and(self.check_fn_param_count(ty_expr.params.len(), def.location));
            }

            ast::TyExprKind::ForAll(_) => {
                if !self.m.is_feature_enabled(FeatureKind::UniversalTypes) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::UniversalTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::UniversalTypes,
                    ));
                }
            }

            ast::TyExprKind::Mu(_) => {
                if !self.m.is_feature_enabled(FeatureKind::RecursiveTypes) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::RecursiveTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::RecursiveTypes,
                    ));
                }
            }

            ast::TyExprKind::Tuple(ty_expr) => {
                result = result.and(self.check_tuple(ty_expr.elems.len(), def.location));
            }

            ast::TyExprKind::Record(ty_expr) => {
                result = result.and(self.check_record(ty_expr.fields.len(), def.location));
            }

            ast::TyExprKind::Variant(ty_expr) => {
                if !self.m.is_feature_enabled(FeatureKind::Variants) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::VariantNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Variants,
                    ));
                } else {
                    for field in &ty_expr.fields {
                        if field.ty_expr.is_none()
                            && !self.m.is_feature_enabled(FeatureKind::NullaryVariantLabels)
                        {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::NullaryVariantLabelNotAllowed {
                                    location: field.name.location(),
                                    variant_location: def.location,
                                },
                                FeatureKind::NullaryVariantLabels,
                            ));
                        }
                    }
                }
            }

            ast::TyExprKind::List(_) => {
                if !self.m.is_feature_enabled(FeatureKind::Lists) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ListNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Lists,
                    ));
                }
            }

            ast::TyExprKind::Unit(_) => {
                if !self.m.is_feature_enabled(FeatureKind::UnitType) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::UnitTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::UnitType,
                    ));
                }
            }

            ast::TyExprKind::Top(_) => {
                if !self.m.is_feature_enabled(FeatureKind::TopType) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::TopTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::TopType,
                    ));
                }
            }

            ast::TyExprKind::Bot(_) => {
                if !self.m.is_feature_enabled(FeatureKind::BottomType) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::BotTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::BottomType,
                    ));
                }
            }

            ast::TyExprKind::Auto(_) => {
                if !self.m.is_feature_enabled(FeatureKind::TypeInference) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::TyInferenceNotAvailable {
                            location: def.location,
                        },
                        FeatureKind::TypeInference,
                    ));
                }
            }

            ast::TyExprKind::Name(_) => {}
        }

        result
    }

    fn check_exprs(&mut self) -> Result {
        let expr_ids = self.m.exprs.keys().collect::<Vec<_>>();
        let mut result = Ok(());

        for expr_id in expr_ids {
            result = result.and(self.check_expr(expr_id));
        }

        result
    }

    fn check_expr(&mut self, expr_id: ExprId) -> Result {
        let mut result = Ok(());
        let def = self.m.exprs[expr_id].def;

        match &def.kind {
            ast::ExprKind::Dummy => {}
            ast::ExprKind::Bool(_) => {}

            ast::ExprKind::Unit(_) => {
                if !self.m.is_feature_enabled(FeatureKind::UnitType) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::UnitTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::UnitType,
                    ));
                }
            }

            ast::ExprKind::Int(expr) => {
                if expr.value != 0u32.into()
                    && !self.m.is_feature_enabled(FeatureKind::NaturalLiterals)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::NaturalLiteralNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::NaturalLiterals,
                    ));
                }
            }

            ast::ExprKind::Address(_) => {
                if !self.m.is_feature_enabled(FeatureKind::AddressLiterals) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::AddressLiteralNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::AddressLiterals,
                    ));
                }
            }

            ast::ExprKind::Name(_) => {}

            ast::ExprKind::Field(expr) => match &expr.field {
                ast::ExprFieldName::Name(_) if !self.m.is_feature_enabled(FeatureKind::Records) => {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::FieldExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Records,
                    ));
                }

                ast::ExprFieldName::Index(_, idx)
                    if !self.m.is_feature_enabled(FeatureKind::Tuples)
                        && !self.m.is_feature_enabled(FeatureKind::Pairs) =>
                {
                    result = Err(());
                    let mut report = make_feature_disabled_error(
                        SemaDiag::FieldExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Tuples,
                    );

                    if (1..=2).contains(idx) {
                        report.add_note(format!(
                            "alternately, you can enable pairs only with the #{} extension",
                            FeatureKind::Pairs.extension().unwrap(),
                        ));
                    }

                    self.diag.emit(report);
                }

                _ => {}
            },

            ast::ExprKind::Panic(_) => {
                if !self.m.is_feature_enabled(FeatureKind::Panic) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::PanicExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Panic,
                    ));
                }
            }

            ast::ExprKind::Throw(_) => {
                if !self.m.is_feature_enabled(FeatureKind::Exceptions) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ThrowExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Exceptions,
                    ));
                }
            }

            ast::ExprKind::Try(_) => {
                if !self.m.is_feature_enabled(FeatureKind::Exceptions) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::TryCatchExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Exceptions,
                    ));
                }
            }

            ast::ExprKind::Cast(_) => {
                if !self.m.is_feature_enabled(FeatureKind::CastExprs) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::CastExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::CastExprs,
                    ));
                }
            }

            ast::ExprKind::TryCast(_) => {
                if !self.m.is_feature_enabled(FeatureKind::TryCastExprs) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::CastExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::TryCastExprs,
                    ));
                }
            }

            ast::ExprKind::Fix(_) => {
                if !self.m.is_feature_enabled(FeatureKind::FixpointCombinator) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::FixExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::FixpointCombinator,
                    ));
                }
            }

            ast::ExprKind::Fold(_) | ast::ExprKind::Unfold(_) => {
                if !self.m.is_feature_enabled(FeatureKind::IsorecursiveTypes) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::FoldExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::IsorecursiveTypes,
                    ));
                }
            }

            ast::ExprKind::Apply(expr) => match expr.callee {
                ast::Callee::Builtin { builtin, .. } => match builtin {
                    ast::Builtin::Inl | ast::Builtin::Inr => {
                        if !self.m.is_feature_enabled(FeatureKind::SumTypes) {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::ApplyExprNotAllowed {
                                    location: def.location,
                                },
                                FeatureKind::SumTypes,
                            ));
                        }
                    }

                    ast::Builtin::Cons
                    | ast::Builtin::ListHead
                    | ast::Builtin::ListIsEmpty
                    | ast::Builtin::ListTail => {
                        if !self.m.is_feature_enabled(FeatureKind::Lists) {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::ApplyExprNotAllowed {
                                    location: def.location,
                                },
                                FeatureKind::Lists,
                            ));
                        }
                    }

                    ast::Builtin::Succ => {}

                    ast::Builtin::Not => {
                        if !self.m.is_feature_enabled(FeatureKind::LogicalOperators) {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::ApplyExprNotAllowed {
                                    location: def.location,
                                },
                                FeatureKind::LogicalOperators,
                            ));
                        }
                    }

                    ast::Builtin::NatPred => {}
                    ast::Builtin::NatIsZero => {}
                    ast::Builtin::NatRec => {}
                },

                ast::Callee::Expr(_) => {}
            },

            ast::ExprKind::TyApply(_) => {
                if !self.m.is_feature_enabled(FeatureKind::TypeParameters) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::TyApplyExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::TypeParameters,
                    ));
                }
            }

            ast::ExprKind::Ascription(expr) => {
                if !self.m.is_feature_enabled(FeatureKind::TypeAscriptions) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::AscriptionExprNotAllowed {
                            location: def.location,
                            as_location: expr.as_kw.as_ref().map(|token| token.span).into(),
                        },
                        FeatureKind::TypeAscriptions,
                    ));
                }
            }

            ast::ExprKind::Fn(expr) => {
                result = result.and(self.check_fn_param_count(expr.params.len(), def.location));
            }

            ast::ExprKind::Tuple(expr) => {
                result = result.and(self.check_tuple(expr.elems.len(), def.location));
            }

            ast::ExprKind::Record(expr) => {
                result = result.and(self.check_record(expr.fields.len(), def.location));
            }

            ast::ExprKind::Variant(expr) => {
                if !self.m.is_feature_enabled(FeatureKind::Variants) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::VariantNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Variants,
                    ));
                } else if expr.expr.is_none()
                    && !self.m.is_feature_enabled(FeatureKind::NullaryVariantLabels)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::NullaryVariantLabelNotAllowed {
                            location: expr.label.location(),
                            variant_location: def.location,
                        },
                        FeatureKind::NullaryVariantLabels,
                    ));
                }
            }

            ast::ExprKind::Match(_) => {}

            ast::ExprKind::List(_) => {
                if !self.m.is_feature_enabled(FeatureKind::Lists) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ListNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Lists,
                    ));
                }
            }

            ast::ExprKind::If(_) => {}

            ast::ExprKind::Seq(expr) => {
                if !self.m.is_feature_enabled(FeatureKind::Sequencing) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::SeqExprNotAllowed {
                            location: def.location,
                            semicolon_locations: expr
                                .exprs
                                .iter()
                                .map(|(_, token)| token.as_ref().map(|token| token.span).into())
                                .collect(),
                        },
                        FeatureKind::Sequencing,
                    ));
                }
            }

            ast::ExprKind::Let(expr) => {
                if expr.rec && !self.m.is_feature_enabled(FeatureKind::LetrecBindings) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::LetrecExprNotAllowed {
                            location: def.location,
                            letrec_location: expr.let_kw.as_ref().map(|token| token.span).into(),
                        },
                        FeatureKind::LetrecBindings,
                    ));
                } else if !expr.rec && !self.m.is_feature_enabled(FeatureKind::LetBindings) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::LetExprNotAllowed {
                            location: def.location,
                            let_location: expr.let_kw.as_ref().map(|token| token.span).into(),
                        },
                        FeatureKind::LetBindings,
                    ));
                }

                if expr.bindings.len() > 1 {
                    if expr.rec
                        && !self
                            .m
                            .is_feature_enabled(FeatureKind::MultipleLetrecBindings)
                    {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::MultipleLetrecBindingsNotAllowed {
                                location: def.location,
                                letrec_location: expr
                                    .let_kw
                                    .as_ref()
                                    .map(|token| token.span)
                                    .into(),
                            },
                            FeatureKind::MultipleLetrecBindings,
                        ));
                    } else if !expr.rec
                        && !self.m.is_feature_enabled(FeatureKind::MultipleLetBindings)
                    {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::MultipleLetBindingsNotAllowed {
                                location: def.location,
                                let_location: expr.let_kw.as_ref().map(|token| token.span).into(),
                            },
                            FeatureKind::MultipleLetBindings,
                        ));
                    }
                }

                for binding in &expr.bindings {
                    match binding.pat.kind {
                        ast::PatKind::Dummy => {}
                        ast::PatKind::Name(_) => {}
                        _ if self.m.is_feature_enabled(FeatureKind::LetPatterns) => {}

                        _ => {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::GeneralPatNotAllowed {
                                    location: binding.pat.location,
                                },
                                FeatureKind::LetPatterns,
                            ));
                        }
                    }
                }
            }

            ast::ExprKind::Generic(_) => {
                if !self.m.is_feature_enabled(FeatureKind::TypeParameters) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::GenericExprNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::TypeParameters,
                    ));
                }
            }

            ast::ExprKind::Unary(expr) => match expr.op {
                ast::UnOp::New => {
                    if !self.m.is_feature_enabled(FeatureKind::References) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::NewExprNotAllowed {
                                location: def.location,
                            },
                            FeatureKind::References,
                        ));
                    }
                }

                ast::UnOp::Deref => {
                    if !self.m.is_feature_enabled(FeatureKind::References) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::DerefExprNotAllowed {
                                location: def.location,
                                star_location: expr.token.as_ref().map(|token| token.span).into(),
                            },
                            FeatureKind::References,
                        ));
                    }
                }
            },

            ast::ExprKind::Binary(expr) => match expr.op {
                ast::BinOp::Add | ast::BinOp::Sub | ast::BinOp::Mul | ast::BinOp::Div => {
                    if !self.m.is_feature_enabled(FeatureKind::ArithmeticOperators) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::ArithOpNotAllowed {
                                location: def.location,
                                op_location: expr.token.as_ref().map(|token| token.span).into(),
                            },
                            FeatureKind::ArithmeticOperators,
                        ));
                    }
                }

                ast::BinOp::And | ast::BinOp::Or => {
                    if !self.m.is_feature_enabled(FeatureKind::LogicalOperators) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::LogicOpNotAllowed {
                                location: def.location,
                                op_location: expr.token.as_ref().map(|token| token.span).into(),
                            },
                            FeatureKind::LogicalOperators,
                        ));
                    }
                }

                ast::BinOp::Lt
                | ast::BinOp::Le
                | ast::BinOp::Gt
                | ast::BinOp::Ge
                | ast::BinOp::Eq
                | ast::BinOp::Ne => {
                    if !self.m.is_feature_enabled(FeatureKind::ComparisonOperators) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::CmpOpNotAllowed {
                                location: def.location,
                                op_location: expr.token.as_ref().map(|token| token.span).into(),
                            },
                            FeatureKind::ComparisonOperators,
                        ));
                    }
                }

                ast::BinOp::Assign => {
                    if !self.m.is_feature_enabled(FeatureKind::References) {
                        result = Err(());
                        self.diag.emit(make_feature_disabled_error(
                            SemaDiag::AssignExprNotAllowed {
                                location: def.location,
                                colon_eq_location: expr
                                    .token
                                    .as_ref()
                                    .map(|token| token.span)
                                    .into(),
                            },
                            FeatureKind::References,
                        ));
                    }
                }
            },
        }

        result
    }

    fn check_pats(&mut self) -> Result {
        let pat_ids = self.m.pats.keys().collect::<Vec<_>>();
        let mut result = Ok(());

        for pat_id in pat_ids {
            result = result.and(self.check_pat(pat_id));
        }

        result
    }

    fn check_pat(&mut self, pat_id: PatId) -> Result {
        let mut result = Ok(());
        let def = self.m.pats[pat_id].def;

        match &def.kind {
            ast::PatKind::Dummy => {}

            ast::PatKind::Variant(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::Variants) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::VariantNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Variants,
                    ));
                } else {
                    match &pat.pat {
                        Some(subpat) if !def.nested => {
                            result = result.and(self.check_nested_pat(subpat));
                        }

                        None if !self.m.is_feature_enabled(FeatureKind::NullaryVariantLabels) => {
                            result = Err(());
                            self.diag.emit(make_feature_disabled_error(
                                SemaDiag::NullaryVariantLabelNotAllowed {
                                    location: pat.label.location(),
                                    variant_location: def.location,
                                },
                                FeatureKind::NullaryVariantLabels,
                            ));
                        }

                        _ => {}
                    }
                }
            }

            ast::PatKind::Cons(pat) => {
                if !matches!(pat.cons, ast::Cons::Inl | ast::Cons::Inr)
                    && !self.m.is_feature_enabled(FeatureKind::StructuralPatterns)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                } else {
                    match pat.cons {
                        ast::Cons::Inl | ast::Cons::Inr => {
                            if !self.m.is_feature_enabled(FeatureKind::SumTypes) {
                                result = Err(());
                                self.diag.emit(make_feature_disabled_error(
                                    SemaDiag::InjectionPatNotAllowed {
                                        location: def.location,
                                    },
                                    FeatureKind::SumTypes,
                                ));
                            }
                        }

                        ast::Cons::Cons => {
                            if !self.m.is_feature_enabled(FeatureKind::Lists) {
                                result = Err(());
                                self.diag.emit(make_feature_disabled_error(
                                    SemaDiag::ListNotAllowed {
                                        location: def.location,
                                    },
                                    FeatureKind::Lists,
                                ));
                            }
                        }

                        ast::Cons::Succ => {}
                    }

                    if !def.nested {
                        for arg in &pat.args {
                            result = result.and(self.check_nested_pat(arg));
                        }
                    }
                }
            }

            ast::PatKind::Tuple(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                } else {
                    result = result.and(self.check_tuple(pat.elems.len(), def.location));

                    if !def.nested {
                        for elem in &pat.elems {
                            result = result.and(self.check_nested_pat(elem));
                        }
                    }
                }
            }

            ast::PatKind::Record(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                } else {
                    result = result.and(self.check_record(pat.fields.len(), def.location));

                    if !def.nested {
                        for field in &pat.fields {
                            result = result.and(self.check_nested_pat(&field.pat));
                        }
                    }
                }
            }

            ast::PatKind::List(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                } else if !self.m.is_feature_enabled(FeatureKind::Lists) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::ListNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::Lists,
                    ));
                } else if !def.nested {
                    for elem in &pat.elems {
                        result = result.and(self.check_nested_pat(elem));
                    }
                }
            }

            ast::PatKind::Bool(_) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                }
            }

            ast::PatKind::Unit(_) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                } else if !self.m.is_feature_enabled(FeatureKind::UnitType) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::UnitTyNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::UnitType,
                    ));
                }
            }

            ast::PatKind::Int(_) => {
                if !self.m.is_feature_enabled(FeatureKind::StructuralPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::StructuralPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::StructuralPatterns,
                    ));
                }
            }

            ast::PatKind::Name(_) => {}

            ast::PatKind::Ascription(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::PatternAscriptions) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::AscriptionPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::PatternAscriptions,
                    ));
                } else if !def.nested {
                    result = result.and(self.check_nested_pat(&pat.pat));
                }
            }

            ast::PatKind::Cast(pat) => {
                if !self.m.is_feature_enabled(FeatureKind::CastPatterns) {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaDiag::CastPatNotAllowed {
                            location: def.location,
                        },
                        FeatureKind::CastPatterns,
                    ));
                } else if !def.nested {
                    result = result.and(self.check_nested_pat(&pat.pat));
                }
            }
        }

        result
    }

    fn check_fn_param_count(&mut self, count: usize, location: Location) -> Result {
        match count {
            0 if !self.m.is_feature_enabled(FeatureKind::NullaryFunctions) => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::NoFnParams { location },
                    FeatureKind::NullaryFunctions,
                ));

                Err(())
            }

            2.. if !self
                .m
                .is_feature_enabled(FeatureKind::MultiparameterFunctions) =>
            {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::MultipleFnParams { location },
                    FeatureKind::MultiparameterFunctions,
                ));

                Err(())
            }

            _ => Ok(()),
        }
    }

    fn check_tuple(&mut self, count: usize, location: Location) -> Result {
        match count {
            _ if self.m.is_feature_enabled(FeatureKind::Tuples) => Ok(()),
            0 if self.m.is_feature_enabled(FeatureKind::EmptyTuple) => Ok(()),
            2 if self.m.is_feature_enabled(FeatureKind::Pairs) => Ok(()),

            0 => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::EmptyTupleNotAllowed { location },
                    FeatureKind::EmptyTuple,
                ));

                Err(())
            }

            2 => {
                self.diag.emit(
                    make_feature_disabled_error(
                        SemaDiag::TupleNotAllowed { location },
                        FeatureKind::Pairs,
                    )
                    .with_note(format!(
                        "alternately, you can enable tuples of arbitrary sizes with the #{} extension",
                        FeatureKind::Tuples.extension().unwrap(),
                    )),
                );

                Err(())
            }

            _ if self.m.is_feature_enabled(FeatureKind::Pairs) => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::IllegalPairElementCount { location },
                    FeatureKind::Tuples,
                ));

                Err(())
            }

            _ => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::TupleNotAllowed { location },
                    FeatureKind::Tuples,
                ));

                Err(())
            }
        }
    }

    fn check_record(&mut self, count: usize, location: Location) -> Result {
        match count {
            _ if self.m.is_feature_enabled(FeatureKind::Records) => Ok(()),
            0 if self.m.is_feature_enabled(FeatureKind::EmptyTuple) => Ok(()),

            0 => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::EmptyTupleNotAllowed { location },
                    FeatureKind::EmptyTuple,
                ));

                Err(())
            }

            _ => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::RecordNotAllowed { location },
                    FeatureKind::Records,
                ));

                Err(())
            }
        }
    }

    fn check_nested_pat(&mut self, pat: &ast::Pat<'_>) -> Result {
        match pat.kind {
            ast::PatKind::Dummy => Ok(()),
            ast::PatKind::Name(_) => Ok(()),
            _ if self.m.is_feature_enabled(FeatureKind::StructuralPatterns) => Ok(()),

            _ => {
                self.diag.emit(make_feature_disabled_error(
                    SemaDiag::NestedPatNotAllowed {
                        location: pat.location,
                    },
                    FeatureKind::StructuralPatterns,
                ));

                Err(())
            }
        }
    }
}
