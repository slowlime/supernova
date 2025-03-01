use ariadne::ReportBuilder;
use fxhash::FxHashSet;

use crate::ast;
use crate::diag::{DiagCtx, IntoReportBuilder};
use crate::location::Location;

use super::feature::{EnableReason, Feature, FeatureKind};
use super::{DeclId, ExprId, Module, PatId, Result, SemaError, TyExprId};

impl Module<'_> {
    pub(super) fn process_features(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

struct Pass<'ast, 'm, D> {
    m: &'m mut Module<'ast>,
    diag: &'m mut D,
}

fn make_feature_disabled_error(
    report: impl IntoReportBuilder,
    feature: FeatureKind,
) -> ReportBuilder<'static, Location> {
    let mut report = report
        .into_report_builder()
        .with_note(format!("feature {feature} is disabled"));

    if let Some(extension) = feature.extension() {
        report = report.with_help(format!(
            "you can enable the feature with the {extension} extension"
        ));
    }

    report
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

            let location = conflicting_features
                .iter()
                .filter_map(|(_, reason)| match reason {
                    EnableReason::Extension(location) => Some(*location),
                    _ => None,
                })
                .min()
                .unwrap_or(self.m.location);

            self.diag.emit(SemaError::ConflictingFeatures {
                location,
                features: conflicting_features,
            });
            result = Err(());
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
                result = result.and(self.check_fn_param_count(decl.params.len(), def.location));

                if (decl.generic_kw.is_some() || !decl.generics.is_empty())
                    && !self.m.is_feature_enabled(FeatureKind::TypeParameters)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaError::FunctionHasTypeParams {
                            location: def.location,
                            generic_kw_location: decl
                                .generic_kw
                                .as_ref()
                                .map(|token| token.span)
                                .into(),
                        },
                        FeatureKind::TypeParameters,
                    ));
                }

                // TODO: check the return type?

                if (decl.throws_kw.is_some() || !decl.throws.is_empty())
                    && !self.m.is_feature_enabled(FeatureKind::Exceptions)
                {
                    result = Err(());
                    self.diag.emit(make_feature_disabled_error(
                        SemaError::FunctionHasThrows {
                            location: def.location,
                            throws_kw_location: decl
                                .throws_kw
                                .as_ref()
                                .map(|token| token.span)
                                .into(),
                        },
                        FeatureKind::Exceptions,
                    ));
                }

                for subdecl in &decl.decls {
                    match subdecl.kind {
                        ast::DeclKind::Dummy => {}

                        ast::DeclKind::TypeAlias(_)
                        | ast::DeclKind::ExceptionType(_)
                        | ast::DeclKind::ExceptionVariant(_) => {
                            result = Err(());
                            self.diag.emit(SemaError::IllegalNestedDecl {
                                location: subdecl.location,
                                func_name_location: decl.name.location(),
                            });
                        }

                        ast::DeclKind::Fn(_) => {
                            if !self
                                .m
                                .is_feature_enabled(FeatureKind::NestedFunctionDeclarations)
                            {
                                result = Err(());
                                self.diag.emit(make_feature_disabled_error(
                                    SemaError::IllegalNestedDecl {
                                        location: subdecl.location,
                                        func_name_location: decl.name.location(),
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
                    SemaError::TypeAliasNotAllowed {
                        location: def.location,
                    },
                    FeatureKind::TypeAliases,
                ));
            }

            ast::DeclKind::ExceptionType(_) => {
                result = Err(());
                self.diag.emit(make_feature_disabled_error(
                    SemaError::ExceptionTypeDeclNotAllowed {
                        location: def.location,
                    },
                    FeatureKind::ExceptionTypeDeclaration,
                ));
            }

            ast::DeclKind::ExceptionVariant(_) => {
                result = Err(());
                self.diag.emit(make_feature_disabled_error(
                    SemaError::ExceptionVariantDeclNotAllowed {
                        location: def.location,
                    },
                    FeatureKind::OpenVariantExceptions,
                ));
            }
        }

        result
    }

    fn check_fn_param_count(&mut self, count: usize, location: Location) -> Result {
        match count {
            0 if !self.m.is_feature_enabled(FeatureKind::NullaryFunctions) => {
                self.diag.emit(make_feature_disabled_error(
                    SemaError::NoFunctionParams { location },
                    FeatureKind::NullaryFunctions,
                ));

                Err(())
            }

            2.. if !self
                .m
                .is_feature_enabled(FeatureKind::MultiparameterFunctions) =>
            {
                self.diag.emit(make_feature_disabled_error(
                    SemaError::MultipleFunctionParams { location },
                    FeatureKind::MultiparameterFunctions,
                ));

                Err(())
            }

            _ => Ok(()),
        }
    }

    fn check_ty_exprs(&mut self) -> Result {
        todo!()
    }

    fn check_ty_expr(&mut self, ty_expr_id: TyExprId) -> Result {
        todo!()
    }

    fn check_exprs(&mut self) -> Result {
        todo!()
    }

    fn check_expr(&mut self, expr_id: ExprId) -> Result {
        todo!()
    }

    fn check_pats(&mut self) -> Result {
        todo!()
    }

    fn check_pat(&mut self, pat_id: PatId) -> Result {
        todo!()
    }
}
