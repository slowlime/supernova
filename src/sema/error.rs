use ariadne::{Color, Label, Report, ReportBuilder, ReportKind};
use thiserror::Error;

use crate::diag::IntoReportBuilder;
use crate::location::Location;
use crate::util::format_iter;

use super::feature::{EnableReason, FeatureKind};

#[derive(Error, Debug, Clone)]
pub enum SemaError {
    #[error(
        "features {} conflict with each other",
        format_iter(
            features.iter().map(|&(feature, _)| feature),
            "and",
            "<unknown>",
        ),
    )]
    ConflictingFeatures {
        location: Location,
        features: Vec<(FeatureKind, EnableReason)>,
    },

    #[error("the function must have parameters")]
    NoFunctionParams { location: Location },

    #[error("the function cannot have multiple parameters")]
    MultipleFunctionParams { location: Location },

    #[error("the function cannot have type parameters")]
    FunctionHasTypeParams {
        location: Location,
        generic_kw_location: Location,
    },

    #[error("the function cannot have exception specifiers")]
    FunctionHasThrows {
        location: Location,
        throws_kw_location: Location,
    },

    #[error("this declaration cannot be nested within a function")]
    IllegalNestedDecl {
        location: Location,
        func_name_location: Location,
    },

    #[error("type aliases are not allowed")]
    TypeAliasNotAllowed { location: Location },

    #[error("exception type declarations are not allowed")]
    ExceptionTypeDeclNotAllowed { location: Location },

    #[error("exception variant declarations are not allowed")]
    ExceptionVariantDeclNotAllowed { location: Location },
}

impl IntoReportBuilder for SemaError {
    fn into_report_builder(self) -> ReportBuilder<'static, Location> {
        match &self {
            Self::ConflictingFeatures { location, features } => {
                let mut builder = Report::build(ReportKind::Error, *location)
                    .with_code("sema::conflicting_features")
                    .with_message(&self);

                for (feature, reason) in features {
                    match reason {
                        EnableReason::Extension(location @ Location::UserCode(_)) => builder
                            .add_label(Label::new(*location).with_message(format!(
                                "the feature {feature} was enabled by the extension here"
                            ))),

                        EnableReason::Extension(_) => builder
                            .add_note(format!("the feature {feature} was enabled by an extension")),

                        EnableReason::Feature(f) => builder.add_note(format!(
                            "the feature {feature} was enabled as a dependency of the feature {f}"
                        )),
                    }
                }

                builder
            }

            Self::NoFunctionParams { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::no_function_params")
                .with_message(&self),

            Self::MultipleFunctionParams { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::multiple_function_params")
                    .with_message(&self)
            }

            Self::FunctionHasTypeParams {
                location,
                generic_kw_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::function_has_type_params")
                    .with_message(&self);

                if generic_kw_location.has_span() {
                    report.add_label(Label::new(*generic_kw_location).with_color(Color::Red));
                }

                report
            }

            Self::FunctionHasThrows {
                location,
                throws_kw_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::function_has_throws")
                    .with_message(&self);

                if throws_kw_location.has_span() {
                    report.add_label(Label::new(*throws_kw_location).with_color(Color::Red));
                }

                report
            }

            Self::IllegalNestedDecl {
                location,
                func_name_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::illegal_nested_decl")
                    .with_message(&self);

                if func_name_location.has_span() {
                    report.add_label(
                        Label::new(*func_name_location)
                            .with_message("in the function defined here"),
                    );
                }

                report
            }

            Self::TypeAliasNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::type_alias_not_allowed")
                .with_message(&self),

            Self::ExceptionTypeDeclNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::exception_type_decl_not_allowed")
                    .with_message(&self)
            }

            Self::ExceptionVariantDeclNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::exception_variant_decl_not_allowed")
                    .with_message(&self)
            }
        }
    }
}
