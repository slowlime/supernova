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

    #[error("reference types are not allowed")]
    ReferenceTypeNotAllowed { location: Location },

    #[error("sum types are not allowed")]
    SumTypeNotAllowed {
        location: Location,
        plus_location: Location,
    },

    #[error("universal types are not allowed")]
    UniversalTypeNotAllowed { location: Location },

    #[error("recursive types (μ-types) are not allowed")]
    RecursiveTypeNotAllowed { location: Location },

    #[error("empty tuples/records are not allowed")]
    EmptyTupleNotAllowed { location: Location },

    #[error("tuples are not allowed")]
    TupleNotAllowed { location: Location },

    #[error("pairs must have exactly two elements")]
    IllegalPairElementCount { location: Location },

    #[error("records are not allowed")]
    RecordNotAllowed { location: Location },

    #[error("variants are not allowed")]
    VariantNotAllowed { location: Location },

    #[error("lists are not allowed")]
    ListNotAllowed { location: Location },

    #[error("nullary variant labels are not allowed")]
    NullaryVariantLabelNotAllowed {
        location: Location,
        variant_location: Location,
    },

    #[error("unit types are not allowed")]
    UnitTypeNotAllowed { location: Location },

    #[error("the top type is not allowed")]
    TopTypeNotAllowed { location: Location },

    #[error("the botom type is not allowed")]
    BotTypeNotAllowed { location: Location },

    #[error("explicit type inference is not available")]
    TypeInferenceNotAvailable { location: Location },

    #[error("natural literals are not allowed")]
    NaturalLiteralNotAllowed { location: Location },

    #[error("memory address literals are not allowed")]
    AddressLiteralNotAllowed { location: Location },

    #[error("field expressions are not allowed")]
    FieldExprNotAllowed { location: Location },

    #[error("panic expressions are not allowed")]
    PanicExprNotAllowed { location: Location },

    #[error("throw expressions are not allowed")]
    ThrowExprNotAllowed { location: Location },

    #[error("try/catch expressions are not allowed")]
    TryCatchExprNotAllowed { location: Location },

    #[error("cast expressions are not allowed")]
    CastExprNotAllowed { location: Location },

    #[error("fixpoint combinator expressions are not allowed")]
    FixExprNotAllowed { location: Location },

    #[error("explicit fold/unfold expressions are not allowed")]
    FoldExprNotAllowed { location: Location },

    #[error("this function application expression is not allowed")]
    ApplyExprNotAllowed { location: Location },

    #[error("type application expressions are not allowed")]
    TyApplyExprNotAllowed { location: Location },

    #[error("type ascription expressions is not allowed")]
    AscriptionExprNotAllowed {
        location: Location,
        as_location: Location,
    },

    #[error("match expressions are not allowed")]
    MatchExprNotAllowed { location: Location },

    #[error("sequence expressions are not allowed")]
    SeqExprNotAllowed {
        location: Location,
        semicolon_locations: Vec<Location>,
    },

    #[error("`let` expressions are not allowed")]
    LetExprNotAllowed {
        location: Location,
        let_location: Location,
    },

    #[error("`letrec` expressions are not allowed")]
    LetrecExprNotAllowed {
        location: Location,
        letrec_location: Location,
    },

    #[error("`generic` (type abstraction) expressions are not allowed")]
    GenericExprNotAllowed { location: Location },

    #[error("`new` expressions are not allowed")]
    NewExprNotAllowed { location: Location },

    #[error("dereference expressions are not allowed")]
    DerefExprNotAllowed {
        location: Location,
        star_location: Location,
    },

    #[error("arithmetic operators are not allowed")]
    ArithOpNotAllowed {
        location: Location,
        op_location: Location,
    },

    #[error("comparison operators are not allowed")]
    ComparisonOpNotAllowed {
        location: Location,
        op_location: Location,
    },

    #[error("assignment expressions are not allowed")]
    AssignExprNotAllowed {
        location: Location,
        colon_eq_location: Location,
    },

    #[error("nested patterns are not allowed")]
    NestedPatternNotAllowed { location: Location },

    #[error("general patterns are not allowed")]
    GeneralPatternNotAllowed { location: Location },

    #[error("structural patterns are not allowed")]
    StructuralPatternNotAllowed { location: Location },

    #[error("injection patterns are not allowed")]
    InjectionPatternNotAllowed { location: Location },

    #[error("ascription patterns are not allowed")]
    AscriptionPatternNotAllowed { location: Location },

    #[error("cast patterns are not allowed")]
    CastPatternNotAllowed { location: Location },
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

            Self::ReferenceTypeNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::reference_type_not_allowed")
                    .with_message(&self)
            }

            Self::SumTypeNotAllowed {
                location,
                plus_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::sum_type_not_allowed")
                    .with_message(&self);

                if plus_location.has_span() {
                    report.add_label(Label::new(*plus_location).with_color(Color::Red));
                }

                report
            }

            Self::UniversalTypeNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::universal_type_not_allowed")
                    .with_message(&self)
            }

            Self::RecursiveTypeNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::recursive_type_not_allowed")
                    .with_message(&self)
            }

            Self::EmptyTupleNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::empty_tuple_not_allowed")
                .with_message(&self),

            Self::TupleNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::tuple_not_allowed")
                .with_message(&self),

            Self::IllegalPairElementCount { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::illegal_pair_element_count")
                    .with_message(&self)
            }

            Self::RecordNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::record_not_allowed")
                .with_message(&self),

            Self::VariantNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::variant_not_allowed")
                .with_message(&self),

            Self::NullaryVariantLabelNotAllowed {
                location,
                variant_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::nullary_variant_label_not_allowed")
                    .with_message(&self);

                if variant_location.has_span() {
                    report.add_label(
                        Label::new(*variant_location).with_message("in the variant here"),
                    )
                }

                report
            }

            Self::ListNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::list_not_allowed")
                .with_message(&self),

            Self::UnitTypeNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unit_type_not_allowed")
                .with_message(&self),

            Self::TopTypeNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::top_type_not_allowed")
                .with_message(&self),

            Self::BotTypeNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::bot_type_not_allowed")
                .with_message(&self),

            Self::TypeInferenceNotAvailable { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::type_inference_not_available")
                    .with_message(&self)
            }

            Self::NaturalLiteralNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::natural_literal_not_allowed")
                    .with_message(&self)
            }

            Self::AddressLiteralNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::address_literal_not_allowed")
                    .with_message(&self)
            }

            Self::FieldExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::field_expr_not_allowed")
                .with_message(&self),

            Self::PanicExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::panic_expr_not_allowed")
                .with_message(&self),

            Self::ThrowExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::throw_expr_not_allowed")
                .with_message(&self),

            Self::TryCatchExprNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::try_catch_expr_not_allowed")
                    .with_message(&self)
            }

            Self::CastExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::cast_expr_not_allowed")
                .with_message(&self),

            Self::FixExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::fix_expr_not_allowed")
                .with_message(&self),

            Self::FoldExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::fold_expr_not_allowed")
                .with_message(&self),

            Self::ApplyExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::apply_expr_not_allowed")
                .with_message(&self),

            Self::TyApplyExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::ty_apply_expr_not_allowed")
                .with_message(&self),

            Self::AscriptionExprNotAllowed {
                location,
                as_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::ascription_expr_not_allowed")
                    .with_message(&self);

                if as_location.has_span() {
                    report.add_label(Label::new(*as_location).with_color(Color::Red));
                }

                report
            }

            Self::MatchExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::match_expr_not_allowed")
                .with_message(&self),

            Self::SeqExprNotAllowed {
                location,
                semicolon_locations,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::seq_expr_not_allowed")
                    .with_message(&self);

                for semicolon_location in semicolon_locations {
                    if semicolon_location.has_span() {
                        report.add_label(Label::new(*semicolon_location).with_color(Color::Red));
                    }
                }

                report
            }

            Self::LetExprNotAllowed {
                location,
                let_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::let_expr_not_allowed")
                    .with_message(&self);

                if let_location.has_span() {
                    report.add_label(Label::new(*let_location).with_color(Color::Red));
                }

                report
            }

            Self::LetrecExprNotAllowed {
                location,
                letrec_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::letrec_expr_not_allowed")
                    .with_message(&self);

                if letrec_location.has_span() {
                    report.add_label(Label::new(*letrec_location).with_color(Color::Red));
                }

                report
            }

            Self::GenericExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::generic_expr_not_allowed")
                .with_message(&self),

            Self::NewExprNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::new_expr_not_allowed")
                .with_message(&self),

            Self::DerefExprNotAllowed {
                location,
                star_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::deref_expr_not_allowed")
                    .with_message(&self);

                if star_location.has_span() {
                    report.add_label(Label::new(*star_location).with_color(Color::Red));
                }

                report
            }

            Self::ArithOpNotAllowed {
                location,
                op_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::arith_op_not_allowed")
                    .with_message(&self);

                if op_location.has_span() {
                    report.add_label(Label::new(*op_location).with_color(Color::Red));
                }

                report
            }

            Self::ComparisonOpNotAllowed {
                location,
                op_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::cmp_op_not_allowed")
                    .with_message(&self);

                if op_location.has_span() {
                    report.add_label(Label::new(*op_location).with_color(Color::Red));
                }

                report
            }

            Self::AssignExprNotAllowed {
                location,
                colon_eq_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::assign_expr_not_allowed")
                    .with_message(&self);

                if colon_eq_location.has_span() {
                    report.add_label(Label::new(*colon_eq_location).with_color(Color::Red));
                }

                report
            }

            Self::NestedPatternNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::nested_pattern_not_allowed")
                    .with_message(&self)
            }

            Self::GeneralPatternNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::general_pattern_not_allowed")
                    .with_message(&self)
            }

            Self::StructuralPatternNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::structural_pattern_not_allowed")
                    .with_message(&self)
            }

            Self::InjectionPatternNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::injection_pattern_not_allowed")
                    .with_message(&self)
            }

            Self::AscriptionPatternNotAllowed { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ascription_pattern_not_allowed")
                    .with_message(&self)
            }

            Self::CastPatternNotAllowed { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::cast_pattern_not_allowed")
                .with_message(&self),
        }
    }
}
