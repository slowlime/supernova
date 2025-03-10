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

    #[error("the field `{name}` is declared multiple times in the same record type")]
    DuplicateRecordTypeFields {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the label `{name}` is declared multiple times in the same variant type")]
    DuplicateVariantTypeFields {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the field `{name}` is initialized multiple times in the same record")]
    DuplicateRecordFields {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the field `{name}` is matched multiple times in the same record pattern")]
    DuplicateRecordPatternFields {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the type `{name}` is undefined")]
    UndefinedTy { name: String, location: Location },

    #[error("the variable `{name}` is undefined")]
    UndefinedVariable { name: String, location: Location },

    #[error("the variable `{name}` is defined multiple times")]
    DuplicateVariableDef {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the type `{name}` is defined multiple times")]
    DuplicateTyDef {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the program is missing a `main` function")]
    MissingMain { location: Location },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got `{actual_ty}`")]
    UnexpectedTypeForExpression {
        location: Location,
        expected_ty: String,
        actual_ty: String,
    },

    #[error("the record has no field `{field}`")]
    UnexpectedFieldAccess {
        location: Location,
        field: String,
        record_ty: String,
        base_location: Location,
        field_location: Location,
    },

    #[error("cannot get the field `{field}` of a non-record type `{actual_ty}`")]
    ExtractingFieldOfNonRecordTy {
        location: Location,
        field: String,
        actual_ty: String,
        base_location: Location,
        field_location: Location,
    },

    #[error("cannot index a non-tuple type `{actual_ty}`")]
    IndexingNonTupleTy {
        location: Location,
        actual_ty: String,
        base_location: Location,
        field_location: Location,
    },

    #[error("the tuple has no element `{idx}`")]
    TupleIndexOutOfBounds {
        location: Location,
        idx: usize,
        tuple_len: usize,
        actual_ty: String,
        base_location: Location,
        field_location: Location,
    },

    #[error("the fixpoint combinator can only be applied to functions")]
    FixNotFunction {
        location: Location,
        actual_ty: String,
        inner_location: Location,
    },

    #[error("the fixpoint combinator requires a function of a single argument")]
    FixWrongFunctionParamCount {
        location: Location,
        actual_ty: String,
        inner_location: Location,
    },

    #[error("the expression has a wrong number of arguments: expected {expected}, got {actual}")]
    IncorrectNumberOfArgumentsInExpr {
        location: Location,
        expected: usize,
        actual: usize,
    },

    #[error("the pattern has a wrong number of arguments: expected {expected}, got {actual}")]
    IncorrectNumberOfArgumentsInPat {
        location: Location,
        expected: usize,
        actual: usize,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a sum type")]
    UnexpectedInjection {
        location: Location,
        expected_ty: String,
    },

    #[error("could not determine the type of a sum type injection expression")]
    AmbiguousSumTypeInExpr { location: Location },

    #[error("could not determine the type of a sum type injection pattern")]
    AmbiguousSumTypeInPat { location: Location },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a list type")]
    UnexpectedList {
        location: Location,
        expected_ty: String,
    },

    #[error("this expression has a wrong type: expected a list, got `{actual_ty}`")]
    ExprTyNotList {
        location: Location,
        actual_ty: String,
    },

    #[error("cannot apply arguments to an expression of a non-function type `{actual_ty}`")]
    ApplyNotFunction {
        location: Location,
        actual_ty: String,
        callee_location: Location,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a function type")]
    UnexpectedLambda {
        location: Location,
        expected_ty: String,
    },

    #[error(
        "the parameter count in this anonymous function ({actual}) does not match the expected count ({expected})"
    )]
    UnexpectedNumberOfParametersInLambda {
        location: Location,
        actual: usize,
        expected: usize,
    },

    #[error(
        "the parameter `{name}` has an unexpected type: expected `{expected_ty}`, got `{actual_ty}`"
    )]
    UnexpectedTypeForParameter {
        location: Location,
        name: String,
        expected_ty: String,
        actual_ty: String,
        expr_location: Location,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a tuple type")]
    UnexpectedTuple {
        location: Location,
        expected_ty: String,
    },

    #[error(
        "the number of elements in the tuple expression ({actual}) does not match the expected count ({expected})"
    )]
    UnexpectedTupleLengthInExpr {
        location: Location,
        actual: usize,
        expected: usize,
    },

    #[error(
        "the number of elements in the tuple pattern ({actual}) does not match the expected count ({expected})"
    )]
    UnexpectedTupleLengthInPat {
        location: Location,
        actual: usize,
        expected: usize,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a record type")]
    UnexpectedRecord {
        location: Location,
        expected_ty: String,
    },

    #[error("the field `{name}` is not present in the expected type `{expected_ty}`")]
    UnexpectedRecordFieldInExpr {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error("the field `{name}` is not present in the expected type `{expected_ty}`")]
    UnexpectedRecordFieldInPat {
        location: Location,
        name: String,
        expected_ty: String,
        pat_location: Location,
    },

    #[error("the field `{name}` is missing to match the expected type `{expected_ty}`")]
    MissingRecordFieldInExpr {
        location: Location,
        name: String,
        expected_ty: String,
    },

    #[error("the field `{name}` is missing to match the expected type `{expected_ty}`")]
    MissingRecordFieldInPat {
        location: Location,
        name: String,
        expected_ty: String,
    },

    #[error("could not determine the type of a variant expression")]
    AmbiguousVariantExprType { location: Location },

    #[error("could not determine the type of a variant pattern")]
    AmbiguousVariantPatType { location: Location },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a variant type")]
    UnexpectedVariant {
        location: Location,
        expected_ty: String,
    },

    #[error("the label `{name}` is not present in the expected type `{expected_ty}`")]
    UnexpectedVariantLabelInExpr {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error("the label `{name}` is not present in the expected type `{expected_ty}`")]
    UnexpectedVariantLabelInPat {
        location: Location,
        name: String,
        expected_ty: String,
        pat_location: Location,
    },

    #[error(
        "the label `{name}` does not have associated data in the expected type `{expected_ty}`"
    )]
    UnexpectedDataForNullaryLabel {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error(
        "the label `{name}` does not have associated data in the expected type `{expected_ty}`"
    )]
    UnexpectedNonNullaryVariantPattern {
        location: Location,
        name: String,
        expected_ty: String,
        pat_location: Location,
    },

    #[error("the label `{name}` must have associated data")]
    MissingDataForLabel {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error("the label `{name}` must have associated data")]
    UnexpectedNullaryVariantPattern {
        location: Location,
        name: String,
        expected_ty: String,
        pat_location: Location,
    },

    #[error("this match expression must have at least a single match arm")]
    IllegalEmptyMatching { location: Location },

    #[error("could not determine the type of an empty list expression")]
    AmbiguousEmptyListExprTy { location: Location },

    #[error("could not determine the type of an empty list pattern")]
    AmbiguousEmptyListPatTy { location: Location },

    #[error("this pattern cannot be used with values of the type `{expected_ty}`")]
    UnexpectedPatternForType {
        location: Location,
        expected_ty: String,
    },

    #[error("could not determine the type of a binding pattern")]
    AmbiguousBindingPatType { location: Location },

    #[error("the match arms are non-exhaustive")]
    NonExhaustiveMatchPatterns {
        location: Location,
        scrutinee_location: Location,
        witness: String,
    },

    #[error("the pattern is not irrefutable")]
    NonIrrefutableLetPattern { location: Location, witness: String },
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

            Self::DuplicateRecordTypeFields {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_record_type_fields")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the field was previously declared here"),
                    );
                }

                report
            }

            Self::DuplicateVariantTypeFields {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_variant_type_fields")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the field was previously declared here"),
                    );
                }

                report
            }

            Self::DuplicateRecordFields {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_record_fields")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the field was previously declared here"),
                    );
                }

                report
            }

            Self::DuplicateRecordPatternFields {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_record_pattern_fields")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the field was previously matched here"),
                    );
                }

                report
            }

            Self::UndefinedTy { name: _, location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::undefined_type")
                .with_message(&self),

            Self::UndefinedVariable { name: _, location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::undefined_variable")
                    .with_message(&self)
            }

            Self::DuplicateVariableDef {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_variable_def")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the variable was previously defined here"),
                    );
                }

                report
            }

            Self::DuplicateTyDef {
                name: _,
                location,
                prev_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::duplicate_ty_def")
                    .with_message(&self);

                if prev_location.has_span() {
                    report.add_label(
                        Label::new(*prev_location)
                            .with_message("the type was previously defined here"),
                    );
                }

                report
            }

            Self::MissingMain { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::missing_main")
                .with_message(&self),

            Self::UnexpectedTypeForExpression {
                location,
                expected_ty: _,
                actual_ty,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_type_for_expression")
                .with_message(&self)
                .with_label(
                    Label::new(*location)
                        .with_message(format!("this expression has the type `{actual_ty}`"))
                        .with_color(Color::Red),
                ),

            Self::UnexpectedFieldAccess {
                location,
                field: _,
                record_ty,
                base_location,
                field_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_field_access")
                    .with_message(&self);

                if base_location.has_span() {
                    report.add_label(
                        Label::new(*base_location)
                            .with_message(format!("the record has the type `{record_ty}`")),
                    );
                }

                if field_location.has_span() {
                    report.add_label(Label::new(*field_location).with_color(Color::Red));
                }

                report
            }

            Self::ExtractingFieldOfNonRecordTy {
                location,
                field: _,
                actual_ty,
                base_location,
                field_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::not_a_record")
                    .with_message(&self);

                if base_location.has_span() {
                    report.add_label(
                        Label::new(*base_location)
                            .with_message(format!("this expression has the type `{actual_ty}`")),
                    );
                }

                if field_location.has_span() {
                    report.add_label(Label::new(*field_location).with_color(Color::Red));
                }

                report
            }

            Self::IndexingNonTupleTy {
                location,
                actual_ty,
                base_location,
                field_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::not_a_tuple")
                    .with_message(&self);

                if base_location.has_span() {
                    report.add_label(
                        Label::new(*base_location)
                            .with_message(format!("this expression has the type `{actual_ty}`")),
                    );
                }

                if field_location.has_span() {
                    report.add_label(Label::new(*field_location).with_color(Color::Red));
                }

                report
            }

            Self::TupleIndexOutOfBounds {
                location,
                idx,
                tuple_len,
                actual_ty,
                base_location,
                field_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::tuple_index_out_of_bounds")
                    .with_message(&self)
                    .with_note(format!("the tuple's length is {tuple_len}"));

                if base_location.has_span() {
                    report.add_label(
                        Label::new(*base_location)
                            .with_message(format!("this tuple has the type `{actual_ty}`")),
                    );
                }

                if field_location.has_span() {
                    report.add_label(Label::new(*field_location).with_color(Color::Red));
                }

                if *idx == 0 {
                    report.set_help("perhaps you meant to access the first element: tuple elements are indexed starting from 1");
                }

                report
            }

            Self::FixNotFunction {
                location,
                actual_ty,
                inner_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::not_a_function")
                    .with_message(&self);

                if inner_location.has_span() {
                    report.add_label(
                        Label::new(*inner_location)
                            .with_message(format!("this expression has the type `{actual_ty}`")),
                    );
                }

                report
            }

            Self::FixWrongFunctionParamCount {
                location,
                actual_ty,
                inner_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::fix_wrong_function_param_count")
                    .with_message(&self);

                if inner_location.has_span() {
                    report.add_label(
                        Label::new(*inner_location)
                            .with_message(format!("this expression has the type `{actual_ty}`",)),
                    );
                }

                report
            }

            Self::IncorrectNumberOfArgumentsInExpr {
                location,
                expected: _,
                actual: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::incorrect_number_of_arguments")
                .with_message(&self),

            Self::IncorrectNumberOfArgumentsInPat {
                location,
                expected: _,
                actual: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::incorrect_number_of_arguments")
                .with_message(&self),

            Self::UnexpectedInjection {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_injection")
                .with_message(&self),

            Self::AmbiguousSumTypeInExpr { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_sum_type")
                    .with_message(&self)
                    .with_help("ascribe a sum type to the expression with the `as` operator")
            }

            Self::AmbiguousSumTypeInPat { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::ambiguous_sum_type")
                .with_message(&self)
                .with_help("ascribe a sum type to the pattern with the `as` operator"),

            Self::UnexpectedList {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_list")
                .with_message(&self),

            Self::ExprTyNotList {
                location,
                actual_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::not_a_list")
                .with_message(&self),

            Self::ApplyNotFunction {
                location,
                actual_ty,
                callee_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::not_a_function")
                    .with_message(&self);

                if callee_location.has_span() {
                    report.add_label(
                        Label::new(*callee_location)
                            .with_message(format!("this expression has the type `{actual_ty}`"))
                            .with_color(Color::Red),
                    );
                }

                report
            }

            Self::UnexpectedLambda {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_lambda")
                .with_message(&self),

            Self::UnexpectedNumberOfParametersInLambda {
                location,
                actual: _,
                expected: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_number_of_parameters_in_lambda")
                .with_message(&self),

            Self::UnexpectedTypeForParameter {
                location,
                name: _,
                expected_ty: _,
                actual_ty,
                expr_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_type_for_parameter")
                    .with_message(&self)
                    .with_label(
                        Label::new(*location)
                            .with_message(format!("this parameter has the type `{actual_ty}`"))
                            .with_color(Color::Red),
                    );

                if expr_location.has_span() {
                    report.add_label(
                        Label::new(*expr_location)
                            .with_message("in this anonymous function expression"),
                    );
                }

                report
            }

            Self::UnexpectedTuple {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_tuple")
                .with_message(&self),

            Self::UnexpectedTupleLengthInExpr {
                location,
                actual: _,
                expected: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_tuple_length")
                .with_message(&self),

            Self::UnexpectedTupleLengthInPat {
                location,
                actual: _,
                expected: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_tuple_length")
                .with_message(&self),

            Self::UnexpectedRecord {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_record")
                .with_message(&self),

            Self::UnexpectedRecordFieldInExpr {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_record_fields")
                    .with_message(&self);

                if expr_location.has_span() {
                    report.add_label(
                        Label::new(*expr_location).with_message("in this record expression"),
                    );
                }

                report
            }

            Self::UnexpectedRecordFieldInPat {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_record_fields")
                    .with_message(&self);

                if pat_location.has_span() {
                    report.add_label(
                        Label::new(*pat_location).with_message("in this record pattern"),
                    );
                }

                report
            }

            Self::MissingRecordFieldInExpr {
                location,
                name: _,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::missing_record_fields")
                .with_message(&self),

            Self::MissingRecordFieldInPat {
                location,
                name: _,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::missing_record_fields")
                .with_message(&self),

            Self::AmbiguousVariantExprType { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_variant_type")
                    .with_message(&self)
                    .with_help("ascribe a variant type to the expression with the `as` operator")
            }

            Self::AmbiguousVariantPatType { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_variant_type")
                    .with_message(&self)
                    .with_help("ascribe a variant type to the pattern with the `as` operator")
            }

            Self::UnexpectedVariant {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_variant")
                .with_message(&self),

            Self::UnexpectedVariantLabelInExpr {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_variant_label")
                    .with_message(&self);

                if expr_location.has_span() {
                    report.add_label(
                        Label::new(*expr_location).with_message("in this variant expression"),
                    );
                }

                report
            }

            Self::UnexpectedVariantLabelInPat {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_variant_label")
                    .with_message(&self);

                if pat_location.has_span() {
                    report.add_label(
                        Label::new(*pat_location).with_message("in this variant pattern"),
                    );
                }

                report
            }

            Self::UnexpectedDataForNullaryLabel {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_data_for_nullary_label")
                    .with_message(&self);

                if expr_location.has_span() {
                    report.add_label(
                        Label::new(*expr_location).with_message("in this variant expression"),
                    );
                }

                report
            }

            Self::UnexpectedNonNullaryVariantPattern {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_non_nullary_variant_pattern")
                    .with_message(&self);

                if pat_location.has_span() {
                    report.add_label(
                        Label::new(*pat_location).with_message("in this variant pattern"),
                    );
                }

                report
            }

            Self::MissingDataForLabel {
                location,
                name: _,
                expected_ty,
                expr_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::missing_data_for_label")
                    .with_message(&self);

                if expr_location.has_span() {
                    report.add_label(Label::new(*expr_location).with_message(format!(
                        "this variant expression has the type `{expected_ty}`"
                    )));
                }

                report
            }

            Self::UnexpectedNullaryVariantPattern {
                location,
                name: _,
                expected_ty,
                pat_location,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::unexpected_nullary_variant_pattern")
                    .with_message(&self);

                if pat_location.has_span() {
                    report.add_label(Label::new(*pat_location).with_message(format!(
                        "this variant pattern has the type `{expected_ty}`"
                    )));
                }

                report
            }

            Self::IllegalEmptyMatching { location } => Report::build(ReportKind::Error, *location)
                .with_code("sema::illegal_empty_matching")
                .with_message(&self),

            Self::AmbiguousEmptyListExprTy { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_list_type")
                    .with_message(&self)
                    .with_help("ascribe a list type to the expression with the `as` operator")
            }

            Self::AmbiguousEmptyListPatTy { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_list_type")
                    .with_message(&self)
                    .with_help("ascribe a list type to the pattern with the `as` operator")
            }

            Self::UnexpectedPatternForType {
                location,
                expected_ty: _,
            } => Report::build(ReportKind::Error, *location)
                .with_code("sema::unexpected_pattern_for_type")
                .with_message(&self),

            Self::AmbiguousBindingPatType { location } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::ambiguous_binding_type")
                    .with_message(&self)
            }

            Self::NonExhaustiveMatchPatterns {
                location,
                scrutinee_location,
                witness,
            } => {
                let mut report = Report::build(ReportKind::Error, *location)
                    .with_code("sema::non_exhaustive_match_patterns")
                    .with_message(&self);

                if scrutinee_location.has_span() {
                    report.add_label(
                        Label::new(*scrutinee_location)
                            .with_message(format!("no pattern matches `{witness}`",))
                            .with_color(Color::Red),
                    );
                }

                report
            }

            Self::NonIrrefutableLetPattern { location, witness } => {
                Report::build(ReportKind::Error, *location)
                    .with_code("sema::non_exhaustive_match_patterns")
                    .with_message(&self)
                    .with_note(format!("no pattern matches `{witness}`"))
                    .with_note("a let pattern must be applicable to all values of this type")
            }
        }
    }
}
