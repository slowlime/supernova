use thiserror::Error;

use crate::ast;
use crate::diag::{Code, Diagnostic, IntoDiagnostic, Label, code};
use crate::location::Location;
use crate::util::format_iter;

use super::feature::{EnableReason, FeatureKind};

const ERROR_UNEXPECTED_TUPLE_LENGTH: Code =
    code!(sema::tuple_length_mismatch as "ERROR_UNEXPECTED_TUPLE_LENGTH");
const ERROR_UNEXPECTED_RECORD_FIELDS: Code =
    code!(sema::unexpected_record_field as "ERROR_UNEXPECTED_RECORD_FIELDS");
const ERROR_MISSING_RECORD_FIELDS: Code =
    code!(sema::missing_record_field as "ERROR_MISSING_RECORD_FIELDS");
const ERROR_UNEXPECTED_VARIANT_LABEL: Code =
    code!(sema::no_such_variant_label as "ERROR_UNEXPECTED_VARIANT_LABEL");
const ERROR_AMBIGUOUS_SUM_TYPE: Code =
    code!(sema::ambiguous_sum_type as "ERROR_AMBIGUOUS_SUM_TYPE");
const ERROR_AMBIGUOUS_VARIANT_TYPE: Code =
    code!(sema::ambiguous_variant_type as "ERROR_AMBIGUOUS_VARIANT_TYPE");
const ERROR_AMBIGUOUS_LIST_TYPE: Code = code!(sema::ambiguous_list_type as "ERROR_AMBIGUOUS_LIST");
const ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS: Code =
    code!(sema::match_non_exhaustive as "ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS");
const ERROR_INCORRECT_NUMBER_OF_ARGUMENTS: Code =
    code!(sema::wrong_arg_count as "ERROR_INCORRECT_NUMBER_OF_ARGUMENTS");

#[derive(Error, Debug, Clone)]
pub enum SemaDiag {
    #[error("extension #{extension} is enabled several times")]
    DuplicateExtension {
        extension: ast::Extension,
        location: Location,
        prev_location: Location,
    },

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

    #[error("multiple bindings in `let` expressions are not allowed")]
    MultipleLetBindingsNotAllowed {
        location: Location,
        let_location: Location,
    },

    #[error("multiple bindings in `letrec` expressions are not allowed")]
    MultipleLetrecBindingsNotAllowed {
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
    MissingMain,

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

    #[error("expected the `main` function to have one parameter, got {actual}")]
    IncorrectArityOfMain { location: Location, actual: usize },
}

impl IntoDiagnostic for SemaDiag {
    fn into_diagnostic(self) -> Diagnostic {
        match &self {
            Self::DuplicateExtension {
                extension: _,
                location,
                prev_location,
            } => Diagnostic::warn()
                .at(*location)
                .with_code(code!(sema::duplicate_extension))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the extension was previously enabled here"),
                )
                .make(),

            Self::ConflictingFeatures { location, features } => {
                let mut diag = Diagnostic::error()
                    .at(*location)
                    .with_code(code!(sema::conflicting_features))
                    .with_msg(&self)
                    .with_label(Label::primary(*location))
                    .make();

                for (feature, reason) in features {
                    match reason {
                        EnableReason::Extension(location @ Location::UserCode(_)) => diag
                            .add_label(Label::secondary(*location).with_msg(format!(
                                "the feature {feature} was enabled by the extension here"
                            ))),

                        EnableReason::Extension(_) => diag
                            .add_note(format!("the feature {feature} was enabled by an extension")),

                        EnableReason::Feature(f) => diag.add_note(format!(
                            "the feature {feature} was enabled as a dependency of the feature {f}"
                        )),
                    }
                }

                diag
            }

            Self::NoFunctionParams { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::no_function_params))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::MultipleFunctionParams { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::multiple_function_params))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::FunctionHasTypeParams {
                location,
                generic_kw_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::function_has_type_params))
                .with_msg(&self)
                .with_label(Label::primary(*generic_kw_location))
                .make(),

            Self::FunctionHasThrows {
                location,
                throws_kw_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::function_has_throws))
                .with_msg(&self)
                .with_label(Label::primary(*throws_kw_location))
                .make(),

            Self::IllegalNestedDecl {
                location,
                func_name_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::illegal_nested_decl))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*func_name_location).with_msg("in the function defined here"),
                )
                .make(),

            Self::TypeAliasNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::type_alias_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExceptionTypeDeclNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::exception_type_decl_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExceptionVariantDeclNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::exception_variant_decl_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ReferenceTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::reference_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::SumTypeNotAllowed {
                location,
                plus_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::sum_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*plus_location))
                .make(),

            Self::UniversalTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::universal_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::RecursiveTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::recursive_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::EmptyTupleNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::empty_tuple_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TupleNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::tuple_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::IllegalPairElementCount { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::illegal_pair_element_count))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::RecordNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::record_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::VariantNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::variant_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::NullaryVariantLabelNotAllowed {
                location,
                variant_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::nullary_variant_label_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*variant_location).with_msg("in the variant here"))
                .make(),

            Self::ListNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::list_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnitTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unit_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TopTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::top_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::BotTypeNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::bot_type_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TypeInferenceNotAvailable { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::type_inference_not_available))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::NaturalLiteralNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::natural_literal_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AddressLiteralNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::address_literal_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::FieldExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::field_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::PanicExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::panic_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ThrowExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::throw_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TryCatchExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::try_catch_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::CastExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::cast_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::FixExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fix_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::FoldExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fold_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ApplyExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::apply_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TyApplyExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ty_apply_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AscriptionExprNotAllowed {
                location,
                as_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ascription_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*as_location))
                .make(),

            Self::SeqExprNotAllowed {
                location,
                semicolon_locations,
            } => {
                let mut diag = Diagnostic::error()
                    .at(*location)
                    .with_code(code!(sema::seq_expr_not_allowed))
                    .with_msg(&self)
                    .make();

                for semicolon_location in semicolon_locations {
                    diag.add_label(Label::primary(*semicolon_location));
                }

                diag
            }

            Self::LetExprNotAllowed {
                location,
                let_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::let_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*let_location))
                .make(),

            Self::LetrecExprNotAllowed {
                location,
                letrec_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::letrec_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*letrec_location))
                .make(),

            Self::MultipleLetBindingsNotAllowed {
                location,
                let_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::multiple_let_bindings_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*let_location))
                .make(),

            Self::MultipleLetrecBindingsNotAllowed {
                location,
                letrec_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::multiple_letrec_bindings_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*letrec_location))
                .make(),

            Self::GenericExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::generic_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::NewExprNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::new_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::DerefExprNotAllowed {
                location,
                star_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::deref_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*star_location))
                .make(),

            Self::ArithOpNotAllowed {
                location: _,
                op_location,
            } => Diagnostic::error()
                .at(*op_location)
                .with_code(code!(sema::arith_op_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*op_location))
                .make(),

            Self::ComparisonOpNotAllowed {
                location: _,
                op_location,
            } => Diagnostic::error()
                .at(*op_location)
                .with_code(code!(sema::cmp_op_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*op_location))
                .make(),

            Self::AssignExprNotAllowed {
                location: _,
                colon_eq_location,
            } => Diagnostic::error()
                .at(*colon_eq_location)
                .with_code(code!(sema::assign_expr_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*colon_eq_location))
                .make(),

            Self::NestedPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::nested_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::GeneralPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::general_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::StructuralPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::structural_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::InjectionPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::injection_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AscriptionPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ascription_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::CastPatternNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::cast_pattern_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::DuplicateRecordTypeFields {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::duplicate_record_type_fields
                    as "ERROR_DUPLICATE_RECORD_TYPE_FIELDS"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateVariantTypeFields {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::duplicate_variant_type_fields
                    as "ERROR_DUPLICATE_VARIANT_TYPE_FIELDS"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateRecordFields {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_record_fields as "ERROR_DUPLICATE_RECORD_FIELDS"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateRecordPatternFields {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_record_pattern_fields))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously matched here"),
                )
                .make(),

            Self::UndefinedTy { name: _, location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::undefined_type))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UndefinedVariable { name: _, location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::undefined_variable as "ERROR_UNDEFINED_VARIABLE"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::DuplicateVariableDef {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_variable_def))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the variable was previously defined here"),
                )
                .make(),

            Self::DuplicateTyDef {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_ty_def))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the type was previously defined here"),
                )
                .make(),

            Self::MissingMain => Diagnostic::error()
                .without_location()
                .with_code(code!(sema::missing_main as "ERROR_MISSING_MAIN"))
                .with_msg(&self)
                .make(),

            Self::UnexpectedTypeForExpression {
                location,
                expected_ty: _,
                actual_ty,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::expr_type_mismatch
                    as "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION"
                ))
                .with_msg(&self)
                .with_label(
                    Label::primary(*location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::UnexpectedFieldAccess {
                location,
                field: _,
                record_ty,
                base_location,
                field_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::no_such_field as "ERROR_UNEXPECTED_FIELD_ACCESS"))
                .with_msg(&self)
                .with_label(Label::primary(*field_location))
                .with_label(
                    Label::secondary(*base_location)
                        .with_msg(format!("the record has the type `{record_ty}`")),
                )
                .make(),

            Self::ExtractingFieldOfNonRecordTy {
                location,
                field: _,
                actual_ty,
                base_location,
                field_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::extracting_field_of_non_record_ty as "ERROR_NOT_A_RECORD"))
                .with_msg(&self)
                .with_label(Label::primary(*field_location))
                .with_label(
                    Label::secondary(*base_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::IndexingNonTupleTy {
                location,
                actual_ty,
                base_location,
                field_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::indexing_non_tuple_ty as "ERROR_NOT_A_TUPLE"))
                .with_msg(&self)
                .with_label(Label::primary(*field_location))
                .with_label(
                    Label::secondary(*base_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::TupleIndexOutOfBounds {
                location,
                idx,
                tuple_len,
                actual_ty,
                base_location,
                field_location,
            } => {
                let mut diag = Diagnostic::error()
                    .at(*location)
                    .with_code(code!(sema::no_such_element as "ERROR_TUPLE_INDEX_OUT_OF_BOUNDS"))
                    .with_msg(&self)
                    .with_note(format!("the tuple's length is {tuple_len}"))
                    .with_label(Label::primary(*field_location))
                    .with_label(
                        Label::secondary(*base_location)
                            .with_msg(format!("this tuple has the type `{actual_ty}`")),
                    )
                    .make();

                if *idx == 0 {
                    diag.add_note("perhaps you meant to access the first element: tuple elements are indexed starting from 1");
                }

                diag
            }

            Self::FixNotFunction {
                location,
                actual_ty,
                inner_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fix_not_function as "ERROR_NOT_A_FUNCTION"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*inner_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::FixWrongFunctionParamCount {
                location,
                actual_ty,
                inner_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fix_wrong_function_param_count))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*inner_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`",)),
                )
                .make(),

            Self::IncorrectNumberOfArgumentsInExpr {
                location,
                expected: _,
                actual: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_INCORRECT_NUMBER_OF_ARGUMENTS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::IncorrectNumberOfArgumentsInPat {
                location,
                expected: _,
                actual: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_INCORRECT_NUMBER_OF_ARGUMENTS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedInjection {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_injection as "ERROR_UNEXPECTED_INJECTION"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousSumTypeInExpr { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_SUM_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a sum type to the expression with the `as` operator")
                .make(),

            Self::AmbiguousSumTypeInPat { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_SUM_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a sum type to the pattern with the `as` operator")
                .make(),

            Self::UnexpectedList {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_list as "ERROR_UNEXPECTED_LIST"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExprTyNotList {
                location,
                actual_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::expr_ty_not_list as "ERROR_NOT_A_LIST"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ApplyNotFunction {
                location,
                actual_ty,
                callee_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::apply_not_function as "ERROR_NOT_A_FUNCTION"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*callee_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::UnexpectedLambda {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_fn as "ERROR_UNEXPECTED_LAMBDA"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedNumberOfParametersInLambda {
                location,
                actual: _,
                expected: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::wrong_fn_param_count
                    as "ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedTypeForParameter {
                location,
                name: _,
                expected_ty: _,
                actual_ty,
                expr_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::param_ty_mismatch as "ERROR_UNEXPECTED_TYPE_FOR_PARAMETER"))
                .with_msg(&self)
                .with_label(
                    Label::primary(*location)
                        .with_msg(format!("this parameter has the type `{actual_ty}`")),
                )
                .with_label(
                    Label::secondary(*expr_location)
                        .with_msg("in this anonymous function expression"),
                )
                .make(),

            Self::UnexpectedTuple {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_tuple as "ERROR_UNEXPECTED_TUPLE"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedTupleLengthInExpr {
                location,
                actual: _,
                expected: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_TUPLE_LENGTH)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedTupleLengthInPat {
                location,
                actual: _,
                expected: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_TUPLE_LENGTH)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedRecord {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_record as "ERROR_UNEXPECTED_RECORD"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedRecordFieldInExpr {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_RECORD_FIELDS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg("in this record expression"))
                .make(),

            Self::UnexpectedRecordFieldInPat {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_RECORD_FIELDS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*pat_location).with_msg("in this record pattern"))
                .make(),

            Self::MissingRecordFieldInExpr {
                location,
                name: _,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_MISSING_RECORD_FIELDS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::MissingRecordFieldInPat {
                location,
                name: _,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_MISSING_RECORD_FIELDS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousVariantExprType { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_VARIANT_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a variant type to the expression with the `as` operator")
                .make(),

            Self::AmbiguousVariantPatType { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_VARIANT_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a variant type to the pattern with the `as` operator")
                .make(),

            Self::UnexpectedVariant {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_variant as "ERROR_UNEXPECTED_VARIANT"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedVariantLabelInExpr {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_VARIANT_LABEL)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg("in this variant expression"))
                .make(),

            Self::UnexpectedVariantLabelInPat {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_VARIANT_LABEL)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*pat_location).with_msg("in this variant pattern"))
                .make(),

            Self::UnexpectedDataForNullaryLabel {
                location,
                name: _,
                expected_ty: _,
                expr_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_data_for_nullary_label))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg("in this variant expression"))
                .make(),

            Self::UnexpectedNonNullaryVariantPattern {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_non_nullary_variant_pattern))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*pat_location).with_msg("in this variant pattern"))
                .make(),

            Self::MissingDataForLabel {
                location,
                name: _,
                expected_ty,
                expr_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::missing_data_for_label))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg(format!(
                    "this variant expression has the type `{expected_ty}`"
                )))
                .make(),

            Self::UnexpectedNullaryVariantPattern {
                location,
                name: _,
                expected_ty,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_nullary_variant_pattern))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*pat_location)
                        .with_msg(format!("this variant pattern has the type `{expected_ty}`")),
                )
                .make(),

            Self::IllegalEmptyMatching { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::empty_match as "ERROR_ILLEGAL_EMPTY_MATCHING"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousEmptyListExprTy { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_LIST_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a list type to the expression with the `as` operator")
                .make(),

            Self::AmbiguousEmptyListPatTy { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_LIST_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a list type to the pattern with the `as` operator")
                .make(),

            Self::UnexpectedPatternForType {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(
                    code!(sema::invalid_pattern_for_ty as "ERROR_UNEXPECTED_PATTERN_FOR_TYPE"),
                )
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousBindingPatType { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ambiguous_binding_type))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::NonExhaustiveMatchPatterns {
                location,
                scrutinee_location,
                witness,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS)
                .with_msg(&self)
                .with_label(
                    Label::primary(*scrutinee_location)
                        .with_msg(format!("no pattern matches `{witness}`")),
                )
                .make(),

            Self::NonIrrefutableLetPattern { location, witness } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS)
                .with_msg(&self)
                .with_label(
                    Label::primary(*location).with_msg(format!("no pattern matches `{witness}`")),
                )
                .with_note("a let pattern must be applicable to all values of this type")
                .make(),

            Self::IncorrectArityOfMain {
                location,
                actual: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::wrong_main_param_count as "ERROR_INCORRECT_ARITY_OF_MAIN"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),
        }
    }
}
