use thiserror::Error;

use crate::ast;
use crate::diag::{Code, Diagnostic, IntoDiagnostic, Label, code};
use crate::location::Location;
use crate::util::format_iter;

use super::feature::{EnableReason, FeatureKind};

const ERROR_UNEXPECTED_TUPLE_LENGTH: Code =
    code!(sema::wrong_tuple_len as "ERROR_UNEXPECTED_TUPLE_LENGTH");
const ERROR_UNEXPECTED_RECORD_FIELDS: Code =
    code!(sema::no_such_record_field as "ERROR_UNEXPECTED_RECORD_FIELDS");
const ERROR_MISSING_RECORD_FIELDS: Code =
    code!(sema::missing_record_field as "ERROR_MISSING_RECORD_FIELDS");
const ERROR_UNEXPECTED_VARIANT_LABEL: Code =
    code!(sema::no_such_variant_label as "ERROR_UNEXPECTED_VARIANT_LABEL");
const ERROR_AMBIGUOUS_SUM_TYPE: Code = code!(sema::ambiguous_sum_ty as "ERROR_AMBIGUOUS_SUM_TYPE");
const ERROR_AMBIGUOUS_VARIANT_TYPE: Code =
    code!(sema::ambiguous_variant_ty as "ERROR_AMBIGUOUS_VARIANT_TYPE");
const ERROR_AMBIGUOUS_LIST_TYPE: Code = code!(sema::ambiguous_list_ty as "ERROR_AMBIGUOUS_LIST");
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
    NoFnParams { location: Location },

    #[error("the function cannot have multiple parameters")]
    MultipleFnParams { location: Location },

    #[error("the function cannot have type parameters")]
    FnHasTypeParams {
        location: Location,
        generic_kw_location: Location,
    },

    #[error("the function cannot have exception specifiers")]
    FnHasThrows {
        location: Location,
        throws_kw_location: Location,
    },

    #[error("this declaration cannot be nested within a function")]
    NestedDeclNotAllowed {
        location: Location,
        func_name_location: Location,
    },

    #[error("type aliases are not allowed")]
    TyAliasNotAllowed { location: Location },

    #[error("exception type declarations are not allowed")]
    ExceptionTyDeclNotAllowed { location: Location },

    #[error("exception variant declarations are not allowed")]
    ExceptionVariantDeclNotAllowed { location: Location },

    #[error("reference types are not allowed")]
    ReferenceTyNotAllowed { location: Location },

    #[error("sum types are not allowed")]
    SumTyNotAllowed {
        location: Location,
        plus_location: Location,
    },

    #[error("universal types are not allowed")]
    UniversalTyNotAllowed { location: Location },

    #[error("recursive types (μ-types) are not allowed")]
    RecursiveTyNotAllowed { location: Location },

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
    UnitTyNotAllowed { location: Location },

    #[error("the top type is not allowed")]
    TopTyNotAllowed { location: Location },

    #[error("the botom type is not allowed")]
    BotTyNotAllowed { location: Location },

    #[error("explicit type inference is not available")]
    TyInferenceNotAvailable { location: Location },

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
    CmpOpNotAllowed {
        location: Location,
        op_location: Location,
    },

    #[error("logical operators are not allowed")]
    LogicOpNotAllowed {
        location: Location,
        op_location: Location,
    },

    #[error("assignment expressions are not allowed")]
    AssignExprNotAllowed {
        location: Location,
        colon_eq_location: Location,
    },

    #[error("nested patterns are not allowed")]
    NestedPatNotAllowed { location: Location },

    #[error("general patterns are not allowed")]
    GeneralPatNotAllowed { location: Location },

    #[error("structural patterns are not allowed")]
    StructuralPatNotAllowed { location: Location },

    #[error("injection patterns are not allowed")]
    InjectionPatNotAllowed { location: Location },

    #[error("ascription patterns are not allowed")]
    AscriptionPatNotAllowed { location: Location },

    #[error("cast patterns are not allowed")]
    CastPatNotAllowed { location: Location },

    #[error("the field `{name}` is declared multiple times in the same record type")]
    DuplicateRecordTyField {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the label `{name}` is declared multiple times in the same variant type")]
    DuplicateVariantTyField {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the field `{name}` is initialized multiple times in the same record")]
    DuplicateRecordField {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the field `{name}` is matched multiple times in the same record pattern")]
    DuplicateRecordPatField {
        name: String,
        location: Location,
        prev_location: Location,
    },

    #[error("the type `{name}` is undefined")]
    UndefinedTy { name: String, location: Location },

    #[error("the variable `{name}` is undefined")]
    UndefinedVar { name: String, location: Location },

    #[error("the variable `{name}` is defined multiple times")]
    DuplicateVarDef {
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
    ExprTyMismatch {
        location: Location,
        expected_ty: String,
        actual_ty: String,
    },

    #[error("the record has no field `{field}`")]
    NoSuchField {
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
    NoSuchElement {
        location: Location,
        idx: usize,
        tuple_len: usize,
        actual_ty: String,
        base_location: Location,
        field_location: Location,
    },

    #[error("the fixpoint combinator can only be applied to functions")]
    FixNotFn {
        location: Location,
        actual_ty: String,
        inner_location: Location,
    },

    #[error("the fixpoint combinator requires a function of a single argument")]
    FixWrongFnParamCount {
        location: Location,
        actual_ty: String,
        inner_location: Location,
    },

    #[error("the expression has a wrong number of arguments: expected {expected}, got {actual}")]
    WrongArgCountInExpr {
        location: Location,
        expected: usize,
        actual: usize,
    },

    #[error("the pattern has a wrong number of arguments: expected {expected}, got {actual}")]
    WrongArgCountInPat {
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
    AmbiguousSumTyInExpr { location: Location },

    #[error("could not determine the type of a sum type injection pattern")]
    AmbiguousSumTyInPat { location: Location },

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
    ApplyNotFn {
        location: Location,
        actual_ty: String,
        callee_location: Location,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a function type")]
    UnexpectedFn {
        location: Location,
        expected_ty: String,
    },

    #[error(
        "the parameter count in this anonymous function ({actual}) does not match the expected count ({expected})"
    )]
    WrongFnParamCount {
        location: Location,
        actual: usize,
        expected: usize,
    },

    #[error(
        "the parameter `{name}` has an unexpected type: expected `{expected_ty}`, got `{actual_ty}`"
    )]
    ParamTyMismatch {
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
    WrongTupleLengthInExpr {
        location: Location,
        actual: usize,
        expected: usize,
    },

    #[error(
        "the number of elements in the tuple pattern ({actual}) does not match the expected count ({expected})"
    )]
    WrongTupleLengthInPat {
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
    NoSuchRecordFieldInExpr {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error("the field `{name}` is not present in the expected type `{expected_ty}`")]
    NoSuchRecordFieldInPat {
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
    AmbiguousVariantTyInExpr { location: Location },

    #[error("could not determine the type of a variant pattern")]
    AmbiguousVariantTyInPat { location: Location },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a variant type")]
    UnexpectedVariant {
        location: Location,
        expected_ty: String,
    },

    #[error("the label `{name}` is not present in the expected type `{expected_ty}`")]
    NoSuchVariantLabelInExpr {
        location: Location,
        name: String,
        expected_ty: String,
        expr_location: Location,
    },

    #[error("the label `{name}` is not present in the expected type `{expected_ty}`")]
    NoSuchVariantLabelInPat {
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
    UnexpectedNonNullaryVariantPat {
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
    UnexpectedNullaryVariantPat {
        location: Location,
        name: String,
        expected_ty: String,
        pat_location: Location,
    },

    #[error("this match expression must have at least one match arm")]
    EmptyMatch { location: Location },

    #[error("could not determine the type of an empty list expression")]
    AmbiguousEmptyListExprTy { location: Location },

    #[error("could not determine the type of an empty list pattern")]
    AmbiguousEmptyListPatTy { location: Location },

    #[error("this pattern cannot be used with values of the type `{expected_ty}`")]
    IllegalPatForTy {
        location: Location,
        expected_ty: String,
    },

    #[error("could not determine the type of a binding pattern")]
    AmbiguousBindingPatTy { location: Location },

    #[error("the match arms are non-exhaustive")]
    MatchNonExhaustive {
        location: Location,
        scrutinee_location: Location,
        witness: String,
    },

    #[error("the pattern is not irrefutable")]
    NonIrrefutableLetPat { location: Location, witness: String },

    #[error("expected the `main` function to have one parameter, got {actual}")]
    WrongMainParamCount { location: Location, actual: usize },

    #[error("could not determine the type of a memory address literal expression")]
    AmbiguousAddressExprTy { location: Location },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a reference type")]
    UnexpectedAddressExpr {
        location: Location,
        expected_ty: String,
    },

    #[error("the expression has a wrong type: expected `{expected_ty}`, got a reference type")]
    UnexpectedNewExpr {
        location: Location,
        expected_ty: String,
    },

    #[error("this expression has a wrong type: expected a reference, got `{actual_ty}`")]
    ExprTyNotReference {
        location: Location,
        actual_ty: String,
    },
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

            Self::NoFnParams { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::no_fn_params))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::MultipleFnParams { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::multiple_fn_params))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::FnHasTypeParams {
                location,
                generic_kw_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fn_has_ty_params))
                .with_msg(&self)
                .with_label(Label::primary(*generic_kw_location))
                .make(),

            Self::FnHasThrows {
                location,
                throws_kw_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fn_has_throws))
                .with_msg(&self)
                .with_label(Label::primary(*throws_kw_location))
                .make(),

            Self::NestedDeclNotAllowed {
                location,
                func_name_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::nested_decl_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*func_name_location).with_msg("in the function defined here"),
                )
                .make(),

            Self::TyAliasNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ty_alias_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExceptionTyDeclNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::exception_ty_decl_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExceptionVariantDeclNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::exception_variant_decl_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ReferenceTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::reference_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::SumTyNotAllowed {
                location,
                plus_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::sum_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*plus_location))
                .make(),

            Self::UniversalTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::universal_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::RecursiveTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::recursive_ty_not_allowed))
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

            Self::UnitTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unit_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TopTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::top_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::BotTyNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::bot_ty_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::TyInferenceNotAvailable { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ty_inference_not_available))
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

            Self::CmpOpNotAllowed {
                location: _,
                op_location,
            } => Diagnostic::error()
                .at(*op_location)
                .with_code(code!(sema::cmp_op_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*op_location))
                .make(),

            Self::LogicOpNotAllowed {
                location: _,
                op_location,
            } => Diagnostic::error()
                .at(*op_location)
                .with_code(code!(sema::logic_op_not_allowed))
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

            Self::NestedPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::nested_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::GeneralPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::general_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::StructuralPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::structural_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::InjectionPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::injection_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AscriptionPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ascription_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::CastPatNotAllowed { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::cast_pat_not_allowed))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::DuplicateRecordTyField {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::duplicate_record_ty_field
                    as "ERROR_DUPLICATE_RECORD_TYPE_FIELDS"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateVariantTyField {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::duplicate_variant_ty_field
                    as "ERROR_DUPLICATE_VARIANT_TYPE_FIELDS"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateRecordField {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_record_field as "ERROR_DUPLICATE_RECORD_FIELDS"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously declared here"),
                )
                .make(),

            Self::DuplicateRecordPatField {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_record_pat_field))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*prev_location)
                        .with_msg("the field was previously matched here"),
                )
                .make(),

            Self::UndefinedTy { name: _, location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::undefined_ty))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UndefinedVar { name: _, location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::undefined_var as "ERROR_UNDEFINED_VARIABLE"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::DuplicateVarDef {
                name: _,
                location,
                prev_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::duplicate_var_def))
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

            Self::ExprTyMismatch {
                location,
                expected_ty: _,
                actual_ty,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::expr_ty_mismatch
                    as "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION"
                ))
                .with_msg(&self)
                .with_label(
                    Label::primary(*location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::NoSuchField {
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

            Self::NoSuchElement {
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

            Self::FixNotFn {
                location,
                actual_ty,
                inner_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fix_not_fn as "ERROR_NOT_A_FUNCTION"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*inner_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::FixWrongFnParamCount {
                location,
                actual_ty,
                inner_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::fix_wrong_fn_param_count))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*inner_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`",)),
                )
                .make(),

            Self::WrongArgCountInExpr {
                location,
                expected: _,
                actual: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_INCORRECT_NUMBER_OF_ARGUMENTS)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::WrongArgCountInPat {
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

            Self::AmbiguousSumTyInExpr { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_SUM_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a sum type to the expression with the `as` operator")
                .make(),

            Self::AmbiguousSumTyInPat { location } => Diagnostic::error()
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

            Self::ApplyNotFn {
                location,
                actual_ty,
                callee_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::apply_not_fn as "ERROR_NOT_A_FUNCTION"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*callee_location)
                        .with_msg(format!("this expression has the type `{actual_ty}`")),
                )
                .make(),

            Self::UnexpectedFn {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::unexpected_fn as "ERROR_UNEXPECTED_LAMBDA"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::WrongFnParamCount {
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

            Self::ParamTyMismatch {
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

            Self::WrongTupleLengthInExpr {
                location,
                actual: _,
                expected: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_UNEXPECTED_TUPLE_LENGTH)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::WrongTupleLengthInPat {
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

            Self::NoSuchRecordFieldInExpr {
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

            Self::NoSuchRecordFieldInPat {
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

            Self::AmbiguousVariantTyInExpr { location } => Diagnostic::error()
                .at(*location)
                .with_code(ERROR_AMBIGUOUS_VARIANT_TYPE)
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a variant type to the expression with the `as` operator")
                .make(),

            Self::AmbiguousVariantTyInPat { location } => Diagnostic::error()
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

            Self::NoSuchVariantLabelInExpr {
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

            Self::NoSuchVariantLabelInPat {
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
                .with_code(code!(
                    sema::unexpected_data_for_nullary_label
                    as "ERROR_DATA_FOR_NULLARY_LABEL"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg("in this variant expression"))
                .make(),

            Self::UnexpectedNonNullaryVariantPat {
                location,
                name: _,
                expected_ty: _,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::unexpected_non_nullary_variant_pat
                    as "ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN"
                ))
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
                .with_code(code!(
                    sema::missing_data_for_label
                    as "ERROR_MISSING_DATA_FOR_LABEL"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(Label::secondary(*expr_location).with_msg(format!(
                    "this variant expression has the type `{expected_ty}`"
                )))
                .make(),

            Self::UnexpectedNullaryVariantPat {
                location,
                name: _,
                expected_ty,
                pat_location,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::unexpected_nullary_variant_pat
                    as "ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_label(
                    Label::secondary(*pat_location)
                        .with_msg(format!("this variant pattern has the type `{expected_ty}`")),
                )
                .make(),

            Self::EmptyMatch { location } => Diagnostic::error()
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

            Self::IllegalPatForTy {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::illegal_pat_for_ty as "ERROR_UNEXPECTED_PATTERN_FOR_TYPE"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousBindingPatTy { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::ambiguous_binding_ty))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::MatchNonExhaustive {
                location,
                scrutinee_location,
                witness,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::match_non_exhaustive
                    as "ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS"
                ))
                .with_msg(&self)
                .with_label(
                    Label::primary(*scrutinee_location)
                        .with_msg(format!("no pattern matches `{witness}`")),
                )
                .make(),

            Self::NonIrrefutableLetPat { location, witness } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::non_irrefutable_let_pat
                    as "ERROR_NON_EXHAUSTIVE_MATCH_PATTERNS"
                ))
                .with_msg(&self)
                .with_label(
                    Label::primary(*location).with_msg(format!("no pattern matches `{witness}`")),
                )
                .with_note("a let pattern must be applicable to all values of this type")
                .make(),

            Self::WrongMainParamCount {
                location,
                actual: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::wrong_main_param_count as "ERROR_INCORRECT_ARITY_OF_MAIN"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::AmbiguousAddressExprTy { location } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::ambiguous_address_expr_ty
                    as "ERROR_AMBIGUOUS_REFERENCE_TYPE"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .with_note("ascribe a reference type to the expression with the `as` operator")
                .make(),

            Self::UnexpectedAddressExpr {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::unexpected_address_expr
                    as "ERROR_UNEXPECTED_MEMORY_ADDRESS"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::UnexpectedNewExpr {
                location,
                expected_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(
                    sema::unexpected_new_expr
                    as "ERROR_UNEXPECTED_REFERENCE"
                ))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),

            Self::ExprTyNotReference {
                location,
                actual_ty: _,
            } => Diagnostic::error()
                .at(*location)
                .with_code(code!(sema::expr_ty_not_reference as "ERROR_NOT_A_REFERENCE"))
                .with_msg(&self)
                .with_label(Label::primary(*location))
                .make(),
        }
    }
}
