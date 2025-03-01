use std::fmt::{self, Display};
use derive_more::Display;

use crate::ast;
use crate::location::Location;

macro_rules! to_option {
    () => {
        None
    };

    ($expr:expr) => {
        Some($expr)
    };
}

macro_rules! define_ext {
    {
        $(
            $name:ident $str:literal $(($($ext:tt)+))? $(=> $($dep:ident),+)?;
        )+
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum FeatureKind {
            $($name,)+
        }

        impl FeatureKind {
            pub const ALL: &[Self] = &[
                $(Self::$name),+
            ];

            pub const fn to_str(self) -> &'static str {
                match self {
                    $(
                        Self::$name => $str,
                    )+
                }
            }

            pub const fn extension(self) -> Option<ast::Extension> {
                match self {
                    $(
                        Self::$name => to_option!($($($ext)+)?),
                    )+
                }
            }

            pub const fn depends(self) -> &'static [Self] {
                match self {
                    $(
                        Self::$name => &[$($(Self::$dep),+)?],
                    )+
                }
            }

            pub const fn from_extension(extension: ast::Extension) -> Option<Self> {
                match extension {
                    $(
                        $($($ext)+ => Some(Self::$name),)?
                    )+
                    _ => None,
                }
            }
        }

        impl Display for FeatureKind {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.to_str())
            }
        }
    };
}

define_ext! {
    // Syntactic sugar and derived forms.
    Patterns "patterns";
    StructuralPatterns "structural patterns" (ast::Extension::StructuralPatterns) => Patterns;
    LetBindings "let-bindings" (ast::Extension::LetBindings);
    NestedFunctionDeclarations "nested function declarations"
        (ast::Extension::NestedFunctionDeclarations);
    NaturalLiterals "natural literals" (ast::Extension::NaturalLiterals);
    ArithmeticOperations "arithmetic operations" (ast::Extension::ArithmeticOperations);
    ComparisonOperations "comparison operations" (ast::Extension::ComparisonOperations);
    NullaryFunctions "nullary functions" (ast::Extension::NullaryFunctions);
    MultiparameterFunctions "multi-parameter functions" (ast::Extension::MultiparameterFunctions);
    CurriedMultiparameterFunctions "automatic currying";
    Sequencing "sequence expressions" (ast::Extension::Sequencing);
    PatternAscriptions "ascription patterns" (ast::Extension::PatternAscriptions);
    LetrecBindings "letrec-bindings" (ast::Extension::LetrecBindings);

    // Simple types.
    TypeAscriptions "type ascriptions" (ast::Extension::TypeAscriptions);
    TypeAliases "type aliases";
    UnitType "unit type" (ast::Extension::UnitType);
    Pairs "pairs" (ast::Extension::Pairs);
    EmptyTuple "empty tuple/record";
    Tuples "tuples" (ast::Extension::Tuples) => EmptyTuple, Pairs;
    Records "records" (ast::Extension::Records) => EmptyTuple;
    SumTypes "sum types" (ast::Extension::SumTypes) => Patterns;
    Variants "variant types" (ast::Extension::Variants) => Patterns;
    NullaryVariantLabels "nullary variant labels" (ast::Extension::NullaryVariantLabels);
    Enumerations "enumeration types" => Patterns;
    Lists "list types" (ast::Extension::Lists);

    // References.
    References "references";

    // Exceptions.
    ExceptionTypeDeclaration "exception type declaration";
    OpenVariantExceptions "open variant exceptions";
    Exceptions "exceptions";
    Panic "panics";

    // Subtyping.
    Subtyping "subtyping";
    TopType "top type" => Subtyping;
    BottomType "bottom type" => Subtyping;

    // Recursive types.
    RecursiveTypes "recursive types";
    EquirecursiveTypes "equi-recursive types" => RecursiveTypes;
    IsorecursiveTypes "iso-recursive types" => RecursiveTypes;

    // Universal types.
    TypeInference "type inference";
    UniversalTypes "universal types";
}

#[derive(Debug, Clone)]
pub struct Feature {
    pub kind: FeatureKind,
    pub reason: EnableReason,
}

impl Feature {
    pub fn from_extension(extension: ast::Extension, location: Location) -> Option<Self> {
        if let Some(kind) = FeatureKind::from_extension(extension) {
            Some(Self {
                kind,
                reason: EnableReason::Extension(location),
            })
        } else {
            None
        }
    }
}

#[derive(Display, Debug, Clone)]
pub enum EnableReason {
    #[display("enabled by extension")]
    Extension(Location),

    #[display("enabled by another feature: {_0}")]
    Feature(FeatureKind),
}
