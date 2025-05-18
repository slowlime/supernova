use std::fmt::{self, Display};
use std::sync::LazyLock;

use derive_more::Display;
use fxhash::{FxHashMap, FxHashSet};

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

macro_rules! define_features {
    {
        $(
            $name:ident $str:literal $(($($ext:tt)+))? $(=> $($dep:ident),+)?;
        )+
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

            pub fn enabled_by_extensions(self) -> Vec<ast::Extension> {
                let mut result = vec![];
                let mut discovered = FxHashSet::default();
                discovered.insert(self);
                let mut unprocessed = vec![self];

                while let Some(feature) = unprocessed.pop() {
                    result.extend(feature.extension());

                    for &dep in feature.dependents() {
                        if discovered.insert(dep) {
                            unprocessed.push(dep);
                        }
                    }
                }

                result
            }

            pub const fn depends(self) -> &'static [Self] {
                match self {
                    $(
                        Self::$name => &[$($(Self::$dep),+)?],
                    )+
                }
            }

            pub fn dependents(self) -> &'static [Self] {
                static DEPENDENDS: LazyLock<FxHashMap<FeatureKind, Vec<FeatureKind>>> =
                    LazyLock::new(|| {
                        let mut result = FxHashMap::from_iter(
                            FeatureKind::ALL
                                .iter()
                                .map(|&feature| (feature, vec![]))
                        );

                        $(
                            $(
                                $(
                                    result.get_mut(&FeatureKind::$dep)
                                        .unwrap()
                                        .push(FeatureKind::$name);
                                )+
                            )?
                        )+

                        result
                    });

                &DEPENDENDS[&self]
            }

            pub const fn from_extension(extension: ast::Extension) -> Option<Self> {
                match extension {
                    $(
                        $($($ext)+ => Some(Self::$name),)?
                    )+
                }
            }
        }

        impl Display for FeatureKind {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "\"{}\"", self.to_str())
            }
        }
    };
}

define_features! {
    // Syntactic sugar and derived forms.
    StructuralPatterns "structural patterns" (ast::Extension::StructuralPatterns);
    LetBindings "let-bindings" (ast::Extension::LetBindings);
    NestedFunctionDeclarations "nested function declarations"
        (ast::Extension::NestedFunctionDeclarations);
    NaturalLiterals "natural literals" (ast::Extension::NaturalLiterals);
    ArithmeticOperators "arithmetic operators" (ast::Extension::ArithmeticOperators);
    ComparisonOperators "comparison operators" (ast::Extension::ComparisonOperators);
    LogicalOperators "logical operators" (ast::Extension::LogicalOperators);
    NullaryFunctions "nullary functions" (ast::Extension::NullaryFunctions);
    MultiparameterFunctions "multi-parameter functions" (ast::Extension::MultiparameterFunctions);
    CurriedMultiparameterFunctions "automatic currying";
    Sequencing "sequence expressions" (ast::Extension::Sequencing);
    PatternAscriptions "ascription patterns" (ast::Extension::PatternAscriptions);
    LetrecBindings "letrec-bindings" (ast::Extension::LetrecBindings);
    FixpointCombinator "fixpoint combinator" (ast::Extension::FixpointCombinator);
    LetPatterns "patterns in let expressions" (ast::Extension::LetPatterns);
    MultipleLetBindings "multiple bindings in let expressions" (ast::Extension::LetManyBindings);
    MultipleLetrecBindings "multiple bindings in letrec expressions"
        (ast::Extension::LetrecManyBindings);

    // Simple types.
    TypeAscriptions "type ascriptions" (ast::Extension::TypeAscriptions);
    TypeAliases "type aliases";
    UnitType "unit type" (ast::Extension::UnitType);
    Pairs "pairs" (ast::Extension::Pairs);
    EmptyTuple "empty tuple/record";
    Tuples "tuples" (ast::Extension::Tuples) => EmptyTuple, Pairs;
    Records "records" (ast::Extension::Records) => EmptyTuple;
    SumTypes "sum types" (ast::Extension::SumTypes);
    Variants "variant types" (ast::Extension::Variants);
    NullaryVariantLabels "nullary variant labels" (ast::Extension::NullaryVariantLabels);
    Enumerations "enumeration types";
    Lists "list types" (ast::Extension::Lists);

    // References.
    AddressLiterals "memory address literals";
    References "references" (ast::Extension::References) => AddressLiterals;

    // Exceptions.
    ExceptionTypeDeclaration "exception type declaration"
        (ast::Extension::ExceptionTypeDeclaration);
    OpenVariantExceptions "open variant exceptions" (ast::Extension::OpenVariantExceptions);
    Exceptions "exceptions" (ast::Extension::Exceptions);
    ThrowsAnnotations "throw annotation in function declarations";
    Panic "panics" (ast::Extension::Panic);

    // Subtyping.
    Subtyping "subtyping" (ast::Extension::StructuralSubtyping);
    TopType "top type" (ast::Extension::TopType);
    BottomType "bottom type" (ast::Extension::BottomType);
    CastExprs "cast expressions" (ast::Extension::TypeCast);
    TryCastExprs "try-cast expressions" (ast::Extension::TryCastAs);
    CastPatterns "cast patterns" (ast::Extension::TypeCastPatterns);
    AmbiguousTyAsBot "resolve expression type ambiguity as Bot"
        (ast::Extension::AmbiguousTypeAsBottom);

    // Recursive types.
    RecursiveTypes "recursive types";
    EquirecursiveTypes "equi-recursive types" => RecursiveTypes;
    IsorecursiveTypes "iso-recursive types" => RecursiveTypes;

    // Universal types.
    TypeParameters "type parameters";
    UniversalTypes "universal types" (ast::Extension::UniversalTypes) => TypeParameters;

    TypeInference "type inference";
}

#[derive(Debug, Clone)]
pub struct Feature {
    pub kind: FeatureKind,
    pub reason: EnableReason,
}

impl Feature {
    pub const MUTUALLY_EXCLUSIVE_FEATURES: &[&[FeatureKind]] = &[
        &[
            FeatureKind::EquirecursiveTypes,
            FeatureKind::IsorecursiveTypes,
        ],
        &[
            FeatureKind::ExceptionTypeDeclaration,
            FeatureKind::OpenVariantExceptions,
        ],
        &[
            FeatureKind::UniversalTypes,
            FeatureKind::TypeInference,
            FeatureKind::Subtyping,
        ],
    ];

    pub fn disallowed_features_for(feature: FeatureKind) -> &'static [FeatureKind] {
        static DISALLOWED_FEATURES: LazyLock<FxHashMap<FeatureKind, &[FeatureKind]>> =
            LazyLock::new(|| {
                use FeatureKind::*;

                const SECOND_STAGE_FEATURES: &[FeatureKind] = &[
                    Sequencing,
                    References,
                    Panic,
                    Exceptions,
                    ExceptionTypeDeclaration,
                    OpenVariantExceptions,
                    Subtyping,
                    CastExprs,
                    CastPatterns,
                    TryCastExprs,
                    AmbiguousTyAsBot,
                    TopType,
                    BottomType,
                ];

                let mut result = FxHashMap::default();
                result.extend([
                    (UniversalTypes, SECOND_STAGE_FEATURES),
                    (TypeInference, SECOND_STAGE_FEATURES),
                ]);

                result
            });

        DISALLOWED_FEATURES
            .get(&feature)
            .copied()
            .unwrap_or_default()
    }

    pub fn from_extension(extension: ast::Extension, location: Location) -> Option<Self> {
        FeatureKind::from_extension(extension).map(|kind| Self {
            kind,
            reason: EnableReason::Extension(location),
        })
    }
}

#[derive(Display, Debug, Clone)]
pub enum EnableReason {
    #[display("enabled by extension")]
    Extension(Location),

    #[display("enabled by another feature: {_0}")]
    Feature(FeatureKind),
}
