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

macro_rules! define_ext {
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
                write!(f, "{}", self.to_str())
            }
        }
    };
}

define_ext! {
    // Syntactic sugar and derived forms.
    StructuralPatterns "structural patterns" (ast::Extension::StructuralPatterns);
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
    FixpointCombinator "fixpoint combinator" (ast::Extension::FixpointCombinator);
    LetPatterns "patterns in let expresions" (ast::Extension::LetPatterns);

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
    References "references";
    AddressLiterals "memory address literals";

    // Exceptions.
    ExceptionTypeDeclaration "exception type declaration";
    OpenVariantExceptions "open variant exceptions";
    Exceptions "exceptions";
    Panic "panics";

    // Subtyping.
    Subtyping "subtyping";
    TopType "top type" => Subtyping;
    BottomType "bottom type" => Subtyping;
    CastExprs "cast expressions";
    CastPatterns "cast patterns";

    // Recursive types.
    RecursiveTypes "recursive types";
    EquirecursiveTypes "equi-recursive types" => RecursiveTypes;
    IsorecursiveTypes "iso-recursive types" => RecursiveTypes;

    // Universal types.
    TypeParameters "type parameters";
    TypeInference "type inference";
    UniversalTypes "universal types" => TypeParameters;
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
    ];

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
