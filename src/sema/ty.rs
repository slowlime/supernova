use std::fmt::{self, Display};
use std::hash::{Hash, Hasher};

use fxhash::{FxHashMap, FxHashSet};

use super::{BindingId, Module, TyId};

impl Module<'_> {
    pub fn display_ty(&self, ty_id: TyId) -> impl Display {
        self.display_ty_prec(ty_id, 0)
    }

    pub fn display_ty_prec(&self, ty_id: TyId, prec: usize) -> impl Display {
        struct Formatter<'a>(&'a Module<'a>, TyId, usize);

        impl Display for Formatter<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let ty_kind = &self.0.tys[self.1].kind;

                let prec = match ty_kind {
                    TyKind::Untyped { .. } => 3,
                    TyKind::Unit => 3,
                    TyKind::Bool => 3,
                    TyKind::Nat => 3,
                    TyKind::Ref(..) => 3,
                    TyKind::Sum(..) => 2,
                    TyKind::Fn(..) => 1,
                    TyKind::Tuple(..) => 3,
                    TyKind::Record(..) => 3,
                    TyKind::Variant(..) => 3,
                    TyKind::List(..) => 3,
                    TyKind::Top => 3,
                    TyKind::Bot => 3,
                    TyKind::Var(..) => 3,
                    TyKind::ForAll(..) => 1,
                };

                if prec < self.2 {
                    write!(f, "(")?;
                }

                match ty_kind {
                    TyKind::Untyped { error: true } => write!(f, "<error>")?,
                    TyKind::Untyped { error: false } => write!(f, "<any>")?,
                    TyKind::Unit => write!(f, "Unit")?,
                    TyKind::Bool => write!(f, "Bool")?,
                    TyKind::Nat => write!(f, "Nat")?,

                    TyKind::Ref(ty_id, RefMode::Source) => {
                        write!(f, "&(? <: {})", self.0.display_ty_prec(*ty_id, prec))?
                    }

                    TyKind::Ref(ty_id, RefMode::Ref) => {
                        write!(f, "&{}", self.0.display_ty_prec(*ty_id, prec))?
                    }

                    TyKind::Sum(lhs_ty_id, rhs_ty_id) => write!(
                        f,
                        "{} + {}",
                        self.0.display_ty_prec(*lhs_ty_id, prec),
                        self.0.display_ty_prec(*rhs_ty_id, prec + 1),
                    )?,

                    TyKind::Fn(ty) => {
                        write!(f, "fn(")?;

                        for (idx, &param_ty_id) in ty.params.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}", self.0.display_ty_prec(param_ty_id, 0))?;
                        }

                        write!(f, ") -> {}", self.0.display_ty_prec(ty.ret, prec))?;
                    }

                    TyKind::Tuple(ty) => {
                        write!(f, "{{")?;

                        for (idx, &elem_ty_id) in ty.elems.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}", self.0.display_ty_prec(elem_ty_id, 0))?;
                        }

                        write!(f, "}}")?;
                    }

                    TyKind::Record(ty) => {
                        write!(f, "{{")?;

                        for (idx, (name, elem_ty_id)) in ty.elems.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{name} : {}", self.0.display_ty_prec(*elem_ty_id, 0))?;
                        }

                        write!(f, "}}")?;
                    }

                    TyKind::Variant(ty) => {
                        write!(f, "<|")?;

                        for (idx, (name, elem_ty_id)) in ty.elems.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            if let Some(elem_ty_id) = *elem_ty_id {
                                write!(f, "{name} : {}", self.0.display_ty_prec(elem_ty_id, 0))?;
                            } else {
                                write!(f, "{name}")?;
                            }
                        }

                        write!(f, "|>")?;
                    }

                    TyKind::List(elem_ty_id) => {
                        write!(f, "[{}]", self.0.display_ty_prec(*elem_ty_id, 0))?;
                    }

                    TyKind::Top => write!(f, "Top")?,
                    TyKind::Bot => write!(f, "Bot")?,

                    TyKind::Var(binding_id) => {
                        write!(f, "{}", self.0.bindings[*binding_id].name)?;
                    }

                    TyKind::ForAll(binding_ids, inner_ty_id) => {
                        write!(f, "forall")?;

                        for (idx, binding_id) in binding_ids.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ",")?;
                            }

                            write!(f, " {}", self.0.bindings[*binding_id].name)?;
                        }

                        write!(f, ". {}", self.0.display_ty_prec(*inner_ty_id, prec))?;
                    }
                }

                if prec < self.2 {
                    write!(f, ")")?;
                }

                Ok(())
            }
        }

        Formatter(self, ty_id, prec)
    }
}

#[derive(Debug, Default, Clone)]
pub struct WellKnownTys {
    pub error: TyId,
    pub untyped: TyId,
    pub unit: TyId,
    pub bool: TyId,
    pub nat: TyId,
    pub empty_tuple: TyId,
    pub top: TyId,
    pub bot: TyId,
}

#[derive(Debug, Clone)]
pub struct Ty {
    pub kind: TyKind,
    pub vars: FxHashSet<BindingId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Untyped { error: bool },

    Unit,
    Bool,
    Nat,
    Ref(TyId, RefMode),
    Sum(TyId, TyId),
    Fn(TyFn),
    Tuple(TyTuple),
    Record(TyRecord),
    Variant(TyVariant),
    List(TyId),
    Top,
    Bot,
    Var(BindingId),
    ForAll(Vec<BindingId>, TyId),
}

impl TyKind {
    /// Returns `true` if it's not a variable nor contains subtypes.
    pub fn is_atomic(&self) -> bool {
        match self {
            Self::Untyped { .. } | Self::Unit | Self::Bool | Self::Nat | Self::Top | Self::Bot => {
                true
            }

            Self::Ref(..)
            | Self::Sum(..)
            | Self::Fn(..)
            | Self::Tuple(..)
            | Self::Record(..)
            | Self::Variant(..)
            | Self::List(..)
            | Self::Var(..)
            | Self::ForAll(..) => false,
        }
    }
}

impl Default for TyKind {
    fn default() -> Self {
        Self::Untyped { error: true }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefMode {
    Source,
    Ref,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyFn {
    pub params: Vec<TyId>,
    pub ret: TyId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyTuple {
    pub elems: Vec<TyId>,
}

#[derive(Debug, Clone, Eq)]
pub struct TyRecord {
    pub elems: Vec<(String, TyId)>,
    pub fields: FxHashMap<String, usize>,
}

impl TyRecord {
    pub fn new(elems: Vec<(String, TyId)>) -> Self {
        let fields = elems
            .iter()
            .enumerate()
            .map(|(idx, (k, _))| (k.clone(), idx))
            .collect();

        Self { elems, fields }
    }
}

impl PartialEq for TyRecord {
    fn eq(&self, other: &Self) -> bool {
        self.elems == other.elems
    }
}

impl Hash for TyRecord {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.elems.hash(state)
    }
}

#[derive(Debug, Clone, Eq)]
pub struct TyVariant {
    pub elems: Vec<(String, Option<TyId>)>,
    pub labels: FxHashMap<String, usize>,
}

impl TyVariant {
    pub fn new(elems: Vec<(String, Option<TyId>)>) -> Self {
        let labels = elems
            .iter()
            .enumerate()
            .map(|(idx, (k, _))| (k.clone(), idx))
            .collect();

        Self { elems, labels }
    }
}

impl PartialEq for TyVariant {
    fn eq(&self, other: &Self) -> bool {
        self.elems == other.elems
    }
}

impl Hash for TyVariant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.elems.hash(state)
    }
}
