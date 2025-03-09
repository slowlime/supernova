use std::fmt::{self, Display};
use std::hash::{Hash, Hasher};

use fxhash::FxHashMap;

use super::{Module, TyId};

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
                    TyKind::Error => 3,
                    TyKind::Unit => 3,
                    TyKind::Bool => 3,
                    TyKind::Nat => 3,
                    TyKind::Sum(..) => 2,
                    TyKind::Fn(..) => 1,
                    TyKind::Tuple(..) => 3,
                    TyKind::Record(..) => 3,
                    TyKind::Variant(..) => 3,
                    TyKind::List(..) => 3,
                };

                if prec < self.2 {
                    write!(f, "(")?;
                }

                match ty_kind {
                    TyKind::Error => write!(f, "<error>")?,
                    TyKind::Unit => write!(f, "Unit")?,
                    TyKind::Bool => write!(f, "Bool")?,
                    TyKind::Nat => write!(f, "Nat")?,

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
    pub unit: TyId,
    pub bool: TyId,
    pub nat: TyId,
    pub empty_tuple: TyId,
}

#[derive(Debug, Clone)]
pub struct Ty {
    pub kind: TyKind,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    #[default]
    Error,

    Unit,
    Bool,
    Nat,
    Sum(TyId, TyId),
    Fn(TyFn),
    Tuple(TyTuple),
    Record(TyRecord),
    Variant(TyVariant),
    List(TyId),
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
