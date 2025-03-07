use std::hash::{Hash, Hasher};

use fxhash::FxHashMap;

use crate::location::Location;

use super::TyId;

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
