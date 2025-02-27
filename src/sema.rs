pub mod ty;

use fxhash::FxHashMap;
use slotmap::{new_key_type, SlotMap};
use ty::{TyKind, WellKnownTys};

use crate::ast;
use crate::location::Location;
use self::ty::Ty;

new_key_type! {
    pub struct DeclId;
    pub struct TyExprId;
    pub struct ExprId;
    pub struct PatId;
    pub struct TyId;
    pub struct BindingId;
    pub struct ScopeId;
}

#[derive(Debug, Clone)]
pub struct DeclInfo<'ast> {
    pub def: &'ast ast::Decl<'ast>,
}

#[derive(Debug, Clone)]
pub struct ExprInfo<'ast> {
    pub def: &'ast ast::Expr<'ast>,
}

#[derive(Debug, Clone)]
pub struct TyExprInfo<'ast> {
    pub def: &'ast ast::TyExpr<'ast>,
}

#[derive(Debug, Clone)]
pub struct PatInfo<'ast> {
    pub def: &'ast ast::Pat<'ast>,
}

#[derive(Debug, Clone)]
pub struct BindingInfo {
    pub location: Location,
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub tys: FxHashMap<String, TyId>,
    pub values: FxHashMap<String, BindingId>,
}

#[derive(Debug)]
pub struct Module<'ast> {
    pub decls: SlotMap<DeclId, DeclInfo<'ast>>,
    pub ty_exprs: SlotMap<TyExprId, TyExprInfo<'ast>>,
    pub exprs: SlotMap<ExprId, ExprInfo<'ast>>,
    pub pats: SlotMap<PatId, PatInfo<'ast>>,
    pub bindings: SlotMap<BindingId, BindingInfo>,
    pub scopes: SlotMap<ScopeId, Scope>,
    pub root_scope_id: ScopeId,
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: FxHashMap<TyKind, TyId>,
    pub well_known_tys: WellKnownTys,
}
