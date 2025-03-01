pub mod feature;
mod error;
mod load_ast;
mod process_features;
pub mod ty;

use fxhash::FxHashMap;
use slotmap::{new_key_type, SlotMap};

use crate::ast;
use crate::diag::DiagCtx;
use crate::location::Location;

use self::feature::{Feature, FeatureKind};
use self::ty::{Ty, TyKind, WellKnownTys};

pub use self::error::SemaError;

new_key_type! {
    pub struct DeclId;
    pub struct TyExprId;
    pub struct ExprId;
    pub struct PatId;
    pub struct TyId;
    pub struct BindingId;
    pub struct ScopeId;
}

pub type Result<T = (), E = ()> = std::result::Result<T, E>;

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
    pub location: Location,                            // initialized by load_ast
    pub features: FxHashMap<FeatureKind, Feature>, // initialized by load_ast and process_features
    pub decls: SlotMap<DeclId, DeclInfo<'ast>>,    // initialized by load_ast
    pub ty_exprs: SlotMap<TyExprId, TyExprInfo<'ast>>, // initialized by load_ast
    pub exprs: SlotMap<ExprId, ExprInfo<'ast>>,    // initialized by load_ast
    pub pats: SlotMap<PatId, PatInfo<'ast>>,       // initialized by load_ast
    pub bindings: SlotMap<BindingId, BindingInfo>,
    pub scopes: SlotMap<ScopeId, Scope>,
    pub root_scope_id: ScopeId,
    pub tys: SlotMap<TyId, Ty>,
    ty_dedup: FxHashMap<TyKind, TyId>,
    pub well_known_tys: WellKnownTys,
}

impl Module<'_> {
    fn new() -> Self {
        Self {
            location: Default::default(),
            features: Default::default(),
            decls: Default::default(),
            ty_exprs: Default::default(),
            exprs: Default::default(),
            pats: Default::default(),
            bindings: Default::default(),
            scopes: Default::default(),
            root_scope_id: Default::default(),
            tys: Default::default(),
            ty_dedup: Default::default(),
            well_known_tys: Default::default(),
        }
    }

    fn is_feature_enabled(&self, feature: FeatureKind) -> bool {
        self.features.contains_key(&feature)
    }
}

pub fn process<'ast>(
    ast: &'ast mut ast::Program<'ast>,
    diag: &mut impl DiagCtx,
) -> (Module<'ast>, Result) {
    let mut module = Module::new();
    module.load_ast(ast);

    let result = (|| -> Result {
        module.process_features(diag)?;

        Ok(())
    })();

    (module, result)
}
