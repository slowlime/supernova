mod error;
pub mod feature;
mod load_ast;
mod process_features;
mod resolve;
pub mod ty;
mod typeck;

use fxhash::FxHashMap;
use slotmap::{SlotMap, SparseSecondaryMap, new_key_type};

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
    pub parent: Option<DeclId>,
}

impl DeclInfo<'_> {
    pub fn for_each_child(&self, mut f: impl FnMut(DeclId)) {
        match &self.def.kind {
            ast::DeclKind::Dummy => {}
            ast::DeclKind::Fn(decl) => decl.decls.iter().for_each(|decl| f(decl.id)),
            ast::DeclKind::TypeAlias(_) => todo!(),
            ast::DeclKind::ExceptionType(_) => todo!(),
            ast::DeclKind::ExceptionVariant(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprInfo<'ast> {
    pub def: &'ast ast::Expr<'ast>,
    pub ty_id: TyId,
}

#[derive(Debug, Clone)]
pub struct TyExprInfo<'ast> {
    pub def: &'ast ast::TyExpr<'ast>,
    pub ty_id: TyId,
}

#[derive(Debug, Clone)]
pub struct PatInfo<'ast> {
    pub def: &'ast ast::Pat<'ast>,
    pub ty_id: TyId,
}

#[derive(Debug, Clone)]
pub struct BindingInfo {
    pub location: Location,
    pub name: String,
    pub ty_id: TyId,
    pub kind: BindingKind,
}

#[derive(Debug, Default, Clone)]
pub enum BindingKind {
    #[default]
    Dummy,

    FnDecl(DeclId),
    DeclFnParam(DeclId, usize),
    ExprFnParam(ExprId, usize),
    Pat(PatId),

    Ty(TyId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Namespace {
    Ty,
    Value,
}

#[derive(Debug, Clone)]
pub struct Scope {
    /// The scope this scope belongs to.
    pub parent: Option<ScopeId>,

    /// The scope that undefined names are resolved in.
    pub visible_parent: Option<ScopeId>,

    pub tys: FxHashMap<String, BindingId>,
    pub values: FxHashMap<String, BindingId>,
}

impl Scope {
    fn get_bindings(&self, ns: Namespace) -> &FxHashMap<String, BindingId> {
        match ns {
            Namespace::Ty => &self.tys,
            Namespace::Value => &self.values,
        }
    }

    fn get_bindings_mut(&mut self, ns: Namespace) -> &mut FxHashMap<String, BindingId> {
        match ns {
            Namespace::Ty => &mut self.tys,
            Namespace::Value => &mut self.values,
        }
    }
}

#[derive(Debug)]
pub struct Module<'ast> {
    pub location: Location,                            // initialized by load_ast
    pub features: FxHashMap<FeatureKind, Feature>, // initialized by load_ast and process_features
    pub decls: SlotMap<DeclId, DeclInfo<'ast>>,    // initialized by load_ast
    pub ty_exprs: SlotMap<TyExprId, TyExprInfo<'ast>>, // initialized by load_ast
    pub exprs: SlotMap<ExprId, ExprInfo<'ast>>,    // initialized by load_ast
    pub pats: SlotMap<PatId, PatInfo<'ast>>,       // initialized by load_ast
    pub bindings: SlotMap<BindingId, BindingInfo>, // initialized by load_ast and resolve
    pub scopes: SlotMap<ScopeId, Scope>,           // initialized by resolve
    pub fn_decl_scopes: SparseSecondaryMap<DeclId, ScopeId>, // initialized by resolve
    pub root_scope_id: ScopeId,                    // initialized by resolve
    pub prelude_scope_id: ScopeId,                 // initialized by resolve
    pub ty_name_exprs: SparseSecondaryMap<TyExprId, BindingId>, // initialized by resolve
    pub name_exprs: SparseSecondaryMap<ExprId, BindingId>, // initialized by resolve
    pub tys: SlotMap<TyId, Ty>,                    // initialized by typeck
    ty_dedup: FxHashMap<TyKind, TyId>,             // initialized by typeck
    pub well_known_tys: WellKnownTys,              // initialized by typeck
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
            fn_decl_scopes: Default::default(),
            root_scope_id: Default::default(),
            prelude_scope_id: Default::default(),
            ty_name_exprs: Default::default(),
            name_exprs: Default::default(),
            tys: Default::default(),
            ty_dedup: Default::default(),
            well_known_tys: Default::default(),
        }
    }

    fn is_feature_enabled(&self, feature: FeatureKind) -> bool {
        self.features.contains_key(&feature)
    }

    fn root_decl_ids(&self) -> impl Iterator<Item = DeclId> {
        self.decls
            .iter()
            .filter(|(_, decl)| decl.parent.is_none())
            .map(|(decl_id, _)| decl_id)
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
        module.resolve(diag)?;
        module.typeck(diag)?;

        Ok(())
    })();

    (module, result)
}
