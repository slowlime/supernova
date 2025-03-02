pub mod visit;

use std::sync::LazyLock;

use derive_more::From;
use num::BigUint;
use visit::{AstRecurse, Visitor, VisitorMut};

use crate::location::Location;
use crate::parse::Token;
use crate::sema::{DeclId, ExprId, PatId, TyExprId};

#[derive(Debug, Clone)]
pub struct Program<'src> {
    pub location: Location,
    pub extensions: Vec<(Extension, Location)>,
    pub decls: Vec<Decl<'src>>,
}

#[derive(
    strum::Display, strum::EnumString, strum::VariantArray, Debug, Clone, Copy, PartialEq, Eq, Hash,
)]
#[strum(serialize_all = "kebab-case")]
pub enum Extension {
    UnitType,
    Pairs,
    Tuples,
    Records,
    TypeAscriptions,
    SumTypes,
    Lists,
    Variants,
    FixpointCombinator,
    NaturalLiterals,
    NestedFunctionDeclarations,
    NullaryFunctions,
    MultiparameterFunctions,
    StructuralPatterns,
    NullaryVariantLabels,
    LetBindings,
    LetrecBindings,
    PatternAscriptions,
    ArithmeticOperations,
    ComparisonOperations,
    Sequencing,
    LetPatterns,
}

#[derive(Debug, Default, Clone)]
pub struct Decl<'src> {
    pub id: DeclId,
    pub location: Location,
    pub kind: DeclKind<'src>,
}

pub static DUMMY_DECL: LazyLock<Decl<'_>> = LazyLock::new(Default::default);

impl<'src> AstRecurse<'src> for Decl<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse_mut(visitor);
    }
}

#[derive(From, Debug, Default, Clone)]
pub enum DeclKind<'src> {
    #[default]
    Dummy,

    Fn(DeclFn<'src>),
    TypeAlias(DeclTypeAlias<'src>),
    ExceptionType(DeclExceptionType<'src>),
    ExceptionVariant(DeclExceptionVariant<'src>),
}

impl<'src> AstRecurse<'src> for DeclKind<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Fn(decl) => decl.recurse(visitor),
            Self::TypeAlias(decl) => decl.recurse(visitor),
            Self::ExceptionType(decl) => decl.recurse(visitor),
            Self::ExceptionVariant(decl) => decl.recurse(visitor),
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Fn(decl) => decl.recurse_mut(visitor),
            Self::TypeAlias(decl) => decl.recurse_mut(visitor),
            Self::ExceptionType(decl) => decl.recurse_mut(visitor),
            Self::ExceptionVariant(decl) => decl.recurse_mut(visitor),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DeclFn<'src> {
    pub annotations: Vec<Annotation>,
    pub generic_kw: Option<Token<'src>>,
    pub fn_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub generics: Vec<Name<'src>>,
    pub params: Vec<Param<'src>>,
    pub ret_token: Option<Token<'src>>,
    pub ret: Option<TyExpr<'src>>,
    pub throws_kw: Option<Token<'src>>,
    pub throws: Vec<TyExpr<'src>>,
    pub decls: Vec<Decl<'src>>,
    pub body: Body<'src>,
}

impl<'src> AstRecurse<'src> for DeclFn<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &self.params {
            param.recurse(visitor);
        }

        if let Some(ret) = &self.ret {
            visitor.visit_ty_expr(ret);
        }

        for ty_expr in &self.throws {
            visitor.visit_ty_expr(ty_expr);
        }

        for decl in &self.decls {
            decl.recurse(visitor);
        }

        self.body.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &mut self.params {
            param.recurse_mut(visitor);
        }

        if let Some(ret) = &mut self.ret {
            visitor.visit_ty_expr(ret);
        }

        for ty_expr in &mut self.throws {
            visitor.visit_ty_expr(ty_expr);
        }

        for decl in &mut self.decls {
            decl.recurse_mut(visitor);
        }

        self.body.recurse_mut(visitor);
    }
}

#[derive(Debug, Clone)]
pub struct DeclTypeAlias<'src> {
    pub type_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub eq_token: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for DeclTypeAlias<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct DeclExceptionType<'src> {
    pub exception_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for DeclExceptionType<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct DeclExceptionVariant<'src> {
    pub exception_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub variant_ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for DeclExceptionVariant<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.variant_ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.variant_ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct Annotation {
    pub location: Location,
    pub kind: AnnotationKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AnnotationKind {
    Inline,
}

#[derive(Debug, Clone)]
pub enum Name<'src> {
    Token(Token<'src>),
    Synthetic(String),
}

impl Name<'_> {
    pub fn location(&self) -> Location {
        match self {
            Self::Token(token) => token.span.into(),
            Self::Synthetic(_) => Location::Builtin,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Param<'src> {
    pub name: Name<'src>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for Param<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct Body<'src> {
    pub ret_kw: Option<Token<'src>>,
    pub ret: Expr<'src>,
}

impl<'src> AstRecurse<'src> for Body<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.ret);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.ret);
    }
}

#[derive(Debug, Default, Clone)]
pub struct TyExpr<'src> {
    pub id: TyExprId,
    pub location: Location,
    pub kind: TyExprKind<'src>,
}

pub static DUMMY_TY_EXPR: LazyLock<TyExpr<'_>> = LazyLock::new(Default::default);

impl<'src> AstRecurse<'src> for TyExpr<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse_mut(visitor);
    }
}

#[derive(From, Debug, Default, Clone)]
pub enum TyExprKind<'src> {
    #[default]
    Dummy,

    Bool(TyExprBool),
    Nat(TyExprNat),
    Ref(TyExprRef<'src>),
    Sum(TyExprSum<'src>),
    Fn(TyExprFn<'src>),
    ForAll(TyExprForAll<'src>),
    Mu(TyExprMu<'src>),
    Tuple(TyExprTuple<'src>),
    Record(TyExprRecord<'src>),
    Variant(TyExprVariant<'src>),
    List(TyExprList<'src>),
    Unit(TyExprUnit),
    Top(TyExprTop),
    Bot(TyExprBot),
    Auto(TyExprAuto),
    Name(TyExprName<'src>),
}

impl<'src> AstRecurse<'src> for TyExprKind<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Bool(_) => {}
            Self::Nat(_) => {}
            Self::Ref(ty_expr) => ty_expr.recurse(visitor),
            Self::Sum(ty_expr) => ty_expr.recurse(visitor),
            Self::Fn(ty_expr) => ty_expr.recurse(visitor),
            Self::ForAll(ty_expr) => ty_expr.recurse(visitor),
            Self::Mu(ty_expr) => ty_expr.recurse(visitor),
            Self::Tuple(ty_expr) => ty_expr.recurse(visitor),
            Self::Record(ty_expr) => ty_expr.recurse(visitor),
            Self::Variant(ty_expr) => ty_expr.recurse(visitor),
            Self::List(ty_expr) => ty_expr.recurse(visitor),
            Self::Unit(_) => {}
            Self::Top(_) => {}
            Self::Bot(_) => {}
            Self::Auto(_) => {}
            Self::Name(_) => {}
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Bool(_) => {}
            Self::Nat(_) => {}
            Self::Ref(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Sum(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Fn(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::ForAll(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Mu(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Tuple(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Record(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Variant(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::List(ty_expr) => ty_expr.recurse_mut(visitor),
            Self::Unit(_) => {}
            Self::Top(_) => {}
            Self::Bot(_) => {}
            Self::Auto(_) => {}
            Self::Name(_) => {}
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyExprBool;

#[derive(Debug, Clone)]
pub struct TyExprNat;

#[derive(Debug, Clone)]
pub struct TyExprRef<'src> {
    pub ref_token: Option<Token<'src>>,
    pub ty_expr: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprRef<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprSum<'src> {
    pub lhs: Box<TyExpr<'src>>,
    pub plus_token: Option<Token<'src>>,
    pub rhs: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprSum<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.lhs);
        visitor.visit_ty_expr(&self.rhs);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.lhs);
        visitor.visit_ty_expr(&mut self.rhs);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprFn<'src> {
    pub fn_kw: Option<Token<'src>>,
    pub params: Vec<TyExpr<'src>>,
    pub ret: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprFn<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &self.params {
            visitor.visit_ty_expr(param);
        }

        visitor.visit_ty_expr(&self.ret);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &mut self.params {
            visitor.visit_ty_expr(param);
        }

        visitor.visit_ty_expr(&mut self.ret);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprForAll<'src> {
    pub forall_location: Location,
    pub synthetic: bool,
    pub name: Name<'src>,
    pub ty_expr: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprForAll<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprMu<'src> {
    pub mu_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub ty_expr: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprMu<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprTuple<'src> {
    pub elems: Vec<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprTuple<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            visitor.visit_ty_expr(elem);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            visitor.visit_ty_expr(elem);
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyExprRecord<'src> {
    pub fields: Vec<TyExprRecordField<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprRecord<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &self.fields {
            field.recurse(visitor);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &mut self.fields {
            field.recurse_mut(visitor);
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyExprRecordField<'src> {
    pub name: Name<'src>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for TyExprRecordField<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprVariant<'src> {
    pub fields: Vec<TyExprVariantField<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprVariant<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &self.fields {
            field.recurse(visitor);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &mut self.fields {
            field.recurse_mut(visitor);
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyExprVariantField<'src> {
    pub name: Name<'src>,
    pub ty_expr: Option<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprVariantField<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(ty_expr) = &self.ty_expr {
            visitor.visit_ty_expr(ty_expr);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(ty_expr) = &mut self.ty_expr {
            visitor.visit_ty_expr(ty_expr);
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyExprList<'src> {
    pub ty_expr: Box<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for TyExprList<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct TyExprUnit;

#[derive(Debug, Clone)]
pub struct TyExprTop;

#[derive(Debug, Clone)]
pub struct TyExprBot;

#[derive(Debug, Clone)]
pub struct TyExprAuto;

#[derive(Debug, Clone)]
pub struct TyExprName<'src> {
    pub name: Name<'src>,
}

#[derive(Debug, Default, Clone)]
pub struct Expr<'src> {
    pub id: ExprId,
    pub location: Location,
    pub kind: ExprKind<'src>,
}

pub static DUMMY_EXPR: LazyLock<Expr<'_>> = LazyLock::new(Default::default);

impl<'src> AstRecurse<'src> for Expr<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse_mut(visitor);
    }
}

#[derive(From, Debug, Default, Clone)]
pub enum ExprKind<'src> {
    #[default]
    Dummy,

    Bool(ExprBool),
    Unit(ExprUnit),
    Int(ExprInt),
    Address(ExprAddress),
    Name(ExprName<'src>),

    Field(ExprField<'src>),
    Panic(ExprPanic),
    Throw(ExprThrow<'src>),
    TryCatch(ExprTry<'src>),
    TryCast(ExprTryCast<'src>),
    Fix(ExprFix<'src>),
    Fold(ExprFold<'src>),
    Unfold(ExprUnfold<'src>),
    Apply(ExprApply<'src>),
    TyApply(ExprTyApply<'src>),
    Ascription(ExprAscription<'src>),
    Cast(ExprCast<'src>),
    Fn(ExprFn<'src>),
    Tuple(ExprTuple<'src>),
    Record(ExprRecord<'src>),
    Variant(ExprVariant<'src>),
    Match(ExprMatch<'src>),
    List(ExprList<'src>),
    If(ExprIf<'src>),
    Seq(ExprSeq<'src>),
    Let(ExprLet<'src>),
    Generic(ExprGeneric<'src>),

    Unary(ExprUnary<'src>),
    Binary(ExprBinary<'src>),
}

impl<'src> AstRecurse<'src> for ExprKind<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Bool(_) => {}
            Self::Unit(_) => {}
            Self::Int(_) => {}
            Self::Address(_) => {}
            Self::Name(_) => {}
            Self::Field(expr) => expr.recurse(visitor),
            Self::Panic(_) => {}
            Self::Throw(expr) => expr.recurse(visitor),
            Self::TryCatch(expr) => expr.recurse(visitor),
            Self::TryCast(expr) => expr.recurse(visitor),
            Self::Fix(expr) => expr.recurse(visitor),
            Self::Fold(expr) => expr.recurse(visitor),
            Self::Unfold(expr) => expr.recurse(visitor),
            Self::Apply(expr) => expr.recurse(visitor),
            Self::TyApply(expr) => expr.recurse(visitor),
            Self::Ascription(expr) => expr.recurse(visitor),
            Self::Cast(expr) => expr.recurse(visitor),
            Self::Fn(expr) => expr.recurse(visitor),
            Self::Tuple(expr) => expr.recurse(visitor),
            Self::Record(expr) => expr.recurse(visitor),
            Self::Variant(expr) => expr.recurse(visitor),
            Self::Match(expr) => expr.recurse(visitor),
            Self::List(expr) => expr.recurse(visitor),
            Self::If(expr) => expr.recurse(visitor),
            Self::Seq(expr) => expr.recurse(visitor),
            Self::Let(expr) => expr.recurse(visitor),
            Self::Generic(expr) => expr.recurse(visitor),
            Self::Unary(expr) => expr.recurse(visitor),
            Self::Binary(expr) => expr.recurse(visitor),
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Bool(_) => {}
            Self::Unit(_) => {}
            Self::Int(_) => {}
            Self::Address(_) => {}
            Self::Name(_) => {}
            Self::Field(expr) => expr.recurse_mut(visitor),
            Self::Panic(_) => {}
            Self::Throw(expr) => expr.recurse_mut(visitor),
            Self::TryCatch(expr) => expr.recurse_mut(visitor),
            Self::TryCast(expr) => expr.recurse_mut(visitor),
            Self::Fix(expr) => expr.recurse_mut(visitor),
            Self::Fold(expr) => expr.recurse_mut(visitor),
            Self::Unfold(expr) => expr.recurse_mut(visitor),
            Self::Apply(expr) => expr.recurse_mut(visitor),
            Self::TyApply(expr) => expr.recurse_mut(visitor),
            Self::Ascription(expr) => expr.recurse_mut(visitor),
            Self::Cast(expr) => expr.recurse_mut(visitor),
            Self::Fn(expr) => expr.recurse_mut(visitor),
            Self::Tuple(expr) => expr.recurse_mut(visitor),
            Self::Record(expr) => expr.recurse_mut(visitor),
            Self::Variant(expr) => expr.recurse_mut(visitor),
            Self::Match(expr) => expr.recurse_mut(visitor),
            Self::List(expr) => expr.recurse_mut(visitor),
            Self::If(expr) => expr.recurse_mut(visitor),
            Self::Seq(expr) => expr.recurse_mut(visitor),
            Self::Let(expr) => expr.recurse_mut(visitor),
            Self::Generic(expr) => expr.recurse_mut(visitor),
            Self::Unary(expr) => expr.recurse_mut(visitor),
            Self::Binary(expr) => expr.recurse_mut(visitor),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprBool {
    pub value: bool,
}

#[derive(Debug, Clone)]
pub struct ExprUnit;

#[derive(Debug, Clone)]
pub struct ExprInt {
    pub value: BigUint,
}

#[derive(Debug, Clone)]
pub struct ExprAddress {
    pub value: BigUint,
}

#[derive(Debug, Clone)]
pub struct ExprName<'src> {
    pub name: Name<'src>,
}

#[derive(Debug, Clone)]
pub struct ExprField<'src> {
    pub base: Box<Expr<'src>>,
    pub field: ExprFieldName<'src>,
}

impl<'src> AstRecurse<'src> for ExprField<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.base);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.base);
    }
}

#[derive(Debug, Clone)]
pub enum ExprFieldName<'src> {
    Name(Name<'src>),
    Index(Location, usize),
}

#[derive(Debug, Clone)]
pub struct ExprPanic;

#[derive(Debug, Clone)]
pub struct ExprThrow<'src> {
    pub exc: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprThrow<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.exc);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.exc);
    }
}

#[derive(Debug, Clone)]
pub struct ExprTry<'src> {
    pub try_expr: Box<Expr<'src>>,
    pub fallback: ExprTryFallback<'src>,
}

impl<'src> AstRecurse<'src> for ExprTry<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.try_expr);
        self.fallback.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.try_expr);
        self.fallback.recurse_mut(visitor);
    }
}

#[derive(Debug, Clone)]
pub enum ExprTryFallback<'src> {
    Catch(Box<Arm<'src>>),
    With(Box<Expr<'src>>),
}

impl<'src> AstRecurse<'src> for ExprTryFallback<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Catch(arm) => arm.recurse(visitor),
            Self::With(expr) => visitor.visit_expr(expr),
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Catch(arm) => arm.recurse_mut(visitor),
            Self::With(expr) => visitor.visit_expr(expr),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprTryCast<'src> {
    pub try_expr: Box<Expr<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub arm: Box<Arm<'src>>,
    pub fallback: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprTryCast<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.try_expr);
        visitor.visit_ty_expr(&self.ty_expr);
        self.arm.recurse(visitor);
        visitor.visit_expr(&self.fallback);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.try_expr);
        visitor.visit_ty_expr(&mut self.ty_expr);
        self.arm.recurse_mut(visitor);
        visitor.visit_expr(&mut self.fallback);
    }
}

#[derive(Debug, Clone)]
pub struct ExprFix<'src> {
    pub fix_kw: Option<Token<'src>>,
    pub expr: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprFix<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprFold<'src> {
    pub fold_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub expr: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprFold<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprUnfold<'src> {
    pub unfold_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub expr: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprUnfold<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&self.ty_expr);
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_ty_expr(&mut self.ty_expr);
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprApply<'src> {
    pub callee: Callee<'src>,
    pub lparen: Option<Token<'src>>,
    pub args: Vec<Expr<'src>>,
    pub rparen: Option<Token<'src>>,
}

impl<'src> AstRecurse<'src> for ExprApply<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.callee.recurse(visitor);

        for arg in &self.args {
            visitor.visit_expr(arg);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.callee.recurse_mut(visitor);

        for arg in &mut self.args {
            visitor.visit_expr(arg);
        }
    }
}

#[derive(Debug, Clone)]
pub enum Callee<'src> {
    Builtin {
        kw: Option<Token<'src>>,
        builtin: Builtin,
    },

    Expr(Box<Expr<'src>>),
}

impl Callee<'_> {
    pub fn location(&self) -> Location {
        match self {
            Self::Builtin { kw: Some(kw), .. } => kw.span.into(),
            Self::Builtin { .. } => Location::Builtin,
            Self::Expr(expr) => expr.location,
        }
    }
}

impl<'src> AstRecurse<'src> for Callee<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Builtin { .. } => {}
            Self::Expr(expr) => visitor.visit_expr(expr),
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Builtin { .. } => {}
            Self::Expr(expr) => visitor.visit_expr(expr),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    Inl,
    Inr,
    Cons,
    ListHead,
    ListIsEmpty,
    ListTail,
    Succ,
    Not,
    NatPred,
    NatIsZero,
    NatRec,
}

#[derive(Debug, Clone)]
pub struct ExprTyApply<'src> {
    pub callee: Box<Expr<'src>>,
    pub args: Vec<TyExpr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprTyApply<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.callee);

        for arg in &self.args {
            visitor.visit_ty_expr(arg);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.callee);

        for arg in &mut self.args {
            visitor.visit_ty_expr(arg);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprAscription<'src> {
    pub expr: Box<Expr<'src>>,
    pub as_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for ExprAscription<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprCast<'src> {
    pub expr: Box<Expr<'src>>,
    pub cast_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for ExprCast<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprFn<'src> {
    pub params: Vec<Param<'src>>,
    pub body: Box<Body<'src>>,
}

impl<'src> AstRecurse<'src> for ExprFn<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &self.params {
            param.recurse(visitor);
        }

        self.body.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for param in &mut self.params {
            param.recurse_mut(visitor);
        }

        self.body.recurse_mut(visitor);
    }
}

#[derive(Debug, Clone)]
pub struct ExprTuple<'src> {
    pub elems: Vec<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprTuple<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            visitor.visit_expr(elem);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            visitor.visit_expr(elem);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprRecord<'src> {
    pub elems: Vec<ExprRecordField<'src>>,
}

impl<'src> AstRecurse<'src> for ExprRecord<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            elem.recurse(visitor);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            elem.recurse_mut(visitor);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprRecordField<'src> {
    pub name: Name<'src>,
    pub expr: Expr<'src>,
}

impl<'src> AstRecurse<'src> for ExprRecordField<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprVariant<'src> {
    pub label: Name<'src>,
    pub expr: Option<Box<Expr<'src>>>,
}

impl<'src> AstRecurse<'src> for ExprVariant<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(expr) = &self.expr {
            visitor.visit_expr(expr);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(expr) = &mut self.expr {
            visitor.visit_expr(expr);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprMatch<'src> {
    pub expr: Box<Expr<'src>>,
    pub arms: Vec<Arm<'src>>,
}

impl<'src> AstRecurse<'src> for ExprMatch<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);

        for arm in &self.arms {
            arm.recurse(visitor);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);

        for arm in &mut self.arms {
            arm.recurse_mut(visitor);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprList<'src> {
    pub elems: Vec<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprList<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            visitor.visit_expr(elem);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            visitor.visit_expr(elem);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprIf<'src> {
    pub cond: Box<Expr<'src>>,
    pub then_expr: Box<Expr<'src>>,
    pub else_expr: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprIf<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.cond);
        visitor.visit_expr(&self.then_expr);
        visitor.visit_expr(&self.else_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.cond);
        visitor.visit_expr(&mut self.then_expr);
        visitor.visit_expr(&mut self.else_expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprSeq<'src> {
    pub exprs: Vec<(Expr<'src>, Option<Token<'src>>)>,
}

impl<'src> AstRecurse<'src> for ExprSeq<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for (expr, _) in &self.exprs {
            visitor.visit_expr(expr);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for (expr, _) in &mut self.exprs {
            visitor.visit_expr(expr);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExprLet<'src> {
    pub let_kw: Option<Token<'src>>,
    pub rec: bool,
    pub bindings: Vec<Binding<'src>>,
    pub body: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprLet<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for binding in &self.bindings {
            binding.recurse(visitor);
        }

        visitor.visit_expr(&self.body);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for binding in &mut self.bindings {
            binding.recurse_mut(visitor);
        }

        visitor.visit_expr(&mut self.body);
    }
}

#[derive(Debug, Clone)]
pub struct Binding<'src> {
    pub pat: Pat<'src>,
    pub expr: Expr<'src>,
}

impl<'src> AstRecurse<'src> for Binding<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&self.pat);
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&mut self.pat);
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprGeneric<'src> {
    pub generics: Vec<Name<'src>>,
    pub expr: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprGeneric<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.expr);
    }
}

#[derive(Debug, Clone)]
pub struct ExprUnary<'src> {
    pub token: Option<Token<'src>>,
    pub op: UnOp,
    pub rhs: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprUnary<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.rhs);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.rhs);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    New,
    Deref,
}

#[derive(Debug, Clone)]
pub struct ExprBinary<'src> {
    pub lhs: Box<Expr<'src>>,
    pub token: Option<Token<'src>>,
    pub op: BinOp,
    pub rhs: Box<Expr<'src>>,
}

impl<'src> AstRecurse<'src> for ExprBinary<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&self.lhs);
        visitor.visit_expr(&self.rhs);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_expr(&mut self.lhs);
        visitor.visit_expr(&mut self.rhs);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    Assign,
}

#[derive(Debug, Clone)]
pub struct Arm<'src> {
    pub pat: Pat<'src>,
    pub body: Expr<'src>,
}

impl<'src> AstRecurse<'src> for Arm<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&self.pat);
        visitor.visit_expr(&self.body);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&mut self.pat);
        visitor.visit_expr(&mut self.body);
    }
}

#[derive(Debug, Default, Clone)]
pub struct Pat<'src> {
    pub id: PatId,
    pub location: Location,
    pub nested: bool,
    pub kind: PatKind<'src>,
}

impl Pat<'_> {
    pub fn with_nested(self, nested: bool) -> Self {
        Self {
            nested,
            ..self
        }
    }
}

pub static DUMMY_PAT: LazyLock<Pat<'_>> = LazyLock::new(Default::default);

impl<'src> AstRecurse<'src> for Pat<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse(visitor);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        self.kind.recurse_mut(visitor);
    }
}

#[derive(From, Debug, Default, Clone)]
pub enum PatKind<'src> {
    #[default]
    Dummy,

    Variant(PatVariant<'src>),
    Cons(PatCons<'src>),
    Tuple(PatTuple<'src>),
    Record(PatRecord<'src>),
    List(PatList<'src>),
    Bool(PatBool),
    Unit(PatUnit),
    Int(PatInt),
    Name(PatName<'src>),
    Ascription(PatAscription<'src>),
    Cast(PatCast<'src>),
}

impl<'src> AstRecurse<'src> for PatKind<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Variant(pat) => pat.recurse(visitor),
            Self::Cons(pat) => pat.recurse(visitor),
            Self::Tuple(pat) => pat.recurse(visitor),
            Self::Record(pat) => pat.recurse(visitor),
            Self::List(pat) => pat.recurse(visitor),
            Self::Bool(_) => {}
            Self::Unit(_) => {}
            Self::Int(_) => {}
            Self::Name(_) => {}
            Self::Ascription(pat) => pat.recurse(visitor),
            Self::Cast(pat) => pat.recurse(visitor),
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        match self {
            Self::Dummy => {}
            Self::Variant(pat) => pat.recurse_mut(visitor),
            Self::Cons(pat) => pat.recurse_mut(visitor),
            Self::Tuple(pat) => pat.recurse_mut(visitor),
            Self::Record(pat) => pat.recurse_mut(visitor),
            Self::List(pat) => pat.recurse_mut(visitor),
            Self::Bool(_) => {}
            Self::Unit(_) => {}
            Self::Int(_) => {}
            Self::Name(_) => {}
            Self::Ascription(pat) => pat.recurse_mut(visitor),
            Self::Cast(pat) => pat.recurse_mut(visitor),
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatVariant<'src> {
    pub label: Name<'src>,
    pub pat: Option<Box<Pat<'src>>>,
}

impl<'src> AstRecurse<'src> for PatVariant<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(pat) = &self.pat {
            visitor.visit_pat(pat);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        if let Some(pat) = &mut self.pat {
            visitor.visit_pat(pat);
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatCons<'src> {
    pub cons: Cons,
    pub args: Vec<Pat<'src>>,
}

impl<'src> AstRecurse<'src> for PatCons<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for arg in &self.args {
            visitor.visit_pat(arg);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for arg in &mut self.args {
            visitor.visit_pat(arg);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cons {
    Inl,
    Inr,
    Cons,
    Succ,
}

#[derive(Debug, Clone)]
pub struct PatTuple<'src> {
    pub elems: Vec<Pat<'src>>,
}

impl<'src> AstRecurse<'src> for PatTuple<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            visitor.visit_pat(elem);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            visitor.visit_pat(elem);
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatRecord<'src> {
    pub fields: Vec<PatRecordField<'src>>,
}

impl<'src> AstRecurse<'src> for PatRecord<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &self.fields {
            field.recurse(visitor);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for field in &mut self.fields {
            field.recurse_mut(visitor);
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatRecordField<'src> {
    pub name: Name<'src>,
    pub pat: Pat<'src>,
}

impl<'src> AstRecurse<'src> for PatRecordField<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&self.pat);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&mut self.pat);
    }
}

#[derive(Debug, Clone)]
pub struct PatList<'src> {
    pub elems: Vec<Pat<'src>>,
}

impl<'src> AstRecurse<'src> for PatList<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &self.elems {
            visitor.visit_pat(elem);
        }
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        for elem in &mut self.elems {
            visitor.visit_pat(elem);
        }
    }
}

#[derive(Debug, Clone)]
pub struct PatBool {
    pub value: bool,
}

#[derive(Debug, Clone)]
pub struct PatUnit;

#[derive(Debug, Clone)]
pub struct PatInt {
    pub value: BigUint,
}

#[derive(Debug, Clone)]
pub struct PatName<'src> {
    pub name: Name<'src>,
}

#[derive(Debug, Clone)]
pub struct PatAscription<'src> {
    pub pat: Box<Pat<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for PatAscription<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&self.pat);
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&mut self.pat);
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}

#[derive(Debug, Clone)]
pub struct PatCast<'src> {
    pub pat: Box<Pat<'src>>,
    pub ty_expr: TyExpr<'src>,
}

impl<'src> AstRecurse<'src> for PatCast<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&self.pat);
        visitor.visit_ty_expr(&self.ty_expr);
    }

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast,
    {
        visitor.visit_pat(&mut self.pat);
        visitor.visit_ty_expr(&mut self.ty_expr);
    }
}
