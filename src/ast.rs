use derive_more::From;
use num::BigUint;

use crate::location::Location;
use crate::parse::Token;
use crate::sema::{DeclId, ExprId, PatId, TyExprId};

#[derive(Debug, Clone)]
pub struct Program<'src> {
    pub location: Location,
    pub extensions: Vec<Extension>,
    pub decls: Vec<Decl<'src>>,
}

#[derive(strum::Display, strum::EnumString, strum::VariantArray, Debug, Clone, Copy)]
#[strum(serialize_all = "kebab-case")]
pub enum Extension {
    UnitType,
}

#[derive(Debug, Clone)]
pub struct Decl<'src> {
    pub id: DeclId,
    pub location: Location,
    pub kind: DeclKind<'src>,
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

#[derive(Debug, Clone)]
pub struct DeclFn<'src> {
    pub annotations: Vec<Annotation>,
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

#[derive(Debug, Clone)]
pub struct DeclTypeAlias<'src> {
    pub type_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub eq_token: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

#[derive(Debug, Clone)]
pub struct DeclExceptionType<'src> {
    pub exception_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

#[derive(Debug, Clone)]
pub struct DeclExceptionVariant<'src> {
    pub exception_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub variant_ty_expr: TyExpr<'src>,
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

#[derive(Debug, Clone)]
pub struct Body<'src> {
    pub ret_kw: Option<Token<'src>>,
    pub ret: Expr<'src>,
}

#[derive(Debug, Clone)]
pub struct TyExpr<'src> {
    pub id: TyExprId,
    pub location: Location,
    pub kind: TyExprKind<'src>,
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

#[derive(Debug, Clone)]
pub struct TyExprBool;

#[derive(Debug, Clone)]
pub struct TyExprNat;

#[derive(Debug, Clone)]
pub struct TyExprRef<'src> {
    pub ref_token: Option<Token<'src>>,
    pub ty_expr: Box<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprSum<'src> {
    pub lhs: Box<TyExpr<'src>>,
    pub plus_token: Option<Token<'src>>,
    pub rhs: Box<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprFn<'src> {
    pub fn_kw: Option<Token<'src>>,
    pub params: Vec<TyExpr<'src>>,
    pub ret: Box<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprForAll<'src> {
    pub forall_location: Location,
    pub name: Name<'src>,
    pub ty_expr: Box<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprMu<'src> {
    pub mu_kw: Option<Token<'src>>,
    pub name: Name<'src>,
    pub ty_expr: Box<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprTuple<'src> {
    pub elems: Vec<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprRecord<'src> {
    pub fields: Vec<TyExprRecordField<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprRecordField<'src> {
    pub name: Name<'src>,
    pub ty_expr: TyExpr<'src>,
}

#[derive(Debug, Clone)]
pub struct TyExprVariant<'src> {
    pub fields: Vec<TyExprVariantField<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprVariantField<'src> {
    pub name: Name<'src>,
    pub ty_expr: Option<TyExpr<'src>>,
}

#[derive(Debug, Clone)]
pub struct TyExprList<'src> {
    pub ty_expr: Box<TyExpr<'src>>,
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

#[derive(Debug, Clone)]
pub struct Expr<'src> {
    pub id: ExprId,
    pub location: Location,
    pub kind: ExprKind<'src>,
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

#[derive(Debug, Clone)]
pub struct ExprTry<'src> {
    pub try_expr: Box<Expr<'src>>,
    pub fallback: ExprTryFallback<'src>,
}

#[derive(Debug, Clone)]
pub enum ExprTryFallback<'src> {
    Catch(Box<Arm<'src>>),
    With(Box<Expr<'src>>),
}

#[derive(Debug, Clone)]
pub struct ExprTryCast<'src> {
    pub try_expr: Box<Expr<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub arm: Box<Arm<'src>>,
    pub fallback: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprFix<'src> {
    pub fix_kw: Option<Token<'src>>,
    pub expr: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprFold<'src> {
    pub fold_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub expr: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprUnfold<'src> {
    pub unfold_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
    pub expr: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprApply<'src> {
    pub callee: Callee<'src>,
    pub lparen: Option<Token<'src>>,
    pub args: Vec<Expr<'src>>,
    pub rparen: Option<Token<'src>>,
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

#[derive(Debug, Clone)]
pub struct ExprAscription<'src> {
    pub expr: Box<Expr<'src>>,
    pub as_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

#[derive(Debug, Clone)]
pub struct ExprCast<'src> {
    pub expr: Box<Expr<'src>>,
    pub cast_kw: Option<Token<'src>>,
    pub ty_expr: TyExpr<'src>,
}

#[derive(Debug, Clone)]
pub struct ExprFn<'src> {
    pub params: Vec<Param<'src>>,
    pub body: Box<Body<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprTuple<'src> {
    pub elems: Vec<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprRecord<'src> {
    pub elems: Vec<ExprRecordField<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprRecordField<'src> {
    pub name: Name<'src>,
    pub expr: Expr<'src>,
}

#[derive(Debug, Clone)]
pub struct ExprVariant<'src> {
    pub label: Name<'src>,
    pub expr: Option<Box<Expr<'src>>>,
}

#[derive(Debug, Clone)]
pub struct ExprMatch<'src> {
    pub expr: Box<Expr<'src>>,
    pub arms: Vec<Arm<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprList<'src> {
    pub elems: Vec<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprIf<'src> {
    pub cond: Box<Expr<'src>>,
    pub then_expr: Box<Expr<'src>>,
    pub else_expr: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprSeq<'src> {
    pub exprs: Vec<(Expr<'src>, Option<Token<'src>>)>,
}

#[derive(Debug, Clone)]
pub struct ExprLet<'src> {
    pub let_kw: Option<Token<'src>>,
    pub rec: bool,
    pub bindings: Vec<Binding<'src>>,
    pub body: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct Binding<'src> {
    pub pat: Pat<'src>,
    pub expr: Expr<'src>,
}

#[derive(Debug, Clone)]
pub struct ExprGeneric<'src> {
    pub generics: Vec<Name<'src>>,
    pub expr: Box<Expr<'src>>,
}

#[derive(Debug, Clone)]
pub struct ExprUnary<'src> {
    pub token: Option<Token<'src>>,
    pub op: UnOp,
    pub rhs: Box<Expr<'src>>,
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

#[derive(Debug, Clone)]
pub struct Pat<'src> {
    pub id: PatId,
    pub location: Location,
    pub kind: PatKind<'src>,
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

#[derive(Debug, Clone)]
pub struct PatVariant<'src> {
    pub label: Name<'src>,
    pub pat: Option<Box<Pat<'src>>>,
}

#[derive(Debug, Clone)]
pub struct PatCons<'src> {
    pub cons: Cons,
    pub args: Vec<Pat<'src>>,
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

#[derive(Debug, Clone)]
pub struct PatRecord<'src> {
    pub fields: Vec<PatRecordField<'src>>,
}

#[derive(Debug, Clone)]
pub struct PatRecordField<'src> {
    pub name: Name<'src>,
    pub pat: Pat<'src>,
}

#[derive(Debug, Clone)]
pub struct PatList<'src> {
    pub elems: Vec<Pat<'src>>,
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

#[derive(Debug, Clone)]
pub struct PatCast<'src> {
    pub pat: Box<Pat<'src>>,
    pub ty_expr: TyExpr<'src>,
}
