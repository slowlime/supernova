use std::borrow::Cow;

use fxhash::FxHashMap;
use strum::VariantArray;
use thiserror::Error;

use crate::ast;
use crate::diag::{Diagnostic, IntoDiagnostic, Label, code};
use crate::location::{ConvexHull, Location, Span};
use crate::util::{format_iter, format_list};

use super::token::Symbol;
use super::{Lexer, LexerError, Token, TokenKind, TokenValue};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParserError<'src> {
    #[error(
        "unexpected token {}, expected {}",
        token.value,
        format_list(expected, "or", "nothing"),
    )]
    UnexpectedToken {
        token: Token<'src>,
        expected: Vec<Cow<'static, str>>,
    },

    #[error("unknown language `{language}`")]
    UnknownLanguage { span: Span, language: String },

    #[error("unknown extension `{extension}`")]
    UnknownExtension { span: Span, extension: String },

    #[error("duplicate annotation")]
    DuplicateAnnotation { span: Span, prev_span: Span },

    #[error("the tuple index is too large")]
    TupleIndexTooLarge { span: Span },

    #[error(transparent)]
    LexerError(#[from] LexerError),
}

impl IntoDiagnostic for ParserError<'_> {
    fn into_diagnostic(self) -> Diagnostic {
        match self {
            Self::UnexpectedToken {
                ref token,
                ref expected,
            } => Diagnostic::error()
                .at(token.span)
                .with_msg(format!("unexpected token {}", token.value))
                .with_code(code!(parser::unexpected_token))
                .with_label(Label::primary(token.span))
                .with_note(format!(
                    "expected {}",
                    format_list(expected, "or", "nothing")
                ))
                .make(),

            Self::UnknownLanguage { span, language: _ } => Diagnostic::error()
                .at(span)
                .with_msg(&self)
                .with_code(code!(parser::unknown_language))
                .with_label(Label::primary(span))
                .with_note("the only supported language is `core`")
                .make(),

            Self::UnknownExtension { span, extension: _ } => Diagnostic::error()
                .at(span)
                .with_msg(&self)
                .with_code(code!(parser::unknown_extension))
                .with_label(Label::primary(span))
                .with_note(format!(
                    "supported extensions are {}",
                    format_iter(
                        ast::Extension::VARIANTS.iter().map(|ext| format!("#{ext}")),
                        "and",
                        "none",
                    )
                ))
                .make(),

            Self::DuplicateAnnotation { span, prev_span } => Diagnostic::error()
                .at(span)
                .with_msg(&self)
                .with_code(code!(parser::duplicate_annotation))
                .with_label(Label::primary(span))
                .with_label(
                    Label::secondary(prev_span)
                        .with_msg("the previous such annotation was provided here"),
                )
                .make(),

            Self::TupleIndexTooLarge { span } => Diagnostic::error()
                .at(span)
                .with_msg(&self)
                .with_code(code!(parser::tuple_index_too_large))
                .with_label(Label::primary(span))
                .make(),

            Self::LexerError(e) => e.into_diagnostic(),
        }
    }
}

trait Matcher {
    fn matches(&self, token: &Token<'_>) -> bool;
}

trait Expected {
    fn expected(&self) -> Vec<Cow<'static, str>>;
}

impl<const N: usize> Matcher for [TokenKind; N] {
    fn matches(&self, token: &Token<'_>) -> bool {
        self.contains(&token.kind())
    }
}

impl<const N: usize> Expected for [TokenKind; N] {
    fn expected(&self) -> Vec<Cow<'static, str>> {
        self.iter().map(|kind| format!("{kind}").into()).collect()
    }
}

impl<const N: usize> Matcher for [Symbol; N] {
    fn matches(&self, token: &Token<'_>) -> bool {
        match token.kind() {
            TokenKind::Symbol(sym) => self.contains(&sym),
            _ => false,
        }
    }
}

impl<const N: usize> Expected for [Symbol; N] {
    fn expected(&self) -> Vec<Cow<'static, str>> {
        self.iter().map(|sym| format!("{sym}").into()).collect()
    }
}

impl Matcher for TokenKind {
    fn matches(&self, token: &Token<'_>) -> bool {
        self == &token.kind()
    }
}

impl Expected for TokenKind {
    fn expected(&self) -> Vec<Cow<'static, str>> {
        vec![format!("{self}").into()]
    }
}

impl Matcher for Symbol {
    fn matches(&self, token: &Token<'_>) -> bool {
        match token.value {
            TokenValue::Symbol(sym) => *self == sym,
            _ => false,
        }
    }
}

impl Expected for Symbol {
    fn expected(&self) -> Vec<Cow<'static, str>> {
        vec![format!("{self}").into()]
    }
}

impl<T: Matcher> Matcher for &'_ T {
    fn matches(&self, token: &Token<'_>) -> bool {
        T::matches(self, token)
    }
}

impl<T: Expected> Expected for &'_ T {
    fn expected(&self) -> Vec<Cow<'static, str>> {
        T::expected(self)
    }
}

trait IntoExpected {
    fn into_expected(self) -> Vec<Cow<'static, str>>;
}

impl IntoExpected for Vec<Cow<'static, str>> {
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        self
    }
}

impl IntoExpected for Vec<&'static str> {
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        self.into_iter().map(Into::into).collect()
    }
}

impl IntoExpected for Cow<'static, str> {
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        vec![self]
    }
}

impl IntoExpected for &'static str {
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        vec![self.into()]
    }
}

impl<const N: usize, T: IntoExpected> IntoExpected for [T; N] {
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        self.into_iter()
            .flat_map(IntoExpected::into_expected)
            .collect()
    }
}

impl<F, T> IntoExpected for F
where
    F: FnOnce() -> T,
    T: IntoExpected,
{
    fn into_expected(self) -> Vec<Cow<'static, str>> {
        self().into_expected()
    }
}

trait ParseResultFamily {
    type R<'src>;
}

struct TyExprFamily;

impl ParseResultFamily for TyExprFamily {
    type R<'src> = ast::TyExpr<'src>;
}

struct ExprFamily;

impl ParseResultFamily for ExprFamily {
    type R<'src> = ast::Expr<'src>;
}

struct PatFamily;

impl ParseResultFamily for PatFamily {
    type R<'src> = ast::Pat<'src>;
}

#[allow(
    clippy::type_complexity,
    reason = "there's no point in factoring out the internal details"
)]
struct PrecTable<F: ParseResultFamily> {
    prefix: FxHashMap<
        TokenKind,
        (
            (),
            u8,
            for<'src> fn(&mut Parser<'src>, u8) -> Result<F::R<'src>, ParserError<'src>>,
        ),
    >,

    infix: FxHashMap<
        TokenKind,
        (
            u8,
            u8,
            for<'src> fn(
                &mut Parser<'src>,
                u8,
                F::R<'src>,
            ) -> Result<F::R<'src>, ParserError<'src>>,
        ),
    >,

    postfix: FxHashMap<
        TokenKind,
        (
            u8,
            (),
            for<'src> fn(
                &mut Parser<'src>,
                u8,
                F::R<'src>,
            ) -> Result<F::R<'src>, ParserError<'src>>,
        ),
    >,
}

impl<F: ParseResultFamily> Default for PrecTable<F> {
    fn default() -> Self {
        Self {
            prefix: Default::default(),
            infix: Default::default(),
            postfix: Default::default(),
        }
    }
}

macro_rules! prec_table {
    {
        static $name:ident<$family:ty> = {
            $(
                $($kind:ident)+ {
                    $($matcher:expr => $fn:expr),+ $(,)?
                }
            ),+ $(,)?
        } ;
    } => {
        static $name: ::std::sync::LazyLock<PrecTable<$family>> = ::std::sync::LazyLock::new(|| {
            let mut result = PrecTable::<$family>::default();
            let mut prec = 1u8;

            $(
                prec_table!(@entry(result, prec), $($kind)+ {$($matcher => $fn),+});
            )+

            let _ = prec;

            result
        });
    };

    (@entry($result:ident, $prec:ident), prefix {$($matcher:expr => $fn:expr),+}) => {{
        $(
            $result.prefix.insert($matcher.into(), ((), $prec, $fn));
        )+

        $prec += 2u8;
    }};

    (@entry($result:ident, $prec:ident), left infix {$($matcher:expr => $fn:expr),+}) => {{
        $(
            $result.infix.insert($matcher.into(), ($prec, $prec + 1, $fn));
        )+

        $prec += 2u8;
    }};

    (@entry($result:ident, $prec:ident), none infix {$($matcher:expr => $fn:expr),+}) => {{
        $(
            $result.infix.insert($matcher.into(), ($prec + 1, $prec + 1, $fn));
        )+

        $prec += 2u8;
    }};

    (@entry($result:ident, $prec:ident), right infix {$($matcher:expr => $fn:expr),+}) => {{
        $(
            $result.infix.insert($matcher.into(), ($prec + 1, $prec, $fn));
        )+

        $prec += 2u8;
    }};

    (@entry($result:ident, $prec:ident), postfix {$($matcher:expr => $fn:expr),+}) => {{
        $(
            $result.postfix.insert($matcher.into(), ($prec, (), $fn));
        )+

        $prec += 2u8;
    }};
}

prec_table! {
    static TY_EXPR_PREC_TABLE<TyExprFamily> = {
        prefix {
            Symbol::Auto => |parser, prec| parser.parse_ty_expr_auto(prec),
            Symbol::Fn => |parser, prec| parser.parse_ty_expr_fn(prec),
            Symbol::Forall => |parser, prec| parser.parse_ty_expr_forall(prec),
            Symbol::Mu => |parser, prec| parser.parse_ty_expr_mu(prec),
        },

        none infix {
            Symbol::Plus => |parser, prec, lhs| parser.parse_ty_expr_sum(prec, lhs),
        },

        prefix {
            Symbol::LBrace => |parser, prec| parser.parse_ty_expr_tuple_or_record(prec),
            Symbol::LTriangle => |parser, prec| parser.parse_ty_expr_variant(prec),
            Symbol::LBracket => |parser, prec| parser.parse_ty_expr_list(prec),
            Symbol::BoolTy => |parser, prec| parser.parse_ty_expr_bool(prec),
            Symbol::NatTy => |parser, prec| parser.parse_ty_expr_nat(prec),
            Symbol::UnitTy => |parser, prec| parser.parse_ty_expr_unit(prec),
            Symbol::TopTy => |parser, prec| parser.parse_ty_expr_top(prec),
            Symbol::BotTy => |parser, prec| parser.parse_ty_expr_bot(prec),
            Symbol::Amp => |parser, prec| parser.parse_ty_expr_ref(prec),
            TokenKind::Ident => |parser, prec| parser.parse_ty_expr_name(prec),

            Symbol::LParen => |parser, _prec| {
                parser.expect(Symbol::LParen)?;
                let ty_expr = parser.parse_ty_expr_impl(0)?;
                parser.expect(Symbol::RParen)?;

                Ok(ty_expr)
            },
        },
    };
}

prec_table! {
    static EXPR_PREC_TABLE<ExprFamily> = {
        prefix {
            Symbol::Let => |parser, prec| parser.parse_expr_let(prec),
            Symbol::LetRec => |parser, prec| parser.parse_expr_let(prec),
            Symbol::Generic => |parser, prec| parser.parse_expr_generic(prec),

            Symbol::LParen => |parser, _prec| {
                parser.expect(Symbol::LParen)?;
                let expr = parser.parse_expr_impl(0)?;
                parser.expect(Symbol::RParen)?;

                Ok(expr)
            },
        },

        left infix {
            Symbol::Semicolon => |parser, prec, lhs| parser.parse_expr_seq(prec, lhs),
        },

        prefix {
            Symbol::If => |parser, prec| parser.parse_expr_if(prec),
        },

        right infix {
            Symbol::ColonEquals => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
        },

        none infix {
            Symbol::Less => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::LessEquals => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::Greater => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::GreaterEquals => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::EqualsEquals => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::BangEquals => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
        },

        postfix {
            Symbol::As => |parser, prec, lhs| parser.parse_expr_ascription(prec, lhs),
            Symbol::Cast => |parser, prec, lhs| parser.parse_expr_cast(prec, lhs),
        },

        prefix {
            Symbol::Fn => |parser, prec| parser.parse_expr_fn(prec),
            Symbol::LTriangle => |parser, prec| parser.parse_expr_variant(prec),
            Symbol::Match => |parser, prec| parser.parse_expr_match(prec),
            Symbol::LBracket => |parser, prec| parser.parse_expr_list(prec),
        },

        left infix {
            Symbol::Plus => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::Minus => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::Or => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
        },

        left infix {
            Symbol::Star => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::Slash => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
            Symbol::And => |parser, prec, lhs| parser.parse_expr_binary(prec, lhs),
        },

        prefix {
            Symbol::New => |parser, prec| parser.parse_expr_unary(prec),
            Symbol::Star => |parser, prec| parser.parse_expr_unary(prec),
        },

        postfix {
            Symbol::LParen => |parser, prec, lhs| parser.parse_expr_apply(prec, Some(lhs)),
            Symbol::LBracket => |parser, prec, lhs| parser.parse_expr_ty_apply(prec, lhs),
            Symbol::Dot => |parser, prec, lhs| parser.parse_expr_field(prec, lhs),
        },

        prefix {
            Symbol::LBrace => |parser, prec| parser.parse_expr_tuple_or_record(prec),
            Symbol::Cons => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::ListHead => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::ListIsEmpty => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::ListTail => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::PanicBang => |parser, prec| parser.parse_expr_panic(prec),
            Symbol::Throw => |parser, prec| parser.parse_expr_throw(prec),
            Symbol::Try => |parser, prec| parser.parse_expr_try(prec),
            Symbol::Inl => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::Inr => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::Succ => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::Not => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::NatPred => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::NatIsZero => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::Fix => |parser, prec| parser.parse_expr_fix(prec),
            Symbol::NatRec => |parser, prec| parser.parse_expr_apply(prec, None),
            Symbol::Fold => |parser, prec| parser.parse_expr_fold(prec),
            Symbol::Unfold => |parser, prec| parser.parse_expr_unfold(prec),
        },

        prefix {
            Symbol::True => |parser, prec| parser.parse_expr_bool(prec),
            Symbol::False => |parser, prec| parser.parse_expr_bool(prec),
            Symbol::Unit => |parser, prec| parser.parse_expr_unit(prec),
            TokenKind::Int => |parser, prec| parser.parse_expr_int(prec),
            TokenKind::Address => |parser, prec| parser.parse_expr_address(prec),
            TokenKind::Ident => |parser, prec| parser.parse_expr_name(prec),
        },
    };
}

fn primary_ty_expr_prec() -> u8 {
    TY_EXPR_PREC_TABLE
        .prefix
        .get(&TokenKind::Symbol(Symbol::LBrace))
        .unwrap()
        .1
}

fn rel_expr_prec() -> u8 {
    EXPR_PREC_TABLE
        .infix
        .get(&TokenKind::Symbol(Symbol::Less))
        .unwrap()
        .1
}

pub struct Parser<'src> {
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(lexer: Lexer<'src>) -> Self {
        Self { lexer }
    }

    fn consume(&mut self, matcher: impl Matcher) -> Result<Option<Token<'src>>, ParserError<'src>> {
        match self.lexer.peek().unwrap() {
            Ok(token) if matcher.matches(token) => Ok(Some(self.lexer.next().unwrap().unwrap())),
            Ok(_) => Ok(None),
            Err(_) => Err(self.lexer.next().unwrap().unwrap_err().into()),
        }
    }

    fn at(&mut self, matcher: impl Matcher) -> bool {
        match self.lexer.peek().unwrap() {
            Ok(token) => matcher.matches(token),
            _ => false,
        }
    }

    fn lookahead(&mut self, n: usize, matcher: impl Matcher) -> bool {
        match self.lexer.peek_nth(n).unwrap() {
            Ok(token) => matcher.matches(token),
            _ => false,
        }
    }

    fn expect_with_message(
        &mut self,
        matcher: impl Matcher,
        expected: impl IntoExpected,
    ) -> Result<Token<'src>, ParserError<'src>> {
        match self.lexer.peek().unwrap() {
            Ok(token) if matcher.matches(token) => Ok(self.lexer.next().unwrap().unwrap()),
            Ok(token) => Err(ParserError::UnexpectedToken {
                token: token.clone(),
                expected: expected.into_expected(),
            }),
            Err(_) => Err(self.lexer.next().unwrap().unwrap_err().into()),
        }
    }

    fn expect(
        &mut self,
        matcher: impl Matcher + Expected,
    ) -> Result<Token<'src>, ParserError<'src>> {
        match self.lexer.peek().unwrap() {
            Ok(token) if matcher.matches(token) => Ok(self.lexer.next().unwrap().unwrap()),
            Ok(token) => Err(ParserError::UnexpectedToken {
                token: token.clone(),
                expected: matcher.expected(),
            }),
            Err(_) => Err(self.lexer.next().unwrap().unwrap_err().into()),
        }
    }

    fn parse_pratt_prec<F: ParseResultFamily>(
        &mut self,
        table: &PrecTable<F>,
        prec: u8,
        expected: impl IntoExpected,
    ) -> Result<F::R<'src>, ParserError<'src>> {
        let mut lhs = match self.lexer.peek().unwrap() {
            Ok(token) => match table.prefix.get(&token.kind()) {
                Some(&((), rhs_prec, parse)) => parse(self, rhs_prec)?,

                None => {
                    return Err(ParserError::UnexpectedToken {
                        token: self.lexer.peek().unwrap().clone().unwrap(),
                        expected: expected.into_expected(),
                    });
                }
            },

            Err(_) => return Err(self.lexer.next().unwrap().unwrap_err().into()),
        };

        loop {
            match self.lexer.peek().unwrap() {
                Ok(token) => {
                    if let Some(&(lhs_prec, (), parse)) = table.postfix.get(&token.kind()) {
                        if lhs_prec < prec {
                            break;
                        }

                        lhs = parse(self, lhs_prec, lhs)?;
                    } else if let Some(&(lhs_prec, rhs_prec, parse)) =
                        table.infix.get(&token.kind())
                    {
                        if lhs_prec < prec {
                            break;
                        }

                        lhs = parse(self, rhs_prec, lhs)?;
                    } else {
                        break;
                    }
                }

                Err(_) => return Err(self.lexer.next().unwrap().unwrap_err().into()),
            }
        }

        Ok(lhs)
    }

    pub fn parse(mut self) -> Result<ast::Program<'src>, ParserError<'src>> {
        let start = self.lexer.pos();
        self.parse_language()?;
        let extensions = self.parse_extensions()?;
        let decls = self.parse_decls()?;

        self.expect(TokenKind::Eof)?;

        Ok(ast::Program {
            location: (self.lexer.source_id(), start..self.lexer.pos()).into(),
            extensions,
            decls,
        })
    }

    fn parse_language(&mut self) -> Result<(), ParserError<'src>> {
        self.expect_with_message(Symbol::Language, "a language declaration")?;
        let name = self.expect_with_message(TokenKind::Ident, "a language name")?;
        self.expect(Symbol::Semicolon)?;
        let language = name.value.as_ident().unwrap();

        if language != "core" {
            return Err(ParserError::UnknownLanguage {
                span: name.span,
                language: language.to_owned(),
            });
        }

        Ok(())
    }

    fn parse_extensions(&mut self) -> Result<Vec<(ast::Extension, Location)>, ParserError<'src>> {
        let mut result = vec![];

        while self.consume(Symbol::Extend)?.is_some() {
            self.expect(Symbol::With)?;

            loop {
                let extension = self.expect(TokenKind::Extension)?;
                let name = extension.value.as_extension().unwrap();

                match name.parse::<ast::Extension>() {
                    Ok(ext) => result.push((ext, extension.span.into())),

                    Err(_) => {
                        return Err(ParserError::UnknownExtension {
                            span: extension.span,
                            extension: name.to_owned(),
                        });
                    }
                }

                if self
                    .consume([Symbol::Comma, Symbol::Semicolon])?
                    .is_some_and(|token| token.value.as_symbol().unwrap() == Symbol::Semicolon)
                {
                    break;
                }
            }
        }

        Ok(result)
    }

    fn parse_decls(&mut self) -> Result<Vec<ast::Decl<'src>>, ParserError<'src>> {
        let mut result = vec![];

        while let Some(decl) = self.parse_decl()? {
            result.push(decl);
        }

        Ok(result)
    }

    fn parse_decl(&mut self) -> Result<Option<ast::Decl<'src>>, ParserError<'src>> {
        if let Some(annotations) = self.parse_annotations()? {
            return Ok(Some(self.parse_decl_fn(annotations)?));
        }

        if self.at(Symbol::Generic) || self.at(Symbol::Fn) {
            return Ok(Some(self.parse_decl_fn(vec![])?));
        }

        if self.at(Symbol::Type) {
            return Ok(Some(self.parse_decl_type_alias()?));
        }

        if self.at(Symbol::Exception) {
            return Ok(Some(self.parse_decl_exception_type_or_variant()?));
        }

        Ok(None)
    }

    fn parse_annotations(&mut self) -> Result<Option<Vec<ast::Annotation>>, ParserError<'src>> {
        let mut dedup = FxHashMap::default();
        let mut result = vec![];

        #[allow(clippy::while_let_loop)]
        loop {
            let (annotation, span) = if let Some(token) = self.consume(Symbol::Inline)? {
                (ast::AnnotationKind::Inline, token.span)
            } else {
                break;
            };

            if let Some(prev_span) = dedup.insert(annotation, span) {
                return Err(ParserError::DuplicateAnnotation { span, prev_span });
            }

            result.push(ast::Annotation {
                location: span.into(),
                kind: annotation,
            });
        }

        if result.is_empty() {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }

    fn parse_decl_fn(
        &mut self,
        annotations: Vec<ast::Annotation>,
    ) -> Result<ast::Decl<'src>, ParserError<'src>> {
        let generic_kw = self.consume(Symbol::Generic)?;
        let fn_kw = self.expect_with_message(Symbol::Fn, "a function declaration")?;
        let binding = ast::Binding {
            id: Default::default(),
            name: self.parse_name("a function name")?,
        };

        let mut generics = vec![];

        if generic_kw.is_some() {
            self.expect_with_message(Symbol::LBracket, "a generic parameter list")?;

            loop {
                generics.push(ast::Binding {
                    id: Default::default(),
                    name: self.parse_name("a generic parameter")?,
                });

                if Symbol::RBracket.matches(&self.expect([Symbol::RBracket, Symbol::Comma])?) {
                    break;
                }
            }
        }

        let mut params = vec![];
        self.expect_with_message(Symbol::LParen, "a parameter list")?;

        if self.consume(Symbol::RParen)?.is_none() {
            loop {
                if params.is_empty() && self.consume(Symbol::RParen)?.is_some() {
                    break;
                }

                let binding = ast::Binding {
                    id: Default::default(),
                    name: self.parse_name("a parameter")?,
                };
                self.expect(Symbol::Colon)?;
                let ty_expr = self.parse_ty_expr()?;

                params.push(ast::Param { binding, ty_expr });

                if Symbol::RParen.matches(&self.expect([Symbol::RParen, Symbol::Comma])?) {
                    break;
                }
            }
        }

        let ret_token = self.consume(Symbol::Arrow)?;
        let ret = if ret_token.is_some() {
            Some(self.parse_ty_expr()?)
        } else {
            None
        };

        let throws_kw = self.consume(Symbol::Throws)?;
        let mut throws = vec![];

        if throws_kw.is_some() {
            loop {
                throws.push(self.parse_ty_expr()?);

                if self.consume(Symbol::Comma)?.is_none() {
                    break;
                }
            }
        }

        self.expect_with_message(Symbol::LBrace, "a function body")?;
        let decls = self.parse_decls()?;
        let body = self.parse_fn_body()?;
        let end = self.expect(Symbol::RBrace)?;

        let start = annotations
            .iter()
            .flat_map(|annotation| annotation.location.span())
            .chain(generic_kw.as_ref().map(|token| token.span))
            .next()
            .unwrap_or(fn_kw.span);
        let span = start.convex_hull(&end.span);

        Ok(ast::Decl {
            id: Default::default(),
            location: span.into(),
            kind: ast::DeclFn {
                annotations,
                generic_kw,
                fn_kw: Some(fn_kw),
                binding,
                generics,
                params,
                ret_token,
                ret,
                throws_kw,
                throws,
                decls,
                body,
            }
            .into(),
        })
    }

    fn parse_decl_type_alias(&mut self) -> Result<ast::Decl<'src>, ParserError<'src>> {
        let type_kw = self.consume(Symbol::Type)?.unwrap();
        let binding = ast::Binding {
            id: Default::default(),
            name: self.parse_name("a type alias name")?,
        };
        let eq_token = self.expect(Symbol::Equals)?;
        let ty_expr = self.parse_ty_expr()?;

        Ok(ast::Decl {
            id: Default::default(),
            location: type_kw.span.convex_hull(&ty_expr.location),
            kind: ast::DeclTypeAlias {
                type_kw: Some(type_kw),
                binding,
                eq_token: Some(eq_token),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_decl_exception_type_or_variant(
        &mut self,
    ) -> Result<ast::Decl<'src>, ParserError<'src>> {
        let exception_kw = self.consume(Symbol::Exception)?.unwrap();

        match self
            .expect([Symbol::Type, Symbol::Variant])?
            .value
            .as_symbol()
            .unwrap()
        {
            Symbol::Type => self.parse_decl_exception_type(exception_kw),
            Symbol::Variant => self.parse_decl_exception_variant(exception_kw),
            _ => unreachable!(),
        }
    }

    fn parse_decl_exception_type(
        &mut self,
        exception_kw: Token<'src>,
    ) -> Result<ast::Decl<'src>, ParserError<'src>> {
        self.expect(Symbol::Equals)?;
        let ty_expr = self.parse_ty_expr()?;

        Ok(ast::Decl {
            id: Default::default(),
            location: exception_kw.span.convex_hull(&ty_expr.location),
            kind: ast::DeclExceptionType {
                exception_kw: Some(exception_kw),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_decl_exception_variant(
        &mut self,
        exception_kw: Token<'src>,
    ) -> Result<ast::Decl<'src>, ParserError<'src>> {
        let name = self.parse_name("an exception variant name")?;
        self.expect(Symbol::Comma)?;
        let variant_ty_expr = self.parse_ty_expr()?;

        Ok(ast::Decl {
            id: Default::default(),
            location: exception_kw.span.convex_hull(&variant_ty_expr.location),
            kind: ast::DeclExceptionVariant {
                exception_kw: Some(exception_kw),
                name,
                variant_ty_expr,
            }
            .into(),
        })
    }

    fn parse_name(
        &mut self,
        expected: impl IntoExpected,
    ) -> Result<ast::Name<'src>, ParserError<'src>> {
        self.expect_with_message(TokenKind::Ident, expected)
            .map(ast::Name::Token)
    }

    fn parse_fn_body(&mut self) -> Result<ast::Body<'src>, ParserError<'src>> {
        let ret_kw = self.expect(Symbol::Return)?;
        let ret = self.parse_expr()?;

        Ok(ast::Body {
            ret_kw: Some(ret_kw),
            ret,
        })
    }

    fn parse_ty_expr(&mut self) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        self.parse_ty_expr_impl(0)
    }

    fn parse_ty_expr_impl(&mut self, prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        self.parse_pratt_prec(&TY_EXPR_PREC_TABLE, prec, "a type expression")
    }

    fn parse_ty_expr_bool(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let kw = self.expect(Symbol::BoolTy)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: kw.span.into(),
            kind: ast::TyExprBool.into(),
        })
    }

    fn parse_ty_expr_nat(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let kw = self.expect(Symbol::NatTy)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: kw.span.into(),
            kind: ast::TyExprNat.into(),
        })
    }

    fn parse_ty_expr_ref(&mut self, prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let ref_token = self.expect(Symbol::Amp)?;
        let ty_expr = self.parse_ty_expr_impl(prec)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: ref_token.span.convex_hull(&ty_expr.location),
            kind: ast::TyExprRef {
                ref_token: Some(ref_token),
                ty_expr: Box::new(ty_expr),
            }
            .into(),
        })
    }

    fn parse_ty_expr_sum(
        &mut self,
        prec: u8,
        lhs: ast::TyExpr<'src>,
    ) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let plus_token = self.expect(Symbol::Plus)?;
        let rhs = self.parse_ty_expr_impl(prec)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: lhs.location.convex_hull(&rhs.location),
            kind: ast::TyExprSum {
                lhs: Box::new(lhs),
                plus_token: Some(plus_token),
                rhs: Box::new(rhs),
            }
            .into(),
        })
    }

    fn parse_ty_expr_fn(&mut self, prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let fn_kw = self.expect(Symbol::Fn)?;

        let mut params = vec![];
        self.expect(Symbol::LParen)?;

        if self.consume(Symbol::RParen)?.is_none() {
            loop {
                params.push(self.parse_ty_expr_impl(0)?);

                if Symbol::RParen.matches(&self.expect([Symbol::RParen, Symbol::Comma])?) {
                    break;
                }
            }
        }

        self.expect(Symbol::Arrow)?;
        let ret = self.parse_ty_expr_impl(prec)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: fn_kw.span.convex_hull(&ret.location),
            kind: ast::TyExprFn {
                fn_kw: Some(fn_kw),
                params,
                ret: Box::new(ret),
            }
            .into(),
        })
    }

    fn parse_ty_expr_forall(&mut self, prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let forall_kw = self.expect(Symbol::Forall)?;
        let mut bindings = vec![];

        while self.consume(Symbol::Dot)?.is_none() {
            bindings.push(ast::Binding {
                id: Default::default(),
                name: self.parse_name(|| {
                    [
                        Cow::from("a type variable name"),
                        Cow::from(Symbol::Dot.to_string()),
                    ]
                })?,
            });
        }

        let ty_expr = self.parse_ty_expr_impl(prec)?;
        let location = forall_kw.span.convex_hull(&ty_expr.location);

        Ok(bindings
            .into_iter()
            .enumerate()
            .rfold(ty_expr, |ty_expr, (idx, binding)| ast::TyExpr {
                id: Default::default(),
                location,
                kind: ast::TyExprForAll {
                    forall_location: forall_kw.span.into(),
                    synthetic: idx != 0,
                    binding,
                    ty_expr: Box::new(ty_expr),
                }
                .into(),
            }))
    }

    fn parse_ty_expr_mu(&mut self, prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let mu_kw = self.expect(Symbol::Mu)?;
        let binding = ast::Binding {
            id: Default::default(),
            name: self.parse_name("a type variable name")?,
        };
        self.expect(Symbol::Dot)?;
        let ty_expr = self.parse_ty_expr_impl(prec)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: mu_kw.span.convex_hull(&ty_expr.location),
            kind: ast::TyExprMu {
                mu_kw: Some(mu_kw),
                binding,
                ty_expr: Box::new(ty_expr),
            }
            .into(),
        })
    }

    fn parse_ty_expr_tuple_or_record(
        &mut self,
        _prec: u8,
    ) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let lbrace = self.expect(Symbol::LBrace)?;

        if self.at(TokenKind::Ident) && self.lookahead(1, Symbol::Colon) {
            self.parse_ty_expr_record(lbrace)
        } else {
            self.parse_ty_expr_tuple(lbrace)
        }
    }

    fn parse_ty_expr_tuple(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let mut elems = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                elems.push(self.parse_ty_expr_impl(0)?);

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::TyExpr {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            kind: ast::TyExprTuple { elems }.into(),
        })
    }

    fn parse_ty_expr_record(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let mut fields = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                let name = self.parse_name("a record field name")?;
                self.expect(Symbol::Colon)?;
                let ty_expr = self.parse_ty_expr_impl(0)?;
                fields.push(ast::TyExprRecordField { name, ty_expr });

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::TyExpr {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            kind: ast::TyExprRecord { fields }.into(),
        })
    }

    fn parse_ty_expr_variant(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let ltriangle = self.expect(Symbol::LTriangle)?;
        let mut fields = vec![];

        let rtriangle = if let Some(token) = self.consume(Symbol::RTriangle)? {
            token
        } else {
            loop {
                let name = self.parse_name("a variant name")?;

                let ty_expr = if self.consume(Symbol::Colon)?.is_some() {
                    Some(self.parse_ty_expr_impl(0)?)
                } else {
                    None
                };

                fields.push(ast::TyExprVariantField { name, ty_expr });

                let token = self.expect([Symbol::Comma, Symbol::RTriangle])?;

                if Symbol::RTriangle.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::TyExpr {
            id: Default::default(),
            location: ltriangle.span.convex_hull(&rtriangle.span).into(),
            kind: ast::TyExprVariant { fields }.into(),
        })
    }

    fn parse_ty_expr_list(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let lbracket = self.expect(Symbol::LBracket)?;
        let ty_expr = self.parse_ty_expr_impl(0)?;
        let rbracket = self.expect(Symbol::RBracket)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: lbracket.span.convex_hull(&rbracket.span).into(),
            kind: ast::TyExprList {
                ty_expr: Box::new(ty_expr),
            }
            .into(),
        })
    }

    fn parse_ty_expr_unit(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let unit_kw = self.expect(Symbol::UnitTy)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: unit_kw.span.into(),
            kind: ast::TyExprUnit.into(),
        })
    }

    fn parse_ty_expr_top(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let top_kw = self.expect(Symbol::TopTy)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: top_kw.span.into(),
            kind: ast::TyExprTop.into(),
        })
    }

    fn parse_ty_expr_bot(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let bot_kw = self.expect(Symbol::BotTy)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: bot_kw.span.into(),
            kind: ast::TyExprBot.into(),
        })
    }

    fn parse_ty_expr_auto(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let auto_kw = self.expect(Symbol::Auto)?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: auto_kw.span.into(),
            kind: ast::TyExprAuto.into(),
        })
    }

    fn parse_ty_expr_name(&mut self, _prec: u8) -> Result<ast::TyExpr<'src>, ParserError<'src>> {
        let name = self.parse_name("a type name")?;

        Ok(ast::TyExpr {
            id: Default::default(),
            location: name.location(),
            kind: ast::TyExprName { name }.into(),
        })
    }

    fn parse_expr(&mut self) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.parse_expr_impl(0)
    }

    fn parse_expr_impl(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.parse_pratt_prec(&EXPR_PREC_TABLE, prec, "an expression")
    }

    fn parse_expr_bool(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect([Symbol::True, Symbol::False])?;
        let value = Symbol::True.matches(&token);

        Ok(ast::Expr {
            id: Default::default(),
            location: token.span.into(),
            kind: ast::ExprBool { value }.into(),
        })
    }

    fn parse_expr_unit(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect(Symbol::Unit)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: token.span.into(),
            kind: ast::ExprUnit.into(),
        })
    }

    fn parse_expr_int(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect(TokenKind::Int)?;
        let value = token.value.into_int().unwrap();

        Ok(ast::Expr {
            id: Default::default(),
            location: token.span.into(),
            kind: ast::ExprInt { value }.into(),
        })
    }

    fn parse_expr_address(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect(TokenKind::Address)?;
        let value = token.value.into_address().unwrap();

        Ok(ast::Expr {
            id: Default::default(),
            location: token.span.into(),
            kind: ast::ExprAddress { value }.into(),
        })
    }

    fn parse_expr_name(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let name = self.parse_name("a variable name")?;

        Ok(ast::Expr {
            id: Default::default(),
            location: name.location(),
            kind: ast::ExprName { name }.into(),
        })
    }

    fn parse_expr_field(
        &mut self,
        _prec: u8,
        base: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.expect(Symbol::Dot)?;

        let field_location;
        let field = if self.at(TokenKind::Ident) {
            let name = self.parse_name("a field name")?;
            field_location = name.location();

            ast::ExprFieldName::Name(name)
        } else {
            let token = self.expect_with_message(TokenKind::Int, ["a field name", "an index"])?;
            let index = token
                .value
                .into_int()
                .unwrap()
                .try_into()
                .map_err(|_| ParserError::TupleIndexTooLarge { span: token.span })?;
            field_location = token.span.into();

            ast::ExprFieldName::Index(field_location, index)
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: base.location.convex_hull(&field_location),
            kind: ast::ExprField {
                base: Box::new(base),
                field,
            }
            .into(),
        })
    }

    fn parse_expr_panic(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let panic_kw = self.expect(Symbol::PanicBang)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: panic_kw.span.into(),
            kind: ast::ExprPanic.into(),
        })
    }

    fn parse_expr_throw(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let throw_kw = self.expect(Symbol::Throw)?;
        self.expect(Symbol::LParen)?;
        let exc = self.parse_expr_impl(0)?;
        let rparen = self.expect(Symbol::RParen)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: throw_kw.span.convex_hull(&rparen.span).into(),
            kind: ast::ExprThrow { exc: Box::new(exc) }.into(),
        })
    }

    fn parse_expr_try(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let try_kw = self.expect(Symbol::Try)?;
        self.expect(Symbol::LBrace)?;
        let try_expr = self.parse_expr_impl(0)?;
        self.expect(Symbol::RBrace)?;

        match self
            .expect([Symbol::Catch, Symbol::Cast, Symbol::With])?
            .value
            .as_symbol()
            .unwrap()
        {
            Symbol::Catch => self.parse_expr_try_catch(try_kw, try_expr),
            Symbol::Cast => self.parse_expr_try_cast(try_kw, try_expr),
            Symbol::With => self.parse_expr_try_with(try_kw, try_expr),
            _ => unreachable!(),
        }
    }

    fn parse_expr_try_catch(
        &mut self,
        try_kw: Token<'src>,
        try_expr: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.expect(Symbol::LBrace)?;
        let arm = self.parse_arm()?;
        let rbrace = self.expect(Symbol::RBrace)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: try_kw.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprTry {
                try_expr: Box::new(try_expr),
                fallback: ast::ExprTryFallback::Catch(Box::new(arm)),
            }
            .into(),
        })
    }

    fn parse_expr_try_cast(
        &mut self,
        try_kw: Token<'src>,
        try_expr: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.expect(Symbol::As)?;
        let ty_expr = self.parse_ty_expr()?;
        self.expect(Symbol::LBrace)?;
        let arm = self.parse_arm()?;
        self.expect(Symbol::RBrace)?;
        self.expect(Symbol::With)?;
        self.expect(Symbol::LBrace)?;
        let fallback = self.parse_expr_impl(0)?;
        let rbrace = self.expect(Symbol::RBrace)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: try_kw.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprTryCast {
                try_expr: Box::new(try_expr),
                ty_expr,
                arm: Box::new(arm),
                fallback: Box::new(fallback),
            }
            .into(),
        })
    }

    fn parse_expr_try_with(
        &mut self,
        try_kw: Token<'src>,
        try_expr: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.expect(Symbol::LBrace)?;
        let fallback = self.parse_expr_impl(0)?;
        let rbrace = self.expect(Symbol::RBrace)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: try_kw.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprTry {
                try_expr: Box::new(try_expr),
                fallback: ast::ExprTryFallback::With(Box::new(fallback)),
            }
            .into(),
        })
    }

    fn parse_expr_fix(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let fix_kw = self.expect(Symbol::Fix)?;
        self.expect(Symbol::LParen)?;
        let expr = self.parse_expr_impl(0)?;
        let rparen = self.expect(Symbol::RParen)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: fix_kw.span.convex_hull(&rparen.span).into(),
            kind: ast::ExprFix {
                fix_kw: Some(fix_kw),
                expr: Box::new(expr),
            }
            .into(),
        })
    }

    fn parse_expr_fold(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let fold_kw = self.expect(Symbol::Fold)?;
        self.expect(Symbol::LBracket)?;
        let ty_expr = self.parse_ty_expr()?;
        self.expect(Symbol::RBracket)?;
        let expr = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: fold_kw.span.convex_hull(&expr.location),
            kind: ast::ExprFold {
                fold_kw: Some(fold_kw),
                ty_expr,
                expr: Box::new(expr),
            }
            .into(),
        })
    }

    fn parse_expr_unfold(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let unfold_kw = self.expect(Symbol::Unfold)?;
        self.expect(Symbol::LBracket)?;
        let ty_expr = self.parse_ty_expr()?;
        self.expect(Symbol::RBracket)?;
        let expr = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: unfold_kw.span.convex_hull(&expr.location),
            kind: ast::ExprUnfold {
                unfold_kw: Some(unfold_kw),
                ty_expr,
                expr: Box::new(expr),
            }
            .into(),
        })
    }

    fn parse_expr_apply(
        &mut self,
        _prec: u8,
        lhs: Option<ast::Expr<'src>>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let callee = match lhs {
            Some(lhs) => ast::Callee::Expr(Box::new(lhs)),

            None => {
                let kw = self.expect_with_message(
                    [
                        Symbol::Inl,
                        Symbol::Inr,
                        Symbol::Cons,
                        Symbol::ListHead,
                        Symbol::ListIsEmpty,
                        Symbol::ListTail,
                        Symbol::Succ,
                        Symbol::Not,
                        Symbol::NatPred,
                        Symbol::NatIsZero,
                        Symbol::NatRec,
                    ],
                    "a built-in function name",
                )?;

                let builtin = match kw.value.as_symbol().unwrap() {
                    Symbol::Inl => ast::Builtin::Inl,
                    Symbol::Inr => ast::Builtin::Inr,
                    Symbol::Cons => ast::Builtin::Cons,
                    Symbol::ListHead => ast::Builtin::ListHead,
                    Symbol::ListIsEmpty => ast::Builtin::ListIsEmpty,
                    Symbol::ListTail => ast::Builtin::ListTail,
                    Symbol::Succ => ast::Builtin::Succ,
                    Symbol::Not => ast::Builtin::Not,
                    Symbol::NatPred => ast::Builtin::NatPred,
                    Symbol::NatIsZero => ast::Builtin::NatIsZero,
                    Symbol::NatRec => ast::Builtin::NatRec,
                    _ => unreachable!(),
                };

                ast::Callee::Builtin {
                    kw: Some(kw),
                    builtin,
                }
            }
        };

        let lparen = self.expect(Symbol::LParen)?;
        let mut args = vec![];

        let rparen = if let Some(rparen) = self.consume(Symbol::RParen)? {
            rparen
        } else {
            loop {
                args.push(self.parse_expr_impl(0)?);
                let token = self.expect([Symbol::Comma, Symbol::RParen])?;

                if Symbol::RParen.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: callee.location().convex_hull(&rparen.span),
            kind: ast::ExprApply {
                callee,
                lparen: Some(lparen),
                args,
                rparen: Some(rparen),
            }
            .into(),
        })
    }

    fn parse_expr_ty_apply(
        &mut self,
        _prec: u8,
        lhs: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        self.expect(Symbol::LBracket)?;

        let mut args = vec![];

        let rbracket = if let Some(rbracket) = self.consume(Symbol::RBracket)? {
            rbracket
        } else {
            loop {
                args.push(self.parse_ty_expr()?);

                let token = self.expect([Symbol::Comma, Symbol::RBracket])?;

                if Symbol::RBracket.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: lhs.location.convex_hull(&rbracket.span),
            kind: ast::ExprTyApply {
                callee: Box::new(lhs),
                args,
            }
            .into(),
        })
    }

    fn parse_expr_ascription(
        &mut self,
        _prec: u8,
        lhs: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let as_kw = self.expect(Symbol::As)?;
        let ty_expr = self.parse_ty_expr_impl(primary_ty_expr_prec())?;

        Ok(ast::Expr {
            id: Default::default(),
            location: lhs.location.convex_hull(&ty_expr.location),
            kind: ast::ExprAscription {
                expr: Box::new(lhs),
                as_kw: Some(as_kw),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_expr_cast(
        &mut self,
        _prec: u8,
        lhs: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let cast_kw = self.expect(Symbol::Cast)?;
        self.expect(Symbol::As)?;
        let ty_expr = self.parse_ty_expr_impl(primary_ty_expr_prec())?;

        Ok(ast::Expr {
            id: Default::default(),
            location: lhs.location.convex_hull(&ty_expr.location),
            kind: ast::ExprCast {
                expr: Box::new(lhs),
                cast_kw: Some(cast_kw),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_expr_fn(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let fn_kw = self.expect(Symbol::Fn)?;
        self.expect(Symbol::LParen)?;

        let mut params = vec![];

        if self.consume(Symbol::RParen)?.is_none() {
            loop {
                let binding = ast::Binding {
                    id: Default::default(),
                    name: self.parse_name("a parameter name")?,
                };
                self.expect(Symbol::Colon)?;
                let ty_expr = self.parse_ty_expr()?;

                params.push(ast::Param { binding, ty_expr });

                if Symbol::RParen.matches(&self.expect([Symbol::Comma, Symbol::RParen])?) {
                    break;
                }
            }
        }

        self.expect(Symbol::LBrace)?;
        let body = self.parse_fn_body()?;
        let rbrace = self.expect(Symbol::RBrace)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: fn_kw.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprFn {
                params,
                body: Box::new(body),
            }
            .into(),
        })
    }

    fn parse_expr_tuple_or_record(
        &mut self,
        _prec: u8,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let lbrace = self.expect(Symbol::LBrace)?;

        if self.at(TokenKind::Ident) && self.lookahead(1, Symbol::Equals) {
            self.parse_expr_record(lbrace)
        } else {
            self.parse_expr_tuple(lbrace)
        }
    }

    fn parse_expr_tuple(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let mut elems = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                elems.push(self.parse_expr_impl(0)?);

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprTuple { elems }.into(),
        })
    }

    fn parse_expr_record(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let mut fields = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                let name = self.parse_name("a record field name")?;
                self.expect(Symbol::Equals)?;
                let expr = self.parse_expr_impl(0)?;
                fields.push(ast::ExprRecordField { name, expr });

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprRecord { fields }.into(),
        })
    }

    fn parse_expr_variant(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let ltriangle = self.expect(Symbol::LTriangle)?;
        let label = self.parse_name("a variant label")?;

        let expr = if self.consume(Symbol::Equals)?.is_some() {
            Some(self.parse_expr_impl(0)?)
        } else {
            None
        };

        let rtriangle = self.expect(Symbol::RTriangle)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: ltriangle.span.convex_hull(&rtriangle.span).into(),
            kind: ast::ExprVariant {
                label,
                expr: expr.map(Box::new),
            }
            .into(),
        })
    }

    fn parse_expr_match(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let match_kw = self.expect(Symbol::Match)?;
        let expr = self.parse_expr_impl(rel_expr_prec())?;
        self.expect(Symbol::LBrace)?;

        let mut arms = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                arms.push(self.parse_arm()?);

                let token = self.expect([Symbol::Pipe, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: match_kw.span.convex_hull(&rbrace.span).into(),
            kind: ast::ExprMatch {
                expr: Box::new(expr),
                arms,
            }
            .into(),
        })
    }

    fn parse_expr_list(&mut self, _prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let lbracket = self.expect(Symbol::LBracket)?;
        let mut elems = vec![];

        let rbracket = if let Some(token) = self.consume(Symbol::RBracket)? {
            token
        } else {
            loop {
                elems.push(self.parse_expr_impl(0)?);

                let token = self.expect([Symbol::Comma, Symbol::RBracket])?;

                if Symbol::RBracket.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Expr {
            id: Default::default(),
            location: lbracket.span.convex_hull(&rbracket.span).into(),
            kind: ast::ExprList { elems }.into(),
        })
    }

    fn parse_expr_if(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let if_kw = self.expect(Symbol::If)?;
        let cond = self.parse_expr_impl(prec)?;
        self.expect(Symbol::Then)?;
        let then_expr = self.parse_expr_impl(prec)?;
        self.expect(Symbol::Else)?;
        let else_expr = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: if_kw.span.convex_hull(&else_expr.location),
            kind: ast::ExprIf {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            }
            .into(),
        })
    }

    fn parse_expr_seq(
        &mut self,
        prec: u8,
        lhs: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let semicolon = self.expect(Symbol::Semicolon)?;
        let mut exprs = vec![(lhs, Some(semicolon))];

        loop {
            if !self
                .lexer
                .peek()
                .unwrap()
                .as_ref()
                .is_ok_and(|token| EXPR_PREC_TABLE.prefix.contains_key(&token.kind()))
            {
                break;
            }

            let expr = self.parse_expr_impl(prec)?;
            let semicolon = self.consume(Symbol::Semicolon)?;
            let is_end = semicolon.is_none();
            exprs.push((expr, semicolon));

            if is_end {
                break;
            }
        }

        if exprs.len() == 1 {
            // we have an expression terminated with `;`.
            // this is not a sequence expression.
            return Ok(exprs.pop().unwrap().0);
        }

        Ok(ast::Expr {
            id: Default::default(),
            location: match exprs.last().unwrap() {
                (_, Some(semicolon)) => exprs
                    .first()
                    .unwrap()
                    .0
                    .location
                    .convex_hull(&semicolon.span),

                (expr, _) => exprs
                    .first()
                    .unwrap()
                    .0
                    .location
                    .convex_hull(&expr.location),
            },
            kind: ast::ExprSeq { exprs }.into(),
        })
    }

    fn parse_expr_let(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let let_kw = self.expect([Symbol::Let, Symbol::LetRec])?;
        let rec = Symbol::LetRec.matches(&let_kw);
        let mut bindings = vec![];

        loop {
            let pat = self.parse_pat()?;
            self.expect(Symbol::Equals)?;
            let expr = self.parse_expr_impl(0)?;
            bindings.push(ast::LetBinding { pat, expr });

            if Symbol::In.matches(&self.expect([Symbol::Comma, Symbol::In])?) {
                break;
            }
        }

        let body = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: let_kw.span.convex_hull(&body.location),
            kind: ast::ExprLet {
                let_kw: Some(let_kw),
                rec,
                bindings,
                body: Box::new(body),
            }
            .into(),
        })
    }

    fn parse_expr_generic(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let generic_kw = self.expect(Symbol::Generic)?;
        self.expect(Symbol::LBracket)?;
        let mut generics = vec![];

        if self.consume(Symbol::RBracket)?.is_none() {
            loop {
                generics.push(ast::Binding {
                    id: Default::default(),
                    name: self.parse_name("a type variable name")?,
                });

                if Symbol::RBracket.matches(&self.expect([Symbol::Comma, Symbol::RBracket])?) {
                    break;
                }
            }
        }

        let expr = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: generic_kw.span.convex_hull(&expr.location),
            kind: ast::ExprGeneric {
                generics,
                expr: Box::new(expr),
            }
            .into(),
        })
    }

    fn parse_expr_unary(&mut self, prec: u8) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect([Symbol::New, Symbol::Star])?;

        let op = match token.value.as_symbol().unwrap() {
            Symbol::New => ast::UnOp::New,
            Symbol::Star => ast::UnOp::Deref,
            _ => unreachable!(),
        };

        let rhs = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: token.span.convex_hull(&rhs.location),
            kind: ast::ExprUnary {
                token: Some(token),
                op,
                rhs: Box::new(rhs),
            }
            .into(),
        })
    }

    fn parse_expr_binary(
        &mut self,
        prec: u8,
        lhs: ast::Expr<'src>,
    ) -> Result<ast::Expr<'src>, ParserError<'src>> {
        let token = self.expect_with_message(
            [
                Symbol::Plus,
                Symbol::Minus,
                Symbol::Star,
                Symbol::Slash,
                Symbol::And,
                Symbol::Or,
                Symbol::Less,
                Symbol::LessEquals,
                Symbol::Greater,
                Symbol::GreaterEquals,
                Symbol::EqualsEquals,
                Symbol::BangEquals,
                Symbol::ColonEquals,
            ],
            "a binary operator",
        )?;

        let op = match token.value.as_symbol().unwrap() {
            Symbol::Plus => ast::BinOp::Add,
            Symbol::Minus => ast::BinOp::Sub,
            Symbol::Star => ast::BinOp::Mul,
            Symbol::Slash => ast::BinOp::Div,
            Symbol::And => ast::BinOp::And,
            Symbol::Or => ast::BinOp::Or,
            Symbol::Less => ast::BinOp::Lt,
            Symbol::LessEquals => ast::BinOp::Le,
            Symbol::Greater => ast::BinOp::Lt,
            Symbol::GreaterEquals => ast::BinOp::Ge,
            Symbol::EqualsEquals => ast::BinOp::Eq,
            Symbol::BangEquals => ast::BinOp::Ne,
            Symbol::ColonEquals => ast::BinOp::Assign,
            _ => unreachable!(),
        };

        let rhs = self.parse_expr_impl(prec)?;

        Ok(ast::Expr {
            id: Default::default(),
            location: lhs.location.convex_hull(&rhs.location),
            kind: ast::ExprBinary {
                lhs: Box::new(lhs),
                token: Some(token),
                op,
                rhs: Box::new(rhs),
            }
            .into(),
        })
    }

    fn parse_arm(&mut self) -> Result<ast::Arm<'src>, ParserError<'src>> {
        let pat = self.parse_pat()?;
        self.expect(Symbol::FatArrow)?;
        let body = self.parse_expr_impl(0)?;

        Ok(ast::Arm { pat, body })
    }

    fn parse_pat(&mut self) -> Result<ast::Pat<'src>, ParserError<'src>> {
        self.parse_pat_impl(0)
    }

    fn parse_pat_impl(&mut self, prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        prec_table! {
            static PAT_PREC_TABLE<PatFamily> = {
                postfix {
                    Symbol::Cast => |parser, prec, lhs| parser.parse_pat_cast(prec, lhs),
                    Symbol::As => |parser, prec, lhs| parser.parse_pat_ascription(prec, lhs),
                },

                prefix {
                    Symbol::LTriangle => |parser, prec| parser.parse_pat_variant(prec),
                    Symbol::Inl => |parser, prec| parser.parse_pat_cons(prec),
                    Symbol::Inr => |parser, prec| parser.parse_pat_cons(prec),
                    Symbol::LBrace => |parser, prec| parser.parse_pat_tuple_or_record(prec),
                    Symbol::LBracket => |parser, prec| parser.parse_pat_list(prec),
                    Symbol::Cons => |parser, prec| parser.parse_pat_cons(prec),
                    Symbol::LParen => |parser, prec| parser.parse_pat_paren(prec),
                    Symbol::False => |parser, prec| parser.parse_pat_bool(prec),
                    Symbol::True => |parser, prec| parser.parse_pat_bool(prec),
                    Symbol::Unit => |parser, prec| parser.parse_pat_unit(prec),
                    TokenKind::Int => |parser, prec| parser.parse_pat_int(prec),
                    Symbol::Succ => |parser, prec| parser.parse_pat_cons(prec),
                    TokenKind::Ident => |parser, prec| parser.parse_pat_name(prec),
                },
            };
        };

        self.parse_pratt_prec(&PAT_PREC_TABLE, prec, "a pattern")
    }

    fn parse_pat_variant(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let ltriangle = self.expect(Symbol::LTriangle)?;
        let label = self.parse_name("a variant label")?;

        let pat = if self.consume(Symbol::Equals)?.is_some() {
            Some(self.parse_pat_impl(0)?.with_nested(true))
        } else {
            None
        };

        let rtriangle = self.expect(Symbol::RTriangle)?;

        Ok(ast::Pat {
            id: Default::default(),
            location: ltriangle.span.convex_hull(&rtriangle.span).into(),
            nested: false,
            kind: ast::PatVariant {
                label,
                pat: pat.map(Box::new),
            }
            .into(),
        })
    }

    fn parse_pat_cons(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let token = self.expect([Symbol::Inl, Symbol::Inr, Symbol::Cons, Symbol::Succ])?;
        let cons = match token.value.as_symbol().unwrap() {
            Symbol::Inl => ast::Cons::Inl,
            Symbol::Inr => ast::Cons::Inr,
            Symbol::Cons => ast::Cons::Cons,
            Symbol::Succ => ast::Cons::Succ,
            _ => unreachable!(),
        };

        self.expect(Symbol::LParen)?;
        let mut args = vec![];

        let rparen = if let Some(token) = self.consume(Symbol::RParen)? {
            token
        } else {
            loop {
                args.push(self.parse_pat_impl(0)?.with_nested(true));

                let token = self.expect([Symbol::Comma, Symbol::RParen])?;

                if Symbol::RParen.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Pat {
            id: Default::default(),
            location: token.span.convex_hull(&rparen.span).into(),
            nested: false,
            kind: ast::PatCons { cons, args }.into(),
        })
    }

    fn parse_pat_tuple_or_record(
        &mut self,
        _prec: u8,
    ) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let lbrace = self.expect(Symbol::LBrace)?;

        if self.at(TokenKind::Ident) && self.lookahead(1, Symbol::Equals) {
            self.parse_pat_record(lbrace)
        } else {
            self.parse_pat_tuple(lbrace)
        }
    }

    fn parse_pat_tuple(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let mut elems = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                elems.push(self.parse_pat_impl(0)?.with_nested(true));

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Pat {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            nested: false,
            kind: ast::PatTuple { elems }.into(),
        })
    }

    fn parse_pat_record(
        &mut self,
        lbrace: Token<'src>,
    ) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let mut fields = vec![];

        let rbrace = if let Some(token) = self.consume(Symbol::RBrace)? {
            token
        } else {
            loop {
                let name = self.parse_name("a record field name")?;
                self.expect(Symbol::Equals)?;
                let pat = self.parse_pat_impl(0)?.with_nested(true);
                fields.push(ast::PatRecordField { name, pat });

                let token = self.expect([Symbol::Comma, Symbol::RBrace])?;

                if Symbol::RBrace.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Pat {
            id: Default::default(),
            location: lbrace.span.convex_hull(&rbrace.span).into(),
            nested: false,
            kind: ast::PatRecord { fields }.into(),
        })
    }

    fn parse_pat_list(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let lbracket = self.expect(Symbol::LBracket)?;
        let mut elems = vec![];

        let rbracket = if let Some(token) = self.consume(Symbol::RBracket)? {
            token
        } else {
            loop {
                elems.push(self.parse_pat_impl(0)?.with_nested(true));

                let token = self.expect([Symbol::Comma, Symbol::RBracket])?;

                if Symbol::RBracket.matches(&token) {
                    break token;
                }
            }
        };

        Ok(ast::Pat {
            id: Default::default(),
            location: lbracket.span.convex_hull(&rbracket.span).into(),
            nested: false,
            kind: ast::PatList { elems }.into(),
        })
    }

    fn parse_pat_bool(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let kw = self.expect([Symbol::True, Symbol::False])?;
        let value = Symbol::True.matches(&kw);

        Ok(ast::Pat {
            id: Default::default(),
            location: kw.span.into(),
            nested: false,
            kind: ast::PatBool { value }.into(),
        })
    }

    fn parse_pat_unit(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let kw = self.expect(Symbol::Unit)?;

        Ok(ast::Pat {
            id: Default::default(),
            location: kw.span.into(),
            nested: false,
            kind: ast::PatUnit.into(),
        })
    }

    fn parse_pat_int(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let token = self.expect(TokenKind::Int)?;
        let span = token.span;
        let value = token.value.into_int().unwrap();

        Ok(ast::Pat {
            id: Default::default(),
            location: span.into(),
            nested: false,
            kind: ast::PatInt { value }.into(),
        })
    }

    fn parse_pat_name(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let binding = ast::Binding {
            id: Default::default(),
            name: self.parse_name("a variable name")?,
        };

        Ok(ast::Pat {
            id: Default::default(),
            location: binding.location(),
            nested: false,
            kind: ast::PatName { binding }.into(),
        })
    }

    fn parse_pat_ascription(
        &mut self,
        _prec: u8,
        pat: ast::Pat<'src>,
    ) -> Result<ast::Pat<'src>, ParserError<'src>> {
        self.expect(Symbol::As)?;
        let ty_expr = self.parse_ty_expr()?;

        Ok(ast::Pat {
            id: Default::default(),
            location: pat.location.convex_hull(&ty_expr.location),
            nested: false,
            kind: ast::PatAscription {
                pat: Box::new(pat),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_pat_cast(
        &mut self,
        _prec: u8,
        pat: ast::Pat<'src>,
    ) -> Result<ast::Pat<'src>, ParserError<'src>> {
        self.expect(Symbol::Cast)?;
        self.expect(Symbol::As)?;
        let ty_expr = self.parse_ty_expr()?;

        Ok(ast::Pat {
            id: Default::default(),
            location: pat.location.convex_hull(&ty_expr.location),
            nested: false,
            kind: ast::PatCast {
                pat: Box::new(pat),
                ty_expr,
            }
            .into(),
        })
    }

    fn parse_pat_paren(&mut self, _prec: u8) -> Result<ast::Pat<'src>, ParserError<'src>> {
        let lparen = self.expect(Symbol::LParen)?;
        let pat = self.parse_pat_impl(0)?;

        if self.consume(Symbol::Comma)?.is_some() {
            let rhs = self.parse_pat_impl(0)?.with_nested(true);
            let rparen = self.expect(Symbol::RParen)?;

            Ok(ast::Pat {
                id: Default::default(),
                location: lparen.span.convex_hull(&rparen.span).into(),
                nested: false,
                kind: ast::PatCons {
                    cons: ast::Cons::Cons,
                    args: vec![pat.with_nested(true), rhs],
                }
                .into(),
            })
        } else {
            self.expect(Symbol::RParen)?;

            Ok(pat)
        }
    }
}
