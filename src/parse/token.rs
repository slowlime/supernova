use std::fmt::{self, Display};

use derive_more::{Display, From};
use num::BigUint;
use phf::phf_map;

use crate::location::Span;
use crate::util::try_match;

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub span: Span,
    pub value: TokenValue<'a>,
}

impl Token<'_> {
    pub fn kind(&self) -> TokenKind {
        self.value.kind()
    }
}

#[derive(Display, Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenValue<'a> {
    #[display("EOF")]
    Eof,

    #[display("{_0}")]
    Symbol(Symbol),

    #[display("`{_0}`")]
    Ident(&'a str),

    #[display("`#{_0}`")]
    Extension(&'a str),

    #[display("`<0x{_0:x}>`")]
    Address(BigUint),

    #[display("`{_0}`")]
    Int(BigUint),
}

impl<'a> TokenValue<'a> {
    pub fn kind(&self) -> TokenKind {
        match self {
            Self::Eof => TokenKind::Eof,
            Self::Symbol(sym) => TokenKind::Symbol(*sym),
            Self::Ident(_) => TokenKind::Ident,
            Self::Extension(_) => TokenKind::Extension,
            Self::Address(_) => TokenKind::Address,
            Self::Int(_) => TokenKind::Int,
        }
    }

    pub fn as_symbol(&self) -> Option<Symbol> {
        try_match!(*self, Self::Symbol(sym) => sym)
    }

    pub fn as_ident(&self) -> Option<&'a str> {
        try_match!(*self, Self::Ident(v) => v)
    }

    pub fn as_extension(&self) -> Option<&'a str> {
        try_match!(*self, Self::Extension(v) => v)
    }

    pub fn into_address(self) -> Option<BigUint> {
        try_match!(self, Self::Address(v) => v)
    }

    pub fn into_int(self) -> Option<BigUint> {
        try_match!(self, Self::Int(v) => v)
    }
}

#[derive(From, Display, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    #[display("EOF")]
    Eof,

    #[display("{_0}")]
    Symbol(Symbol),

    #[display("an identifier")]
    Ident,

    #[display("an extension")]
    Extension,

    #[display("an address")]
    Address,

    #[display("an integer")]
    Int,
}

macro_rules! symbols {
    {
        $(
            $cat:ident {
                $($lit:literal => $variant:ident),+ $(,)?
            }
        )+
    } => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Symbol {
            $($($variant,)+)+
        }

        impl Display for Symbol {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "`{}`", self.to_str())
            }
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum SymbolCategory {
            $($cat,)+
        }

        const fn has_lengths<const N: usize>(values: &[usize]) -> [bool; N] {
            let mut result = [false; N];
            let mut i = 0;

            while i < values.len() {
                result[values[i] - 1] = true;
                i += 1;
            }

            result
        }

        const fn count_true(values: &[bool]) -> usize {
            let mut result = 0;
            let mut i = 0;

            while i < values.len() {
                if values[i] {
                    result += 1;
                }

                i += 1;
            }

            result
        }

        const fn true_indices<const N: usize>(values: &[bool]) -> [usize; N] {
            let mut result = [0usize; N];
            let mut rd = 0;
            let mut wr = 0;

            while rd < values.len() {
                let i = values.len() - rd - 1;

                if values[i] {
                    result[wr] = i;
                    wr += 1;
                }

                rd += 1;
            }

            result
        }

        impl Symbol {
            const SYMBOLS: phf::Map<&str, Symbol> = phf_map! {
                $($($lit => Self::$variant,)+)+
            };

            const MAX_LENGTH: usize = const {
                let values = [$($($lit.len(),)+)+];
                let mut result = 0;
                let mut i = 0;

                while i < values.len() {
                    if values[i] > result {
                        result = values[i];
                    }

                    i += 1;
                }

                result
            };

            const LENGTHS: &[usize] = [$($($lit.len(),)+)+].as_slice();
            const HAS_LENGTHS: &[bool] = has_lengths::<{Self::MAX_LENGTH}>(Self::LENGTHS).as_slice();
            const PREFIX_LENGTHS_SIZE: usize = count_true(Self::HAS_LENGTHS);

            const PREFIX_LENGTHS: [usize; Self::PREFIX_LENGTHS_SIZE] = true_indices(Self::HAS_LENGTHS);

            pub fn parse_prefix(input: &str) -> Option<Self> {
                Self::PREFIX_LENGTHS
                    .iter()
                    .filter_map(|&len| input.get(0..len))
                    .find_map(|prefix| Self::SYMBOLS.get(prefix))
                    .copied()
            }

            pub fn parse_exact(input: &str) -> Option<Self> {
                Self::SYMBOLS.get(input).copied()
            }

            pub const fn to_str(self) -> &'static str {
                match self {
                    $($(Self::$variant => $lit,)+)+
                }
            }

            pub fn category(self) -> SymbolCategory {
                match self {
                    $($(Self::$variant => SymbolCategory::$cat,)+)+
                }
            }
        }
    };
}

symbols! {
    Keyword {
        "Bool" => BoolTy,
        "Bot" => BotTy,
        "List::head" => ListHead,
        "List::isempty" => ListIsEmpty,
        "List::tail" => ListTail,
        "Nat" => NatTy,
        "Nat::iszero" => NatIsZero,
        "Nat::pred" => NatPred,
        "Nat::rec" => NatRec,
        "Top" => TopTy,
        "Unit" => UnitTy,
        "and" => And,
        "as" => As,
        "auto" => Auto,
        "cast" => Cast,
        "catch" => Catch,
        "cons" => Cons,
        "else" => Else,
        "exception" => Exception,
        "extend" => Extend,
        "false" => False,
        "fix" => Fix,
        "fn" => Fn,
        "fold" => Fold,
        "forall" => Forall,
        "generic" => Generic,
        "if" => If,
        "in" => In,
        "inl" => Inl,
        "inline" => Inline,
        "inr" => Inr,
        "language" => Language,
        "let" => Let,
        "letrec" => LetRec,
        "match" => Match,
        "new" => New,
        "not" => Not,
        "or" => Or,
        "panic!" => PanicBang,
        "return" => Return,
        "succ" => Succ,
        "then" => Then,
        "throw" => Throw,
        "throws" => Throws,
        "true" => True,
        "try" => Try,
        "type" => Type,
        "unfold" => Unfold,
        "unit" => Unit,
        "variant" => Variant,
        "with" => With,
        "µ" => Mu,
    }

    Special {
        "," => Comma,
        ";" => Semicolon,
        "(" => LParen,
        ")" => RParen,
        "{" => LBrace,
        "}" => RBrace,
        "=" => Equals,
        ":" => Colon,
        "->" => Arrow,
        "=>" => FatArrow,
        "|" => Pipe,
        "<|" => LTriangle,
        "|>" => RTriangle,
        "[" => LBracket,
        "]" => RBracket,
        "<" => Less,
        "<=" => LessEquals,
        ">" => Greater,
        ">=" => GreaterEquals,
        "==" => EqualsEquals,
        "!=" => BangEquals,
        "+" => Plus,
        "-" => Minus,
        "*" => Star,
        "/" => Slash,
        "." => Dot,
        ":=" => ColonEquals,
        "&" => Amp,
    }
}
