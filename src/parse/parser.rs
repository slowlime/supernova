use miette::Diagnostic;
use thiserror::Error;

use super::token::{Symbol, Token, TokenKind, TokenValue};

#[derive(Error, Diagnostic, Debug, Clone, PartialEq)]
pub enum ParserError {}

trait Matcher {
    fn matches(&self, token: &Token<'_>) -> bool;
}

impl<const N: usize> Matcher for [TokenKind; N] {
    fn matches(&self, token: &Token<'_>) -> bool {
        self.contains(&token.kind())
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

impl Matcher for TokenKind {
    fn matches(&self, token: &Token<'_>) -> bool {
        self == &token.kind()
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

pub struct Parser {}
