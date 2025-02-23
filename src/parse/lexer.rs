use std::collections::VecDeque;
use std::fmt::{self, Display};

use miette::{Diagnostic, SourceOffset};
use num::{BigUint, Num};
use thiserror::Error;

use crate::location::Span;
use crate::parse::token::Symbol;

use super::cursor::Cursor;
use super::token::{Token, TokenValue};

type ScanResult<'a> = Result<TokenValue<'a>, PosLexerError>;

#[derive(Debug, Clone, Eq, PartialEq)]
struct PosLexerError {
    end: SourceOffset,
    kind: LexerErrorKind,
}

impl PosLexerError {
    fn with_start(self, start: SourceOffset) -> LexerError {
        LexerError {
            kind: self.kind,
            span: (start.offset()..self.end.offset()).into(),
        }
    }
}

#[derive(Error, Diagnostic, Debug, Clone, Eq, PartialEq)]
#[error("lexical analysis failed: {kind}")]
pub struct LexerError {
    pub kind: LexerErrorKind,

    #[label]
    pub span: Span,
}

fn format_char(c: char) -> impl Display {
    struct CharFormatter(char);

    impl Display for CharFormatter {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.0.is_ascii_graphic() {
                write!(f, "`{}`", self.0)
            } else {
                write!(f, "U+{:04x}", self.0 as u32)
            }
        }
    }

    CharFormatter(c)
}

#[derive(Error, Diagnostic, Debug, Clone, Copy, Eq, PartialEq)]
pub enum LexerErrorKind {
    #[error("the multiline comment is not terminated")]
    #[diagnostic(code(lexer::unterminated_comment))]
    UnterminatedComment,

    #[error("encountered an unrecognized character {}", format_char(*.0))]
    #[diagnostic(code(lexer::unrecognized_character))]
    UnrecognizedCharacter(char),

    #[error("the number is malformed")]
    #[diagnostic(code(lexer::malformed_number))]
    MalformedNumber,

    #[error("the address literal is malformed")]
    #[diagnostic(code(lexer::malformed_address))]
    MalformedAddress,

    #[error("the extension name is malformed")]
    #[diagnostic(code(lexer::malformed_extension))]
    MalformedExtension,

    #[error("the address literal is unterminated")]
    #[diagnostic(
        code(lexer::unterminated_address),
        help("the address literal must be immediately followed by '>'")
    )]
    UnterminatedAddress,
}

pub struct Lexer<'a> {
    cursor: Cursor<'a>,
    eof: bool,
    buf: VecDeque<(Result<Token<'a>, LexerError>, SourceOffset)>,
}

impl Lexer<'_> {
    fn is_whitespace(c: char) -> bool {
        " \r\t\n\x0c".find(c).is_some()
    }

    fn is_newline(c: char) -> bool {
        "\r\n".find(c).is_some()
    }

    fn is_letter(c: char) -> bool {
        c.is_ascii_alphabetic()
            || ('\u{c0}'..='\u{d6}').contains(&c)
            || ('\u{d8}'..='\u{de}').contains(&c)
            || ('\u{df}'..='\u{f6}').contains(&c)
            || ('\u{f8}'..='\u{ff}').contains(&c)
    }

    fn is_address_digit(c: char) -> bool {
        c.is_ascii_hexdigit()
    }

    fn is_extension_letter(c: char) -> bool {
        "-_".contains(c) || Self::is_letter(c) || Self::is_digit(c)
    }

    fn is_digit(c: char) -> bool {
        c.is_ascii_digit()
    }

    fn is_ident_start(c: char) -> bool {
        c == '_' || Self::is_letter(c)
    }

    fn is_ident_cont(c: char) -> bool {
        "!-:?".contains(c) || Self::is_ident_start(c) || Self::is_digit(c)
    }
}

impl<'a> Lexer<'a> {
    pub fn new(cursor: Cursor<'a>) -> Self {
        Self {
            cursor,
            eof: false,
            buf: Default::default(),
        }
    }

    fn make_error_at_pos(&self, kind: LexerErrorKind) -> PosLexerError {
        PosLexerError {
            end: self.cursor.pos(),
            kind,
        }
    }

    fn skip_whitespace(&mut self) {
        self.cursor.consume_while(Self::is_whitespace);
    }

    fn skip_line_comment(&mut self) {
        self.cursor.consume_expecting("//").unwrap();
        self.cursor.consume_while(|c| !Self::is_newline(c));
        self.cursor.consume_newline();
    }

    fn skip_multiline_comment(&mut self) -> Result<(), PosLexerError> {
        self.cursor.consume_expecting("/*").unwrap();

        loop {
            self.cursor.consume_while(|c| c != '*');

            if self.cursor.consume_expecting("*/").is_some() {
                break;
            } else if self.cursor.peek().is_none() {
                return Err(self.make_error_at_pos(LexerErrorKind::UnterminatedComment));
            }
        }

        Ok(())
    }

    fn scan_address(&mut self) -> ScanResult<'a> {
        self.cursor.consume_expecting("<0x").unwrap();
        let digits = self.cursor.consume_while(Self::is_address_digit);
        let Ok(value) = BigUint::from_str_radix(digits, 16) else {
            return Err(self.make_error_at_pos(LexerErrorKind::MalformedAddress));
        };

        if self.cursor.consume_expecting(">").is_none() {
            return Err(self.make_error_at_pos(LexerErrorKind::UnterminatedAddress));
        }

        Ok(TokenValue::Address(value))
    }

    fn scan_extension(&mut self) -> ScanResult<'a> {
        self.cursor.consume_expecting("#").unwrap();
        let name = self.cursor.consume_while(Self::is_extension_letter);

        if name.is_empty() {
            return Err(self.make_error_at_pos(LexerErrorKind::MalformedExtension));
        }

        Ok(TokenValue::Extension(name))
    }

    fn scan_int(&mut self) -> ScanResult<'a> {
        let digits = self.cursor.consume_while(Self::is_digit);
        let value = digits.parse::<BigUint>().unwrap();

        if self.cursor.peek().is_some_and(Self::is_ident_start) {
            return Err(self.make_error_at_pos(LexerErrorKind::MalformedNumber));
        }

        Ok(TokenValue::Int(value))
    }

    fn scan_ident_or_symbol(&mut self) -> ScanResult<'a> {
        let ident = self.cursor.consume_while(Self::is_ident_cont);

        Ok(Symbol::parse_exact(ident)
            .map(TokenValue::Symbol)
            .unwrap_or(TokenValue::Ident(ident)))
    }

    fn scan_next(&mut self) -> Option<Result<Token<'a>, LexerError>> {
        let mut start = self.cursor.pos();

        let scan_result: ScanResult = (|| loop {
            start = self.cursor.pos();

            break match self.cursor.peek() {
                None => {
                    self.eof = true;

                    return Ok(TokenValue::Eof);
                }

                Some('/') if self.cursor.starts_with("//") => {
                    self.skip_line_comment();

                    continue;
                }

                Some('/') if self.cursor.starts_with("/*") => {
                    self.skip_multiline_comment()?;

                    continue;
                }

                Some(c) if Self::is_whitespace(c) => {
                    self.skip_whitespace();

                    continue;
                }

                Some('<') if self.cursor.starts_with("<0x") => self.scan_address(),

                Some('#') => self.scan_extension(),

                Some(c) if Self::is_digit(c) => self.scan_int(),

                Some(c) if Self::is_ident_start(c) => self.scan_ident_or_symbol(),

                Some(c) => match Symbol::parse_prefix(self.cursor.remaining()) {
                    Some(sym) => {
                        self.cursor.consume_n(sym.to_str().len());

                        Ok(TokenValue::Symbol(sym))
                    }

                    None => Err(self.make_error_at_pos(LexerErrorKind::UnrecognizedCharacter(c))),
                },
            };
        })();

        Some(match scan_result {
            Ok(value) => Ok(Token {
                span: (start..self.cursor.pos()).into(),
                value,
            }),

            Err(e) => {
                self.eof = true;

                Err(e.with_start(start))
            }
        })
    }

    pub fn next(&mut self) -> Option<Result<Token<'a>, LexerError>> {
        self.buf
            .pop_front()
            .map(|entry| entry.0)
            .or_else(|| self.scan_next())
    }

    pub fn peek(&mut self) -> Option<&Result<Token<'a>, LexerError>> {
        self.peek_nth(0)
    }

    pub fn peek_nth(&mut self, n: usize) -> Option<&Result<Token<'a>, LexerError>> {
        while self.buf.len() < n {
            let pos = self.cursor.pos();

            if let Some(r) = self.scan_next() {
                self.buf.push_back((r, pos));
            } else {
                return None;
            }
        }

        Some(&self.buf[n].0)
    }

    pub fn pos(&self) -> SourceOffset {
        // FIXME: WRONG
        self.buf
            .front()
            .map(|entry| entry.1)
            .unwrap_or(self.cursor.pos())
    }
}
