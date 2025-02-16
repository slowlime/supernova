use std::fmt::{self, Display};

use miette::{Diagnostic, SourceOffset};
use num_bigint::BigUint;
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
}

pub struct Lexer<'a> {
    cursor: Cursor<'a>,
    eof: bool,
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
        Self { cursor, eof: false }
    }

    pub fn pos(&self) -> SourceOffset {
        self.cursor.pos()
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
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.eof {
            return None;
        }

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
}
