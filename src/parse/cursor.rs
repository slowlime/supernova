use crate::sourcemap::{SourceFile, SourceId};

#[derive(Debug, Clone)]
pub struct Cursor<'a> {
    iter: std::str::Chars<'a>,
    source_id: SourceId,
    pos: u64,
    eof: bool,
}

impl<'a> Cursor<'a> {
    pub fn new(file: &'a SourceFile) -> Self {
        Self {
            iter: file.contents().chars(),
            source_id: file.id(),
            pos: 0,
            eof: false,
        }
    }

    pub fn source_id(&self) -> SourceId {
        self.source_id
    }

    /// Returns the position of the immediately following character.
    pub fn pos(&self) -> u64 {
        self.pos
    }

    pub fn peek(&self) -> Option<char> {
        self.iter.clone().next()
    }

    pub fn remaining(&self) -> &'a str {
        self.iter.as_str()
    }

    pub fn starts_with(&self, value: &str) -> bool {
        self.remaining().starts_with(value)
    }

    #[must_use = "the method returns None if the expected string is not matched"]
    pub fn consume_expecting(&mut self, expected: &str) -> Option<&'a str> {
        self.starts_with(expected)
            .then(|| self.consume_n(expected.len()))
    }

    pub fn consume_n(&mut self, n: usize) -> &'a str {
        let remaining = self.remaining();
        let start = self.pos;

        for _ in 0..n {
            self.next();
        }

        let end = self.pos;

        &remaining[0..(end - start) as usize]
    }

    pub fn consume_while(&mut self, mut predicate: impl FnMut(char) -> bool) -> &'a str {
        self.consume_n(self.iter.clone().take_while(|&c| predicate(c)).count())
    }

    pub fn consume_newline(&mut self) -> Option<&'a str> {
        if self.starts_with("\r\n") {
            Some(self.consume_n(2))
        } else if self.starts_with("\n") {
            Some(self.consume_n(1))
        } else {
            None
        }
    }
}

impl Iterator for Cursor<'_> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.eof {
            return None;
        }

        let c = if let Some(c) = self.iter.next() {
            c
        } else {
            self.eof = true;

            return None;
        };

        self.pos += 1;

        Some(c)
    }
}
