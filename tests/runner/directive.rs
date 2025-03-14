use std::ops::Range;
use std::sync::LazyLock;

use derive_more::From;
use regex::{Regex, RegexSet};
use supernova::diag::Level;

use crate::{TestResult, TestRunData};

#[derive(From)]
pub enum Directive {
    Error(DirectiveError),
    Pass(DirectivePass),
}

impl Directive {
    pub fn check(&self, run_data: &TestRunData) -> TestResult {
        match self {
            Self::Error(d) => d.check(run_data),
            Self::Pass(d) => d.check(run_data),
        }
    }
}

pub struct DirectiveError {
    line: usize,
    err_start: Range<usize>,
    code: Option<String>,
}

static DIRECTIVE_ERROR_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"^ERROR\((?<code>[[:word:]]+::[[:word:]]+)\)$"#).unwrap());

impl DirectiveError {
    fn parse(directive: &str, line: usize, next_line_range: Range<usize>) -> Self {
        let captures = DIRECTIVE_ERROR_REGEX.captures(directive).unwrap();
        let code = captures.name("code").map(|m| m.as_str().into());

        DirectiveError {
            line,
            err_start: next_line_range,
            code,
        }
    }

    pub fn check(&self, run_data: &TestRunData) -> TestResult {
        if run_data.diags.iter().any(|diag| {
            diag.level == Level::Error
                && diag
                    .location
                    .span()
                    .is_some_and(|span| self.err_start.contains(&span.start()))
                && self
                    .code
                    .as_ref()
                    .is_none_or(|code| diag.code.code() == code)
        }) {
            TestResult::Passed
        } else {
            eprintln!(
                "Could not find a diagnostic matching the ERROR directive at line {}",
                self.line,
            );

            TestResult::Failed
        }
    }
}

pub struct DirectivePass;

static DIRECTIVE_PASS_REGEX: LazyLock<Regex> = LazyLock::new(|| Regex::new(r#"^PASS$"#).unwrap());

impl DirectivePass {
    pub fn parse(_directive: &str) -> Self {
        Self
    }

    pub fn check(&self, run_data: &TestRunData) -> TestResult {
        if run_data.failed {
            eprintln!("The file failed unexpectedly!");

            TestResult::Failed
        } else {
            TestResult::Passed
        }
    }
}

static DIRECTIVE_REGEX: LazyLock<RegexSet> = LazyLock::new(|| {
    RegexSet::new([
        DIRECTIVE_ERROR_REGEX.as_str(),
        DIRECTIVE_PASS_REGEX.as_str(),
    ])
    .unwrap()
});

fn split_lines(mut s: &str) -> Vec<(Range<usize>, &str)> {
    let mut next_start = 0;
    let mut result = vec![];

    while !s.is_empty() {
        let start = next_start;

        let (len, nl_len) = match s.find('\n') {
            Some(pos) if s.get(pos.saturating_sub(1)..pos) == Some("\r\n") => (pos - 1, 2),
            Some(pos) => (pos, 1),
            None => (s.len(), 0),
        };

        let line = &s[0..len];
        s = &s[len + nl_len..];
        next_start += len + nl_len;

        result.push((start..start + len, line));
    }

    result
}

pub fn parse_directives(s: &str) -> Result<Vec<Directive>, String> {
    let lines = split_lines(s);
    let mut directives = vec![];

    for (idx, (_, line)) in lines.iter().enumerate() {
        let Some((_, directive)) = line.split_once("//!") else {
            continue;
        };
        let directive = directive.trim();

        let matches = DIRECTIVE_REGEX.matches(directive);

        if !matches.matched_any() {
            return Err(format!("unrecognized directive at line {}", idx + 1));
        }

        let directive = if matches.matched(0) {
            let next_line_range = lines
                .get(idx + 1)
                .map(|(r, _)| r.clone())
                .unwrap_or(s.len()..s.len());

            DirectiveError::parse(directive, idx + 1, next_line_range).into()
        } else if matches.matched(1) {
            DirectivePass::parse(directive).into()
        } else {
            unreachable!();
        };

        directives.push(directive);
    }

    if directives.is_empty() {
        return Err("no directives found".into());
    }

    Ok(directives)
}
