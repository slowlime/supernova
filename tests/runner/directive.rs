use std::ops::Range;
use std::sync::LazyLock;

use derive_more::From;
use regex::{Regex, RegexSet};
use supernova::diag::Level;

use crate::{TestResult, TestRunData};

#[derive(From)]
pub enum Directive {
    Diag(DirectiveDiag),
    Pass(DirectivePass),
}

impl Directive {
    pub fn check(&self, run_data: &TestRunData) -> TestResult {
        match self {
            Self::Diag(d) => d.check(run_data),
            Self::Pass(d) => d.check(run_data),
        }
    }
}

pub struct DirectiveDiag {
    level: Level,
    line: usize,
    diag_line: Option<(usize, Range<usize>)>,
    code: Option<String>,
}

static DIRECTIVE_DIAG_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"^(?<level>ERROR|WARN)\((?<code>[[:word:]]+::[[:word:]]+)\)$"#).unwrap()
});

impl DirectiveDiag {
    fn parse(directive: &str, line: usize, diag_line: Option<(usize, Range<usize>)>) -> Self {
        let captures = DIRECTIVE_DIAG_REGEX.captures(directive).unwrap();
        let level = match captures.name("level").unwrap().as_str() {
            "ERROR" => Level::Error,
            "WARN" => Level::Warn,
            level => panic!("unsupported diagnostic level `{level}`"),
        };
        let code = captures.name("code").map(|m| m.as_str().into());

        Self {
            level,
            line,
            diag_line,
            code,
        }
    }

    pub fn check(&self, run_data: &TestRunData) -> TestResult {
        if run_data.diags.iter().any(|diag| {
            diag.level == self.level
                && match &self.diag_line {
                    Some((_, diag_start)) => diag
                        .location
                        .span()
                        .is_some_and(|span| diag_start.contains(&span.start())),
                    None => diag.location.is_builtin(),
                }
                && self
                    .code
                    .as_ref()
                    .is_none_or(|code| diag.code.code() == code)
        }) {
            TestResult::Passed
        } else {
            eprintln!(
                "Could not find a diagnostic matching the directive at line {}",
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
    RegexSet::new([DIRECTIVE_DIAG_REGEX.as_str(), DIRECTIVE_PASS_REGEX.as_str()]).unwrap()
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

        let (directive, selected_line_idx) = if let Some(d) = directive.strip_prefix('<') {
            (d, Some(idx))
        } else if let Some(d) = directive.strip_prefix('^') {
            (d, Some(idx.saturating_sub(1)))
        } else if let Some(d) = directive.strip_prefix('#') {
            (d, None)
        } else {
            (directive, Some(idx + 1))
        };

        let directive = directive.trim();
        let matches = DIRECTIVE_REGEX.matches(directive);

        if !matches.matched_any() {
            return Err(format!("unrecognized directive at line {}", idx + 1));
        }

        let selected_line = selected_line_idx.map(|selected_line_idx| {
            (
                selected_line_idx + 1,
                lines
                    .get(selected_line_idx)
                    .map(|(r, _)| r.clone())
                    .unwrap_or(s.len()..s.len()),
            )
        });

        let directive = if matches.matched(0) {
            DirectiveDiag::parse(directive, idx + 1, selected_line).into()
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
