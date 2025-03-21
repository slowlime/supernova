use std::fmt::Display;

use ariadne::{Color, ColorGenerator, IndexType, Report, ReportKind};
use yansi::Paint;

use crate::location::Location;
use crate::sourcemap::SourceMap;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Code {
    code: &'static str,
    stella: Option<&'static str>,
}

impl Code {
    pub const INTERNAL_ERROR: Self = Self::new("internal_error");

    pub const fn new(code: &'static str) -> Self {
        Self { code, stella: None }
    }

    pub const fn with_stella(self, stella: &'static str) -> Self {
        Self {
            stella: Some(stella),
            ..self
        }
    }

    pub fn code(&self) -> &'static str {
        self.code
    }

    pub fn stella(&self) -> Option<&'static str> {
        self.stella
    }
}

macro_rules! code {
    ($base:ident::$code:ident) => {
        $crate::diag::Code::new(concat!(stringify!($base), "::", stringify!($code)))
    };

    ($base:ident::$code:ident as $stella:literal) => {
        $crate::diag::Code::new(concat!(stringify!($base), "::", stringify!($code)))
            .with_stella($stella)
    };
}

pub(crate) use code;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Error,
    Warn,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: Level,
    pub location: Location,
    pub code: Code,
    pub msg: String,
    pub notes: Vec<String>,
    pub labels: Vec<Label>,
}

impl Diagnostic {
    pub fn with_label(mut self, label: Label) -> Self {
        self.add_label(label);

        self
    }

    pub fn add_label(&mut self, label: Label) {
        if label.location.has_span() {
            self.labels.push(label);
        }
    }

    pub fn with_note(mut self, note: impl Display) -> Self {
        self.add_note(note);

        self
    }

    pub fn add_note(&mut self, note: impl Display) {
        self.notes.push(note.to_string());
    }

    pub fn build(level: Level) -> DiagnosticBuilder<false, false, false> {
        DiagnosticBuilder {
            diag: Self {
                level,
                location: Default::default(),
                code: Default::default(),
                msg: Default::default(),
                notes: Default::default(),
                labels: Default::default(),
            },
        }
    }

    pub fn error() -> DiagnosticBuilder<false, false, false> {
        Self::build(Level::Error)
    }

    pub fn warn() -> DiagnosticBuilder<false, false, false> {
        Self::build(Level::Warn)
    }
}

pub struct DiagnosticBuilder<const L: bool, const C: bool, const M: bool> {
    diag: Diagnostic,
}

impl<const C: bool, const M: bool> DiagnosticBuilder<false, C, M> {
    pub fn at(self, location: impl Into<Location>) -> DiagnosticBuilder<true, C, M> {
        DiagnosticBuilder {
            diag: Diagnostic {
                location: location.into(),
                ..self.diag
            },
        }
    }

    pub fn without_location(self) -> DiagnosticBuilder<true, C, M> {
        DiagnosticBuilder { diag: self.diag }
    }
}

impl<const L: bool, const M: bool> DiagnosticBuilder<L, false, M> {
    pub fn with_code(self, code: Code) -> DiagnosticBuilder<L, true, M> {
        DiagnosticBuilder {
            diag: Diagnostic { code, ..self.diag },
        }
    }
}

impl<const L: bool, const C: bool> DiagnosticBuilder<L, C, false> {
    pub fn with_msg(self, msg: impl Display) -> DiagnosticBuilder<L, C, true> {
        DiagnosticBuilder {
            diag: Diagnostic {
                msg: msg.to_string(),
                ..self.diag
            },
        }
    }
}

impl<const C: bool, const L: bool, const M: bool> DiagnosticBuilder<C, L, M> {
    pub fn with_label(self, label: Label) -> Self {
        Self {
            diag: self.diag.with_label(label),
        }
    }

    pub fn with_note(self, note: impl Display) -> Self {
        Self {
            diag: self.diag.with_note(note),
        }
    }
}

impl DiagnosticBuilder<true, true, true> {
    pub fn make(self) -> Diagnostic {
        self.diag
    }
}

#[derive(Debug, Clone)]
pub struct Label {
    pub location: Location,
    pub kind: LabelKind,
    pub msg: Option<String>,
}

impl Label {
    pub fn primary(location: impl Into<Location>) -> Self {
        Self {
            location: location.into(),
            kind: LabelKind::Primary,
            msg: None,
        }
    }

    pub fn secondary(location: impl Into<Location>) -> Self {
        Self {
            location: location.into(),
            kind: LabelKind::Secondary,
            msg: None,
        }
    }

    pub fn with_msg(self, msg: impl Display) -> Self {
        Self {
            msg: Some(msg.to_string()),
            ..self
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelKind {
    Primary,
    Secondary,
}

pub trait IntoDiagnostic: Sized {
    fn into_diagnostic(self) -> Diagnostic;
}

impl IntoDiagnostic for Diagnostic {
    fn into_diagnostic(self) -> Diagnostic {
        self
    }
}

pub struct ReportOptions {
    show_stella_codes: bool,
}

impl ReportOptions {
    pub const fn new() -> Self {
        Self {
            show_stella_codes: false,
        }
    }
}

impl Default for ReportOptions {
    fn default() -> Self {
        Self::new()
    }
}

pub fn to_report(diag: &Diagnostic, opts: &ReportOptions) -> Report<'static, Location> {
    let mut report = Report::build(
        match diag.level {
            Level::Error => ReportKind::Error,
            Level::Warn => ReportKind::Warning,
        },
        diag.location,
    )
    .with_config(
        ariadne::Config::new()
            .with_tab_width(2)
            .with_index_type(IndexType::Byte),
    )
    .with_code(
        if let Some(stella) = opts.show_stella_codes.then_some(diag.code.stella).flatten() {
            format!("{} / {stella}", diag.code.code)
        } else {
            diag.code.code.to_string()
        },
    )
    .with_message(&diag.msg);

    report.with_notes(&diag.notes);

    let mut colors = ColorGenerator::from_state([5737, 74, 31337], 0.5);

    for label in &diag.labels {
        let mut report_label = ariadne::Label::new(label.location);

        if let Some(msg) = &label.msg {
            report_label = report_label.with_message(msg);
        }

        let color = match label.kind {
            LabelKind::Primary => match diag.level {
                Level::Error => Color::BrightRed,
                Level::Warn => Color::BrightYellow,
            },

            LabelKind::Secondary => colors.next(),
        };

        report.add_label(report_label.with_color(color));
    }

    report.finish()
}

pub trait DiagCtx {
    fn emit(&mut self, diag: impl IntoDiagnostic);
}

pub struct StderrDiagCtx<'src> {
    source_map: &'src SourceMap,
    opts: ReportOptions,
    first_error_only: bool,
    had_error: bool,
    errors_hidden: usize,
    warnings_hidden: usize,
}

impl<'src> StderrDiagCtx<'src> {
    pub fn new(source_map: &'src SourceMap) -> Self {
        Self {
            source_map,
            opts: Default::default(),
            first_error_only: false,
            had_error: false,
            errors_hidden: 0,
            warnings_hidden: 0,
        }
    }

    pub fn set_show_stella_codes(&mut self, value: bool) {
        self.opts.show_stella_codes = value;
    }

    pub fn set_first_error_only(&mut self, value: bool) {
        self.first_error_only = value;
    }

    pub fn finish(&mut self) {
        fn ending(n: usize) -> &'static str {
            if n == 1 { "" } else { "s" }
        }

        fn copula(n: usize) -> &'static str {
            if n == 1 { "was" } else { "were" }
        }

        match (self.errors_hidden, self.warnings_hidden) {
            (0, 0) => {}

            (errors, 0) => {
                let e = ending(errors);
                let c = copula(errors);
                eprintln!(
                    "\n{}",
                    format_args!("{errors} more error{e} {c} hidden").bright_red()
                );
            }

            (0, warnings) => {
                let e = ending(warnings);
                let c = copula(warnings);
                eprintln!(
                    "\n{}",
                    format_args!("{warnings} more warning{e} {c} hidden",).bright_yellow()
                );
            }

            (errors, warnings) => {
                let err_e = ending(errors);
                let warn_e = ending(warnings);
                let c = ending(errors + warnings);
                eprintln!(
                    "\n{}",
                    format_args!("{errors} error{err_e} and {warnings} warning{warn_e} {c} hidden")
                        .bright_red()
                );
            }
        }
    }
}

impl DiagCtx for StderrDiagCtx<'_> {
    fn emit(&mut self, diag: impl IntoDiagnostic) {
        let diag = diag.into_diagnostic();

        match (diag.level, self.had_error) {
            (Level::Warn, true) => {
                self.warnings_hidden += 1;
                return;
            }

            (Level::Error, true) => {
                self.errors_hidden += 1;
                return;
            }

            (Level::Error, _) => {
                self.had_error = true;
            }

            _ => {}
        }

        let _ = to_report(&diag, &self.opts).eprint(self.source_map.to_cache());
    }
}
