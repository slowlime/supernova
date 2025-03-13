use std::fmt::Display;

use ariadne::{Color, ColorGenerator, IndexType, Report, ReportKind};

use crate::location::Location;
use crate::sourcemap::SourceMap;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Code {
    code: &'static str,
    stella: Option<&'static str>,
}

impl Code {
    pub const fn new(code: &'static str) -> Self {
        Self { code, stella: None }
    }

    pub const fn with_stella(self, stella: &'static str) -> Self {
        Self {
            stella: Some(stella),
            ..self
        }
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

    pub fn error() -> DiagnosticBuilder<false, false, false> {
        DiagnosticBuilder {
            diag: Self {
                level: Level::Error,
                location: Default::default(),
                code: Default::default(),
                msg: Default::default(),
                notes: Default::default(),
                labels: Default::default(),
            },
        }
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

pub trait DiagCtx {
    fn emit(&mut self, diag: impl IntoDiagnostic);
}

pub struct StderrDiagCtx<'src> {
    source_map: &'src SourceMap,
    show_stella_codes: bool,
}

impl<'src> StderrDiagCtx<'src> {
    pub fn new(source_map: &'src SourceMap) -> Self {
        Self {
            source_map,
            show_stella_codes: false,
        }
    }

    pub fn set_show_stella_codes(&mut self, value: bool) {
        self.show_stella_codes = value;
    }
}

impl DiagCtx for StderrDiagCtx<'_> {
    fn emit(&mut self, diag: impl IntoDiagnostic) {
        let diag = diag.into_diagnostic();
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
            if let Some(stella) = self.show_stella_codes.then_some(diag.code.stella).flatten() {
                format!("{} / {stella}", diag.code.code)
            } else {
                diag.code.code.to_string()
            }
        )
        .with_message(diag.msg);

        report.with_notes(diag.notes);

        let mut colors = ColorGenerator::from_state([5737, 74, 31337], 0.5);

        for label in diag.labels {
            let mut report_label = ariadne::Label::new(label.location);

            if let Some(msg) = label.msg {
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

        let _ = report.finish().eprint(self.source_map.to_cache());
    }
}
