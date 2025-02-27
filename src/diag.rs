use ariadne::{Report, ReportBuilder};

use crate::location::Span;
use crate::sourcemap::SourceMap;

pub trait IntoReportBuilder: Sized {
    fn into_report_builder(self) -> ReportBuilder<'static, Span>;
}

pub trait IntoReport: Sized {
    fn into_report(self) -> Report<'static, Span>;
}

impl<T: IntoReportBuilder> IntoReport for T {
    fn into_report(self) -> Report<'static, Span> {
        self.into_report_builder().finish()
    }
}

impl IntoReportBuilder for ReportBuilder<'static, Span> {
    fn into_report_builder(self) -> ReportBuilder<'static, Span> {
        self
    }
}

impl IntoReport for Report<'static, Span> {
    fn into_report(self) -> Report<'static, Span> {
        self
    }
}

pub trait DiagCtx {
    fn emit(&mut self, diag: impl IntoReport);
}

pub struct StderrDiagCtx<'src> {
    source_map: &'src SourceMap,
}

impl<'src> StderrDiagCtx<'src> {
    pub fn new(source_map: &'src SourceMap) -> Self {
        Self { source_map }
    }
}

impl DiagCtx for StderrDiagCtx<'_> {
    fn emit(&mut self, diag: impl IntoReport) {
        let _ = diag.into_report().eprint(self.source_map.to_cache());
    }
}
