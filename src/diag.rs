use ariadne::{Report, ReportBuilder};

use crate::location::Location;
use crate::sourcemap::SourceMap;

pub trait IntoReportBuilder: Sized {
    fn into_report_builder(self) -> ReportBuilder<'static, Location>;
}

pub trait IntoReport: Sized {
    fn into_report(self) -> Report<'static, Location>;
}

impl<T: IntoReportBuilder> IntoReport for T {
    fn into_report(self) -> Report<'static, Location> {
        self.into_report_builder().finish()
    }
}

impl IntoReportBuilder for ReportBuilder<'static, Location> {
    fn into_report_builder(self) -> ReportBuilder<'static, Location> {
        self
    }
}

impl IntoReport for Report<'static, Location> {
    fn into_report(self) -> Report<'static, Location> {
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
