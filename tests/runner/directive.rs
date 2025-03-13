use crate::{TestResult, TestRunData};

pub enum Directive {}

impl Directive {
    pub fn check(&self, run_data: &TestRunData<'_>) -> TestResult {
        todo!()
    }
}

pub fn parse_directives(s: &str) -> Vec<Directive> {
    todo!()
}
