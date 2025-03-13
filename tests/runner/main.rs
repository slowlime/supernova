mod directive;

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use colored::Colorize;
use fxhash::FxHashSet;
use glob::glob;
use supernova::diag::{DiagCtx, Diagnostic, IntoDiagnostic};
use supernova::parse::{Cursor, Lexer, Parser};
use supernova::sema::{self, Module};
use supernova::sourcemap::SourceMap;

use self::directive::{Directive, parse_directives};

#[derive(Debug, Clone, PartialEq, Eq)]
enum TestResult {
    Passed,
    Failed,
}

#[derive(Default)]
struct TestDiagCtx {
    diags: Vec<Diagnostic>,
}

impl DiagCtx for TestDiagCtx {
    fn emit(&mut self, diag: impl IntoDiagnostic) {
        self.diags.push(diag.into_diagnostic());
    }
}

struct Test {
    path: String,
    contents: String,
    directives: Vec<Directive>,
}

enum RunStage<'m> {
    Parsing,
    Sema(&'m Module<'m>),
}

struct TestRunData<'m> {
    diags: Vec<Diagnostic>,
    stopped_at: RunStage<'m>,
    failed: bool,
}

impl Test {
    pub fn run(&mut self, ctx: &TestCtx) -> TestResult {
        let mut source_map = SourceMap::new();
        let file_id = source_map.add_source(self.path.clone(), self.contents.clone()).id();
        let f = source_map.get_by_id(file_id);
        let cursor = Cursor::new(f);
        let lexer = Lexer::new(cursor);
        let parser = Parser::new(lexer);
        let mut diag = TestDiagCtx::default();
        let mut ast = parser.parse();
        let m;

        let (stopped_at, result) = match ast {
            Ok(ref mut ast) => {
                let result;
                (m, result) = sema::process(ast, &mut diag);

                (RunStage::Sema(&m), result)
            }

            Err(e) => {
                diag.emit(e);

                (RunStage::Parsing, Err(()))
            }
        };

        let run_data = TestRunData {
            diags: diag.diags,
            stopped_at,
            failed: result.is_err(),
        };

        for directive in &self.directives {
            if directive.check(&run_data) == TestResult::Failed {
                return TestResult::Failed;
            }
        }

        TestResult::Passed
    }
}

#[derive(Default)]
struct TestCtx {
    passed: FxHashSet<String>,
    failed: FxHashSet<String>,
    ignored: FxHashSet<String>,
}

impl TestCtx {
    pub fn run(&mut self, tests: Vec<Test>) -> ExitCode {
        for mut test in tests {
            eprintln!("{} test `{}`...", "Running".bright_cyan(), test.path);

            match test.run(self) {
                TestResult::Passed => {
                    self.passed.insert(test.path);
                }

                TestResult::Failed => {
                    self.failed.insert(test.path.clone());
                    eprintln!("{}", format!("Test `{}` failed!", test.path).bright_red());
                }
            };
        }

        eprintln!();

        let test_count = self.passed.len() + self.failed.len() + self.ignored.len();
        eprintln!(
            "Results: {passed} ({passed_perc:.2}%), {failed} ({failed_perc:.2}%), and {ignored}",
            passed = format!("{} passed", self.passed.len()).bright_green(),
            passed_perc = self.passed.len() as f64 * 100. / test_count as f64,
            failed = format!("{} failed", self.failed.len()).bright_red(),
            failed_perc = self.failed.len() as f64 * 100. / test_count as f64,
            ignored = format!("{} ignored", self.ignored.len()).bright_black(),
        );

        if self.failed.is_empty() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }
    }
}

fn load_test(path: impl AsRef<Path>) -> Test {
    let path = path.as_ref();
    let contents = fs::read_to_string(path)
        .map_err(|e| format!("could not read `{}`: {e}", path.display()))
        .unwrap();
    let directives = parse_directives(&contents);

    Test {
        path: path.display().to_string(),
        contents,
        directives,
    }
}

fn load_tests() -> Vec<Test> {
    let mut tests = vec![];

    for entry in glob("./tests/programs/**/*.stella").unwrap() {
        tests.push(load_test(entry.unwrap()));
    }

    tests
}

fn main() -> ExitCode {
    let tests = load_tests();
    let mut ctx = TestCtx::default();

    ctx.run(tests)
}
