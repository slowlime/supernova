mod directive;

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use fxhash::FxHashSet;
use glob::glob;
use supernova::diag::{DiagCtx, Diagnostic, IntoDiagnostic, to_report};
use supernova::parse::{Cursor, Lexer, Parser};
use supernova::sema;
use supernova::sourcemap::SourceMap;
use yansi::Paint;

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

struct TestRunData {
    diags: Vec<Diagnostic>,
    failed: bool,
}

impl Test {
    pub fn run(&mut self, _ctx: &TestCtx) -> TestResult {
        let mut source_map = SourceMap::new();
        let file_id = source_map
            .add_source(self.path.clone(), self.contents.clone())
            .id();
        let f = source_map.get_by_id(file_id);
        let cursor = Cursor::new(f);
        let lexer = Lexer::new(cursor);
        let parser = Parser::new(lexer);
        let mut diag = TestDiagCtx::default();
        let mut ast = parser.parse();

        let result = match ast {
            Ok(ref mut ast) => sema::process(ast, &mut diag).1,

            Err(e) => {
                diag.emit(e);

                Err(())
            }
        };

        let run_data = TestRunData {
            diags: diag.diags,
            failed: result.is_err(),
        };

        for directive in &self.directives {
            if directive.check(&run_data) == TestResult::Failed {
                if !run_data.diags.is_empty() {
                    eprintln!("Reported diagnostics:");

                    for diag in &run_data.diags {
                        let _ = to_report(diag, &Default::default()).eprint(source_map.to_cache());
                    }
                }

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
            eprintln!("{} test `{}`...", "Running".bright_cyan().bold(), test.path);

            match test.run(self) {
                TestResult::Passed => {
                    self.passed.insert(test.path);
                }

                TestResult::Failed => {
                    self.failed.insert(test.path.clone());
                    eprintln!(
                        "{}",
                        format_args!("Test `{}` failed!", test.path).bright_red().bold()
                    );
                }
            };
        }

        eprintln!();

        eprintln!(
            "Test status: {}",
            if self.failed.is_empty() {
                "passed".bright_green().bold()
            } else {
                "failed".bright_red().bold()
            },
        );

        let test_count = self.passed.len() + self.failed.len() + self.ignored.len();
        eprintln!(
            "Details: {passed} passed ({passed_perc:.2}%), {failed} failed ({failed_perc:.2}%), and {ignored} ignored",
            passed = self.passed.len().bright_green(),
            passed_perc = self.passed.len() as f64 * 100. / test_count as f64,
            failed = self.failed.len().bright_red(),
            failed_perc = self.failed.len() as f64 * 100. / test_count as f64,
            ignored = self.ignored.len().white(),
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
    let directives = parse_directives(&contents)
        .map_err(|e| format!("could not parse directives in `{}`: {e}", path.display()))
        .unwrap();

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
