mod cli;
mod directive;

use std::path::Path;
use std::process::ExitCode;
use std::{fs, mem};

use fxhash::FxHashSet;
use glob::glob;
use supernova::diag::{DiagCtx, Diagnostic, IntoDiagnostic, print_to_stderr};
use supernova::parse::{Cursor, Lexer, Parser};
use supernova::sema;
use supernova::sourcemap::SourceMap;
use supernova::util::format_iter;
use yansi::Paint;

use self::cli::Args;
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
    pub fn run(&self, ctx: &TestCtx) -> TestResult {
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
            Ok(ref mut ast) => sema::process(ast, &mut diag, vec![]).1,

            Err(e) => {
                diag.emit(e);

                Err(())
            }
        };

        let run_data = TestRunData {
            diags: diag.diags,
            failed: result.is_err(),
        };

        let mut result = TestResult::Passed;

        for directive in &self.directives {
            if directive.check(&run_data) == TestResult::Failed {
                result = TestResult::Failed;

                if ctx.stop_on_first_failure {
                    break;
                }
            }
        }

        if result == TestResult::Failed || ctx.all_diagnostics {
            if !run_data.diags.is_empty() {
                eprintln!("Reported diagnostics:");

                for diag in &run_data.diags {
                    print_to_stderr(diag, &source_map, &Default::default());
                }
            } else {
                eprintln!("No diagnostics reported")
            }
        }

        result
    }
}

struct TestCtx {
    stop_on_first_failure: bool,
    all_diagnostics: bool,
    tests: Vec<Test>,
    passed: FxHashSet<String>,
    failed: FxHashSet<String>,
    ignored: FxHashSet<String>,
}

impl TestCtx {
    pub fn new(args: &Args, tests: Vec<Test>) -> Result<Self, String> {
        let mut result = Self {
            stop_on_first_failure: args.first_failure,
            all_diagnostics: args.all_diagnostics,
            tests,
            passed: Default::default(),
            failed: Default::default(),
            ignored: Default::default(),
        };

        if let Some(selected_tests) = &args.tests {
            let mut selected_tests = selected_tests.iter().collect::<FxHashSet<_>>();

            for test in &result.tests {
                if !selected_tests.remove(&test.path) {
                    result.ignored.insert(test.path.clone());
                }
            }

            match selected_tests.len() {
                0 => {}

                1 => {
                    return Err(format!(
                        "unknown test `{}`",
                        selected_tests.into_iter().next().unwrap(),
                    ));
                }

                _ => {
                    return Err(format!(
                        "unknown tests: {}",
                        format_iter(
                            selected_tests.iter().map(|name| format!("`{name}`")),
                            "and",
                            "",
                        ),
                    ));
                }
            }
        }

        Ok(result)
    }

    pub fn run(mut self) -> ExitCode {
        let tests = mem::take(&mut self.tests);

        for test in tests {
            if self.ignored.contains(&test.path) {
                continue;
            }

            eprintln!("{} test `{}`...", "Running".bright_cyan().bold(), test.path);

            match test.run(&self) {
                TestResult::Passed => {
                    self.passed.insert(test.path);
                }

                TestResult::Failed => {
                    self.failed.insert(test.path.clone());
                    eprintln!(
                        "{}",
                        format_args!("Test `{}` {}!", test.path, "failed").bright_red()
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

        let run_test_count = self.passed.len() + self.failed.len();
        eprintln!(
            "Details: {passed} passed ({passed_perc:.2}%), {failed} failed ({failed_perc:.2}%), and {ignored} ignored",
            passed = self.passed.len().bright_green(),
            passed_perc = self.passed.len() as f64 * 100. / run_test_count as f64,
            failed = self.failed.len().bright_red(),
            failed_perc = self.failed.len() as f64 * 100. / run_test_count as f64,
            ignored = self.ignored.len().white(),
        );

        if self.failed.is_empty() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }
    }
}

fn load_test(path: impl AsRef<Path>) -> Result<Test, String> {
    let path = path.as_ref();
    let contents = fs::read_to_string(path)
        .map_err(|e| format!("could not read `{}`: {e}", path.display()))?;
    let directives = parse_directives(&contents)
        .map_err(|e| format!("could not parse directives in `{}`: {e}", path.display()))?;

    Ok(Test {
        path: path.display().to_string(),
        contents,
        directives,
    })
}

fn load_tests() -> Result<Vec<Test>, String> {
    let mut tests = vec![];

    for entry in glob("./tests/programs/**/*.stella").unwrap() {
        tests.push(load_test(entry.unwrap())?);
    }

    Ok(tests)
}

fn main() -> ExitCode {
    fn load_ctx() -> Result<TestCtx, String> {
        let args = Args::parse();
        let tests = load_tests()?;

        TestCtx::new(&args, tests)
    }

    let ctx = match load_ctx() {
        Ok(ctx) => ctx,

        Err(e) => {
            eprintln!("{}: {e}", "Error".bright_red().bold());

            return ExitCode::from(2);
        }
    };

    ctx.run()
}
