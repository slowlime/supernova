#[derive(clap::Parser, Debug)]
#[command()]
pub struct Args {
    /// Names of tests to run. Defaults to all tests.
    pub tests: Option<Vec<String>>,

    /// Stop on the first failure.
    #[arg(short = 'x', long)]
    pub first_failure: bool,

    /// Emit diagnostics for all run tests regardless of the test result.
    #[arg(short = 'd', long)]
    pub all_diagnostics: bool,
}

impl Args {
    pub fn parse() -> Self {
        clap::Parser::parse()
    }
}
