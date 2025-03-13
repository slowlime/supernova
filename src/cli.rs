#[derive(clap::Parser, Debug)]
#[command()]
pub struct Args {
    /// Path to the source file, or `-` to read from stdin.
    pub input: Option<String>,

    /// Also show Stella error codes in diagnostics when available.
    #[arg(long)]
    pub stella_error_codes: bool,
}

impl Args {
    pub fn parse() -> Self {
        clap::Parser::parse()
    }
}
