use supernova::ast;

#[derive(clap::Parser, Debug)]
#[command()]
pub struct Args {
    /// Path to the source file, or `-` to read from stdin.
    pub input: Option<String>,

    /// Also show Stella error codes in diagnostics when available.
    #[arg(long)]
    pub stella_error_codes: bool,

    /// Only print the first error found.
    #[arg(short = 'x', long)]
    pub first_error_only: bool,

    /// Enable these extensions in addition to those specified in the source file.
    #[arg(short = 'f', long = "extension")]
    pub extensions: Vec<ast::Extension>,
}

impl Args {
    pub fn parse() -> Self {
        clap::Parser::parse()
    }
}
