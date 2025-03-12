#[derive(clap::Parser, Debug)]
#[command()]
pub struct Args {
    /// Path to the source file, or `-` to read from stdin.
    pub input: Option<String>,
}

impl Args {
    pub fn parse() -> Self {
        clap::Parser::parse()
    }
}
