use std::path::PathBuf;

#[derive(clap::Parser, Debug)]
#[command()]
pub struct Args {
    /// Path to the source file.
    pub input: PathBuf,
}

impl Args {
    pub fn parse() -> Self {
        clap::Parser::parse()
    }
}
