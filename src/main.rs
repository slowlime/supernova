pub mod ast;
mod cli;
pub mod diag;
pub mod location;
pub mod parse;
pub mod sema;
pub mod sourcemap;
pub mod util;

use std::process::ExitCode;
use std::{fs, io};

use self::cli::Args;
use self::diag::{DiagCtx, StderrDiagCtx};
use self::parse::{Cursor, Lexer, Parser};
use self::sourcemap::SourceMap;

fn main() -> ExitCode {
    let args = Args::parse();

    let (path, contents) = match &args.input {
        Some(path) if path != "-" => (path.as_str(), fs::read_to_string(path)),
        _ => ("<stdin>", io::read_to_string(io::stdin())),
    };

    let contents = match contents {
        Ok(contents) => contents,

        Err(e) => {
            eprintln!("Could not read the input file `{path}`: {e}");

            return ExitCode::from(2);
        }
    };

    let mut sourcemap = SourceMap::new();
    let file_id = sourcemap.add_source(path.into(), contents).id();
    let f = sourcemap.get_by_id(file_id);
    let cursor = Cursor::new(f);
    let lexer = Lexer::new(cursor);
    let parser = Parser::new(lexer);
    let mut diag = StderrDiagCtx::new(&sourcemap);

    let mut ast = match parser.parse() {
        Ok(ast) => ast,
        Err(e) => {
            diag.emit(e);

            return ExitCode::FAILURE;
        }
    };

    let (_, result) = sema::process(&mut ast, &mut diag);

    if result.is_err() {
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}
