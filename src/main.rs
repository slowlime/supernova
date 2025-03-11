pub mod ast;
mod cli;
pub mod diag;
pub mod location;
pub mod parse;
pub mod sema;
pub mod sourcemap;
pub mod util;

use std::fs;
use std::process::ExitCode;

use self::cli::Args;
use self::diag::{DiagCtx, StderrDiagCtx};
use self::parse::{Cursor, Lexer, Parser};
use self::sourcemap::SourceMap;

fn main() -> ExitCode {
    let args = Args::parse();

    let contents = match fs::read_to_string(&args.input) {
        Ok(input) => input,

        Err(e) => {
            eprintln!(
                "Could not read the input file `{}`: {e}",
                args.input.display()
            );
            return ExitCode::from(2);
        }
    };

    let mut sourcemap = SourceMap::new();
    let file_id = sourcemap.add_source(args.input.display().to_string(), contents).id();
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
