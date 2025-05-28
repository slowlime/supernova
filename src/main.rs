mod cli;

use std::process::ExitCode;
use std::{fs, io};

use supernova::diag::{DiagCtx, StderrDiagCtx};
use supernova::parse::{Cursor, Lexer, Parser};
use supernova::sema;
use supernova::sourcemap::SourceMap;

use self::cli::Args;

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
    diag.set_show_stella_codes(args.stella_error_codes);
    diag.set_first_error_only(args.first_error_only);

    let mut ast = match parser.parse() {
        Ok(ast) => ast,
        Err(e) => {
            diag.emit(e);

            return ExitCode::FAILURE;
        }
    };

    let (_, result) = sema::process(&mut ast, &mut diag, args.extensions);

    diag.finish();

    if result.is_err() {
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}
