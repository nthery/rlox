//! Basic read-evaluate-print loop.

use std::io;
use std::io::prelude::*;

use rlox::interpreter::Interpreter;

fn main() {
    if let Err(e) = run_prompt() {
        eprintln!("fatal error: {}", e);
    }
}

fn run_prompt() -> Result<(), io::Error> {
    let stdin = io::stdin();
    let mut repl_stdout = io::stdout();
    let mut interp_stdout = io::stdout();

    let mut interp = Interpreter::new(&mut interp_stdout);

    let mut input = String::new();
    loop {
        repl_stdout.write_all("\n> ".as_bytes())?;
        repl_stdout.flush()?;

        input.clear();
        let nbytes = stdin.read_line(&mut input)?;
        if nbytes == 0 {
            break;
        }

        if let Err(e) = interp.eval(input.as_bytes()) {
            println!("{}", e);
        }
    }

    Ok(())
}
