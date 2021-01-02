//! Lox interpreter command-line.
//!
//! When called without argument it drops into an interactive read-evaluate-print loop.
//!
//! When called with arguments, it interprets the corresponding files in a single interpreter
//! session (so code and data sharing is possible).

use std::env;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::io::BufReader;

use anyhow::{self, Context};

use rlox::interpreter::Interpreter;

fn main() -> Result<(), anyhow::Error> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    if args.len() > 0 {
        run_all_files(args)?;
    } else {
        run_prompt()?;
    }
    Ok(())
}

fn run_all_files(paths: Vec<String>) -> Result<(), anyhow::Error> {
    let mut interp_stdout = io::stdout();
    let mut interp = Interpreter::new(&mut interp_stdout);

    for p in &paths {
        let reader =
            BufReader::new(File::open(p).with_context(|| format!("failed to open {}", p))?);
        interp.eval(reader)?;
    }

    Ok(())
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
