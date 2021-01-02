//! A port to rust of the interpreters for the Lox language.
//!
//! See [Crafting Interpreters](https://craftinginterpreters.com/).
//!
//! # Examples
//!
//! See [`crate::interpreter::Interpreter`].
//!
//! # Limitations
//!
//! - The scanner and parser do not attempt any error recovery.  They bail out on the first
//! encountered error.
//! - The interpreter implements only a subset of Lox.
//! - ...

#![warn(rust_2018_idioms)]
#![warn(missing_debug_implementations)]

// TODO: eval: pass ref to Env rather than clone?
// TODO: implement for loop
// TODO: implement string

pub mod interpreter;

mod ast;
mod char_reader;
mod ctx;
mod diag;
mod eval;
mod interner;
mod parser;
mod scanner;
mod token;
