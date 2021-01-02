//! API to control the interpreter.

use std::error::Error;
use std::fmt;
use std::io::prelude::*;
use std::rc::Rc;

use crate::ctx::Context;
use crate::eval::{Evaluator, RuntimeError};
use crate::parser::{Parser, ParserError};

/// Tree-walk interpreter.
///
/// # Example
///
/// Invoke the interpreter a first time to define a function then additional times to call this
/// function:
///
/// ```
/// # use rlox::interpreter::{Interpreter, LoxError};
///
/// let mut output: Vec<u8> = Vec::new();
/// let mut interp = Interpreter::new(&mut output);
///
/// let func_def = r#"
///     fun max(x, y) {
///         if ( x > y) {
///             return x;
///         } else {
///             return y;
///         }
///     }
/// "#;
/// interp.eval(func_def.as_bytes())?;
///
/// interp.eval("print max(10,20);".as_bytes()).expect("interpreter error");
/// interp.eval("print max(5,4);".as_bytes()).expect("interpreter error");
///
/// assert_eq!(output, b"20\n5\n");
/// # Ok::<(), LoxError>(())
/// ```
#[derive(Debug)]
pub struct Interpreter<'t, W: Write> {
    ctx: Rc<Context>,
    evaluator: Evaluator<'t, W>,
}

/// Errors the interpreter can raise.
#[derive(Debug)]
pub enum LoxError {
    /// Error occurring during lexical or syntactic analysis.
    Parse(ParserError),

    /// Error occurring during evaluation.
    Runtime(RuntimeError),
}

impl fmt::Display for LoxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoxError::Runtime(e) => write!(f, "runtime error: {}", e),
            LoxError::Parse(e) => write!(f, "{}", e),
        }
    }
}

impl Error for LoxError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            LoxError::Runtime(e) => Some(e),
            LoxError::Parse(e) => Some(e),
        }
    }
}

impl From<RuntimeError> for LoxError {
    fn from(e: RuntimeError) -> LoxError {
        LoxError::Runtime(e)
    }
}

impl From<ParserError> for LoxError {
    fn from(e: ParserError) -> LoxError {
        LoxError::Parse(e)
    }
}

impl<W: Write> Interpreter<'_, W> {
    pub fn new(output: &mut W) -> Interpreter<'_, W> {
        // TODO: Context should be shared between Interpreter values and so be passed as a parameter.
        let ctx = Context::new();
        Interpreter {
            ctx: ctx.clone(),
            evaluator: Evaluator::new(output, ctx),
        }
    }

    pub fn eval<R: BufRead>(&mut self, input: R) -> Result<(), LoxError> {
        let mut parser = Parser::new(input, self.ctx.clone());
        let prg = parser.parse_program()?;
        self.evaluator.eval_stmts_in_global_env(&prg)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interpret(input: &str) -> Result<String, LoxError> {
        let mut raw_output: Vec<u8> = Vec::new();
        let mut interp = Interpreter::new(&mut raw_output);
        interp.eval(input.as_bytes())?;
        let output = String::from_utf8(raw_output).expect("cannot convert output to string");
        Ok(output)
    }

    #[test]
    fn print_expr() -> Result<(), LoxError> {
        assert_eq!(interpret("print 3*2;")?, "6\n");
        Ok(())
    }

    #[test]
    fn init_set_get_var() -> Result<(), LoxError> {
        assert_eq!(interpret("var foo=42; foo=24; print foo;")?, "24\n");
        Ok(())
    }

    #[test]
    fn block_with_shadowed_var() -> Result<(), LoxError> {
        assert_eq!(
            interpret("var foo=42; { var foo=24; print foo; } print foo; ")?,
            "24\n42\n"
        );
        Ok(())
    }

    #[test]
    fn block_accessing_var_in_parent_scope() -> Result<(), LoxError> {
        assert_eq!(interpret("var foo=42; { print foo; } ")?, "42\n");
        Ok(())
    }

    #[test]
    fn inc_var_declared_in_outer_block() -> Result<(), LoxError> {
        assert_eq!(
            interpret("var foo = 2; { foo = foo + 1; } print foo; ")?,
            "3\n"
        );
        Ok(())
    }

    #[test]
    fn var_from_parent_scope_shadowed_and_reset() -> Result<(), LoxError> {
        assert_eq!(
            interpret("var foo=42; { var foo = 1; foo = 1 + foo; print foo; } print foo;")?,
            "2\n42\n"
        );
        Ok(())
    }

    #[test]
    fn if_else() -> Result<(), LoxError> {
        assert_eq!(
            interpret("var foo; if (2 + 2 == 4) foo = 1; else foo = 2; print foo;")?,
            "1\n"
        );
        assert_eq!(
            interpret("var foo; if (2 + 2 != 4) foo = 1; else foo = 2; print foo;")?,
            "2\n"
        );
        Ok(())
    }

    #[test]
    fn null_stmt() -> Result<(), LoxError> {
        assert_eq!(interpret(";")?, "");
        Ok(())
    }

    #[test]
    fn declare_and_call_fn_without_param() -> Result<(), LoxError> {
        let prg = r#"
            fun f() {
                print 1;
            }
            f();
            f();
        "#;
        assert_eq!(interpret(prg)?, "1\n1\n");
        Ok(())
    }

    #[test]
    fn declare_and_call_fn_with_local_var() -> Result<(), LoxError> {
        let prg = r#"
            var v = 24;
            fun f() {
                var v = 42;
                print v;
            }
            f();
            print v;
        "#;
        assert_eq!(interpret(prg)?, "42\n24\n");
        Ok(())
    }

    #[test]
    fn declare_and_call_fn_with_arguments() -> Result<(), LoxError> {
        let prg = r#"
            fun add_and_print(x, y) {
                print x + y;
            }
            add_and_print(6, 4);
        "#;
        assert_eq!(interpret(prg)?, "10\n");
        Ok(())
    }

    #[test]
    fn declare_and_call_fn_with_return_stmts() -> Result<(), LoxError> {
        let prg = r#"
            fun max(x, y) {
                if ( x > y) {
                    return x;
                } else {
                    return y;
                }
                print 666; // can't happen
            }
            print max(10, 20);
        "#;
        assert_eq!(interpret(prg)?, "20\n");
        Ok(())
    }

    #[test]
    fn implicit_return_is_nil() -> Result<(), LoxError> {
        let prg = r#"
            fun f() {}
            print f();
        "#;
        assert_eq!(interpret(prg)?, "nil\n");
        Ok(())
    }

    #[test]
    fn while_stmt() -> Result<(), LoxError> {
        let prg = r#"
            var i = 0;
            while (i < 5) {
                print i;
                i = i + 1;
            }
        "#;
        assert_eq!(interpret(prg)?, "0\n1\n2\n3\n4\n");
        Ok(())
    }
}
