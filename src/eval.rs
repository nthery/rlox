use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io;
use std::io::prelude::*;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::ast::{Expr, Stmt};
use crate::ctx::Context;
use crate::interner::Symbol;

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Nil,
    Number(f64),
    Bool(bool),
    Function(Function),
}

#[derive(Clone)]
pub struct Function {
    name: Symbol,
    arity: usize,
    body: FunctionBody,
}

#[derive(Clone)]
enum FunctionBody {
    Builtin(fn(&[Value]) -> Result<Value, RuntimeError>),
    User(Vec<Symbol>, Box<Stmt>),
}

// TODO: dump builtin vs user
impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Function")
            .field("name", &self.name)
            .field("arity", &self.arity)
            .finish()
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Function {}

impl Value {
    pub fn is_truthy(self) -> bool {
        match self {
            Value::Nil => false,
            Value::Number(n) => n != 0.0,
            Value::Bool(b) => b,
            Value::Function(_) => true, // TODO: error out instead?
        }
    }
}

#[derive(Debug)]
pub struct Evaluator<'t, W: Write> {
    output: &'t mut W,
    globals: Rc<Env>,
    is_returning: Option<Value>,
}

#[derive(Debug)]
pub enum RuntimeError {
    DivByZero,
    TypeMismatch,
    UnknownVar(String),
    Io(io::Error),
    RedefinedVar(String),
    NotCallable,
    BadNumberOfArguments,
}

impl Error for RuntimeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            RuntimeError::DivByZero
            | RuntimeError::TypeMismatch
            | RuntimeError::UnknownVar(_)
            | RuntimeError::NotCallable
            | RuntimeError::BadNumberOfArguments
            | RuntimeError::RedefinedVar(_) => None,
            RuntimeError::Io(e) => Some(e),
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::DivByZero => write!(f, "division by zero"),
            RuntimeError::TypeMismatch => write!(f, "type mismatch"),
            RuntimeError::NotCallable => write!(f, "expression does not result in callable value"),
            RuntimeError::BadNumberOfArguments => write!(f, "bad number of arguments"),
            RuntimeError::UnknownVar(v) => write!(f, "unknown variable: {}", v),
            RuntimeError::Io(e) => write!(f, "I/O error: {}", e),
            RuntimeError::RedefinedVar(v) => write!(f, "Redefined variable: {}", v),
        }
    }
}

impl From<io::Error> for RuntimeError {
    fn from(e: io::Error) -> RuntimeError {
        RuntimeError::Io(e)
    }
}

impl Value {
    fn have_same_type(lhs: &Value, rhs: &Value) -> bool {
        match (lhs, rhs) {
            (Value::Number(_), Value::Number(_)) | (Value::Bool(_), Value::Bool(_)) => true,
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Function(func) => write!(f, "function {}/{}", func.name, func.arity),
        }
    }
}

impl<'a, W: Write> Evaluator<'a, W> {
    pub fn new(output: &'a mut W, ctx: Rc<Context>) -> Evaluator<'a, W> {
        let globals = Env::new();
        globals.add_builtin(&ctx.symbol("clock"), 0, builtin_clock);
        globals.add_builtin(&ctx.symbol("sqrt"), 1, builtin_sqrt);
        Evaluator {
            output,
            globals,
            is_returning: None,
        }
    }

    pub fn eval_stmts_in_global_env(&mut self, stmts: &Vec<Stmt>) -> Result<(), RuntimeError> {
        self.eval_stmts(stmts, self.globals.clone())?;
        Ok(())
    }

    fn eval_stmts(&mut self, stmts: &Vec<Stmt>, env: Rc<Env>) -> Result<(), RuntimeError> {
        for stmt in stmts {
            self.eval_stmt(stmt, env.clone())?
        }
        Ok(())
    }

    fn eval_stmt(&mut self, stmt: &Stmt, env: Rc<Env>) -> Result<(), RuntimeError> {
        if self.is_returning.is_some() {
            return Ok(());
        }

        match stmt {
            Stmt::Nop => (),
            Stmt::Expr(e) => {
                self.eval_expr(e, env)?;
            }
            Stmt::Print(e) => {
                let v = self.eval_expr(e, env)?;
                writeln!(self.output, "{}", v)?;
            }
            Stmt::VarDecl(sym, init) => {
                let expr = self.eval_expr(init, env.clone())?;
                env.set(sym, expr)?;
            }
            Stmt::FunDecl(name, params, body) => {
                // TODO: can we avoid copying all this?
                env.set(
                    name,
                    Value::Function(Function {
                        name: name.clone(),
                        arity: params.len(),
                        body: FunctionBody::User(params.clone(), body.clone()),
                    }),
                )?;
            }
            Stmt::Block(stmts) => {
                self.eval_stmts(stmts, Env::with_parent(Some(env)))?;
            }
            Stmt::If(cond, then_branch, else_branch) => {
                if self.eval_expr(cond, env.clone())?.is_truthy() {
                    self.eval_stmt(then_branch, env.clone())?;
                } else {
                    self.eval_stmt(else_branch, env.clone())?;
                }
            }
            Stmt::While(cond, body) => {
                while self.eval_expr(cond, env.clone())?.is_truthy() {
                    self.eval_stmt(body, env.clone())?;
                }
            }
            Stmt::Return(e) => {
                debug_assert!(self.is_returning.is_none());
                self.is_returning = Some(self.eval_expr(e, env.clone())?);
            }
        };
        Ok(())
    }

    // TODO: factor out match clauses
    fn eval_expr(&mut self, expr: &Expr, env: Rc<Env>) -> Result<Value, RuntimeError> {
        match expr {
            Expr::Nil => Ok(Value::Nil),
            Expr::Number(n) => Ok(Value::Number(*n)),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Var(sym) => {
                if let Some(val) = env.get(sym) {
                    Ok(val.clone())
                } else {
                    Err(RuntimeError::UnknownVar(sym.name().to_owned()))
                }
            }
            Expr::Not(expr) => {
                if let Value::Bool(b) = self.eval_expr(expr, env)? {
                    Ok(Value::Bool(!b))
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::UnaryMinus(expr) => {
                if let Value::Number(n) = self.eval_expr(expr, env)? {
                    Ok(Value::Number(-n))
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Add(lhs, rhs) => {
                if let (Value::Number(l), Value::Number(r)) = (
                    self.eval_expr(lhs, env.clone())?,
                    self.eval_expr(rhs, env.clone())?,
                ) {
                    Ok(Value::Number(l + r))
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Sub(lhs, rhs) => {
                if let (Value::Number(l), Value::Number(r)) = (
                    self.eval_expr(lhs, env.clone())?,
                    self.eval_expr(rhs, env.clone())?,
                ) {
                    Ok(Value::Number(l - r))
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Mul(lhs, rhs) => {
                if let (Value::Number(l), Value::Number(r)) = (
                    self.eval_expr(lhs, env.clone())?,
                    self.eval_expr(rhs, env.clone())?,
                ) {
                    Ok(Value::Number(l * r))
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Div(lhs, rhs) => {
                if let (Value::Number(l), Value::Number(r)) = (
                    self.eval_expr(lhs, env.clone())?,
                    self.eval_expr(rhs, env.clone())?,
                ) {
                    if r == 0.0 {
                        Err(RuntimeError::DivByZero)
                    } else {
                        Ok(Value::Number(l / r))
                    }
                } else {
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Equal(lhs, rhs) => {
                let l = self.eval_expr(lhs, env.clone())?;
                let r = self.eval_expr(rhs, env.clone())?;
                if Value::have_same_type(&l, &r) {
                    Ok(Value::Bool(l == r))
                } else {
                    Ok(Value::Bool(false))
                }
            }
            Expr::NotEqual(lhs, rhs) => {
                let l = self.eval_expr(lhs, env.clone())?;
                let r = self.eval_expr(rhs, env.clone())?;
                if Value::have_same_type(&l, &r) {
                    Ok(Value::Bool(l != r))
                } else {
                    Ok(Value::Bool(true))
                }
            }
            Expr::Less(lhs, rhs) => {
                let l = self.eval_expr(lhs, env.clone())?;
                let r = self.eval_expr(rhs, env.clone())?;
                if let (Value::Number(ln), Value::Number(rn)) = (l, r) {
                    Ok(Value::Bool(ln < rn))
                } else {
                    // TODO: allow comparison on more Value flavors
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Greater(lhs, rhs) => {
                let l = self.eval_expr(lhs, env.clone())?;
                let r = self.eval_expr(rhs, env.clone())?;
                if let (Value::Number(ln), Value::Number(rn)) = (l, r) {
                    Ok(Value::Bool(ln > rn))
                } else {
                    // TODO: allow comparison on more Value flavors
                    Err(RuntimeError::TypeMismatch)
                }
            }
            Expr::Group(e) => self.eval_expr(e, env),
            Expr::Assign(sym, rhs) => {
                let res = self.eval_expr(rhs, env.clone())?;
                env.reset(sym, res.clone())?;
                Ok(res)
            }
            Expr::Call(callee, args) => {
                let c = self.eval_expr(callee, env.clone())?;
                let evaluated_args = args
                    .iter()
                    .map(|a| self.eval_expr(a, env.clone()))
                    .collect::<Result<Vec<Value>, RuntimeError>>()?;
                match c {
                    Value::Function(f) => {
                        if evaluated_args.len() == f.arity {
                            match f.body {
                                FunctionBody::Builtin(pfn) => (pfn)(&evaluated_args),
                                FunctionBody::User(params, stmt) => {
                                    // TODO: should args be in same env as body scope?
                                    let arg_env = Env::with_parent(Some(env.clone()));
                                    for (p, v) in params.iter().zip(evaluated_args.into_iter()) {
                                        arg_env.set(p, v)?;
                                    }
                                    self.eval_stmt(&stmt, arg_env)?;
                                    let code = if let Some(code) = self.is_returning.take() {
                                        code
                                    } else {
                                        Value::Nil
                                    };
                                    Ok(code)
                                }
                            }
                        } else {
                            Err(RuntimeError::BadNumberOfArguments)
                        }
                    }
                    _ => Err(RuntimeError::NotCallable),
                }
            }
        }
    }
}

fn builtin_clock(_args: &[Value]) -> Result<Value, RuntimeError> {
    Ok(Value::Number(
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("error when getting current time")
            .as_secs_f64(),
    ))
}

fn builtin_sqrt(args: &[Value]) -> Result<Value, RuntimeError> {
    if let Value::Number(n) = args[0] {
        Ok(Value::Number(n.sqrt()))
    } else {
        Err(RuntimeError::TypeMismatch)
    }
}

#[derive(Debug)]
struct Env {
    parent: Option<Rc<Env>>,
    bindings: RefCell<HashMap<Symbol, Value>>,
}

impl Env {
    fn new() -> Rc<Env> {
        Self::with_parent(None)
    }

    fn with_parent(parent: Option<Rc<Env>>) -> Rc<Env> {
        Rc::new(Env {
            parent,
            bindings: RefCell::new(HashMap::new()),
        })
    }

    fn set(&self, sym: &Symbol, val: Value) -> Result<(), RuntimeError> {
        if let Entry::Vacant(entry) = self.bindings.borrow_mut().entry(sym.clone()) {
            entry.insert(val);
            Ok(())
        } else {
            Err(RuntimeError::RedefinedVar(sym.name().to_owned()))
        }
    }

    fn reset(&self, sym: &Symbol, val: Value) -> Result<(), RuntimeError> {
        if let Entry::Occupied(mut entry) = self.bindings.borrow_mut().entry(sym.clone()) {
            entry.insert(val);
            Ok(())
        } else {
            if let Some(parent) = self.parent.as_ref() {
                parent.reset(sym, val)
            } else {
                Err(RuntimeError::UnknownVar(sym.name().to_owned()))
            }
        }
    }

    fn get(&self, sym: &Symbol) -> Option<Value> {
        match self.bindings.borrow().get(sym) {
            Some(v) => Some(v.clone()),
            None => self.parent.as_ref().and_then(|p| p.get(sym)),
        }
    }

    fn add_builtin(
        &self,
        name: &Symbol,
        arity: usize,
        body: fn(&[Value]) -> Result<Value, RuntimeError>,
    ) {
        self.set(
            name,
            Value::Function(Function {
                name: name.clone(),
                arity,
                body: FunctionBody::Builtin(body),
            }),
        )
        .expect("error when binding builtin function");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval_expr(expr: &Expr) -> Result<Value, RuntimeError> {
        let mut out: Vec<u8> = Vec::new();
        let ctx = Context::new();
        let mut evaluator = Evaluator::new(&mut out, ctx);
        let globals = evaluator.globals.clone();
        let val = evaluator.eval_expr(expr, globals)?;
        assert!(out.is_empty());
        Ok(val)
    }

    fn eval_prg(prg: &Vec<Stmt>) -> Result<String, RuntimeError> {
        let ctx = Context::new();
        eval_prg_with_ctx(ctx, prg)
    }

    fn eval_prg_with_ctx(ctx: Rc<Context>, prg: &Vec<Stmt>) -> Result<String, RuntimeError> {
        let mut out: Vec<u8> = Vec::new();
        let mut e = Evaluator::new(&mut out, ctx.clone());
        e.globals
            .add_builtin(&ctx.symbol("__test_ultimate_answer__"), 0, |_| {
                Ok(Value::Number(42.0))
            });
        e.globals
            .add_builtin(&ctx.symbol("__test_min__"), 2, |args| {
                match (&args[0], &args[1]) {
                    (Value::Number(l), Value::Number(r)) => {
                        Ok(Value::Number(if *l <= *r { *l } else { *r }))
                    }
                    _ => Err(RuntimeError::TypeMismatch),
                }
            });
        e.eval_stmts_in_global_env(prg)?;
        Ok(String::from_utf8(out).expect("error while converting output"))
    }

    #[test]
    fn number() -> Result<(), RuntimeError> {
        assert_eq!(eval_expr(&Expr::Number(1.0))?, Value::Number(1.0));
        Ok(())
    }

    #[test]
    fn unary_minus() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::UnaryMinus(Box::new(Expr::Number(1.0))))?,
            Value::Number(-1.0)
        );
        Ok(())
    }

    #[test]
    fn logical_not() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Not(Box::new(Expr::Bool(true))))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn unary_minus_on_bool() {
        match eval_expr(&Expr::UnaryMinus(Box::new(Expr::Bool(true)))) {
            Err(RuntimeError::TypeMismatch) => (),
            out => panic!("unexpected output: {:?}", out),
        }
    }

    #[test]
    fn subtraction() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Sub(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Number(3.0))
            ))?,
            Value::Number(-2.0)
        );
        Ok(())
    }

    #[test]
    fn division() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Div(
                Box::new(Expr::Number(6.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Number(3.0)
        );
        Ok(())
    }

    #[test]
    fn division_by_zero() {
        match eval_expr(&Expr::Div(
            Box::new(Expr::Number(6.0)),
            Box::new(Expr::Number(0.0)),
        )) {
            Err(RuntimeError::DivByZero) => (),
            out => panic!("unexpected output: {:?}", out),
        }
    }

    #[test]
    fn nested_arithmetic() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Add(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Number(3.0))
                ))
            ))?,
            Value::Number(7.0)
        );
        Ok(())
    }

    #[test]
    fn number_equality() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Equal(
                Box::new(Expr::Number(6.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(false)
        );
        assert_eq!(
            eval_expr(&Expr::Equal(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn bool_equality() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Equal(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Bool(false))
            ))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn number_inequality() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::NotEqual(
                Box::new(Expr::Number(6.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(true)
        );
        assert_eq!(
            eval_expr(&Expr::NotEqual(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn bool_inequality() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::NotEqual(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Bool(false))
            ))?,
            Value::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn number_less() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Less(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(true)
        );
        assert_eq!(
            eval_expr(&Expr::Less(
                Box::new(Expr::Number(2.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn number_greater() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Greater(
                Box::new(Expr::Number(3.0)),
                Box::new(Expr::Number(2.0))
            ))?,
            Value::Bool(true)
        );
        assert_eq!(
            eval_expr(&Expr::Less(
                Box::new(Expr::Number(3.0)),
                Box::new(Expr::Number(3.0))
            ))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn different_types_are_always_different() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Equal(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Number(1.0))
            ))?,
            Value::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn nested_equality() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_expr(&Expr::Equal(
                Box::new(Expr::NotEqual(
                    Box::new(Expr::Number(3.0)),
                    Box::new(Expr::Number(1.0))
                )),
                Box::new(Expr::NotEqual(
                    Box::new(Expr::Number(2.5)),
                    Box::new(Expr::Number(5.2))
                ))
            ))?,
            Value::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn print_stmt() -> Result<(), RuntimeError> {
        assert_eq!(
            eval_prg(&vec![Stmt::Print(Box::new(Expr::Number(42.0)))])?,
            "42\n"
        );
        Ok(())
    }

    #[test]
    fn set_and_get_var() -> Result<(), RuntimeError> {
        let ctx = Context::new();
        assert_eq!(
            eval_prg_with_ctx(
                ctx.clone(),
                &vec![
                    Stmt::VarDecl(ctx.symbol("foo"), Box::new(Expr::Number(42.0))),
                    Stmt::Print(Box::new(Expr::Var(ctx.symbol("foo"))))
                ]
            )?,
            "42\n"
        );
        Ok(())
    }

    #[test]
    fn set_unknown_var() {
        let ctx = Context::new();
        let foo_sym = ctx.symbol("foo");
        match eval_prg_with_ctx(
            ctx,
            &vec![Stmt::Expr(Box::new(Expr::Assign(
                foo_sym.clone(),
                Box::new(Expr::Number(42.0)),
            )))],
        ) {
            Err(RuntimeError::UnknownVar(sym)) if sym == foo_sym.name() => (),
            out => panic!("unexpected output: {:?}", out),
        }
    }

    #[test]
    fn declare_variable_twice() {
        let ctx = Context::new();
        let foo_sym = ctx.symbol("foo");
        match eval_prg_with_ctx(
            ctx,
            &vec![
                Stmt::VarDecl(foo_sym.clone(), Box::new(Expr::Number(42.0))),
                Stmt::VarDecl(foo_sym.clone(), Box::new(Expr::Number(24.0))),
                Stmt::Print(Box::new(Expr::Var(foo_sym.clone()))),
            ],
        ) {
            Err(RuntimeError::RedefinedVar(sym)) if sym == foo_sym.name() => (),
            out => panic!("unexpected output: {:?}", out),
        }
    }

    #[test]
    fn call_builtin_function_without_arg() -> Result<(), RuntimeError> {
        let ctx = Context::new();
        let ultimate_answer_sym = ctx.symbol("__test_ultimate_answer__");
        assert_eq!(
            eval_prg_with_ctx(
                ctx,
                &vec![Stmt::Print(Box::new(Expr::Call(
                    Box::new(Expr::Var(ultimate_answer_sym.clone())),
                    vec![]
                ))),],
            )?,
            "42\n"
        );
        Ok(())
    }

    #[test]
    fn call_function_with_bad_number_of_arguments() {
        let ctx = Context::new();
        let ultimate_answer_sym = ctx.symbol("__test_ultimate_answer__");
        match eval_prg_with_ctx(
            ctx,
            &vec![Stmt::Print(Box::new(Expr::Call(
                Box::new(Expr::Var(ultimate_answer_sym.clone())),
                vec![Expr::Bool(true)],
            )))],
        ) {
            Err(RuntimeError::BadNumberOfArguments) => (),
            out => panic!("unexpected output: {:?}", out),
        }
    }

    #[test]
    fn call_builtin_sqrt() -> Result<(), RuntimeError> {
        let ctx = Context::new();
        assert_eq!(
            eval_prg_with_ctx(
                ctx.clone(),
                &vec![Stmt::Print(Box::new(Expr::Call(
                    Box::new(Expr::Var(ctx.symbol("sqrt"))),
                    vec![Expr::Number(4.0)]
                ))),],
            )?,
            "2\n"
        );
        Ok(())
    }

    #[test]
    fn call_builtin_function_with_several_args() -> Result<(), RuntimeError> {
        let ctx = Context::new();
        let min_sym = ctx.symbol("__test_min__");
        assert_eq!(
            eval_prg_with_ctx(
                ctx,
                &vec![Stmt::Print(Box::new(Expr::Call(
                    Box::new(Expr::Var(min_sym.clone())),
                    vec![Expr::Number(2.0), Expr::Number(1.0)]
                )))],
            )?,
            "1\n"
        );
        Ok(())
    }
}
