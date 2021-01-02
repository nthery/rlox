use crate::interner::Symbol;

// TODO: Clone added to support Value::UserFunction: take ref instead?
// TODO: do we really need to box Expr?
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    Nop,
    Expr(Box<Expr>),
    Print(Box<Expr>),
    VarDecl(Symbol, Box<Expr>),
    FunDecl(Symbol, Vec<Symbol>, Box<Stmt>),
    Block(Vec<Stmt>),
    If(Box<Expr>, Box<Stmt>, Box<Stmt>),
    While(Box<Expr>, Box<Stmt>),
    Return(Box<Expr>),
}

// TODO: Clone added to support Value::UserFunction: take ref instead?
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Nil,
    Number(f64),
    Bool(bool),
    Var(Symbol),
    UnaryMinus(Box<Expr>),
    Equal(Box<Expr>, Box<Expr>),
    NotEqual(Box<Expr>, Box<Expr>),
    Less(Box<Expr>, Box<Expr>),
    Greater(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Group(Box<Expr>),
    Assign(Symbol, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
}
