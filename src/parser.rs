use std::error::Error;
use std::fmt;
use std::io::prelude::*;
use std::rc::Rc;

use crate::ast::{Expr, Stmt};
use crate::ctx::Context;
use crate::diag::{FullParseError, ParseError, Position};
use crate::interner::Symbol;
use crate::scanner::{Scanner, ScannerError};
use crate::token::Token;

#[derive(Debug)]
pub enum ParserError {
    Parse(FullParseError),
    ReadError(Box<dyn Error + Send + Sync>),
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserError::Parse(e) => write!(f, "{}", e),
            ParserError::ReadError(e) => write!(f, "read error: {}", e),
        }
    }
}

impl Error for ParserError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParserError::Parse(_) => None,
            ParserError::ReadError(e) => Some(e.as_ref()),
        }
    }
}

impl From<ScannerError> for ParserError {
    fn from(e: ScannerError) -> ParserError {
        match e {
            ScannerError::CharReader(e) => ParserError::ReadError(Box::new(e)),
            ScannerError::Parse(d) => ParserError::Parse(d),
        }
    }
}

pub struct Parser<R: BufRead> {
    scanner: Scanner<R>,
    current_token: Token,
    current_pos: Position,
}

impl<R: BufRead> Parser<R> {
    pub fn new(input: R, ctx: Rc<Context>) -> Parser<R> {
        Parser {
            scanner: Scanner::new(input, ctx),
            current_token: Token::Eof, // we haven't scanned anything yet
            current_pos: 1,
        }
    }

    pub fn parse_program(&mut self) -> Result<Vec<Stmt>, ParserError> {
        self.parse_program_body()
    }

    fn parse_program_body(&mut self) -> Result<Vec<Stmt>, ParserError> {
        let mut prg = vec![];
        self.advance()?;
        loop {
            match self.current_token {
                Token::Eof => break,
                _ => prg.push(self.declaration()?),
            }
        }
        Ok(prg)
    }

    #[allow(dead_code)]
    fn parse_expression(&mut self) -> Result<Expr, ParserError> {
        self.parse_expression_body()
    }

    fn parse_expression_body(&mut self) -> Result<Expr, ParserError> {
        self.advance()?;
        self.expression()
    }

    fn declaration(&mut self) -> Result<Stmt, ParserError> {
        let stmt = match self.current_token {
            Token::Var => self.var_decl()?,
            Token::Fun => self.fun_decl()?,
            _ => self.statement()?,
        };
        Ok(stmt)
    }

    /// Parse variable declaration.
    /// Current token is Token.Var.
    fn var_decl(&mut self) -> Result<Stmt, ParserError> {
        self.advance()?;
        match self.current_token.clone() {
            Token::Identifier(sym) => {
                self.advance()?;
                let init = match self.current_token {
                    Token::Equal => {
                        self.advance()?;
                        self.expression()?
                    }
                    _ => Expr::Nil,
                };
                self.consume(Token::Semicolon)?;
                Ok(Stmt::VarDecl(sym.clone(), Box::new(init)))
            }
            _ => todo!(),
        }
    }

    fn fun_decl(&mut self) -> Result<Stmt, ParserError> {
        self.advance()?;
        let name = self.identifier()?;
        self.consume(Token::LeftParen)?;
        let mut params = vec![];
        if Token::RightParen != self.current_token {
            loop {
                params.push(self.identifier()?);
                if Token::Comma != self.current_token {
                    break;
                }
                self.consume(Token::Comma)?;
            }
        }
        self.consume(Token::RightParen)?;
        let body = self.block()?;
        Ok(Stmt::FunDecl(name, params, Box::new(body)))
    }

    fn identifier(&mut self) -> Result<Symbol, ParserError> {
        // TODO: can we avoid cloning tokens?
        if let Token::Identifier(id) = self.current_token.clone() {
            self.advance()?;
            Ok(id)
        } else {
            Err(ParserError::Parse(FullParseError {
                pos: self.current_pos,
                error: ParseError::ExpectedIdentifier,
            }))
        }
    }

    fn statement(&mut self) -> Result<Stmt, ParserError> {
        match self.current_token {
            Token::Print => {
                self.advance()?;
                let expr = Box::new(self.expression()?);
                self.consume(Token::Semicolon)?;
                Ok(Stmt::Print(expr))
            }
            Token::LeftCurly => self.block(),
            Token::If => {
                self.advance()?;
                self.consume(Token::LeftParen)?;
                let cond = Box::new(self.expression()?);
                self.consume(Token::RightParen)?;
                let then_branch = Box::new(self.statement()?);
                let else_branch = if let Token::Else = self.current_token {
                    self.advance()?;
                    Box::new(self.statement()?)
                } else {
                    Box::new(Stmt::Nop)
                };
                Ok(Stmt::If(cond, then_branch, else_branch))
            }
            Token::While => {
                self.advance()?;
                self.consume(Token::LeftParen)?;
                let cond = Box::new(self.expression()?);
                self.consume(Token::RightParen)?;
                let body = Box::new(self.statement()?);
                Ok(Stmt::While(cond, body))
            }
            Token::Semicolon => {
                self.advance()?;
                Ok(Stmt::Nop)
            }
            Token::Return => {
                self.advance()?;
                let ret_expr = if self.current_token == Token::Semicolon {
                    Expr::Nil
                } else {
                    self.expression()?
                };
                self.consume(Token::Semicolon)?;
                Ok(Stmt::Return(Box::new(ret_expr)))
            }
            _ => {
                let expr = Box::new(self.expression()?);
                self.consume(Token::Semicolon)?;
                Ok(Stmt::Expr(expr))
            }
        }
    }

    fn block(&mut self) -> Result<Stmt, ParserError> {
        self.consume(Token::LeftCurly)?;
        let mut stmts = vec![];
        loop {
            match self.current_token {
                Token::RightCurly => {
                    self.advance()?;
                    break;
                }
                _ => stmts.push(self.declaration()?),
            }
        }
        Ok(Stmt::Block(stmts))
    }

    fn expression(&mut self) -> Result<Expr, ParserError> {
        self.assignment()
    }

    fn assignment(&mut self) -> Result<Expr, ParserError> {
        let lhs = self.equality()?;
        if Token::Equal == self.current_token {
            self.advance()?;
            let rhs = self.assignment()?;
            if let Expr::Var(var) = lhs {
                Ok(Expr::Assign(var, Box::new(rhs)))
            } else {
                Err(ParserError::Parse(FullParseError {
                    pos: self.current_pos,
                    error: ParseError::ExpectedLvalue,
                }))
            }
        } else {
            Ok(lhs)
        }
    }

    fn equality(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.comparison()?;
        loop {
            match self.current_token {
                Token::EqualEqual => {
                    self.advance()?;
                    expr = Expr::Equal(Box::new(expr), Box::new(self.comparison()?));
                }
                Token::BangEqual => {
                    self.advance()?;
                    expr = Expr::NotEqual(Box::new(expr), Box::new(self.comparison()?));
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.term()?;
        // TODO: should it really be a loop here?  2 < 3 < 4 does not make much sense does it?
        loop {
            match self.current_token {
                Token::Less => {
                    self.advance()?;
                    expr = Expr::Less(Box::new(expr), Box::new(self.term()?));
                }
                Token::Greater => {
                    self.advance()?;
                    expr = Expr::Greater(Box::new(expr), Box::new(self.term()?));
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn term(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.factor()?;
        loop {
            match self.current_token {
                Token::Plus => {
                    self.advance()?;
                    expr = Expr::Add(Box::new(expr), Box::new(self.factor()?));
                }
                Token::Minus => {
                    self.advance()?;
                    expr = Expr::Sub(Box::new(expr), Box::new(self.factor()?));
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn factor(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.unary()?;
        loop {
            match self.current_token {
                Token::Star => {
                    self.advance()?;
                    expr = Expr::Mul(Box::new(expr), Box::new(self.unary()?));
                }
                Token::Slash => {
                    self.advance()?;
                    expr = Expr::Div(Box::new(expr), Box::new(self.unary()?));
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn unary(&mut self) -> Result<Expr, ParserError> {
        match self.current_token {
            Token::Minus => {
                self.advance()?;
                Ok(Expr::UnaryMinus(Box::new(self.unary()?)))
            }
            _ => self.call(),
        }
    }

    fn call(&mut self) -> Result<Expr, ParserError> {
        let expr = self.primary()?;
        if let Token::LeftParen = self.current_token {
            self.advance()?;
            let mut args = vec![];
            if Token::RightParen != self.current_token {
                loop {
                    args.push(self.expression()?);
                    if Token::Comma != self.current_token {
                        break;
                    }
                    self.consume(Token::Comma)?;
                }
            }
            self.consume(Token::RightParen)?;
            Ok(Expr::Call(Box::new(expr), args))
        } else {
            Ok(expr)
        }
    }

    fn primary(&mut self) -> Result<Expr, ParserError> {
        match self.current_token.clone() {
            Token::Identifier(sym) => {
                let expr = Expr::Var(sym);
                self.advance()?;
                Ok(expr)
            }
            Token::Nil => {
                self.advance()?;
                Ok(Expr::Nil)
            }
            Token::Number(n) => {
                let expr = Expr::Number(n);
                self.advance()?;
                Ok(expr)
            }
            Token::True => {
                self.advance()?;
                Ok(Expr::Bool(true))
            }
            Token::False => {
                self.advance()?;
                Ok(Expr::Bool(false))
            }
            Token::LeftParen => {
                self.advance()?;
                let expr = self.expression()?;
                self.consume(Token::RightParen)?;
                Ok(Expr::Group(Box::new(expr)))
            }
            _ => Err(ParserError::Parse(FullParseError {
                pos: self.current_pos,
                error: ParseError::ExpectedPrimary,
            })),
        }
    }

    fn advance(&mut self) -> Result<&Token, ParserError> {
        let (pos, token) = self.scanner.get_token()?;
        self.current_token = token;
        self.current_pos = pos;
        Ok(&self.current_token)
    }

    fn consume(&mut self, expected: Token) -> Result<(), ParserError> {
        if self.current_token == expected {
            self.advance()?;
            Ok(())
        } else {
            Err(ParserError::Parse(FullParseError {
                pos: self.current_pos,
                error: ParseError::UnexpectedToken(
                    self.current_token.to_string(),
                    expected.to_string(),
                ),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr(input: &str) -> Result<Expr, ParserError> {
        let ctx = Context::new();
        parse_expr_with_ctx(ctx, input)
    }

    fn parse_expr_with_ctx(ctx: Rc<Context>, input: &str) -> Result<Expr, ParserError> {
        let mut parser = Parser::new(input.as_bytes(), ctx);
        parser.parse_expression()
    }

    fn parse_prg(input: &str) -> Result<Vec<Stmt>, ParserError> {
        let ctx = Context::new();
        parse_prg_with_ctx(ctx, input)
    }

    fn parse_prg_with_ctx(ctx: Rc<Context>, input: &str) -> Result<Vec<Stmt>, ParserError> {
        let mut parser = Parser::new(input.as_bytes(), ctx);
        parser.parse_program()
    }

    #[test]
    fn number() -> Result<(), ParserError> {
        assert_eq!(parse_expr("42")?, Expr::Number(42.0));
        Ok(())
    }

    #[test]
    fn bool_literals() -> Result<(), ParserError> {
        assert_eq!(parse_expr("true")?, Expr::Bool(true));
        assert_eq!(parse_expr("false")?, Expr::Bool(false));
        Ok(())
    }

    #[test]
    fn unary_minus() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("--42")?,
            Expr::UnaryMinus(Box::new(Expr::UnaryMinus(Box::new(Expr::Number(42.0)))))
        );
        Ok(())
    }

    #[test]
    fn addition() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 + 24")?,
            Expr::Add(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn subtraction() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 - 24")?,
            Expr::Sub(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn addition_is_left_associative() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("1 + 2 + 3")?,
            Expr::Add(
                Box::new(Expr::Add(
                    Box::new(Expr::Number(1.0)),
                    Box::new(Expr::Number(2.0))
                )),
                Box::new(Expr::Number(3.0))
            )
        );
        Ok(())
    }

    #[test]
    fn multiplication() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 * 24")?,
            Expr::Mul(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn division() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 / 24")?,
            Expr::Div(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn factors_have_precedence_over_terms() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("1 + 2 * 3")?,
            Expr::Add(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Number(3.0))
                )),
            )
        );
        Ok(())
    }

    #[test]
    fn braced_expr_takes_precedence() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("1 * (2 + 3)")?,
            Expr::Mul(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Group(Box::new(Expr::Add(
                    Box::new(Expr::Number(2.0)),
                    Box::new(Expr::Number(3.0))
                ))))
            ),
        );
        Ok(())
    }

    #[test]
    fn missing_right_paren() {
        match parse_expr("(1") {
            Err(ParserError::Parse(FullParseError { pos, error }))
                if pos == 1
                    && error == ParseError::UnexpectedToken("EOF".to_string(), ")".to_string()) =>
            {
                ()
            }
            r => panic!("unexpected output: {:?}", r),
        }
    }

    #[test]
    fn equality() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 == 24")?,
            Expr::Equal(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn inequality() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 != 24")?,
            Expr::NotEqual(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn less_than() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 < 24")?,
            Expr::Less(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn greater_than() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("42 > 24")?,
            Expr::Greater(Box::new(Expr::Number(42.0)), Box::new(Expr::Number(24.0)))
        );
        Ok(())
    }

    #[test]
    fn equality_is_left_associative() -> Result<(), ParserError> {
        assert_eq!(
            parse_expr("1 == 2 == 3")?,
            Expr::Equal(
                Box::new(Expr::Equal(
                    Box::new(Expr::Number(1.0)),
                    Box::new(Expr::Number(2.0))
                )),
                Box::new(Expr::Number(3.0))
            )
        );
        Ok(())
    }

    #[test]
    fn expr_stmts() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("1; 1+2;")?,
            vec![
                Stmt::Expr(Box::new(Expr::Number(1.0))),
                Stmt::Expr(Box::new(Expr::Add(
                    Box::new(Expr::Number(1.0)),
                    Box::new(Expr::Number(2.0))
                )))
            ]
        );
        Ok(())
    }

    #[test]
    fn print_stmt() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("print 1+2;")?,
            vec![Stmt::Print(Box::new(Expr::Add(
                Box::new(Expr::Number(1.0)),
                Box::new(Expr::Number(2.0))
            )))]
        );
        Ok(())
    }

    #[test]
    fn var_decl() -> Result<(), ParserError> {
        let ctx = Context::new();
        let sym_foo = ctx.symbol("foo");
        let sym_bar = ctx.symbol("bar");
        assert_eq!(
            parse_prg_with_ctx(ctx, "var foo; var bar = 2 * 3.14;")?,
            vec![
                Stmt::VarDecl(sym_foo, Box::new(Expr::Nil)),
                Stmt::VarDecl(
                    sym_bar,
                    Box::new(Expr::Mul(
                        Box::new(Expr::Number(2.0)),
                        Box::new(Expr::Number(3.14))
                    ))
                )
            ]
        );
        Ok(())
    }

    #[test]
    fn expr_with_variables() -> Result<(), ParserError> {
        let ctx = Context::new();
        let sym_a = ctx.symbol("a");
        let sym_b = ctx.symbol("b");
        assert_eq!(
            parse_expr_with_ctx(ctx, "a!=b")?,
            Expr::NotEqual(Box::new(Expr::Var(sym_a)), Box::new(Expr::Var(sym_b)))
        );
        Ok(())
    }

    #[test]
    fn simple_assignment() -> Result<(), ParserError> {
        let ctx = Context::new();
        let sym_a = ctx.symbol("a");
        let sym_b = ctx.symbol("b");
        assert_eq!(
            parse_expr_with_ctx(ctx, "a = b")?,
            Expr::Assign(sym_a, Box::new(Expr::Var(sym_b)))
        );
        Ok(())
    }

    #[test]
    fn complex_assignment() -> Result<(), ParserError> {
        let ctx = Context::new();
        let sym_a = ctx.symbol("a");
        let sym_b = ctx.symbol("b");
        assert_eq!(
            parse_expr_with_ctx(ctx, "a = b = 1")?,
            Expr::Assign(
                sym_a,
                Box::new(Expr::Assign(sym_b, Box::new(Expr::Number(1.0))))
            )
        );
        Ok(())
    }

    #[test]
    fn bad_assignment_lhs() {
        match parse_expr("(1+a=b") {
            Err(ParserError::Parse(FullParseError { pos, error }))
                if pos == 1 && error == ParseError::ExpectedLvalue =>
            {
                ()
            }
            r => panic!("unexpected output: {:?}", r),
        }
    }

    #[test]
    fn empty_block() -> Result<(), ParserError> {
        assert_eq!(parse_prg("{ }")?, vec![Stmt::Block(vec![])]);
        Ok(())
    }

    #[test]
    fn block_with_single_stmt() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("{ 1; }")?,
            vec![Stmt::Block(vec![Stmt::Expr(Box::new(Expr::Number(1.0))),])]
        );
        Ok(())
    }

    #[test]
    fn block_with_many_stmts() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("{ 1; 2; }")?,
            vec![Stmt::Block(vec![
                Stmt::Expr(Box::new(Expr::Number(1.0))),
                Stmt::Expr(Box::new(Expr::Number(2.0))),
            ])]
        );
        Ok(())
    }

    #[test]
    fn if_stmt() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("if (true) 1;")?,
            vec![Stmt::If(
                Box::new(Expr::Bool(true)),
                Box::new(Stmt::Expr(Box::new(Expr::Number(1.0)))),
                Box::new(Stmt::Nop)
            )]
        );
        Ok(())
    }

    #[test]
    fn return_stmt_without_expr() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("return;")?,
            vec![Stmt::Return(Box::new(Expr::Nil))]
        );
        Ok(())
    }

    #[test]
    fn return_stmt_with_expr() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("return false;")?,
            vec![Stmt::Return(Box::new(Expr::Bool(false)))]
        );
        Ok(())
    }

    #[test]
    fn if_else_stmt() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("if (true) 1; else 2;")?,
            vec![Stmt::If(
                Box::new(Expr::Bool(true)),
                Box::new(Stmt::Expr(Box::new(Expr::Number(1.0)))),
                Box::new(Stmt::Expr(Box::new(Expr::Number(2.0)))),
            )]
        );
        Ok(())
    }

    #[test]
    fn while_stmt() -> Result<(), ParserError> {
        assert_eq!(
            parse_prg("while (true) 1;")?,
            vec![Stmt::While(
                Box::new(Expr::Bool(true)),
                Box::new(Stmt::Expr(Box::new(Expr::Number(1.0)))),
            )]
        );
        Ok(())
    }

    #[test]
    fn fn_call_without_argument() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "foo();")?,
            vec![Stmt::Expr(Box::new(Expr::Call(
                Box::new(Expr::Var(ctx.symbol("foo"))),
                vec![]
            )))]
        );
        Ok(())
    }

    #[test]
    fn fn_call_with_one_argument() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "foo(1);")?,
            vec![Stmt::Expr(Box::new(Expr::Call(
                Box::new(Expr::Var(ctx.symbol("foo"))),
                vec![Expr::Number(1.0)]
            )))]
        );
        Ok(())
    }

    #[test]
    fn fn_call_with_several_arguments() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "foo(1, false);")?,
            vec![Stmt::Expr(Box::new(Expr::Call(
                Box::new(Expr::Var(ctx.symbol("foo"))),
                vec![Expr::Number(1.0), Expr::Bool(false)]
            )))]
        );
        Ok(())
    }

    #[test]
    fn declare_fn_without_argument() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "fun foo() { true; }")?,
            vec![Stmt::FunDecl(
                ctx.symbol("foo"),
                vec![],
                Box::new(Stmt::Block(vec![Stmt::Expr(Box::new(Expr::Bool(true)))]))
            )]
        );
        Ok(())
    }

    #[test]
    fn declare_fn_with_one_argument() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "fun foo(a) { true; }")?,
            vec![Stmt::FunDecl(
                ctx.symbol("foo"),
                vec![ctx.symbol("a")],
                Box::new(Stmt::Block(vec![Stmt::Expr(Box::new(Expr::Bool(true)))]))
            )]
        );
        Ok(())
    }

    #[test]
    fn declare_fn_with_two_arguments() -> Result<(), ParserError> {
        let ctx = Context::new();
        assert_eq!(
            parse_prg_with_ctx(ctx.clone(), "fun foo(a, b) { true; }")?,
            vec![Stmt::FunDecl(
                ctx.symbol("foo"),
                vec![ctx.symbol("a"), ctx.symbol("b")],
                Box::new(Stmt::Block(vec![Stmt::Expr(Box::new(Expr::Bool(true)))]))
            )]
        );
        Ok(())
    }
}
