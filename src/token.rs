use std::fmt;

use crate::interner::Symbol;

/// "Words" produced by `Scanner`.
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Eof,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    LeftParen,
    RightParen,
    LeftCurly,
    RightCurly,
    Equal,
    EqualEqual,
    Bang,
    BangEqual,
    Less,
    Greater,
    Semicolon,
    Comma,

    // Keywords
    True,
    False,
    Print,
    Var,
    Nil,
    If,
    Else,
    While,
    Fun,
    Return,

    Identifier(Symbol),
    Number(f64),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Eof => write!(f, "EOF"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::LeftCurly => write!(f, "{{"),
            Token::RightCurly => write!(f, "}}"),
            Token::Equal => write!(f, "="),
            Token::EqualEqual => write!(f, "=="),
            Token::Bang => write!(f, "!"),
            Token::BangEqual => write!(f, "!="),
            Token::Less => write!(f, "<"),
            Token::Greater => write!(f, ">"),
            Token::Semicolon => write!(f, ";"),
            Token::Comma => write!(f, ","),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Print => write!(f, "print"),
            Token::Var => write!(f, "var"),
            Token::Nil => write!(f, "nil"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::Fun => write!(f, "fun"),
            Token::Return => write!(f, "return"),
            Token::Identifier(sym) => write!(f, "{}", sym),
            Token::Number(n) => write!(f, "{}", n),
        }
    }
}
