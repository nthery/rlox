//! Lexical analyzer

use std::error::Error;
use std::fmt;
use std::io::prelude::*;
use std::iter::Peekable;
use std::rc::Rc;

use crate::char_reader::{CharReader, CharReaderError};
use crate::ctx::Context;
use crate::diag::{FullParseError, ParseError, Position};
use crate::token::Token;

/// Turn sequence of bytes into sequence of tokens.
pub struct Scanner<R: BufRead> {
    input: Peekable<CharReader<R>>,
    line: Position,
    ctx: Rc<Context>,

    // Buffer used when scanning longer tokens.  Allocated here to reuse memory.
    buf: String,
}

impl<R: BufRead> Scanner<R> {
    /// Creates a new scanner operating on `input`.
    pub fn new(input: R, ctx: Rc<Context>) -> Scanner<R> {
        Scanner {
            input: CharReader::new(input).peekable(),
            line: 1,
            ctx,
            buf: String::new(),
        }
    }

    /// Scan next token and return it.
    pub fn get_token(&mut self) -> Result<(Position, Token), ScannerError> {
        self.get_raw_token().map(|token| (self.line, token))
    }

    fn get_raw_token(&mut self) -> Result<Token, ScannerError> {
        loop {
            match self.input.next() {
                None => return Ok(Token::Eof),
                Some(Err(e)) => return Err(ScannerError::from(e)),
                Some(Ok(ch)) => match ch {
                    '\n' => self.line += 1,
                    ' ' | '\t' | '\r' => (),
                    '+' => return Ok(Token::Plus),
                    '-' => return Ok(Token::Minus),
                    '*' => return Ok(Token::Star),
                    '/' => {
                        if let Some(Ok('/')) = self.input.peek() {
                            self.skip_comment()?;
                        } else {
                            return Ok(Token::Slash);
                        }
                    }
                    '(' => return Ok(Token::LeftParen),
                    ')' => return Ok(Token::RightParen),
                    '{' => return Ok(Token::LeftCurly),
                    '}' => return Ok(Token::RightCurly),
                    ';' => return Ok(Token::Semicolon),
                    ',' => return Ok(Token::Comma),
                    '<' => return Ok(Token::Less),
                    '>' => return Ok(Token::Greater),
                    '=' => {
                        if let Some(Ok('=')) = self.input.peek() {
                            self.input.next();
                            return Ok(Token::EqualEqual);
                        } else {
                            return Ok(Token::Equal);
                        }
                    }
                    '!' => {
                        if let Some(Ok('=')) = self.input.peek() {
                            self.input.next();
                            return Ok(Token::BangEqual);
                        } else {
                            todo!()
                        }
                    }
                    '0'..='9' => return Ok(self.scan_number(ch)?),
                    'a'..='z' | 'A'..='Z' | '_' => return Ok(self.scan_identifier(ch)?),
                    _ => {
                        return Err(ScannerError::Parse(FullParseError {
                            pos: self.line,
                            error: ParseError::BadChar(ch),
                        }));
                    }
                },
            };
        }
    }

    fn scan_number(&mut self, first_digit: char) -> Result<Token, ScannerError> {
        self.buf.clear();
        self.buf.push(first_digit);
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if ch.is_digit(10) || *ch == '.' => {
                    let ch = self.next_char_unchecked()?;
                    self.buf.push(ch);
                }
                _ => break,
            }
        }

        let n = self.buf.parse::<f64>().map_err(|_| {
            ScannerError::Parse(FullParseError {
                pos: self.line,
                error: ParseError::BadFloatLiteral(self.buf.clone()),
            })
        })?;
        Ok(Token::Number(n))
    }

    fn skip_comment(&mut self) -> Result<(), ScannerError> {
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if *ch != '\n' => {
                    self.next_char_unchecked()?;
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn scan_identifier(&mut self, first_char: char) -> Result<Token, ScannerError> {
        self.buf.clear();
        self.buf.push(first_char);
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if ch.is_ascii_alphabetic() || ch.is_ascii_digit() || *ch == '_' => {
                    let ch = self.next_char_unchecked()?;
                    self.buf.push(ch);
                }
                _ => break,
            }
        }

        let sym = self.ctx.symbol(&self.buf);
        if let Some(token) = self.ctx.keyword(&sym) {
            Ok(token)
        } else {
            Ok(Token::Identifier(sym))
        }
    }

    /// Return next character or error.  Panic on EOF.
    /// Use this after peek()ing only.
    fn next_char_unchecked(&mut self) -> Result<char, ScannerError> {
        Ok(self.input.next().unwrap()?)
    }
}

impl<R: BufRead> Iterator for Scanner<R> {
    type Item = Result<Token, ScannerError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.get_token() {
            Ok((_, Token::Eof)) => None,
            Ok((_, t)) => Some(Ok(t)),
            Err(e) => Some(Err(e)),
        }
    }
}

#[derive(Debug)]
pub enum ScannerError {
    CharReader(CharReaderError),
    Parse(FullParseError),
}

impl Error for ScannerError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ScannerError::CharReader(e) => Some(e),
            ScannerError::Parse(_) => None,
        }
    }
}

impl fmt::Display for ScannerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ScannerError::CharReader(e) => write!(f, "read error: {}", e),
            ScannerError::Parse(e) => write!(f, "{}", e),
        }
    }
}

impl From<CharReaderError> for ScannerError {
    fn from(e: CharReaderError) -> ScannerError {
        ScannerError::CharReader(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    fn scan(input: &str) -> Result<Vec<Token>, ScannerError> {
        let ctx = Context::new();
        let s = Scanner::new(BufReader::new(input.as_bytes()), ctx);
        s.collect::<Result<Vec<Token>, ScannerError>>()
    }

    fn scan_with_ctx(input: &str, ctx: Rc<Context>) -> Result<Vec<Token>, ScannerError> {
        let s = Scanner::new(BufReader::new(input.as_bytes()), ctx);
        s.collect::<Result<Vec<Token>, ScannerError>>()
    }

    #[test]
    fn scan_single_token() -> Result<(), ScannerError> {
        assert_eq!(scan("+")?, vec![Token::Plus]);
        Ok(())
    }

    #[test]
    fn fixed_tokens() -> Result<(), ScannerError> {
        assert_eq!(
            scan("+-*/() = == != <>;,{}")?,
            vec![
                Token::Plus,
                Token::Minus,
                Token::Star,
                Token::Slash,
                Token::LeftParen,
                Token::RightParen,
                Token::Equal,
                Token::EqualEqual,
                Token::BangEqual,
                Token::Less,
                Token::Greater,
                Token::Semicolon,
                Token::Comma,
                Token::LeftCurly,
                Token::RightCurly,
            ]
        );
        Ok(())
    }

    #[test]
    fn blanks_are_ignored() -> Result<(), ScannerError> {
        assert_eq!(scan(" \t\n+")?, vec![Token::Plus]);
        Ok(())
    }

    #[test]
    fn single_digit_number() -> Result<(), ScannerError> {
        assert_eq!(scan("1")?, vec![Token::Number(1.0)]);
        Ok(())
    }

    #[test]
    fn multi_digit_integer() -> Result<(), ScannerError> {
        assert_eq!(scan("42")?, vec![Token::Number(42.0)]);
        Ok(())
    }

    #[test]
    fn floating_point() -> Result<(), ScannerError> {
        assert_eq!(scan("4.2")?, vec![Token::Number(4.2)]);
        Ok(())
    }

    #[test]
    fn scan_several_tokens_without_blanks() -> Result<(), ScannerError> {
        assert_eq!(
            scan("42+24")?,
            vec![Token::Number(42.0), Token::Plus, Token::Number(24.0)]
        );
        Ok(())
    }

    #[test]
    fn scanner_keeps_track_of_lines() -> Result<(), ScannerError> {
        let ctx = Context::new();
        let mut s = Scanner::new(BufReader::new("1\n2 3\n4".as_bytes()), ctx);
        assert_eq!(s.get_token()?, (1, Token::Number(1.0)),);
        assert_eq!(s.get_token()?, (2, Token::Number(2.0)));
        assert_eq!(s.get_token()?, (2, Token::Number(3.0)));
        assert_eq!(s.get_token()?, (3, Token::Number(4.0)));
        Ok(())
    }

    #[test]
    fn identifier() -> Result<(), ScannerError> {
        let ctx = Context::new();
        assert_eq!(
            scan_with_ctx("f foo _foo t42", ctx.clone())?,
            vec![
                Token::Identifier(ctx.symbol("f")),
                Token::Identifier(ctx.symbol("foo")),
                Token::Identifier(ctx.symbol("_foo")),
                Token::Identifier(ctx.symbol("t42"))
            ]
        );
        Ok(())
    }

    #[test]
    fn keywords() -> Result<(), ScannerError> {
        assert_eq!(
            scan("true false print var nil if while fun return")?,
            vec![
                Token::True,
                Token::False,
                Token::Print,
                Token::Var,
                Token::Nil,
                Token::If,
                Token::While,
                Token::Fun,
                Token::Return,
            ]
        );
        Ok(())
    }

    #[test]
    fn comments_are_ignored() -> Result<(), ScannerError> {
        assert_eq!(scan("true // false")?, vec![Token::True,]);
        Ok(())
    }
}
