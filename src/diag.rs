use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct FullParseError {
    pub pos: Position,
    pub error: ParseError,
}

impl fmt::Display for FullParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error: {}: {}", self.pos, self.error)
    }
}

impl Error for FullParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Line number (starting at one).
pub type Position = u32;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnexpectedToken(String, String),
    BadChar(char),
    BadFloatLiteral(String),
    ExpectedLvalue,
    ExpectedPrimary,
    ExpectedIdentifier,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken(unexpected, expected) => write!(
                f,
                "unexpected token '{}', expected '{}'",
                unexpected, expected
            ),
            ParseError::BadChar(ch) => {
                write!(f, "unexpected character: {}", ch)
            }
            ParseError::BadFloatLiteral(lit) => {
                write!(f, "cannot parse floating point literal: {}", lit)
            }
            ParseError::ExpectedPrimary => {
                write!(f, "expected primary expression")
            }
            ParseError::ExpectedLvalue => {
                write!(f, "expected lvalue expression")
            }
            ParseError::ExpectedIdentifier => {
                write!(f, "expected identifier")
            }
        }
    }
}
