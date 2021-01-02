//! Convert byte reader to utf8 character iterator.
//!
//! For some reason there is no such facility in `std::*`.

use std::error::Error;
use std::fmt;
use std::io::prelude::*;
use std::io::{self, Bytes};
use std::iter::Peekable;
use std::str::{self, Utf8Error};

/// An iterator over a buffered reader that produces characters rather than bytes.
#[derive(Debug)]
pub struct CharReader<R: BufRead> {
    input: Peekable<Bytes<R>>,

    // Conversion buffer stored here to avoid reallocation.
    buf: Vec<u8>,
}

impl<R: BufRead> CharReader<R> {
    pub fn new(input: R) -> CharReader<R> {
        CharReader {
            input: input.bytes().peekable(),
            buf: vec![],
        }
    }

    fn convert_multi_byte_char(&mut self, first_byte: u8) -> Result<char, CharReaderError> {
        self.buf.clear();
        self.buf.push(first_byte);
        loop {
            match self.input.peek() {
                Some(Err(_)) => {
                    return Err(CharReaderError::from(
                        self.input.next().unwrap().unwrap_err(),
                    ))
                }
                Some(Ok(b)) if (b & 0b11000000) == 0b10000000 => {
                    let b = self.input.next().unwrap().unwrap();
                    self.buf.push(b)
                }
                // EOF or start of next char
                _ => break,
            }
        }
        let s = str::from_utf8(&self.buf)?;
        Ok(s.chars().next().unwrap())
    }
}

impl<R: BufRead> Iterator for CharReader<R> {
    type Item = Result<char, CharReaderError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.input.next() {
            Some(Ok(b)) => {
                if b.is_ascii() {
                    Some(Ok(b as char))
                } else if (b & 0b11000000) == 0b11000000 {
                    Some(self.convert_multi_byte_char(b))
                } else {
                    Some(Err(CharReaderError::BadStartByte(b)))
                }
            }
            Some(Err(e)) => Some(Err(CharReaderError::from(e))),
            _ => None,
        }
    }
}

/// Errors raised when reading and converting to UTF-8.
#[derive(Debug)]
pub enum CharReaderError {
    Io(io::Error),
    BadStartByte(u8),
    Utf8(Utf8Error),
}

impl fmt::Display for CharReaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharReaderError::Io(e) => write!(f, "Failed to read bytes: {}", e),
            CharReaderError::BadStartByte(b) => write!(f, "unexpected UTF-8 start byte: {:b}", b),
            CharReaderError::Utf8(e) => {
                write!(f, "failed to conveert byte sequence to UTF-8: {}", e)
            }
        }
    }
}

impl Error for CharReaderError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            CharReaderError::Io(err) => Some(err),
            CharReaderError::BadStartByte(_) => None,
            CharReaderError::Utf8(err) => Some(err),
        }
    }
}

impl From<io::Error> for CharReaderError {
    fn from(err: io::Error) -> CharReaderError {
        CharReaderError::Io(err)
    }
}

impl From<Utf8Error> for CharReaderError {
    fn from(err: Utf8Error) -> CharReaderError {
        CharReaderError::Utf8(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(input: &str) -> Result<String, CharReaderError> {
        CharReader::new(input.as_bytes()).collect::<Result<String, CharReaderError>>()
    }

    #[test]
    fn read_ascii() -> Result<(), CharReaderError> {
        assert_eq!(read("ABC")?, "ABC");
        Ok(())
    }

    #[test]
    fn read_mb_char_followed_by_eof() -> Result<(), CharReaderError> {
        assert_eq!(read("∏")?, "∏");
        Ok(())
    }

    #[test]
    fn read_mb_char_followed_by_another_one() -> Result<(), CharReaderError> {
        assert_eq!(read("∏X")?, "∏X");
        Ok(())
    }

    #[test]
    fn mb_with_invalid_starting_byte() {
        let input = vec![0b10111111u8];
        let mut reader = CharReader::new(input.as_slice());
        match reader.next() {
            Some(Err(CharReaderError::BadStartByte(0b10111111u8))) => (),
            r => panic!("unexpected output: {:?}", r),
        };
    }

    #[test]
    fn mb_with_invalid_number_of_bytes() {
        let input = vec![0b11100000u8, 0b10000000u8, 42u8];
        let mut reader = CharReader::new(input.as_slice());
        match reader.next() {
            Some(Err(CharReaderError::Utf8(_))) => (),
            r => panic!("unexpected output: {:?}", r),
        };
    }
}
