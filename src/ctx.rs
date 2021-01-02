use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::interner::{Interner, Symbol};
use crate::token::Token;

/// Global mostly read-only state context that can persist across interpreter sessions.
///
/// TODO: Maybe we could git rid of this as it is not optimal to register keywords again and
/// again.
/// This struct was initially introduced to anchor the string interner.  We could use an interner
/// that keeps its state in global data instead.
/// This struct was extended to map keywords to their associated tokens (lazy static does not work
/// here because Symbol and so Token is not Sync).
#[derive(Debug)]
pub struct Context {
    interner: RefCell<Interner>,
    keywords: HashMap<Symbol, Token>,
}

impl Context {
    /// Creates a new context.
    ///
    /// Returns a Rc because the context is shared between various data structures.
    pub fn new() -> Rc<Self> {
        let mut interner = Interner::new();

        let mut keywords = HashMap::new();
        for (name, token) in KEYWORDS.iter().cloned() {
            keywords.insert(interner.symbol(name), token);
        }

        Rc::new(Context {
            interner: RefCell::new(interner),
            keywords,
        })
    }

    /// Intern the given string if needed and return he its associated symbol.
    pub fn symbol(&self, name: &str) -> Symbol {
        self.interner.borrow_mut().symbol(name)
    }

    /// Return the token associated with the given symbol if it is a keyword.
    pub fn keyword(&self, id: &Symbol) -> Option<Token> {
        self.keywords.get(id).map(|t| t.clone())
    }
}

const KEYWORDS: [(&str, Token); 10] = [
    ("true", Token::True),
    ("false", Token::False),
    ("print", Token::Print),
    ("var", Token::Var),
    ("nil", Token::Nil),
    ("if", Token::If),
    ("else", Token::Else),
    ("while", Token::While),
    ("fun", Token::Fun),
    ("return", Token::Return),
];
