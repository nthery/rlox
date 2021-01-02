//! String interner
//!
//! TODO: A design that allocates interned strings globally would be simpler and more performant (no
//! need for Rc).

use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;

/// Stores all known symbols.
#[derive(Debug)]
pub struct Interner(HashSet<Symbol>);

impl Interner {
    pub fn new() -> Interner {
        Interner(HashSet::new())
    }

    /// Maps a string to a symbol.
    pub fn symbol(&mut self, name: &str) -> Symbol {
        if let Some(sym) = self.0.get(name) {
            sym.clone()
        } else {
            let sym = Symbol(Rc::new(name.to_string()));
            self.0.insert(sym.clone());
            sym
        }
    }
}

#[derive(Debug, Hash, Clone)]
pub struct Symbol(Rc<String>);

/// An immutable string that is guaranteed to be unique and so can be compared by address rather
/// than content.
impl Symbol {
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl Eq for Symbol {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_from_string() {
        let mut reg = Interner::new();
        let sym = reg.symbol("foo");
        assert_eq!(sym.name(), "foo");
    }

    #[test]
    fn symbols_with_same_name_are_equal() {
        let mut reg = Interner::new();
        let sym1 = reg.symbol("foo");
        let sym2 = reg.symbol("foo");
        assert_eq!(sym1, sym2);
    }

    #[test]
    fn symbols_with_different_names_are_different() {
        let mut reg = Interner::new();
        let sym1 = reg.symbol("foo");
        let sym2 = reg.symbol("bar");
        assert_ne!(sym1, sym2);
    }
}
