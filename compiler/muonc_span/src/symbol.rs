//! Muon's symbols

use std::{
    fmt, mem,
    num::NonZeroU32,
    ops::RangeInclusive,
    sync::{
        LazyLock, Mutex,
        atomic::{AtomicU32, Ordering},
    },
};

use bumpalo::Bump;
use dashmap::DashMap;
use muonc_macros::symbols;

use crate::{DUMMY_SP, Span};

/// An interned UTF-8 string.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(NonZeroU32);

impl Symbol {
    /// Intern the following string.
    #[inline]
    pub fn intern(s: &str) -> Symbol {
        GLOBAL_INTERNER.intern_str(s)
    }

    /// Create a new symbol from the id, it can cause UB if used incorrectly.
    #[inline]
    pub fn new(n: u32) -> Symbol {
        Symbol(NonZeroU32::new(n).expect("invalid id, cannot be 0"))
    }

    /// Access the underlying string.
    #[must_use]
    #[inline]
    pub fn as_str(&self) -> &'static str {
        GLOBAL_INTERNER.get_str(*self)
    }

    /// The length of the interned string.
    #[inline]
    pub fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Is this symbol predefined?
    #[inline]
    pub fn is_predefined(&self) -> bool {
        self.0.get() < PREDEFINED_SYMBOLS_COUNT as u32
    }

    /// Is the symbol the empty symbol?
    pub fn is_empty(&self) -> bool {
        *self == sym::empty
    }

    /// Get the internal id of the given symbol.
    #[inline]
    pub const fn id(&self) -> u32 {
        self.0.get()
    }

    /// Get the internal id of the given symbol as a usize.
    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.id() as usize
    }

    /// Can this symbol be used as an identifier?
    pub fn can_identifier(&self) -> bool {
        !self.is_empty()
            && !self.is_keyword()
            && self
                .as_str()
                .chars()
                .all(|c| !c.is_whitespace() && (c.is_alphanumeric() || c == '_'))
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sym{:?}", self.as_str())
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Identifier, the name of the identifier cannot be [`sym::empty`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
    pub name: Symbol,
    pub span: Span,
}

impl Identifier {
    /// Create a new identifier.
    pub fn new(name: Symbol, span: Span) -> Identifier {
        debug_assert!(
            name.can_identifier(),
            "cannot create an identifier with a symbol that can't be an identifier."
        );
        Self { name, span }
    }

    /// Create a new identifier with a dummy span.
    pub fn without_span(name: Symbol) -> Identifier {
        Identifier::new(name, DUMMY_SP)
    }

    /// Access the underlying string representing it.
    pub fn as_str(&self) -> &str {
        self.name.as_str()
    }
}

/// The global interner.
pub static GLOBAL_INTERNER: LazyLock<Interner> =
    LazyLock::new(|| Interner::with_predefined_symbols(&PREDEFINED_SYMBOLS));

/// Forces the evaluation of the initializator of the global interner, it should
/// be run before using symbols, it's not mandatory but it may speed up things.
///
/// *N.B: calling this function twice is useless.*
pub fn force_eval_global_interner() {
    LazyLock::force(&GLOBAL_INTERNER);
}

/// [`Symbol`] interner.
#[repr(align(64))] // align to the size of a common cache line.
#[derive(Debug)]
pub struct Interner {
    /// string -> id
    map: DashMap<&'static str, NonZeroU32>,
    /// the stored strings.
    data: boxcar::Vec<&'static str>,
    /// the allocator of the strings.
    alloc: Mutex<Bump>,
    /// next id
    id: AtomicU32,
}

impl Interner {
    const INNER_INVALID: &'static str = if cfg!(debug_assertions) {
        "<INVALID!>"
    } else {
        ""
    };

    /// Create a new empty symbol interner.
    pub fn with_predefined_symbols(predefined: &'static [&'static str]) -> Interner {
        // NOTE: here we make an exception, we do not allocate the strings
        // provided because we know they live forever, it saves sometime.

        let map = DashMap::with_capacity(predefined.len() + 1);
        let data = boxcar::Vec::with_capacity(predefined.len() + 1);

        // push an invalid string at the 0th index so that we can access the
        // interned string just by using the id without having to subtract 1.
        data.push(Interner::INNER_INVALID);

        for (i, sym) in predefined.iter().enumerate() {
            map.insert(*sym, NonZeroU32::new(i as u32 + 1).expect("invalid id"));
            data.push(*sym);
        }

        Interner {
            map,
            data,
            alloc: Mutex::new(Bump::new()),
            id: AtomicU32::new(predefined.len() as u32 + 1),
        }
    }

    /// Intern a string
    pub fn intern_str(&self, str: &str) -> Symbol {
        if let Some(interned) = self.map.get(str) {
            // the symbol is already interned, return early.
            return Symbol(*interned);
        }

        let allocator = self
            .alloc
            .lock()
            .expect("failed to lock the allocator of the interner");

        let id = NonZeroU32::new(self.id.fetch_add(1, Ordering::Relaxed)).expect("invalid id");

        // SAFETY: the lifetime is a lie but we know it.
        let alloced = unsafe { mem::transmute::<&str, &'static str>(allocator.alloc_str(str)) };

        self.map.insert(alloced, id);
        self.data.push(alloced);

        Symbol(id)
    }

    /// Get an interned string.
    #[must_use]
    pub fn get_str(&self, sym: Symbol) -> &str {
        self.data[sym.as_usize()]
    }

    /// Get an owned slice of a range of symbols.
    ///
    /// N.B: due to how this is implemented it may be **SUPER SLOW** here are
    /// some recommendations using this method:
    /// * If the range exists before creating before we start creating symbols, then
    ///   use this method as early as possible.
    /// * Try to memoize the results, you **DO NOT WANT** to run this function
    ///   super often, the less the better.
    #[must_use = "this methods could be super slow so running it without using it's result is just dumb"]
    pub fn get_str_slice(&self, range: RangeInclusive<Symbol>) -> Vec<&str> {
        fn inner(this: &Interner, range: RangeInclusive<u32>) -> impl Iterator<Item = &str> {
            this.data
                .iter()
                .filter_map(move |(idx, val)| range.contains(&(idx as u32)).then_some(*val))
        }

        inner(self, (range.start().id())..=(range.end().id())).collect()
    }
}

symbols! {
    empty = "",

    // NB. by convention the symbols for keywords start with a capital letter
    // because we share many keywords with Rust.

    // keywords.
    keyword: [
        As = "as",
        Break = "break",
        Comptime = "comptime",
        Continue = "continue",
        Else = "else",
        Extern = "extern",
        False = "false",
        For = "for",
        Fun = "fun",
        If = "if",
        Impl = "impl",
        In = "in",
        Let = "let",
        Loop = "loop",
        Mut = "mut",
        Null = "null",
        Pkg = "pkg",
        Pub = "pub",
        Return = "return",
        Self_ = "self",
        Trait = "trait",
        True = "true",
        While = "while",
    ],

    // weak keywords
    weak_kw: [
        Import = "import",
        Mod = "mod",
    ],

    // primitive types.
    primitive: [
        isz,
        i128,
        i64,
        i32,
        i16,
        i8,
        usz,
        u128,
        u64,
        u32,
        u16,
        u8,
        f16,
        f32,
        f64,
        f128,
        bool,
        str,
        char,
        never,
        void,
    ],

    cstr = "cstr",
    underscore = "_",
    dummy = "\u{FFFD}",
    fakepkg = "__pkg\u{FFFD}",
    C,
    Muon,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifiers_checks_test() {
        assert!(Symbol::intern("peekaboo").can_identifier());
        assert!(Symbol::intern("foo_bar").can_identifier());
        assert!(Symbol::intern("_").can_identifier());
        assert!(Symbol::intern("_x_x_").can_identifier());
        assert!(!sym::As.can_identifier());
        assert!(!sym::Self_.can_identifier());
        assert!(!Symbol::intern("Hello, World!").can_identifier());
    }

    #[test]
    fn predefined_symbols() {
        assert_eq!(sym::empty.as_str(), "");
        assert_eq!(sym::As.as_str(), "as");
        assert_eq!(sym::While.as_str(), "while");
        assert_eq!(sym::Import.as_str(), "import");
    }
}
