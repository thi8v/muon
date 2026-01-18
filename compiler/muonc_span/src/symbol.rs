//! Muon's symbols

use std::{
    fmt, mem,
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
pub struct Symbol(u32);

impl Symbol {
    /// Intern the following string.
    #[inline]
    pub fn intern(s: &str) -> Symbol {
        GLOBAL_INTERNER.intern_str(s)
    }

    /// Create a new symbol from the id, it can cause UB if used incorrectly.
    #[inline]
    pub fn new(n: u32) -> Symbol {
        Symbol(n)
    }

    /// Access the underlying string.
    #[inline]
    pub fn as_str(&self) -> &'static str {
        GLOBAL_INTERNER.get_str(*self)
    }

    /// Is this symbol predefined?
    #[inline]
    pub fn is_predefined(&self) -> bool {
        self.0 < PREDEFINED_SYMBOLS_COUNT as u32
    }

    /// Is the symbol the empty symbol?
    pub fn is_empty(&self) -> bool {
        *self == sym::empty
    }

    /// Get the internal id of the given symbol.
    #[inline]
    pub fn id(&self) -> u32 {
        self.0
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

/// Identifier, the name of the identifier cannot be [`sym::empty`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

impl Ident {
    /// Create a new identifier.
    pub fn new(name: Symbol, span: Span) -> Ident {
        debug_assert!(
            !name.can_identifier(),
            "cannot create an identifier with a symbol that can't be an identifier."
        );
        Self { name, span }
    }

    /// Create a new identifier with a dummy span.
    pub fn without_span(name: Symbol) -> Ident {
        Ident::new(name, DUMMY_SP)
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
#[derive(Debug)]
pub struct Interner {
    /// string -> id
    map: DashMap<&'static str, u32>,
    /// the stored strings.
    data: boxcar::Vec<&'static str>,
    /// the allocator of the strings.
    alloc: Mutex<Bump>,
    /// next id
    id: AtomicU32,
}

impl Interner {
    /// Create a new empty symbol interner.
    pub fn with_predefined_symbols(predefined: &'static [&'static str]) -> Interner {
        // NOTE: here we make an exception, we do not allocate the strings
        // provided because we know they live forever, it saves sometime.

        let map = DashMap::with_capacity(predefined.len());
        let data = boxcar::Vec::with_capacity(predefined.len());

        for (i, sym) in predefined.iter().enumerate() {
            map.insert(*sym, i as u32);
            data.push(*sym);
        }

        Interner {
            map,
            data,
            alloc: Mutex::new(Bump::new()),
            id: AtomicU32::new(predefined.len() as u32),
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

        let id = self.id.fetch_add(1, Ordering::Relaxed);

        // SAFETY: the lifetime is a lie but we know it.
        let alloced = unsafe { mem::transmute::<&str, &'static str>(allocator.alloc_str(str)) };

        self.map.insert(alloced, id);
        self.data.push(alloced);

        Symbol(id)
    }

    /// Get an interned string.
    pub fn get_str(&self, sym: Symbol) -> &str {
        self.data[sym.0 as usize]
    }
}

symbols! {
    empty = "",
    cstr = "cstr",

    // keywords.
    keyword: [
        As,
        Break,
        Comptime,
        Continue,
        Else,
        Extern,
        False,
        For,
        Fun,
        If,
        Impl,
        In,
        Let,
        Loop,
        Mut,
        Null,
        Pub,
        Return,
        Self_ = "self",
        Then,
        Trait,
        True,
        While,
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
}
