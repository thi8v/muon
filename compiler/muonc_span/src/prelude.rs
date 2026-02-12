//! Prelude of `muonc_span`.

pub use crate::symbol::{
    GLOBAL_INTERNER, Identifier, PREDEFINED_SYMBOLS_COUNT, Symbol, categories, sym,
};
pub use crate::{Bsz, DUMMY_SP, FileId, Span, Spanned, respan, span};
