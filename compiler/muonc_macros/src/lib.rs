//! Macros used across the Muon compiler

use proc_macro::TokenStream;

mod codes_enum;
mod kv_derive;
mod symbols;

#[proc_macro_derive(KeyValue, attributes(kv))]
pub fn keyvalue_derive(input: TokenStream) -> TokenStream {
    kv_derive::kv_derive(input)
}

/// Creates a module named `sym`, that contains all constants with the provided
/// name and the id of it is the order of apparition in the symbols. A static
/// item containing all the string literals representing the predefined symbols
/// and another constant with the count of those predefined symbols.
#[proc_macro]
pub fn symbols(input: TokenStream) -> TokenStream {
    symbols::symbols(input)
}

#[proc_macro]
pub fn codes_enum(input: TokenStream) -> TokenStream {
    codes_enum::codes_enum(input)
}
