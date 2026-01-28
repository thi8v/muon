// Procedural replacement for the `codes_enum!` declarative macro.
// Put this in a `proc-macro` crate (Cargo.toml: proc-macro = true).
// lib.rs

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{
    Attribute, Ident, LitChar, LitInt, LitStr, Result as SynResult, Token, Visibility, braced,
    parse_macro_input,
};

struct Variant {
    attrs: Vec<Attribute>,
    ident: Ident,
    value: LitInt,
    doc: LitStr,
}

struct CodesEnumInput {
    enum_attrs: Vec<Attribute>,
    vis: Visibility,
    name: Ident,
    char: char,
    variants: Vec<Variant>,
}

impl Parse for CodesEnumInput {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // Outer attributes for the enum (zero or more)
        let enum_attrs = input.call(Attribute::parse_outer)?;

        // visibility, the `enum` token, name, `:` and the char ident
        let vis: Visibility = input.parse()?;
        input.parse::<Token![enum]>()?;
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let lit_char: LitChar = input.parse()?;
        let char = lit_char.value();

        // parse the brace-enclosed variant list
        let content;
        braced!(content in input);

        let mut variants = Vec::new();

        while !content.is_empty() {
            // variant attributes (zero or more)
            let attrs = content.call(Attribute::parse_outer)?;

            let ident: Ident = content.parse()?;
            content.parse::<Token![=]>()?;
            let value: LitInt = content.parse()?;
            let doc = format!(
                "../../../src/doc/{}{:04}.md",
                char,
                value
                    .base10_digits()
                    .parse::<u32>()
                    .expect("parsing failed")
            );
            let doc_path = LitStr::new(&doc, Span::call_site());

            variants.push(Variant {
                attrs,
                ident,
                value,
                doc: doc_path,
            });

            // optional comma separator (allow trailing comma)
            if content.peek(Token![,]) {
                let _comma: Token![,] = content.parse()?;
            } else {
                break;
            }
        }

        Ok(CodesEnumInput {
            enum_attrs,
            vis,
            name,
            char,
            variants,
        })
    }
}

pub(crate) fn codes_enum(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as CodesEnumInput);

    // build variants tokens
    let variant_defs = parsed.variants.iter().map(|v| {
        let attrs = &v.attrs;
        let ident = &v.ident;
        let value = &v.value;
        let doc_path = &v.doc;

        quote! { #( #attrs )* #[doc = ::std::include_str!(#doc_path)] #ident = #value, }
    });

    let documentations = parsed.variants.iter().map(|v| {
        let doc_path = &v.doc;
        quote! { ::std::include_str!(#doc_path), }
    });

    let enum_attrs = &parsed.enum_attrs;
    let vis = &parsed.vis;
    let name = &parsed.name;
    let char = &parsed.char;
    let variant_count = parsed.variants.len();
    let docs = format!(
        "All of the documentations of the error codes, index it like that: \n```\
        rust\n{name}::documentation(/* error code */ as usize);\n```"
    );

    let expanded = quote! {
        #( #enum_attrs )*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #vis enum #name {
            #(#variant_defs)*
        }

        impl #name {
            /// Variant count.
            pub const VARIANT_COUNT: usize = #variant_count;

            #[doc = #docs]
            pub fn documentations() -> [&'static str; #variant_count] {
                [#( #documentations )*]
            }
        }

        impl std::fmt::Display for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                // same formatting behaviour as the original macro
                write!(f, "{}{:04}", #char, *self as usize)
            }
        }
    };

    TokenStream::from(expanded)
}
