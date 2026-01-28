use convert_case::ccase;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{
    Ident, LitStr, Token, bracketed,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
};

#[derive(Debug, Clone)]
struct SymbolDef {
    name: Ident,
    val: String,
    category: Option<String>,
}

impl Parse for SymbolDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name: Ident = input.parse()?;

        let val = if input.peek(Token![=]) {
            input.parse::<Token![=]>()?;

            let str = input.parse::<LitStr>()?;

            str.value()
        } else {
            name.to_string()
        };

        Ok(SymbolDef {
            name,
            val,
            category: None,
        })
    }
}

#[derive(Debug, Clone)]
enum TopItem {
    Symbol(SymbolDef),
    Category {
        name: Ident,
        items: Punctuated<SymbolDef, Token![,]>,
    },
}

#[derive(Debug, Clone)]
struct SymbolsInput {
    items: Vec<TopItem>,
}

impl Parse for SymbolsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut items: Vec<TopItem> = Vec::new();

        while !input.is_empty() {
            // Must start with an identifier either for a symbol or a category name.
            if input.peek(Ident) {
                // Look ahead to see whether this is a category (Ident ':') or a symbol (Ident [= ...]?).
                let fork = input.fork();
                let _ident_ahead: Ident = fork.parse()?;
                if fork.peek(Token![:]) {
                    // category form: NAME : [ ... ]
                    let cat_name: Ident = input.parse()?;
                    input.parse::<Token![:]>()?;
                    let content;
                    bracketed!(content in input);
                    let inner = content.parse_terminated(SymbolDef::parse, Token![,])?;
                    items.push(TopItem::Category {
                        name: cat_name,
                        items: inner,
                    });
                } else {
                    // simple symbol
                    let symbol = input.parse::<SymbolDef>()?;
                    items.push(TopItem::Symbol(symbol));
                }
            } else {
                return Err(input.error("expected identifier for symbol or category"));
            }

            // optional separating comma
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                // allow trailing commas and continue
            } else {
                break;
            }
        }

        Ok(SymbolsInput { items })
    }
}

#[derive(Debug, Clone)]
pub struct Category {
    name: String,
    first: Ident,
    last: Ident,
}

pub(crate) fn symbols(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as SymbolsInput);

    let mut symbols: Vec<SymbolDef> = Vec::with_capacity(parsed.items.len());
    let mut categories: Vec<Category> = Vec::new();

    for top in parsed.items.into_iter() {
        match top {
            TopItem::Symbol(s) => {
                // top-level symbol: category stays None
                symbols.push(s);
            }
            TopItem::Category { name, items } => {
                let cat_name_string = name.to_string();
                // If the category is empty, skip adding boundaries.
                if items.is_empty() {
                    continue;
                }
                // Mark each inner symbol with the category name and push in order.
                let first_ident = items.first().unwrap().name.clone();
                let last_ident = items.last().unwrap().name.clone();

                for mut symdef in items.into_iter() {
                    symdef.category = Some(cat_name_string.clone());
                    symbols.push(symdef);
                }

                categories.push(Category {
                    name: cat_name_string,
                    first: first_ident,
                    last: last_ident,
                });
            }
        }
    }

    // Now build the generated tokens
    let mut sym_constants = Vec::with_capacity(symbols.len());
    let mut strlits: Vec<LitStr> = Vec::with_capacity(symbols.len());

    for (
        i,
        SymbolDef {
            name,
            val,
            category,
        },
    ) in symbols.iter().enumerate()
    {
        let id = i as u32 + 1;

        let doc = category
            .as_ref()
            .map(|cat| format!("*Part of the `{cat}` category.*\n"))
            .into_iter();

        let val_doc = format!("\n\n`{name} = {id};`");

        // SAFETY: id starts at one so we are safe.
        sym_constants.push(quote! {
            #( #[doc = #doc] )*
            #[doc = #val_doc]
            pub const #name: crate::symbol::Symbol = crate::symbol::Symbol(unsafe { ::std::num::NonZeroU32::new_unchecked(#id) });
        });

        strlits.push(LitStr::new(val, Span::call_site()));
    }

    let mut cat_constants = Vec::with_capacity(categories.len());
    let mut is_fns = Vec::with_capacity(categories.len());

    for Category { name, first, last } in categories {
        let start_name = ccase!(constant, format!("{}_START", name));
        let end_name = ccase!(constant, format!("{}_END", name));
        let range_name = ccase!(constant, format!("{}_RANGE", name));
        let fn_name = ccase!(snake, format!("is_{name}"));

        let start_ident = Ident::new(&start_name, Span::call_site());
        let end_ident = Ident::new(&end_name, Span::call_site());
        let range_ident = Ident::new(&range_name, Span::call_site());
        let fn_ident = Ident::new(&fn_name, Span::call_site());

        let start_doc = format!("Lower bound of the `{name}` category (equals to `sym::{first}`)");
        let end_doc = format!("High bound of the `{name}` category (equals to `sym::{last}`)");
        let range_doc = format!("Range of the `{name}` category (equals to `{first}..={last}`)");
        let fn_doc = format!("Is the symbol a `{name}`?");

        cat_constants.push(quote! {
            #[doc = #start_doc]
            pub const #start_ident: crate::symbol::Symbol = crate::symbol::sym::#first;

            #[doc = #end_doc]
            pub const #end_ident: crate::symbol::Symbol = crate::symbol::sym::#last;

            #[doc = #range_doc]
            pub const #range_ident: ::std::ops::RangeInclusive<crate::symbol::Symbol> = crate::symbol::sym::#first..=crate::symbol::sym::#last;
        });

        is_fns.push(quote! {
            #[doc = #fn_doc]
            pub fn #fn_ident(&self) -> bool {
                crate::symbol::categories::#range_ident.contains(self)
            }
        });
    }

    let predef_count = sym_constants.len();

    // the token stream containing the `sym` module and it's constants.
    let sym_mod = quote! {
        /// The predefined symbols, use them like that
        /// <code>sym::*symbol_name*</code>.
        #[allow(non_upper_case_globals)]
        pub mod sym {
            #( #sym_constants )*
        }

        /// The categories defined by the `symbols!` macro.
        pub mod categories {
            #( #cat_constants )*
        }

        /// Count of how many predefined symbol there is in [`sym`].
        pub const PREDEFINED_SYMBOLS_COUNT: usize = #predef_count;

        /// The list of predefined symbols.
        pub static PREDEFINED_SYMBOLS: [&'static str; #predef_count] = [
            #( #strlits ),*
        ];

        impl crate::symbol::Symbol {
            #( #is_fns )*
        }
    };

    sym_mod.into()
}
