//! Macros used across the Muon compiler

extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    Attribute, DeriveInput, LitChar, LitStr, Meta, Type, parse_macro_input, spanned::Spanned,
};

/// Parse attributes of the form: `#[kv(key = "...", help = "...", default = "...")]`
fn parse_kv_field_attributes(
    field: &syn::Field,
) -> Result<(String, String, Option<String>), TokenStream> {
    let mut key_name = field.ident.as_ref().unwrap().to_string();
    let mut help = String::new();
    let mut default = None;

    for attr in &field.attrs {
        if !attr.path().is_ident("kv") {
            continue;
        }

        if let Meta::List(list) = &attr.meta {
            list.parse_nested_meta(|meta| {
                let value = meta.value()?;

                if meta.path.is_ident("key") {
                    let s: LitStr = value.parse()?;

                    key_name = s.value();

                    Ok(())
                } else if meta.path.is_ident("help") {
                    let s: LitStr = value.parse()?;

                    help = s.value();

                    Ok(())
                } else if meta.path.is_ident("default") {
                    let s: LitStr = value.parse()?;

                    default = Some(s.value());

                    Ok(())
                } else {
                    Err(syn::Error::new(meta.path.span(), "unknown key".to_string()))
                }
            })
            .map_err(|e| e.to_compile_error())?;
        }
    }

    Ok((key_name, help, default))
}

/// Parse attributes of the form `#[kv(name = "...", short = '.')]`
fn parse_kv_struct_attribute(attrs: &[Attribute]) -> Result<(String, char), TokenStream> {
    let mut kv_count = 0u8;
    let mut name = None;
    let mut short = None;

    for attr in attrs {
        let Some(ident) = attr.path().get_ident() else {
            continue;
        };

        if kv_count >= 1 {
            return Err(syn::Error::new(
                attr.meta.span(),
                "there is already one `#[kv(name = \"...\", short = '_')]`.",
            )
            .to_compile_error()
            .into());
        }

        if ident != "kv" {
            continue;
        }

        kv_count += 1;

        if let Meta::List(list) = &attr.meta {
            list.parse_nested_meta(|meta| {
                let value = meta.value()?;

                if meta.path.is_ident("name") {
                    let s: LitStr = value.parse()?;

                    name = Some(s.value());

                    Ok(())
                } else if meta.path.is_ident("short") {
                    let c: LitChar = value.parse()?;

                    short = Some(c.value());

                    Ok(())
                } else {
                    Err(syn::Error::new(meta.path.span(), "unknown key".to_string()))
                }
            })
            .map_err(|e| e.to_compile_error())?;
        }
    }

    if let Some(name) = name
        && let Some(short) = short
    {
        Ok((name, short))
    } else {
        Err(syn::Error::new(
            attrs.first().span(),
            "there is already one `#[kv(name = \"...\", short = '_')]`.",
        )
        .to_compile_error()
        .into())
    }
}

/// Detect Option<T> and return inner T type if yes.
fn extract_option_inner(ty: &Type) -> Option<&Type> {
    if let Type::Path(tp) = ty {
        let segs = &tp.path.segments;
        if segs.len() == 1 && segs.first().unwrap().ident == "Option"
            && let syn::PathArguments::AngleBracketed(ab) = &segs.first().unwrap().arguments
                && ab.args.len() == 1
                    && let syn::GenericArgument::Type(inner) = ab.args.first().unwrap() {
                        return Some(inner);
                    }
    }
    None
}

/// Detect Vec<T> and return inner T type if yes.
fn extract_vec_inner(ty: &Type) -> Option<&Type> {
    if let Type::Path(tp) = ty {
        let segs = &tp.path.segments;
        if segs.len() == 1 && segs.first().unwrap().ident == "Vec"
            && let syn::PathArguments::AngleBracketed(ab) = &segs.first().unwrap().arguments
                && ab.args.len() == 1
                    && let syn::GenericArgument::Type(inner) = ab.args.first().unwrap() {
                        return Some(inner);
                    }
    }
    None
}

#[proc_macro_derive(KeyValue, attributes(kv))]
pub fn keyvalue_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let struct_name = input.ident;

    let data = match input.data {
        syn::Data::Struct(s) => s,
        _ => panic!("KvSpec can only be derived for structs"),
    };

    let (name, short) = match parse_kv_struct_attribute(&input.attrs) {
        Ok(v) => v,
        Err(e) => return e,
    };

    let mut build_fields = Vec::new();
    let mut kv_keys_entries = Vec::new();

    for field in data.fields.iter() {
        let ident = field.ident.as_ref().expect("expected named fields").clone();
        let ty = &field.ty;
        let (key_name, help, default) = match parse_kv_field_attributes(field) {
            Ok(t) => t,
            Err(ts) => return ts,
        };

        // push kv_keys entry
        kv_keys_entries.push(quote! { (#key_name, #help) });

        // detect Vec<T>
        if let Some(inner_ty) = extract_vec_inner(ty) {
            // Vec<T>: collect all occurrences; if missing => empty vec; if default provided => vec with parsed default
            if let Some(def_lit) = default {
                let build = quote! {
                    #ident: match muonc_middle::kv::kv_map_get(map, #key_name) {
                        Some(list) => {
                            let mut out = Vec::with_capacity(list.len());
                            for (i, s) in list.iter().enumerate() {
                                let parsed = <#inner_ty as std::str::FromStr>::from_str(s)
                                    .map_err(|e| format!("invalid value for {}[{}]: {}", #key_name, i, e))?;
                                out.push(parsed);
                            }
                            out
                        }
                        None => {
                            let parsed = <#inner_ty as std::str::FromStr>::from_str(#def_lit)
                                .map_err(|e| format!("invalid default for {}: {}", #key_name, e))?;
                            vec![parsed]
                        }
                    }
                };
                build_fields.push(build);
            } else {
                let build = quote! {
                    #ident: match muonc_middle::kv::kv_map_get(map, #key_name) {
                        Some(list) => {
                            let mut out = Vec::with_capacity(list.len());
                            for (i, s) in list.iter().enumerate() {
                                let parsed = <#inner_ty as std::str::FromStr>::from_str(s)
                                    .map_err(|e| format!("invalid value for {}[{}]: {}", #key_name, i, e))?;
                                out.push(parsed);
                            }
                            out
                        }
                        None => Vec::new()
                    }
                };
                build_fields.push(build);
            }
            continue;
        }

        // detect Option<T>
        if let Some(inner_ty) = extract_option_inner(ty) {
            if let Some(def_lit) = default {
                // Option<T> with default -> Some(default) if missing
                let build = quote! {
                    #ident: match muonc_middle::kv::kv_map_get(map, #key_name) {
                        Some(list) => {
                            // take last occurrence
                            let s = list.last().unwrap();
                            let parsed = <#inner_ty as std::str::FromStr>::from_str(s)
                                .map_err(|e| format!("invalid value for {}: {}", #key_name, e))?;
                            Some(parsed)
                        }
                        None => {
                            let parsed = <#inner_ty as std::str::FromStr>::from_str(#def_lit)
                                .map_err(|e| format!("invalid default for {}: {}", #key_name, e))?;
                            Some(parsed)
                        }
                    }
                };
                build_fields.push(build);
            } else {
                // Option<T> no default -> None if missing
                let build = quote! {
                    #ident: match muonc_middle::kv::kv_map_get(map, #key_name) {
                        Some(list) => {
                            let s = list.last().unwrap();
                            let parsed = <#inner_ty as std::str::FromStr>::from_str(s)
                                .map_err(|e| format!("invalid value for {}: {}", #key_name, e))?;
                            Some(parsed)
                        }
                        None => None
                    }
                };
                build_fields.push(build);
            }
            continue;
        }

        // Plain required/with-default field (non-Option, non-Vec)
        if let Some(def_lit) = default {
            let build = quote! {
                #ident: match muonc_middle::kv::kv_map_get(map, #key_name) {
                    Some(list) => {
                        let s = list.last().unwrap();
                        <#ty as std::str::FromStr>::from_str(s)
                            .map_err(|e| format!("invalid value for {}: {}", #key_name, e))?
                    }
                    None => <#ty as std::str::FromStr>::from_str(#def_lit)
                        .map_err(|e| format!("invalid default for {}: {}", #key_name, e))?,
                }
            };
            build_fields.push(build);
        } else {
            let build = quote! {
                #ident: {
                    if let Some(list) = muonc_middle::kv::kv_map_get(map, #key_name) {
                        let s = list.last().unwrap();
                        <#ty as std::str::FromStr>::from_str(s)
                            .map_err(|e| format!("invalid value for {}: {}", #key_name, e))?
                    } else {
                        return Err(format!("missing required key: {} of {}", #key_name, Self::name()));
                    }
                }
            };
            build_fields.push(build);
        }
    }

    let kv_keys_len = kv_keys_entries.len();
    let kv_keys_tokens = quote! {
        [#( #kv_keys_entries ),*]
    };

    let generated = quote! {
        impl muonc_middle::kv::KeyValue for #struct_name {
            fn from_kv_map(map: &[muonc_middle::kv::KvPair]) -> Result<Self, String> {
                Ok(Self {
                    #(#build_fields, )*
                })
            }

            fn keys() -> &'static [(&'static str, &'static str)] {
                static KEYS: [(&str,&str); #kv_keys_len] = #kv_keys_tokens;
                &KEYS
            }

            fn name() -> &'static str {
                #name
            }

            fn short() -> char {
                #short
            }
        }
    };

    generated.into()
}
