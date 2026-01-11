//! Key-value pair for Clap arguments

use std::ffi::OsStr;

use clap::{
    Command,
    builder::{Styles, TypedValueParser, ValueParserFactory},
    error::{Error as ClapError, ErrorKind as ClapErrorKind},
};

pub use muonc_macros::KeyValue;

/// The parsed representation for one -f argument.
/// We register a custom ValueParser so clap's derive will accept `FlagArg` directly as the
/// element type (no `value_parser = ...` needed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KvPair {
    /// The help message
    Help,
    /// A pair.
    Pair(String, String),
}

impl ValueParserFactory for KvPair {
    type Parser = KvPairValueParser;

    fn value_parser() -> Self::Parser {
        KvPairValueParser
    }
}

/// Typed parser object for FlagArg. This type implements `TypedValueParser`.
#[derive(Clone, Debug)]
pub struct KvPairValueParser;

impl TypedValueParser for KvPairValueParser {
    type Value = KvPair;

    fn parse_ref(
        &self,
        _cmd: &Command,
        _arg: Option<&clap::Arg>,
        value: &OsStr,
    ) -> Result<Self::Value, ClapError> {
        // Convert OsStr -> str in a robust manner
        let s = value.to_string_lossy();
        let s = s.trim();

        if s.eq_ignore_ascii_case("help") {
            return Ok(KvPair::Help);
        }

        // accept KEY=VALUE (first '=' splits key/value)
        if let Some(eq) = s.find('=') {
            let key = s[..eq].trim().to_string();
            let val = s[eq + 1..].to_string();
            if key.is_empty() {
                return Err(ClapError::raw(
                    ClapErrorKind::InvalidValue,
                    "empty key in 'KEY=VALUE'\n",
                ));
            }
            return Ok(KvPair::Pair(key, val));
        }

        Err(ClapError::raw(
            ClapErrorKind::InvalidValue,
            format!("expected 'KEY=VALUE' or 'help', but got {:?}\n", value),
        ))
    }
}

pub trait KeyValue: Sized {
    /// Build Self from a map of key -> values (strings).
    fn from_kv_map(map: &[KvPair]) -> Result<Self, String>;

    /// Return a static list of (key, help) for printing.
    fn keys() -> &'static [(&'static str, &'static str)];

    /// Long name of the key value argument.
    fn name() -> &'static str;

    /// Short name of the key value argument.
    fn short() -> char;

    /// Convenience helper to print the help table.
    ///
    /// `arg` must be the short argument name.
    fn print_kv_help() {
        let styles = Styles::styled();
        let header_style = styles.get_header();
        let literal_style = styles.get_literal();

        fn replace_newlines(input: &str, n: usize) -> String {
            let spaces = " ".repeat(n);
            input.replace("\n", &format!("\n    {}", spaces))
        }

        let mut width = 0;

        for (k, _) in Self::keys() {
            width = k.len().max(width);
        }

        println!(
            "{header_style}Available -{arg} KEY=VALUE options:{header_style:#}",
            arg = Self::short()
        );

        println!(
            "  {literal_style}{:width$}{literal_style:#}  Print the help message",
            "help"
        );
        for (k, desc) in Self::keys() {
            println!(
                "  {literal_style}{k:width$}{literal_style:#}  {}",
                replace_newlines(desc, width)
            );
        }
    }
}

pub fn kv_map_get<'map>(map: &'map [KvPair], key: &str) -> Option<Vec<&'map str>> {
    let mut res = vec![];

    for kv in map {
        if let KvPair::Pair(k, v) = kv
            && k == key
        {
            res.push(v as &str);
        }
    }

    (!res.is_empty()).then_some(res)
}
