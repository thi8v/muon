//! Utilities used across the Muon Compiler.

pub mod pretty;

use std::{
    cmp::Ordering,
    fmt::{Display, Write},
};

use muonc_span::symbol::Symbol;
use strsim::sorensen_dice;

use crate::pretty::PrettyDump;

/// returns an `s` if `num` is equal to one.
///
/// use it like that:
/// ```
/// # use muonc_utils::pluralize;
/// let number = 123; // let's imagine `number` is the result of a function
/// let idk = format!("you have {number} dollar{}", pluralize(number));
/// ```
pub fn pluralize<I>(num: I) -> &'static str
where
    I: PartialEq + From<u8>,
{
    if num == I::from(1u8) { "" } else { "s" }
}

/// It's [`list_fmt_with_word`] where word = "or"
pub fn list_fmt(list: &[impl Display]) -> String {
    list_fmt_with_word(list, "or")
}

/// format the list of things with a specified word at the end.
///
/// # Examples
///
/// ```
/// # use muonc_utils::list_fmt_with_word;
/// #
/// assert_eq!(list_fmt_with_word(&[1], ""), "1".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b'], "or"), "a or b".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b'], "and"), "a and b".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b', 'c', 'd', 'e'], "or"), "a, b, c, d or e".to_string());
/// assert_eq!(list_fmt_with_word(&['a', 'b', 'c', 'd', 'e'], "and"), "a, b, c, d and e".to_string());
/// ```
pub fn list_fmt_with_word(list: &[impl Display], word: &str) -> String {
    if list.len() == 1 {
        return list[0].to_string();
    }
    let mut res = String::new();

    for (idx, token) in list.iter().enumerate() {
        if idx == list.len() - 2 {
            write!(res, "{token} ")
        } else if idx == list.len() - 1 {
            write!(res, "{word} {token}")
        } else {
            write!(res, "{token}, ")
        }
        .unwrap();
    }
    res
}

/// Formats a list with commas between
pub fn join_display<T: Display>(items: &[T]) -> String {
    items
        .iter()
        .map(|item| item.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Formats a list with commas between
pub fn join_pretty<I, T: PrettyDump<E>, E>(items: I, extra: &E) -> String
where
    I: IntoIterator<Item = T>,
    I::IntoIter: ExactSizeIterator,
{
    let items = items.into_iter();

    let mut res: Vec<u8> = Vec::new();

    let mut items_str = Vec::with_capacity(items.len());

    for item in items {
        item.dump_to(&mut res, extra);

        items_str.push(String::from_utf8_lossy(&res).into_owned());

        res.clear();
    }

    join_display(&items_str)
}

/// Compute the number of "digits" needed to represent `n` in the given radix (`RADIX`).
///
/// This function supports exactly four radices: 2 (binary), 8 (octal), 10 (decimal), and 16 (hexadecimal).
/// Any other `RADIX` will produce a compile-time error.
///
/// # Parameters
///
/// - `n`: The non-negative integer (`u128`) whose digit-length is computed.
/// - `RADIX`: A const generic specifying the base/radix. Must be one of 2, 8, 10, or 16.
///
/// # Returns
///
/// The count of "digits" (or characters) needed to express `n` in the specified base:
///
/// - **Binary (2)**: number of bits = position of highest set bit + 1 (e.g., 0b10110 = 5 digits).
/// - **Octal (8)**: `ceil(bit_length / 3)` since each octal digit encodes 3 bits.
/// - **Hex (16)**: `ceil(bit_length / 4)` since each hex digit encodes 4 bits.
/// - **Decimal (10)**: uses an unrolled `match` over constant ranges for maximum speed.
///
/// # Panics
///
/// If instantiated with any `RADIX` other than 2, 8, 10, or 16, this will fail
/// at compile time with a type-check error.
///
/// # Complexity
///
/// - **Binary/Octal/Hex**: O(1) bit-operations and arithmetic.
/// - **Decimal**: O(1) range comparisons via a large `match` (constant-time w.r.t. input).
///
/// # Examples
///
/// Basic usage in decimal:
/// ```rust
/// # use muonc_utils::fast_digit_length;
/// let n = 42u128;
/// assert_eq!(fast_digit_length::<10>(n), 2);
/// ```
///
/// Binary bit-length:
/// ```rust
/// # use muonc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<2>(0b101101), 6);
/// ```
///
/// Octal digits:
/// ```rust
/// # use muonc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<8>(0o755), 3);
/// ```
///
/// Hexadecimal digits:
/// ```rust
/// # use muonc_utils::fast_digit_length;
/// assert_eq!(fast_digit_length::<16>(0xdead_beef), 8);
/// ```
pub fn fast_digit_length<const RADIX: u32>(n: u128) -> u32 {
    // Compile‑time check: only these four radices are allowed.
    // The trick below will fail to compile if this assertion can’t be
    // proven true at compile time for your RADIX.
    const {
        assert!(RADIX == 2 || RADIX == 8 || RADIX == 10 || RADIX == 16);
    };

    // Helper for bit‑length: for n>0, 128 - leading_zeros, else 1.
    #[inline]
    fn bit_length(n: u128) -> u32 {
        if n == 0 { 1 } else { 128 - n.leading_zeros() }
    }

    // Dispatch on the const RADIX. Each branch is evaluated at compile time,
    // and the others are dropped completely.
    if RADIX == 2 {
        // binary: one bit per digit
        bit_length(n)
    } else if RADIX == 8 {
        // octal: 3 bits per digit → ceil(bitlen/3)
        let bits = bit_length(n);
        bits.div_ceil(3)
    } else if RADIX == 16 {
        // hex: 4 bits per digit → ceil(bitlen/4)
        let bits = bit_length(n);
        bits.div_ceil(4)
    } else {
        // decimal: unrolled range match, up to 39 digits for u128
        match n {
            0..=9                      => 1,
            10..=99                    => 2,
            100..=999                  => 3,
            1_000..=9_999              => 4,
            10_000..=99_999            => 5,
            100_000..=999_999          => 6,
            1_000_000..=9_999_999      => 7,
            10_000_000..=99_999_999    => 8,
            100_000_000..=999_999_999  => 9,
            1_000_000_000..=9_999_999_999 => 10,
            10_000_000_000..=99_999_999_999 => 11,
            100_000_000_000..=999_999_999_999 => 12,
            1_000_000_000_000..=9_999_999_999_999 => 13,
            10_000_000_000_000..=99_999_999_999_999 => 14,
            100_000_000_000_000..=999_999_999_999_999 => 15,
            1_000_000_000_000_000..=9_999_999_999_999_999 => 16,
            10_000_000_000_000_000..=99_999_999_999_999_999 => 17,
            100_000_000_000_000_000..=999_999_999_999_999_999 => 18,
            1_000_000_000_000_000_000..=9_999_999_999_999_999_999 => 19,
            10_000_000_000_000_000_000..=99_999_999_999_999_999_999 => 20,
            100_000_000_000_000_000_000..=999_999_999_999_999_999_999 => 21,
            1_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999 => 22,
            10_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999 => 23,
            100_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999 => 24,
            1_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999 => 25,
            10_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999 => 26,
            100_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999 => 27,
            1_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999 => 28,
            10_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999 => 29,
            100_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999 => 30,
            1_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999 => 31,
            10_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999 => 32,
            100_000_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999_999 => 33,
            1_000_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999_999 => 34,
            10_000_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999_999 => 35,
            100_000_000_000_000_000_000_000_000_000_000_000..=999_999_999_999_999_999_999_999_999_999_999_999 => 36,
            1_000_000_000_000_000_000_000_000_000_000_000_000..=9_999_999_999_999_999_999_999_999_999_999_999_999 => 37,
            10_000_000_000_000_000_000_000_000_000_000_000_000..=99_999_999_999_999_999_999_999_999_999_999_999_999 => 38,
            _ /* up to u128::MAX */   => 39,
        }
    }
}

/// Adaptive threshold based on word length
pub fn adaptive_threshold(len: usize) -> f64 {
    match len {
        0..=3 => 0.9,
        4..=6 => 0.8,
        7..=12 => 0.7,
        _ => 0.6,
    }
}

/// Suggests the closest match from a dictionary to a given word.
///
/// NB: this function is internally backed by Sørensen-Dice coefficient, nothing
/// is returned if the maximun score isn't above [`adaptive_threshold`].
pub fn suggest_similar(
    query: Symbol,
    dictionary: impl IntoIterator<Item = Symbol>,
) -> Option<Symbol> {
    let len = query.as_str().chars().count();
    let threshold = adaptive_threshold(len);

    dictionary
        .into_iter()
        .map(|word| {
            let score = sorensen_dice(query.as_str(), word.as_str());

            (word, score)
        })
        .filter(|(_, score)| *score >= threshold)
        .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(Ordering::Equal))
        .map(|(word, _)| word)
}
