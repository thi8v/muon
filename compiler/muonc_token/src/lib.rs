//! Token related stuff

use std::{
    borrow::Cow,
    cmp::Ordering,
    fmt::{self, Debug, Display},
    io::{self, Write},
    mem,
    ops::Range,
};

use muonc_span::{
    DUMMY_SP, Span, span,
    symbol::{self, Symbol, sym},
};

/// A list of tokens is ensured to end with the `Eof` token.
#[derive(Clone, Default, PartialEq)]
pub struct TokenStream {
    tokens: Vec<Token>,
    finished: bool,
    eof: Option<Token>,
}

impl TokenStream {
    /// Create a new empty TokenStream.
    pub fn new() -> TokenStream {
        TokenStream {
            tokens: Vec::new(),
            finished: false,
            eof: None,
        }
    }

    /// Finish a TokenStream, will ensure the last token is an end of file token
    /// so if it's not this function will **panic**.
    #[track_caller]
    pub fn finish(&mut self) {
        assert!(!self.finished, "token stream already finished");
        assert_eq!(
            self.tokens.last().map(|t| &t.tt),
            Some(&TokenType::Eof),
            "the last token of a token stream must be the end of file token."
        );

        self.finished = true;
        self.eof = Some(self.tokens.last().unwrap().clone());
    }

    /// Pushes the TokenType with its start and end offsets and return `true`
    /// if the token is End Of File
    #[track_caller]
    pub fn push(&mut self, token: Token) -> bool {
        assert!(
            !self.finished,
            "can't push a token to the token stream if it's already finished"
        );
        assert_ne!(
            token.tt,
            TokenType::Dummy,
            "Dummy tokens are placeholders, they cannot be pushed into a token stream."
        );

        let is_eof = token.tt == TokenType::Eof;

        self.tokens.push(token);

        is_eof
    }

    /// Get the token a the index `idx`, always returns the Eof token if `idx`
    /// is out of bounds of the stream.
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn get(&self, idx: usize) -> &Token {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );
        self.tokens.get(idx).unwrap_or_else(|| self.get_eof())
    }

    /// Get a range of token, if the range exceeds the number of token it will
    /// return `Eof` token.
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn get_slice<'a>(&'a self, range: Range<usize>) -> Cow<'a, [Token]> {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );
        let start = range.start;
        let end = range.end;

        // Empty range
        if start > end {
            return Cow::Borrowed(&[]);
        }

        // Compute requested length safely (avoid overflow)
        let len = match end.checked_sub(start).filter(|d| *d <= isize::MAX as usize) {
            Some(l) => l,
            None => {
                // Overflowed indices or capacity would overflow.
                return Cow::Borrowed(&[]);
            }
        };

        // If the entire inclusive range sits inside `data`, return a borrowed slice.
        if end < self.tokens.len() {
            return Cow::Borrowed(&self.tokens[start..end]);
        }

        // Otherwise build an owned Vec:
        // 1) copy the in-bounds contiguous portion efficiently with extend_from_slice
        // 2) resize to fill remaining requested length with zeros
        let mut out = Vec::with_capacity(len);
        if start < self.tokens.len() {
            let available = self.tokens.len() - start;
            let to_copy = std::cmp::min(len, available);
            out.extend_from_slice(&self.tokens[start..start + to_copy]);
        }

        if out.len() < len {
            out.resize(len, self.get_eof().clone()); // append Eofs
        }

        Cow::Owned(out)
    }

    /// Get the last token of a finished token stream, it will always be the
    /// Eof token
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[inline(always)]
    #[track_caller]
    pub fn get_eof(&self) -> &Token {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );

        let Some(eof) = &self.eof else {
            // NB: `TokenStream::eof` is always `Some(..)` when it is `TokenStream::finished`
            unreachable!();
        };

        eof
    }

    /// The count of tokens, including the last Eof token.
    pub fn count(&self) -> usize {
        self.tokens.len()
    }

    /// Replace the token at index `idx` with two tokens, `replace_with`.
    ///
    /// # Note
    ///
    /// It's the only operation allowed to mutate the content of the token
    /// stream if it's not finished.
    pub fn replace_with_two(&mut self, idx: usize, replace_with: [Token; 2]) {
        if idx <= self.count() {
            let [first_t, second_t] = replace_with;

            // SAFETY: we checked the boundaries just above
            let first = unsafe { self.tokens.get_unchecked_mut(idx) };
            *first = first_t;

            self.tokens.insert(idx + 1, second_t);
        } else {
            unimplemented!("cannot `replace_with_two` if idx >= self.count().")
        }
    }

    /// Format the token stream
    pub fn fmt(&self, out: &mut impl Write, src: &str) -> io::Result<()> {
        writeln!(out, "{{")?;

        for token in &self.tokens {
            token.fmt(out, src)?;
        }

        writeln!(out, "}}")?;
        Ok(())
    }
}

impl Debug for TokenStream {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(&self.tokens).finish()
    }
}

/// A muon token.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub tt: TokenType,
    pub span: Span,
}

impl Token {
    /// Format the token to `out`.
    pub fn fmt<W: Write>(&self, out: &mut W, src: &str) -> io::Result<()> {
        let p_common = |out: &mut W| -> io::Result<()> {
            writeln!(out, "    span: {};", self.span)?;
            writeln!(out, "    lexeme: `{}`;", self.span.slice_str(src))?;
            Ok(())
        };

        let p_punct = |out: &mut W, p: &TokenType| -> io::Result<()> {
            writeln!(out, "  {{")?;
            writeln!(out, "    tt: punct {p:?};")?;
            p_common(out)?;
            writeln!(out, "  }},")?;
            Ok(())
        };

        let tt = &self.tt;
        match tt {
            TokenType::LParen
            | TokenType::RParen
            | TokenType::LBracket
            | TokenType::RBracket
            | TokenType::LCurly
            | TokenType::RCurly
            | TokenType::Plus
            | TokenType::Minus
            | TokenType::Star
            | TokenType::Slash
            | TokenType::Colon
            | TokenType::ColonColon
            | TokenType::Comma
            | TokenType::Eq
            | TokenType::EqEq
            | TokenType::BangEq
            | TokenType::Bang
            | TokenType::LtEq
            | TokenType::Lt
            | TokenType::LtLt
            | TokenType::Gt
            | TokenType::GtGt
            | TokenType::GtEq
            | TokenType::Semi
            | TokenType::MinusGt
            | TokenType::Caret
            | TokenType::And
            | TokenType::AndAnd
            | TokenType::Or
            | TokenType::OrOr
            | TokenType::Percent
            | TokenType::Dot
            | TokenType::DotStar
            | TokenType::Pound => {
                p_punct(out, tt)?;
            }
            TokenType::Kw(kw) => {
                let kw = kw.as_symbol();

                writeln!(out, "  {{")?;
                writeln!(out, "    tt: keyword '{}';", kw)?;
                p_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Ident(id) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: ident '{id}';")?;
                p_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Lit(Lit { kind, value, tag }) => {
                writeln!(out, "  {{")?;

                writeln!(out, "    tt: {kind} {};", value.as_display_with(*kind))?;

                if let Some(tag) = tag {
                    writeln!(out, "    tag: {tag:?};")?;
                }

                p_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Eof => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: end of file;")?;
                writeln!(out, "    span: {};", self.span)?;
                writeln!(out, "    lexeme: N/A;")?;
                writeln!(out, "  }},")?;
            }
            TokenType::Dummy => unreachable!(),
        }

        Ok(())
    }

    /// Create a new dummy token.
    pub const fn dummy() -> Token {
        Token {
            tt: TokenType::Dummy,
            span: DUMMY_SP,
        }
    }

    /// Try to break up the token in two tokens.
    pub fn break_up(&self) -> Option<[Token; 2]> {
        let diff = self.span.hi - self.span.lo;
        assert_eq!(
            self.tt.length()?,
            diff,
            "can't break a token that has an unexpected span."
        );

        let [first_tt, second_tt] = self.tt.break_up()?;

        let first_span = span(
            self.span.lo,
            self.span.lo + first_tt.length()?,
            self.span.fid,
        );
        let second_span = span(
            self.span.hi - second_tt.length()?,
            self.span.hi,
            self.span.fid,
        );

        Some([
            Token {
                tt: first_tt,
                span: first_span,
            },
            Token {
                tt: second_tt,
                span: second_span,
            },
        ])
    }
}

impl PartialEq<TokenType> for Token {
    fn eq(&self, other: &TokenType) -> bool {
        self.tt == *other
    }
}

/// A muon token type.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum TokenType {
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LCurly,
    /// `}`
    RCurly,
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `:`
    Colon,
    /// `::`
    ColonColon,
    /// `,`
    Comma,
    /// `=`
    Eq,
    /// `==`
    EqEq,
    /// `!=`
    BangEq,
    /// `!`
    Bang,
    /// `<=`
    LtEq,
    /// `<`
    Lt,
    /// `<<`
    LtLt,
    /// `>`
    Gt,
    /// `>>`
    GtGt,
    /// `>=`
    GtEq,
    /// `;`
    Semi,
    /// `->`
    MinusGt,
    /// `^`
    Caret,
    /// `&`
    And,
    /// `&&`
    AndAnd,
    /// `|`
    Or,
    /// `||`
    OrOr,
    /// `%`
    Percent,
    /// `.`
    Dot,
    /// `.*`
    DotStar,
    /// `#`
    Pound,

    /// keyword.
    Kw(Keyword),

    /// identifier
    Ident(Symbol),
    /// literal
    Lit(Lit),
    /// End Of File
    Eof,
    /// this is a dummy token, it is used when encountering a comment or a
    /// whitespace it can't be pushed into a token stream.
    #[default]
    Dummy,
}

impl TokenType {
    /// Try to break this token type into if possible.
    ///
    /// eg: `ColonColon` -> `Some((Colon, Colon))`.
    pub fn break_up(&self) -> Option<[TokenType; 2]> {
        use TokenType as Tt;

        match self {
            Tt::ColonColon => Some([Tt::Colon, Tt::Colon]),
            Tt::EqEq => Some([Tt::Eq, Tt::Eq]),
            Tt::BangEq => Some([Tt::Bang, Tt::Eq]),
            Tt::LtEq => Some([Tt::Lt, Tt::Eq]),
            Tt::LtLt => Some([Tt::Lt, Tt::Lt]),
            Tt::GtGt => Some([Tt::Gt, Tt::Gt]),
            Tt::GtEq => Some([Tt::Gt, Tt::Eq]),
            Tt::MinusGt => Some([Tt::Minus, Tt::Gt]),
            Tt::AndAnd => Some([Tt::And, Tt::And]),
            Tt::OrOr => Some([Tt::Or, Tt::Or]),
            Tt::DotStar => Some([Tt::Dot, Tt::Star]),
            _ => None,
        }
    }

    /// Returns the length of a token, if TokenType is ident or a literal or
    /// something that can have a variable length, None is returned.
    ///
    /// eg: `TokenType::EqEq` -> `Some(2)`
    pub fn length(&self) -> Option<usize> {
        match self {
            Self::Eof => Some(0),

            Self::LParen
            | Self::RParen
            | Self::LBracket
            | Self::RBracket
            | Self::LCurly
            | Self::RCurly
            | Self::Plus
            | Self::Minus
            | Self::Star
            | Self::Slash
            | Self::Colon
            | Self::Comma
            | Self::Eq
            | Self::Bang
            | Self::Lt
            | Self::Gt
            | Self::Semi
            | Self::Caret
            | Self::And
            | Self::Or
            | Self::Percent
            | Self::Dot
            | Self::Pound => Some(1),

            Self::ColonColon
            | Self::EqEq
            | Self::BangEq
            | Self::LtEq
            | Self::LtLt
            | Self::GtGt
            | Self::MinusGt
            | Self::AndAnd
            | Self::OrOr
            | Self::GtEq
            | Self::DotStar
            | Self::Kw(Keyword::As)
            | Self::Kw(Keyword::If)
            | Self::Kw(Keyword::In)
            | Self::Kw(Keyword::Pub) => Some(2),

            Self::Kw(Keyword::For)
            | Self::Kw(Keyword::Fun)
            | Self::Kw(Keyword::Let)
            | Self::Kw(Keyword::Mut) => Some(3),

            Self::Kw(Keyword::Else)
            | Self::Kw(Keyword::Impl)
            | Self::Kw(Keyword::Loop)
            | Self::Kw(Keyword::Null)
            | Self::Kw(Keyword::True)
            | Self::Kw(Keyword::Self_) => Some(4),

            Self::Kw(Keyword::Break)
            | Self::Kw(Keyword::False)
            | Self::Kw(Keyword::Trait)
            | Self::Kw(Keyword::While) => Some(5),

            Self::Kw(Keyword::Extern) | Self::Kw(Keyword::Return) => Some(6),

            Self::Kw(Keyword::Comptime) | Self::Kw(Keyword::Continue) => Some(8),

            Self::Ident(sym) => Some(sym.len()),
            Self::Lit(_) => None,
            Self::Dummy => None,
        }
    }
}

impl Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenType as Tt;

        match self {
            Tt::LParen => write!(f, "`(`"),
            Tt::RParen => write!(f, "`)`"),
            Tt::LBracket => write!(f, "`[`"),
            Tt::RBracket => write!(f, "`]`"),
            Tt::LCurly => write!(f, "`{{`"),
            Tt::RCurly => write!(f, "`}}`"),
            Tt::Plus => write!(f, "`+`"),
            Tt::Minus => write!(f, "`-`"),
            Tt::Star => write!(f, "`*`"),
            Tt::Slash => write!(f, "`/`"),
            Tt::Colon => write!(f, "`:`"),
            Tt::ColonColon => write!(f, "`::`"),
            Tt::Comma => write!(f, "`,`"),
            Tt::Eq => write!(f, "`=`"),
            Tt::EqEq => write!(f, "`==`"),
            Tt::BangEq => write!(f, "`!=`"),
            Tt::Bang => write!(f, "`!`"),
            Tt::LtEq => write!(f, "`<=`"),
            Tt::Lt => write!(f, "`<`"),
            Tt::LtLt => write!(f, "`<<`"),
            Tt::Gt => write!(f, "`>`"),
            Tt::GtGt => write!(f, "`>>`"),
            Tt::GtEq => write!(f, "`>=`"),
            Tt::Semi => write!(f, "`;`"),
            Tt::MinusGt => write!(f, "`->`"),
            Tt::Caret => write!(f, "`^`"),
            Tt::And => write!(f, "`&`"),
            Tt::AndAnd => write!(f, "`&&`"),
            Tt::Or => write!(f, "`|`"),
            Tt::OrOr => write!(f, "`||`"),
            Tt::Percent => write!(f, "`%`"),
            Tt::Dot => write!(f, "`.`"),
            Tt::DotStar => write!(f, "`.*`"),
            Tt::Pound => write!(f, "`#`"),
            Tt::Kw(kw) => write!(f, "keyword `{}`", kw.as_symbol()),
            Tt::Ident(_) => write!(f, "identifier"),
            Tt::Lit(Lit { kind, .. }) => write!(f, "{kind} literal"),
            Tt::Eof => write!(f, "end of file"),
            Tt::Dummy => write!(f, "not a token"),
        }
    }
}

/// Muon's keywords.
///
/// # How to add a keyword?
///
/// 1. Add the keyword in this enum in alphabetical order
/// 2. Add the keyword in the predefined symbols in [`muonc_span::symbol`]
/// 3. Add the keyword to the tests: `symbol_to_keyword` and `keyword_to_symbol`
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Keyword {
    /// `as`
    As,
    /// `break`
    Break,
    /// `comptime`
    Comptime,
    /// `continue`
    Continue,
    /// `else`
    Else,
    /// `extern`
    Extern,
    /// `false`
    False,
    /// `for`
    For,
    /// `fun`
    Fun,
    /// `if`
    If,
    /// `impl`
    Impl,
    /// `in`
    In,
    /// `let`
    Let,
    /// `loop`
    Loop,
    /// `mut`
    Mut,
    /// `null`
    Null,
    /// `pub`
    Pub,
    /// `return`
    Return,
    /// `self`
    Self_,
    /// `trait`
    Trait,
    /// `true`
    True,
    /// `while`
    While,
}

impl Keyword {
    /// Converts this keyword into a symbol
    pub fn as_symbol(&self) -> Symbol {
        let idx = *self as u8;

        Symbol::new(
            symbol::categories::KEYWORD_START
                .id()
                .wrapping_add(idx as u32),
        )
    }

    /// Try to convert a symbol to a keyword
    pub fn from_symbol(sym: Symbol) -> Option<Keyword> {
        if !sym.is_keyword() {
            return None;
        }

        let idx = sym.as_usize() - symbol::categories::KEYWORD_START.as_usize();

        // SAFETY: this operation is safe because we checked `idx` was a valid keyword.
        unsafe { Some(mem::transmute::<u8, Keyword>(idx as u8)) }
    }
}

impl PartialEq<ExpToken> for TokenType {
    fn eq(&self, other: &ExpToken) -> bool {
        match self {
            Self::LParen { .. } => *other == ExpToken::LParen,
            Self::RParen { .. } => *other == ExpToken::RParen,
            Self::LBracket { .. } => *other == ExpToken::LBracket,
            Self::RBracket { .. } => *other == ExpToken::RBracket,
            Self::LCurly { .. } => *other == ExpToken::LCurly,
            Self::RCurly { .. } => *other == ExpToken::RCurly,
            Self::Plus { .. } => *other == ExpToken::Plus,
            Self::Minus { .. } => *other == ExpToken::Minus,
            Self::Star { .. } => *other == ExpToken::Star,
            Self::Slash { .. } => *other == ExpToken::Slash,
            Self::Colon { .. } => *other == ExpToken::Colon,
            Self::ColonColon { .. } => *other == ExpToken::ColonColon,
            Self::Comma { .. } => *other == ExpToken::Comma,
            Self::Eq { .. } => *other == ExpToken::Eq,
            Self::EqEq { .. } => *other == ExpToken::EqEq,
            Self::BangEq { .. } => *other == ExpToken::BangEq,
            Self::Bang { .. } => *other == ExpToken::Bang,
            Self::LtEq { .. } => *other == ExpToken::LtEq,
            Self::Lt { .. } => *other == ExpToken::Lt,
            Self::LtLt { .. } => *other == ExpToken::LtLt,
            Self::Gt { .. } => *other == ExpToken::Gt,
            Self::GtGt { .. } => *other == ExpToken::GtGt,
            Self::GtEq { .. } => *other == ExpToken::GtEq,
            Self::Semi { .. } => *other == ExpToken::Semi,
            Self::MinusGt { .. } => *other == ExpToken::MinusGt,
            Self::Caret { .. } => *other == ExpToken::Caret,
            Self::And { .. } => *other == ExpToken::And,
            Self::AndAnd { .. } => *other == ExpToken::AndAnd,
            Self::Or { .. } => *other == ExpToken::Or,
            Self::OrOr { .. } => *other == ExpToken::OrOr,
            Self::Percent { .. } => *other == ExpToken::Percent,
            Self::Dot { .. } => *other == ExpToken::Dot,
            Self::DotStar { .. } => *other == ExpToken::DotStar,
            Self::Pound { .. } => *other == ExpToken::Pound,
            Self::Kw(Keyword::As) => *other == ExpToken::KwAs,
            Self::Kw(Keyword::Break) => *other == ExpToken::KwBreak,
            Self::Kw(Keyword::Comptime) => *other == ExpToken::KwComptime,
            Self::Kw(Keyword::Continue) => *other == ExpToken::KwContinue,
            Self::Kw(Keyword::Else) => *other == ExpToken::KwElse,
            Self::Kw(Keyword::Extern) => *other == ExpToken::KwExtern,
            Self::Kw(Keyword::False) => *other == ExpToken::KwFalse,
            Self::Kw(Keyword::For) => *other == ExpToken::KwFor,
            Self::Kw(Keyword::Fun) => *other == ExpToken::KwFun,
            Self::Kw(Keyword::If) => *other == ExpToken::KwIf,
            Self::Kw(Keyword::Impl) => *other == ExpToken::KwImpl,
            Self::Kw(Keyword::In) => *other == ExpToken::KwIn,
            Self::Kw(Keyword::Let) => *other == ExpToken::KwLet,
            Self::Kw(Keyword::Loop) => *other == ExpToken::KwLoop,
            Self::Kw(Keyword::Mut) => *other == ExpToken::KwMut,
            Self::Kw(Keyword::Null) => *other == ExpToken::KwNull,
            Self::Kw(Keyword::Pub) => *other == ExpToken::KwPub,
            Self::Kw(Keyword::Return) => *other == ExpToken::KwReturn,
            Self::Kw(Keyword::Self_) => *other == ExpToken::KwSelf,
            Self::Kw(Keyword::Trait) => *other == ExpToken::KwTrait,
            Self::Kw(Keyword::True) => *other == ExpToken::KwTrue,
            Self::Kw(Keyword::While) => *other == ExpToken::KwWhile,
            Self::Ident { .. } => *other == ExpToken::Ident,
            Self::Lit { .. } => *other == ExpToken::Lit,
            Self::Eof { .. } => *other == ExpToken::Eof,
            Self::Dummy { .. } => *other == ExpToken::Dummy,
        }
    }
}

/// A literal token
///
/// # Note
///
/// The `kind` and `value` must match, a literal with kind [`LitKind::Float`]
/// and value `LitVal::Int(12)` is invalid, and **can lead to UB**.
#[derive(Clone)]
pub struct Lit {
    pub kind: LitKind,
    value: LitValue,
    pub tag: Option<Symbol>,
}

impl Lit {
    /// Create a new `char` literal.
    pub const fn char(char: char) -> Lit {
        Lit {
            kind: LitKind::Char,
            value: LitValue { char },
            tag: None,
        }
    }

    /// Create a new `int` literal.
    pub const fn int(int: u128) -> Lit {
        Lit {
            kind: LitKind::Integer,
            value: LitValue { int },
            tag: None,
        }
    }

    /// Create a new `float` literal.
    pub const fn float(float: f64) -> Lit {
        Lit {
            kind: LitKind::Float,
            value: LitValue { float },
            tag: None,
        }
    }

    /// Create a new `string` literal.
    pub const fn string(str: Symbol) -> Lit {
        Lit {
            kind: LitKind::Str,
            value: LitValue { str },
            tag: None,
        }
    }
}

impl PartialOrd for Lit {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Lit {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.kind.cmp(&other.kind) {
            Ordering::Equal => {}
            ord => return ord,
        }

        match self.value.cmp(&other.value, self.kind) {
            Ordering::Equal => {}
            ord => return ord,
        }

        self.tag.cmp(&other.tag)
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.value.eq(&other.value, self.kind) && self.tag == other.tag
    }
}

impl Eq for Lit {}

impl Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lit")
            .field("kind", &self.kind)
            .field("value", self.value.as_debug_with(self.kind))
            .field("tag", &self.tag)
            .finish()
    }
}

/// A kind of literal token
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitKind {
    Char,
    Integer,
    Float,
    Str,
}

impl Display for LitKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Char => write!(f, "char"),
            Self::Integer => write!(f, "integer"),
            Self::Float => write!(f, "float"),
            Self::Str => write!(f, "string"),
        }
    }
}

#[derive(Clone, Copy)]
pub union LitValue {
    char: char,
    int: u128,
    float: f64,
    str: Symbol,
}

impl LitValue {
    fn as_debug_with(&self, kind: LitKind) -> &dyn Debug {
        // SAFETY: it's fine we access it with a kind.
        unsafe {
            match kind {
                LitKind::Char => &self.char,
                LitKind::Integer => &self.int,
                LitKind::Float => &self.float,
                LitKind::Str => &self.str,
            }
        }
    }

    fn as_display_with(&self, kind: LitKind) -> &dyn Display {
        // SAFETY: it's fine we access it with a kind.
        unsafe {
            match kind {
                LitKind::Char => &self.char,
                LitKind::Integer => &self.int,
                LitKind::Float => &self.float,
                LitKind::Str => &self.str,
            }
        }
    }

    fn eq(&self, other: &LitValue, kind: LitKind) -> bool {
        // SAFETY: it's fine we access it with a kind.
        unsafe {
            match kind {
                LitKind::Char => self.char == other.char,
                LitKind::Integer => self.int == other.int,
                LitKind::Float => self.float == other.float,
                LitKind::Str => self.str == other.str,
            }
        }
    }

    fn cmp(&self, other: &LitValue, kind: LitKind) -> Ordering {
        // SAFETY: it's fine we access it with a kind.
        unsafe {
            match kind {
                LitKind::Char => self.char.cmp(&other.char),
                LitKind::Integer => self.int.cmp(&other.int),
                LitKind::Float => self.float.total_cmp(&other.float),
                LitKind::Str => self.str.cmp(&other.str),
            }
        }
    }
}

/// Expected token.
///
/// This is used by `E006`, `ExpectedToken`, diagnostics to avoid
/// creating empty tokens when a TokenType expects a value, so [`ExpToken`]
/// don't expect a value.
///
/// This is also used by `check` and `expect` methods of the parser.
///
/// *This is inspired by [rustc's TokenType].*
///
/// [rustc's TokenType]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/parser/token_type/enum.TokenType.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExpToken {
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Plus,
    Minus,
    Star,
    Slash,
    Colon,
    ColonColon,
    Comma,
    Eq,
    EqEq,
    BangEq,
    Bang,
    LtEq,
    Lt,
    LtLt,
    Gt,
    GtGt,
    GtEq,
    Semi,
    MinusGt,
    Caret,
    And,
    AndAnd,
    Or,
    OrOr,
    Percent,
    Dot,
    DotStar,
    Pound,
    KwAs,
    KwBreak,
    KwComptime,
    KwContinue,
    KwElse,
    KwExtern,
    KwFalse,
    KwFor,
    KwFun,
    KwIf,
    KwImpl,
    KwIn,
    KwLet,
    KwLoop,
    KwMut,
    KwNull,
    KwPub,
    KwReturn,
    KwSelf,
    KwTrait,
    KwTrue,
    KwWhile,
    Ident,
    Lit,
    Eof,
    Dummy,
}

impl ExpToken {
    /// The count of how many expected token there is.
    pub const COUNT: usize = 60;
}

impl Display for ExpToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExpToken as Et;

        match self {
            Et::LParen => write!(f, "`(`"),
            Et::RParen => write!(f, "`)`"),
            Et::LBracket => write!(f, "`[`"),
            Et::RBracket => write!(f, "`]`"),
            Et::LCurly => write!(f, "`{{`"),
            Et::RCurly => write!(f, "`}}`"),
            Et::Plus => write!(f, "`+`"),
            Et::Minus => write!(f, "`-`"),
            Et::Star => write!(f, "`*`"),
            Et::Slash => write!(f, "`/`"),
            Et::Colon => write!(f, "`:`"),
            Et::ColonColon => write!(f, "`::`"),
            Et::Comma => write!(f, "`,`"),
            Et::Eq => write!(f, "`=`"),
            Et::EqEq => write!(f, "`==`"),
            Et::BangEq => write!(f, "`!=`"),
            Et::Bang => write!(f, "`!`"),
            Et::LtEq => write!(f, "`<=`"),
            Et::Lt => write!(f, "`<`"),
            Et::LtLt => write!(f, "`<<`"),
            Et::Gt => write!(f, "`>`"),
            Et::GtGt => write!(f, "`>>`"),
            Et::GtEq => write!(f, "`>=`"),
            Et::Semi => write!(f, "`;`"),
            Et::MinusGt => write!(f, "`->`"),
            Et::Caret => write!(f, "`^`"),
            Et::And => write!(f, "`&`"),
            Et::AndAnd => write!(f, "`&&`"),
            Et::Or => write!(f, "`|`"),
            Et::OrOr => write!(f, "`||`"),
            Et::Percent => write!(f, "`%`"),
            Et::Dot => write!(f, "`.`"),
            Et::DotStar => write!(f, "`.*`"),
            Et::Pound => write!(f, "`#`"),
            Et::KwAs => write!(f, "keyword `as`"),
            Et::KwBreak => write!(f, "keyword `break`"),
            Et::KwComptime => write!(f, "keyword `comptime`"),
            Et::KwContinue => write!(f, "keyword `continue`"),
            Et::KwElse => write!(f, "keyword `else`"),
            Et::KwExtern => write!(f, "keyword `extern`"),
            Et::KwFalse => write!(f, "keyword `false`"),
            Et::KwFor => write!(f, "keyword `for`"),
            Et::KwFun => write!(f, "keyword `fun`"),
            Et::KwIf => write!(f, "keyword `if`"),
            Et::KwImpl => write!(f, "keyword `impl`"),
            Et::KwIn => write!(f, "keyword `in`"),
            Et::KwLet => write!(f, "keyword `let`"),
            Et::KwLoop => write!(f, "keyword `loop`"),
            Et::KwMut => write!(f, "keyword `mut`"),
            Et::KwNull => write!(f, "keyword `null`"),
            Et::KwPub => write!(f, "keyword `pub`"),
            Et::KwReturn => write!(f, "keyword `return`"),
            Et::KwSelf => write!(f, "keyword `self`"),
            Et::KwTrait => write!(f, "keyword `trait`"),
            Et::KwTrue => write!(f, "keyword `true`"),
            Et::KwWhile => write!(f, "keyword `while`"),
            Et::Ident => write!(f, "identifier"),
            Et::Lit => write!(f, "literal"),
            Et::Eof => write!(f, "end of file"),
            Et::Dummy => unreachable!(),
        }
    }
}

impl PartialEq<TokenType> for ExpToken {
    fn eq(&self, other: &TokenType) -> bool {
        other.eq(self)
    }
}

/// A bitset used by `Parser::check`, `Parser::eat` and `Parser::expect`
///
/// *This is inspired by [rustc's TokenTypeSet].*
///
/// [rustc's TokenTypeSet]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/parser/token_type/struct.TokenTypeSet.html
#[derive(Clone, Copy, PartialEq)]
pub struct ExpTokenSet(u64);

impl ExpTokenSet {
    /// Create a new ExpToken Set.
    pub fn new() -> ExpTokenSet {
        ExpTokenSet(0)
    }

    /// Insert an ExpToken inside the set.
    pub fn insert(&mut self, exp: ExpToken) {
        self.0 |= 1u64 << exp as u64;
    }

    /// Does this ExpTokenSet contains `exp`?
    pub fn contains(&self, exp: ExpToken) -> bool {
        self.0 & (1u64 << exp as u64) != 0
    }

    /// Clear the set.
    pub fn clear(&mut self) {
        self.0 = 0;
    }

    /// Create an iterator of [`ExpToken`].
    pub fn iter(&self) -> ExpTokenSetIter {
        ExpTokenSetIter(*self)
    }
}

impl Default for ExpTokenSet {
    fn default() -> Self {
        ExpTokenSet::new()
    }
}

impl Debug for ExpTokenSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let exps: Vec<_> = self.iter().map(|exp| format!("{exp:?}")).collect();

        write!(f, "ExpTokenSet({})", exps.join(" | "))
    }
}

/// Iterator of [`ExpToken`] in a [`ExpTokenSet`].
pub struct ExpTokenSetIter(ExpTokenSet);

impl Iterator for ExpTokenSetIter {
    type Item = ExpToken;

    fn next(&mut self) -> Option<Self::Item> {
        let num_bits = (size_of_val(&self.0.0) * 8) as u64;
        debug_assert_eq!(num_bits, 64);

        let zeros = self.0.0.trailing_zeros() as u64;

        if zeros == num_bits {
            None
        } else {
            self.0.0 &= !(1 << zeros);

            if !(0..=60).contains(&zeros) {
                panic!("invalid token repr {zeros}")
            }

            Some(unsafe { mem::transmute::<u8, ExpToken>(zeros as u8) })
        }
    }
}

/// Weak keywords list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WeakKw {
    /// `import` used in import directives.
    Import,
    /// `mod` used in mod directives.
    Mod,
}

impl WeakKw {
    /// The textual representation of this weak keyword.
    pub fn as_symbol(&self) -> Symbol {
        match self {
            Self::Import => sym::Import,
            Self::Mod => sym::Mod,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use muonc_span::FileId;
    use symbol::sym;

    fn build_ts() -> TokenStream {
        let mut ts = TokenStream::new();

        ts.push(Token {
            tt: TokenType::LParen,
            span: span(0, 1, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::RParen,
            span: span(1, 2, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::Kw(Keyword::As),
            span: span(2, 4, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::Kw(Keyword::Comptime),
            span: span(4, 12, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::Eof,
            span: span(12, 12, FileId::ROOT_MODULE),
        });
        ts.finish();

        ts
    }

    #[test]
    fn token_stream_get_slice_in_bounds_returns_borrowed_slice() {
        let ts = build_ts();
        let cow = ts.get_slice(1..4);

        match cow {
            Cow::Borrowed(s) => assert_eq!(
                s,
                &[
                    Token {
                        tt: TokenType::RParen,
                        span: span(1, 2, FileId::ROOT_MODULE)
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::As),
                        span: span(2, 4, FileId::ROOT_MODULE)
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::Comptime),
                        span: span(4, 12, FileId::ROOT_MODULE)
                    },
                ]
            ),
            Cow::Owned(_) => panic!("expected Borrowed for in-bounds range"),
        }
    }

    #[test]
    fn token_stream_get_slice_out_of_bounds_pads_with_zeros_and_returns_owned() {
        let ts = build_ts();
        let cow = ts.get_slice(0..6);

        let root = FileId::ROOT_MODULE;

        match cow {
            Cow::Owned(v) => assert_eq!(
                v,
                vec![
                    Token {
                        tt: TokenType::LParen,
                        span: span(0, 1, root)
                    },
                    Token {
                        tt: TokenType::RParen,
                        span: span(1, 2, root),
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::As),
                        span: span(2, 4, root)
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::Comptime),
                        span: span(4, 12, root)
                    },
                    ts.get_eof().clone(),
                    ts.get_eof().clone(),
                ]
            ),
            Cow::Borrowed(_) => panic!("expected Owned for out-of-bounds range"),
        }
    }

    #[test]
    fn token_stream_get_slice_partial_overlap_owned_and_padded() {
        let ts = build_ts();
        let cow = ts.get_slice(1..6);

        let root = FileId::ROOT_MODULE;

        match cow {
            Cow::Owned(v) => assert_eq!(
                v,
                vec![
                    Token {
                        tt: TokenType::RParen,
                        span: span(1, 2, root)
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::As),
                        span: span(2, 4, root)
                    },
                    Token {
                        tt: TokenType::Kw(Keyword::Comptime),
                        span: span(4, 12, root)
                    },
                    ts.get_eof().clone(),
                    ts.get_eof().clone(),
                ]
            ),
            Cow::Borrowed(_) => panic!("expected Owned for partially out-of-bounds range"),
        }
    }

    #[test]
    #[allow(clippy::reversed_empty_ranges)] // it's intentional
    fn token_stream_get_slice_inverted_range_returns_borrowed_empty_slice() {
        let ts = build_ts();
        let cow = ts.get_slice(5..2); // start > end

        match cow {
            Cow::Borrowed(s) => assert!(s.is_empty()),
            Cow::Owned(_) => panic!("expected Borrowed empty slice for inverted range"),
        }
    }

    #[test]
    fn token_stream_get_slice_start_beyond_len_returns_owned_all_zeros() {
        let ts = build_ts();
        let cow = ts.get_slice(5..8);

        match cow {
            Cow::Owned(v) => assert_eq!(
                v,
                vec![
                    ts.get_eof().clone(),
                    ts.get_eof().clone(),
                    ts.get_eof().clone(),
                ]
            ),
            Cow::Borrowed(_) => panic!("expected Owned (zeros) when start >= len"),
        }
    }

    #[test]
    fn token_stream_get_slice_arithmetic_overflow_range_returns_borrowed_empty_slice() {
        let ts = build_ts();
        let cow = ts.get_slice(0..usize::MAX);

        match cow {
            Cow::Borrowed(s) => assert!(s.is_empty()),
            Cow::Owned(_) => panic!("expected Borrowed empty slice on overflow-safe path"),
        }
    }

    #[test]
    fn token_stream_get_slice_single_element_range_behaves_correctly() {
        let ts = build_ts();
        let cow = ts.get_slice(0..1);

        let root = FileId::ROOT_MODULE;

        match cow {
            Cow::Borrowed(s) => assert_eq!(
                s,
                &[Token {
                    tt: TokenType::LParen,
                    span: span(0, 1, root)
                },]
            ),
            Cow::Owned(_) => panic!("expected Borrowed for single in-bounds element"),
        }
    }

    #[test]
    fn token_break_up() {
        let token = Token {
            tt: TokenType::ColonColon,
            span: span(0, 2, FileId::ROOT_MODULE),
        };

        assert_eq!(
            token.break_up(),
            Some([
                Token {
                    tt: TokenType::Colon,
                    span: span(0usize, 1usize, FileId::ROOT_MODULE),
                },
                Token {
                    tt: TokenType::Colon,
                    span: span(1usize, 2usize, FileId::ROOT_MODULE),
                },
            ])
        )
    }

    #[test]
    fn token_stream_replace_with() {
        let mut expected_ts = TokenStream::new();
        let mut ts = TokenStream::new();

        expected_ts.push(Token {
            tt: TokenType::LParen,
            span: span(0, 1, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::LParen,
            span: span(0, 1, FileId::ROOT_MODULE),
        });

        expected_ts.push(Token {
            tt: TokenType::RParen,
            span: span(1, 2, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::RParen,
            span: span(1, 2, FileId::ROOT_MODULE),
        });

        expected_ts.push(Token {
            tt: TokenType::Colon,
            span: span(2, 3, FileId::ROOT_MODULE),
        });
        expected_ts.push(Token {
            tt: TokenType::Colon,
            span: span(3, 4, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::ColonColon,
            span: span(2, 4, FileId::ROOT_MODULE),
        });

        expected_ts.push(Token {
            tt: TokenType::Kw(Keyword::Comptime),
            span: span(4, 12, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::Kw(Keyword::Comptime),
            span: span(4, 12, FileId::ROOT_MODULE),
        });

        expected_ts.push(Token {
            tt: TokenType::Eof,
            span: span(12, 12, FileId::ROOT_MODULE),
        });
        ts.push(Token {
            tt: TokenType::Eof,
            span: span(12, 12, FileId::ROOT_MODULE),
        });

        expected_ts.finish();
        ts.finish();

        const COLONCOLON_IDX: usize = 2;
        let coloncolon = ts.get(COLONCOLON_IDX);

        let tts = coloncolon.break_up().unwrap();

        ts.replace_with_two(COLONCOLON_IDX, tts);

        assert_eq!(ts, expected_ts);
    }

    macro_rules! eq_test {
        ($name:ident) => {
            assert!(TokenType::$name.eq(&ExpToken::$name));
            assert!(ExpToken::$name.eq(&TokenType::$name));
        };
        (@val $tt:expr, $exp:expr) => {
            assert!($tt.eq(&$exp));
            assert!($exp.eq(&$tt));
        };
    }

    #[test]
    fn exp_token_and_token_type_equality() {
        eq_test!(LParen);
        eq_test!(RParen);
        eq_test!(LBracket);
        eq_test!(RBracket);
        eq_test!(LCurly);
        eq_test!(RCurly);
        eq_test!(Plus);
        eq_test!(Minus);
        eq_test!(Star);
        eq_test!(Slash);
        eq_test!(Colon);
        eq_test!(Comma);
        eq_test!(Eq);
        eq_test!(EqEq);
        eq_test!(BangEq);
        eq_test!(Bang);
        eq_test!(LtEq);
        eq_test!(Lt);
        eq_test!(LtLt);
        eq_test!(Gt);
        eq_test!(GtGt);
        eq_test!(GtEq);
        eq_test!(Semi);
        eq_test!(MinusGt);
        eq_test!(Caret);
        eq_test!(And);
        eq_test!(AndAnd);
        eq_test!(Or);
        eq_test!(OrOr);
        eq_test!(Percent);
        eq_test!(Dot);
        eq_test!(DotStar);
        eq_test!(Pound);
        eq_test!(@val TokenType::Kw(Keyword::As), ExpToken::KwAs);
        eq_test!(@val TokenType::Kw(Keyword::Break), ExpToken::KwBreak);
        eq_test!(@val TokenType::Kw(Keyword::Comptime), ExpToken::KwComptime);
        eq_test!(@val TokenType::Kw(Keyword::Continue), ExpToken::KwContinue);
        eq_test!(@val TokenType::Kw(Keyword::Else), ExpToken::KwElse);
        eq_test!(@val TokenType::Kw(Keyword::Extern), ExpToken::KwExtern);
        eq_test!(@val TokenType::Kw(Keyword::False), ExpToken::KwFalse);
        eq_test!(@val TokenType::Kw(Keyword::For), ExpToken::KwFor);
        eq_test!(@val TokenType::Kw(Keyword::Fun), ExpToken::KwFun);
        eq_test!(@val TokenType::Kw(Keyword::If), ExpToken::KwIf);
        eq_test!(@val TokenType::Kw(Keyword::Impl), ExpToken::KwImpl);
        eq_test!(@val TokenType::Kw(Keyword::In), ExpToken::KwIn);
        eq_test!(@val TokenType::Kw(Keyword::Let), ExpToken::KwLet);
        eq_test!(@val TokenType::Kw(Keyword::Loop), ExpToken::KwLoop);
        eq_test!(@val TokenType::Kw(Keyword::Mut), ExpToken::KwMut);
        eq_test!(@val TokenType::Kw(Keyword::Null), ExpToken::KwNull);
        eq_test!(@val TokenType::Kw(Keyword::Pub), ExpToken::KwPub);
        eq_test!(@val TokenType::Kw(Keyword::Return), ExpToken::KwReturn);
        eq_test!(@val TokenType::Kw(Keyword::Self_), ExpToken::KwSelf);
        eq_test!(@val TokenType::Kw(Keyword::Trait), ExpToken::KwTrait);
        eq_test!(@val TokenType::Kw(Keyword::True), ExpToken::KwTrue);
        eq_test!(@val TokenType::Kw(Keyword::While), ExpToken::KwWhile);
        eq_test!(@val TokenType::Ident(sym::u32), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(sym::empty), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(sym::never), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(sym::cstr), ExpToken::Ident);
        eq_test!(@val TokenType::Lit(Lit::int(123)), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::char('L')), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::float(6.9)), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::string(Symbol::intern("Hello world!"))), ExpToken::Lit);
        eq_test!(Eof);
        eq_test!(Dummy);
    }

    #[test]
    fn keyword_to_symbol() {
        assert_eq!(Keyword::As.as_symbol(), sym::As);
        assert_eq!(Keyword::Break.as_symbol(), sym::Break);
        assert_eq!(Keyword::Comptime.as_symbol(), sym::Comptime);
        assert_eq!(Keyword::Continue.as_symbol(), sym::Continue);
        assert_eq!(Keyword::Else.as_symbol(), sym::Else);
        assert_eq!(Keyword::Extern.as_symbol(), sym::Extern);
        assert_eq!(Keyword::False.as_symbol(), sym::False);
        assert_eq!(Keyword::For.as_symbol(), sym::For);
        assert_eq!(Keyword::Fun.as_symbol(), sym::Fun);
        assert_eq!(Keyword::If.as_symbol(), sym::If);
        assert_eq!(Keyword::Impl.as_symbol(), sym::Impl);
        assert_eq!(Keyword::In.as_symbol(), sym::In);
        assert_eq!(Keyword::Let.as_symbol(), sym::Let);
        assert_eq!(Keyword::Loop.as_symbol(), sym::Loop);
        assert_eq!(Keyword::Mut.as_symbol(), sym::Mut);
        assert_eq!(Keyword::Null.as_symbol(), sym::Null);
        assert_eq!(Keyword::Pub.as_symbol(), sym::Pub);
        assert_eq!(Keyword::Return.as_symbol(), sym::Return);
        assert_eq!(Keyword::Self_.as_symbol(), sym::Self_);
        assert_eq!(Keyword::Trait.as_symbol(), sym::Trait);
        assert_eq!(Keyword::True.as_symbol(), sym::True);
        assert_eq!(Keyword::While.as_symbol(), sym::While);
    }

    #[test]
    fn symbol_to_keyword() {
        // keywords:
        assert_eq!(Keyword::from_symbol(sym::As), Some(Keyword::As));
        assert_eq!(Keyword::from_symbol(sym::Break), Some(Keyword::Break));
        assert_eq!(Keyword::from_symbol(sym::Comptime), Some(Keyword::Comptime));
        assert_eq!(Keyword::from_symbol(sym::Continue), Some(Keyword::Continue));
        assert_eq!(Keyword::from_symbol(sym::Else), Some(Keyword::Else));
        assert_eq!(Keyword::from_symbol(sym::Extern), Some(Keyword::Extern));
        assert_eq!(Keyword::from_symbol(sym::False), Some(Keyword::False));
        assert_eq!(Keyword::from_symbol(sym::For), Some(Keyword::For));
        assert_eq!(Keyword::from_symbol(sym::Fun), Some(Keyword::Fun));
        assert_eq!(Keyword::from_symbol(sym::If), Some(Keyword::If));
        assert_eq!(Keyword::from_symbol(sym::Impl), Some(Keyword::Impl));
        assert_eq!(Keyword::from_symbol(sym::In), Some(Keyword::In));
        assert_eq!(Keyword::from_symbol(sym::Let), Some(Keyword::Let));
        assert_eq!(Keyword::from_symbol(sym::Loop), Some(Keyword::Loop));
        assert_eq!(Keyword::from_symbol(sym::Mut), Some(Keyword::Mut));
        assert_eq!(Keyword::from_symbol(sym::Null), Some(Keyword::Null));
        assert_eq!(Keyword::from_symbol(sym::Pub), Some(Keyword::Pub));
        assert_eq!(Keyword::from_symbol(sym::Return), Some(Keyword::Return));
        assert_eq!(Keyword::from_symbol(sym::Self_), Some(Keyword::Self_));
        assert_eq!(Keyword::from_symbol(sym::Trait), Some(Keyword::Trait));
        assert_eq!(Keyword::from_symbol(sym::True), Some(Keyword::True));
        assert_eq!(Keyword::from_symbol(sym::While), Some(Keyword::While));

        // other:
        assert_eq!(Keyword::from_symbol(sym::empty), None);
        assert_eq!(Keyword::from_symbol(sym::void), None);
        assert_eq!(Keyword::from_symbol(sym::cstr), None);
        assert_eq!(Keyword::from_symbol(Symbol::intern("Hello world!")), None);
    }
}
