//! AST stuff shared by many compiler stages

use std::{
    fmt::{self, Display},
    io::{self, Write},
    str::FromStr,
};

use muonc_span::prelude::*;
use muonc_token::TokenType;
use muonc_utils::pretty::{PrettyCtxt, PrettyDump};

/// Mutability of something.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Not,
    Mut,
}

impl Mutability {
    /// Returns `""` if `No` or `"mut "` if `Mut`.
    pub fn prefix_str(self) -> &'static str {
        match self {
            Self::Not => "",
            Self::Mut => "mut ",
        }
    }

    /// Inverts the mutability
    pub fn invert(self) -> Mutability {
        match self {
            Self::Not => Self::Mut,
            Self::Mut => Self::Not,
        }
    }

    /// Returns true if `Mut`
    #[must_use]
    pub fn is_mut(self) -> bool {
        matches!(self, Self::Mut)
    }

    /// Returns true if `Not`
    #[must_use]
    pub fn is_not(self) -> bool {
        matches!(self, Self::Not)
    }
}

impl<E> PrettyDump<E> for Mutability {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Self::Not => write!(ctx.out, "not"),
            Self::Mut => write!(ctx.out, "mut"),
        }
    }
}

/// Binary operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// addition
    Add,
    /// subtraction
    Sub,
    /// multiplication
    Mul,
    /// division
    Div,
    /// remainder
    Rem,
    /// less than
    CompLT,
    /// less than or equal
    CompLE,
    /// greater than
    CompGT,
    /// greater than or equal
    CompGE,
    /// equal
    CompEq,
    /// not equal
    CompNe,
    /// assignment
    Assignment,
    /// &&
    LogicalAnd,
    /// ||
    LogicalOr,
    /// &
    BitwiseAnd,
    /// ^
    BitwiseXor,
    /// |
    BitwiseOr,
    /// shift right, >>
    Shr,
    /// shift left, <<
    Shl,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::CompLT => "<",
            Self::CompLE => "<=",
            Self::CompGT => ">",
            Self::CompGE => ">=",
            Self::CompEq => "==",
            Self::CompNe => "!=",
            Self::Assignment => "=",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
            Self::BitwiseAnd => "&",
            Self::BitwiseXor => "^",
            Self::BitwiseOr => "|",
            Self::Shr => ">>",
            Self::Shl => "<<",
        };

        f.write_str(str)
    }
}

impl BinOp {
    pub fn from_tt(tt: &TokenType) -> Option<BinOp> {
        match tt {
            TokenType::Eq => Some(BinOp::Assignment),
            TokenType::Star => Some(BinOp::Mul),
            TokenType::Slash => Some(BinOp::Div),
            TokenType::Percent => Some(BinOp::Rem),
            TokenType::Plus => Some(BinOp::Add),
            TokenType::Minus => Some(BinOp::Sub),
            TokenType::Lt => Some(BinOp::CompLT),
            TokenType::Gt => Some(BinOp::CompGT),
            TokenType::LtEq => Some(BinOp::CompLE),
            TokenType::GtEq => Some(BinOp::CompGE),
            TokenType::EqEq => Some(BinOp::CompEq),
            TokenType::BangEq => Some(BinOp::CompNe),
            TokenType::And => Some(BinOp::BitwiseAnd),
            TokenType::AndAnd => Some(BinOp::LogicalAnd),
            TokenType::Caret => Some(BinOp::BitwiseXor),
            TokenType::Or => Some(BinOp::BitwiseOr),
            TokenType::OrOr => Some(BinOp::LogicalOr),
            TokenType::LtLt => Some(BinOp::Shl),
            TokenType::GtGt => Some(BinOp::Shr),
            _ => None,
        }
    }

    /// Is the binary operation rational? < <= > >= == !=
    pub fn is_relational(&self) -> bool {
        matches!(
            self,
            BinOp::CompLT
                | BinOp::CompLE
                | BinOp::CompGT
                | BinOp::CompGE
                | BinOp::CompEq
                | BinOp::CompNe
        )
    }

    pub fn is_logical(&self) -> bool {
        // TODO: implement logical operators like `"not" expr`, `expr "and"
        // expr`, `expr "or" expr`, `expr "xor" expr`
        matches!(self, Self::LogicalAnd | Self::LogicalOr)
    }
}

impl<E> PrettyDump<E> for BinOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}
/// Unary Operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    // left unary operator
    /// `- expression`
    Negation,
    /// `! expression`
    Not,
    // right unary operator
    /// `expression.*`
    Dereference,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Negation => "-",
            Self::Not => "!",
            Self::Dereference => ".*",
        };

        f.write_str(str)
    }
}

impl UnOp {
    /// get the unary operation for left side unary operation
    ///
    /// eg:
    /// `-a` `!a`
    pub fn left_from_token(tt: &TokenType) -> Option<UnOp> {
        match tt {
            TokenType::Minus => Some(UnOp::Negation),
            TokenType::Bang => Some(UnOp::Not),
            _ => None,
        }
    }

    /// get the unary operation for right side unary operation
    ///
    /// eg:
    /// `a.*`
    pub fn right_from_token(tt: &TokenType) -> Option<UnOp> {
        match tt {
            TokenType::DotStar => Some(UnOp::Dereference),
            _ => None,
        }
    }

    pub fn is_right(&self) -> bool {
        matches!(self, UnOp::Dereference)
    }

    pub fn is_left(&self) -> bool {
        !self.is_right()
    }
}

impl<E> PrettyDump<E> for UnOp {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}

/// A 'Path' is a name in Muon, like `pkg`, `hello`, `core::panic`, ..
///
/// It is composed of segments of path, identifiers or pkg.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Vec<PathSegment>,
}

impl Path {
    /// Creates a new empty path
    pub const fn new() -> Path {
        Path {
            segments: Vec::new(),
        }
    }

    /// Creates a new path with just a single segment
    pub fn with_root(root: impl Into<PathSegment>) -> Path {
        Path {
            segments: vec![root.into()],
        }
    }

    /// Returns the amount of members in the path eg:
    ///
    /// `pkg`               -> 1
    /// `hello`             -> 1
    /// `pkg::main`         -> 2
    /// `std::panic::Panic` -> 3
    /// etc..
    pub fn len(&self) -> usize {
        self.segments.len()
    }

    /// Is the path empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the underlying path
    pub fn as_slice(&self) -> &[PathSegment] {
        &self.segments
    }

    /// Returns a mutable reference to the last segment of the path
    ///
    /// # Example
    ///
    /// `pkg`        -> mut ref to `pkg`
    /// `pkg::driver` -> mut ref to `driver`
    /// *etc..*
    pub fn last_mut(&mut self) -> Option<&mut PathSegment> {
        self.segments.last_mut()
    }

    /// Returns a reference to the last segment of the path
    pub fn last(&self) -> Option<&PathSegment> {
        self.segments.last()
    }

    /// Returns a reference to the first segment of the path
    pub fn first(&self) -> Option<&PathSegment> {
        self.segments.first()
    }

    /// Returns a mutable reference to the first segment of the path
    pub fn first_mut(&mut self) -> Option<&mut PathSegment> {
        self.segments.first_mut()
    }

    /// Push a new segment to the path
    ///
    /// # Panic
    ///
    /// This function panics if you push a [`PathSegment::Pkg`] if it's not the
    /// first segment of the path.
    pub fn push(&mut self, segment: impl Into<PathSegment>) {
        let seg = segment.into();

        if !self.is_empty()
            && let PathSegment::Pkg(_) = seg
        {
            panic!("pushed a 'pkg' segment not as the first segment of a path")
        }

        self.segments.push(seg)
    }

    /// Pops the last member of the path and returns it
    pub fn pop(&mut self) -> Option<PathSegment> {
        self.segments.pop()
    }

    /// Is this path the root path? returns true if the path is equal to `pkg`,
    /// false otherwise.
    pub fn is_root(&self) -> bool {
        matches!(self.segments.as_slice(), [PathSegment::Pkg(_), ..])
    }

    /// Append a path to this path
    pub fn append(&mut self, mut other: Path) {
        self.segments.append(&mut other.segments);
    }

    /// Converts this path to a vector of strings.
    pub fn to_string_vec(&self) -> Vec<String> {
        self.segments.iter().map(|seg| seg.to_string()).collect()
    }

    /// Does the path starts with a [`PathSegment::Pkg`]?
    pub fn starts_with_pkg(&self) -> bool {
        matches!(self.first(), Some(PathSegment::Pkg(_)))
    }

    /// Returns `true` if self == `_`
    pub fn is_underscore(&self) -> bool {
        self.len() == 1 && self.segments[0].is_ident_and(|id| id.name == sym::underscore)
    }

    /// Get the `i`th segment of the path.
    pub fn get(&self, i: usize) -> Option<&PathSegment> {
        self.segments.get(i)
    }
}

impl Default for Path {
    fn default() -> Self {
        Path::new()
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.is_empty() {
            write!(
                f,
                "{}",
                self.as_slice()
                    .iter()
                    .map(|seg| seg.to_string())
                    .collect::<Vec<_>>()
                    .join("::")
            )
        } else {
            write!(f, "∅")
        }
    }
}

impl<E> PrettyDump<E> for Path {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        write!(ctx.out, "{self}")
    }
}

/// A segment of a path, `pkg` or an identifier
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathSegment {
    /// Identifier segment like `abc`
    Ident(Identifier),
    /// Package starting segment `pkg`, e.g: `pkg::hello:world`.
    ///
    /// # Note
    ///
    /// This segment is only valid as the first segment of a [Path]
    Pkg(Span),
}

impl PathSegment {
    /// Returns `true` if `self` is `Ident(id)` and the value inside matches a
    /// predicate `f`.
    pub fn is_ident_and(&self, f: impl FnOnce(Identifier) -> bool) -> bool {
        match self {
            Self::Ident(id) => f(*id),
            Self::Pkg(_) => false,
        }
    }

    /// Returns the span of the segment.
    pub fn span(&self) -> Span {
        match self {
            Self::Ident(ident) => ident.span,
            Self::Pkg(span) => *span,
        }
    }
}

impl Display for PathSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(seg) => write!(f, "{}", seg.name),
            Self::Pkg(_) => write!(f, "pkg"),
        }
    }
}

impl From<Identifier> for PathSegment {
    fn from(ident: Identifier) -> Self {
        PathSegment::Ident(ident)
    }
}

/// ABI names usable in an extern block
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum Abi {
    /// `"C"`
    C,
    /// `"Muon"`
    #[default]
    Muon,
}

impl Abi {
    /// Abi name as an anonymous enum variant, like `.Field`.
    pub fn enum_str(&self) -> &'static str {
        match self {
            Abi::C => ".C",
            Abi::Muon => ".Muon",
        }
    }
}

impl FromStr for Abi {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "C" => Ok(Abi::C),
            "Muon" => Ok(Abi::Muon),
            _ => Err(()),
        }
    }
}

impl<E> PrettyDump<E> for Abi {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Abi::C => write!(ctx.out, "C"),
            Abi::Muon => write!(ctx.out, "Muon"),
        }
    }
}

/// The thing that contains the items
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemContainer {
    Module,
    ExternBlock,
}

/// Muon's primitive types
#[derive(Debug, Clone, PartialEq)]
pub enum PrimTy {
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Str,
    Bool,
    Char,
    Never,
    Void,
}

impl PrimTy {
    /// Get the primitive type from it's symbol
    pub const fn from_symbol(sym: Symbol) -> Option<PrimTy> {
        match sym {
            sym::isz => Some(PrimTy::Int(IntTy::Isz)),
            sym::i128 => Some(PrimTy::Int(IntTy::I128)),
            sym::i64 => Some(PrimTy::Int(IntTy::I64)),
            sym::i32 => Some(PrimTy::Int(IntTy::I32)),
            sym::i16 => Some(PrimTy::Int(IntTy::I16)),
            sym::i8 => Some(PrimTy::Int(IntTy::I8)),
            sym::usz => Some(PrimTy::Uint(UintTy::Usz)),
            sym::u128 => Some(PrimTy::Uint(UintTy::U128)),
            sym::u64 => Some(PrimTy::Uint(UintTy::U64)),
            sym::u32 => Some(PrimTy::Uint(UintTy::U32)),
            sym::u16 => Some(PrimTy::Uint(UintTy::U16)),
            sym::u8 => Some(PrimTy::Uint(UintTy::U8)),
            sym::f16 => Some(PrimTy::Float(FloatTy::F16)),
            sym::f32 => Some(PrimTy::Float(FloatTy::F32)),
            sym::f64 => Some(PrimTy::Float(FloatTy::F64)),
            sym::f128 => Some(PrimTy::Float(FloatTy::F128)),
            sym::bool => Some(PrimTy::Bool),
            sym::str => Some(PrimTy::Str),
            sym::char => Some(PrimTy::Char),
            sym::never => Some(PrimTy::Never),
            sym::void => Some(PrimTy::Void),
            _ => None,
        }
    }

    /// Get the symbol corresponding to the primitive type.
    pub const fn to_symbol(&self) -> Symbol {
        match self {
            PrimTy::Int(IntTy::Isz) => sym::isz,
            PrimTy::Int(IntTy::I128) => sym::i128,
            PrimTy::Int(IntTy::I64) => sym::i64,
            PrimTy::Int(IntTy::I32) => sym::i32,
            PrimTy::Int(IntTy::I16) => sym::i16,
            PrimTy::Int(IntTy::I8) => sym::i8,
            PrimTy::Uint(UintTy::Usz) => sym::usz,
            PrimTy::Uint(UintTy::U128) => sym::u128,
            PrimTy::Uint(UintTy::U64) => sym::u64,
            PrimTy::Uint(UintTy::U32) => sym::u32,
            PrimTy::Uint(UintTy::U16) => sym::u16,
            PrimTy::Uint(UintTy::U8) => sym::u8,
            PrimTy::Float(FloatTy::F16) => sym::f16,
            PrimTy::Float(FloatTy::F32) => sym::f32,
            PrimTy::Float(FloatTy::F64) => sym::f64,
            PrimTy::Float(FloatTy::F128) => sym::f128,
            PrimTy::Bool => sym::bool,
            PrimTy::Str => sym::str,
            PrimTy::Char => sym::char,
            PrimTy::Never => sym::never,
            PrimTy::Void => sym::void,
        }
    }
}

/// Muon signed integer types
#[derive(Debug, Clone, PartialEq)]
pub enum IntTy {
    Isz,
    I128,
    I64,
    I32,
    I16,
    I8,
}

/// Muon unsigned integer types
#[derive(Debug, Clone, PartialEq)]
pub enum UintTy {
    Usz,
    U128,
    U64,
    U32,
    U16,
    U8,
}

/// Muon float types
#[derive(Debug, Clone, PartialEq)]
pub enum FloatTy {
    F128,
    F64,
    F32,
    F16,
}

/// Visibility
///
/// NB: `T` is used to add a potential Span to the public variant of this enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility<T = ()> {
    Public(T),
    Private,
}

impl<T> Visibility<T> {
    /// Turns a `Visibility<T>` into a `Visibility<()>`.
    pub fn simplify(self) -> Visibility<()> {
        match self {
            Visibility::Public(_) => Visibility::Public(()),
            Visibility::Private => Visibility::Private,
        }
    }

    /// Get the value inside of the public variant
    pub fn as_val(&self) -> Option<&T> {
        if let Self::Public(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<E> PrettyDump<E> for Visibility {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Visibility::Public(()) => write!(ctx.out, "pub"),
            Visibility::Private => write!(ctx.out, "private"),
        }
    }
}
