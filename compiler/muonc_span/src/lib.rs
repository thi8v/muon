//! Source position and related helper functions in the Muon Compiler.

use std::{
    fmt::{self, Display},
    num::TryFromIntError,
    ops::{Add, AddAssign, BitOr, Range, Sub},
};

pub mod prelude;
pub mod source;
pub mod symbol;

/// 32-byte size in a byte stream, for now it's a 32 bit unsigned integer and
/// is guaranteed to be exactly like a `u32` but it carries with it more type
/// information.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Bsz(pub u32);

impl Bsz {
    /// The smallest value that can be represented by a `Bsz`
    pub const MIN: Bsz = Bsz(u32::MIN);

    /// The largest value that can be represented by a `Bsz`
    pub const MAX: Bsz = Bsz(u32::MAX);

    /// Return the inner value.
    #[inline]
    pub const fn inner(self) -> u32 {
        self.0
    }

    /// Return the inner value as a usize.
    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }
}

macro_rules! from_impl {
    ($t:ty) => {
        impl From<$t> for Bsz {
            fn from(value: $t) -> Bsz {
                Bsz(value.into())
            }
        }
    };

    ($($t:ty,)*) => {
        $( from_impl!( $t ); )*
    };
}

macro_rules! try_from_impl {
    ($t:ty) => {
        impl TryFrom<$t> for Bsz {
            type Error = TryFromIntError;

            fn try_from(value: $t) -> Result<Bsz, Self::Error>{
                Ok(Bsz(value.try_into()?))
            }
        }
    };

    ($($t:ty,)*) => {
        $( try_from_impl!( $t ); )*
    };
}

from_impl! {
    u8,
    u16,
    u32,
}

try_from_impl! {
    u64,
    u128,
    i8,
    i16,
    i32,
    i64,
    i128,
}

impl From<usize> for Bsz {
    fn from(value: usize) -> Self {
        Bsz(value
            .try_into()
            .expect("integer too big cannot fit in 32 bits"))
    }
}

impl Add for Bsz {
    type Output = Bsz;

    fn add(self, rhs: Self) -> Self::Output {
        Bsz(self.0 + rhs.0)
    }
}

impl Add<u32> for Bsz {
    type Output = Bsz;

    fn add(self, rhs: u32) -> Self::Output {
        Bsz(self.0 + rhs)
    }
}

impl Add<Bsz> for u32 {
    type Output = Bsz;

    fn add(self, rhs: Bsz) -> Self::Output {
        Bsz(self + rhs.0)
    }
}

impl Add<usize> for Bsz {
    type Output = Bsz;

    fn add(self, rhs: usize) -> Self::Output {
        Bsz(self.0 + rhs as u32)
    }
}

impl Add<Bsz> for usize {
    type Output = Bsz;

    fn add(self, rhs: Bsz) -> Self::Output {
        Bsz(self as u32 + rhs.0)
    }
}

impl AddAssign<u32> for Bsz {
    fn add_assign(&mut self, rhs: u32) {
        self.0 = self.0 + rhs;
    }
}

impl AddAssign<i32> for Bsz {
    fn add_assign(&mut self, rhs: i32) {
        self.0 = self.0 + rhs as u32;
    }
}

impl AddAssign<usize> for Bsz {
    fn add_assign(&mut self, rhs: usize) {
        self.0 = self.0 + rhs as u32;
    }
}

impl Sub for Bsz {
    type Output = Bsz;

    fn sub(self, rhs: Self) -> Self::Output {
        Bsz(self.0 - rhs.0)
    }
}

impl Sub<u32> for Bsz {
    type Output = Bsz;

    fn sub(self, rhs: u32) -> Self::Output {
        Bsz(self.0 - rhs)
    }
}

impl Sub<Bsz> for u32 {
    type Output = Bsz;

    fn sub(self, rhs: Bsz) -> Self::Output {
        Bsz(self - rhs.0)
    }
}

impl Display for Bsz {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Location of something in a file.
///
/// # Note
///
/// the `lo` and `hi` field expect and byte index into the underlying string,
/// not the nth character. They are byte indices to be more efficient
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub lo: Bsz,
    pub hi: Bsz,
    /// file id, to know which file we are referring to.
    pub fid: FileId,
}

/// Dump location (all zeros).
pub const DUMMY_SP: Span = Span {
    lo: Bsz(0),
    hi: Bsz(0),
    fid: FileId::ROOT_MODULE,
};

impl Span {
    /// Join to spans in one.
    #[inline(always)]
    pub const fn join(lo: Span, hi: Span) -> Span {
        // NOTE: we are implementing debug_assert_eq manually because it doesn't
        // work at compile time
        if cfg!(debug_assertions) && lo.fid.0 != hi.fid.0 {
            panic!("expected the file ids of both lo and hi spans to be the same.")
        }

        Span {
            lo: lo.lo,
            hi: hi.hi,
            fid: lo.fid,
        }
    }

    /// Converts this span to pieces
    pub fn to_parts(self) -> (FileId, Range<usize>) {
        (self.fid, self.lo.as_usize()..self.hi.as_usize())
    }

    /// Take a slice of the string with the provided span.
    pub fn slice_str<'str>(&self, s: &'str str) -> &'str str {
        &s[Range::from(*self)]
    }
}

impl BitOr for Span {
    type Output = Self;

    /// Outputs a span that has `lo` and `hi` as the largest interval between
    /// `self` and `other`.
    ///
    /// **N.B: should only be used on spans with the same [`FileId`].**
    fn bitor(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.fid, rhs.fid);

        Span {
            lo: self.lo.min(rhs.lo),
            hi: self.hi.max(rhs.hi),
            fid: self.fid,
        }
    }
}

/// Create a span with the given bounds and file id.
#[inline(always)]
pub fn span<N2, N1>(lo: N1, hi: N2, fid: FileId) -> Span
where
    N1: TryInto<Bsz>,
    N2: TryInto<Bsz>,
    N2::Error: fmt::Debug,
    N1::Error: fmt::Debug,
{
    Span {
        lo: lo.try_into().unwrap(),
        hi: hi.try_into().unwrap(),
        fid,
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}..{} (fid = {})",
            self.lo,
            self.hi,
            self.fid.as_usize()
        )
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        value.lo.as_usize()..value.hi.as_usize()
    }
}

impl<I: Into<Bsz>, J: Into<Bsz>> From<(I, J, FileId)> for Span {
    fn from((lo, hi, fid): (I, J, FileId)) -> Self {
        span(lo, hi, fid)
    }
}

impl Default for Span {
    fn default() -> Self {
        DUMMY_SP
    }
}

/// A file id, used to represent, which file we are talking about
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl FileId {
    /// Note this, file id always refers to the root of the package.
    pub const ROOT_MODULE: FileId = FileId(0);

    /// Creates a new FileId from an integer.
    #[inline]
    pub fn new(num: impl Into<u32>) -> FileId {
        FileId(num.into())
    }

    /// Converts the file id to a usize
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }

    /// Is the file id, the one to the root module?
    pub fn is_root(&self) -> bool {
        *self == Self::ROOT_MODULE
    }
}

/// Something that can have a span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

/// Respans a node.
#[inline]
pub fn respan<T>(node: T, span: Span) -> Spanned<T> {
    Spanned { node, span }
}

/// Respans a node with [`DUMMY_SP`].
#[inline]
pub fn respan_dummy<T>(node: T) -> Spanned<T> {
    respan(node, DUMMY_SP)
}
