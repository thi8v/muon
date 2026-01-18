//! Source position and related helper functions in the Muon Compiler.

use std::{
    fmt::Display,
    ops::{BitOr, Range},
};

pub mod source;
pub mod symbol;

/// Location of something in a file.
///
/// # Note
///
/// the `lo` and `hi` field expect and byte index into the underlying string,
/// not the nth character. They are byte indices to be more efficient
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
    /// file id, to know which file we are referring to.
    pub fid: FileId,
}

/// Dump location (all zeros).
pub const DUMMY_SP: Span = Span {
    lo: 0,
    hi: 0,
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
        (self.fid, self.lo..self.hi)
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

#[inline(always)]
pub fn span(lo: impl Into<usize>, hi: impl Into<usize>, fid: FileId) -> Span {
    Span {
        lo: lo.into(),
        hi: hi.into(),
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
        value.lo..value.hi
    }
}

impl<I: Into<usize>, J: Into<usize>> From<(I, J, FileId)> for Span {
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
    /// Note this, file id always refers to the root of the `orb`
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
