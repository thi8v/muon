//! Error handling of the Muon compiler with diagnostics.

use std::{
    borrow::Cow,
    fmt::{self, Debug, Display, Write},
    mem,
    ops::Deref,
    panic::Location,
    path::{Component, Path, PathBuf},
    str::FromStr,
    sync::{Arc, RwLock},
};

use bitflags::bitflags;
use indexmap::IndexSet;
use muonc_macros::codes_enum;
use muonc_span::{Bsz, Span, source::SourceMap, symbol::Symbol};
use muonc_utils::pluralize;

use crate::renderer::Renderer;

pub mod prelude;
pub mod renderer;

/// Severity level of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
    Info,
    Note,
    Help,
    /// **N.B: should not be used it's only here for the emit location and some
    /// internal things.**
    #[doc(hidden)]
    Debug,
}

codes_enum! {
    /// List of all the errors Muon can emit.
    pub enum ErrCode: 'E' {
        UnknownToken = 1,
        UnterminatedBlockComment = 2,
        UnknownCharacterEscape = 3,
        TooManyCodepointsInCharLiteral = 4,
        EmptyCharLiteral = 5,
        ReachedEof = 6,
        NotEnoughHexDigits = 7,
        UnterminatedStringLiteral = 8,
        InvalidDigitNumber = 9,
        TooLargeIntegerLiteral = 10,
        InvalidUnicodeEscape = 11,
        ExpectedExponentPart = 12,
        NoDigitsInANonDecimal = 13,
        MutQualifierNotPermitted = 14,
        VisQualifierNotPermitted = 15,
        InvalidAbi = 16,
        MalformedIfExpr = 17,
    }
}

codes_enum! {
    /// List of all the warnings Muon can emit.
    pub enum WarnCode: 'W' {
        // NOTE: placeholders are here temporarily because WarnCode should have
        // the size of a u8
        __PlaceHolder1 = 1,
        __PlaceHolder2 = 2,
    }
}

/// Diagnostic emit location, `-Dtrack-diagnostics=true`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagEmitLoc {
    pub file: Cow<'static, str>,
    pub line: Bsz,
    pub col: Bsz,
}

impl DiagEmitLoc {
    const NOWHERE: DiagEmitLoc = DiagEmitLoc {
        file: Cow::Borrowed("<!NOWHERE!>"),
        line: Bsz::MAX,
        col: Bsz::MAX,
    };

    // marker to tell the dcx to never add the debug thing to a diagnostic, used by the summary diagnostic.
    #[doc(hidden)]
    pub const __NEVER_DEBUG_INFO: DiagEmitLoc = DiagEmitLoc {
        file: Cow::Borrowed("<!NEVER_DEBUG_INFO!>"),
        line: Bsz::MAX,
        col: Bsz::MAX,
    };
}

impl From<&'static Location<'static>> for DiagEmitLoc {
    fn from(loc: &'static Location<'static>) -> Self {
        let file = PathBuf::from(loc.file());

        fn strip_until_compiler(path: &Path) -> Option<PathBuf> {
            let mut found = false;

            let components = path.components().filter(|c| {
                if found {
                    true
                } else if *c == Component::Normal("compiler".as_ref()) {
                    found = true;
                    true
                } else {
                    false
                }
            });

            let result: PathBuf = components.collect();

            if result.as_os_str().is_empty() {
                None
            } else {
                Some(result)
            }
        }

        let file = strip_until_compiler(&file).unwrap_or(file);

        DiagEmitLoc {
            file: Cow::Owned(file.to_str().unwrap().to_owned()),
            line: loc.line().into(),
            col: loc.column().into(),
        }
    }
}

/// A collection of `Span` with an optional message with them.
#[derive(Debug, Clone)]
pub struct MultiSpan {
    pub spans: Vec<Label>,
}

impl MultiSpan {
    /// Create a new empty multi span.
    pub fn new() -> MultiSpan {
        MultiSpan { spans: Vec::new() }
    }

    /// Returns the first span.
    pub fn first(&self) -> Option<&Label> {
        self.spans.first()
    }

    /// Returns the count of spans in the multi span.
    pub fn count(&self) -> usize {
        self.spans.len()
    }

    /// Gets an iterator of the spans.
    pub fn iter(&self) -> impl Iterator<Item = &Label> {
        self.spans.iter()
    }
}

impl Default for MultiSpan {
    fn default() -> Self {
        Self::new()
    }
}

/// The code of a diagnostic.
#[derive(Debug, Clone, Copy)]
pub enum Code {
    Err(ErrCode),
    Warn(WarnCode),
}

impl Code {
    /// Get the docs related to the diagnostic code.
    pub fn get_docs(&self) -> &'static str {
        match *self {
            Code::Err(errcode) => ErrCode::documentations()[errcode as usize - 1],
            Code::Warn(warncode) => WarnCode::documentations()[warncode as usize - 1],
        }
    }
}

impl From<WarnCode> for Code {
    fn from(v: WarnCode) -> Self {
        Self::Warn(v)
    }
}

impl From<ErrCode> for Code {
    fn from(v: ErrCode) -> Self {
        Self::Err(v)
    }
}

impl FromStr for Code {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        let mut chars = s.chars();

        let kind = chars.next().ok_or("empty string")?.to_ascii_uppercase();

        let digits: String = chars.collect();
        if digits.is_empty() {
            return Err("missing numeric code");
        }

        if !digits.chars().all(|c| c.is_ascii_digit()) {
            return Err("invalid numeric code");
        }

        let code: u32 = digits.parse().map_err(|_| "numeric code overflow")?;

        match kind {
            'E' => {
                if code <= 0 || code as usize > ErrCode::VARIANT_COUNT {
                    return Err("invalid error code");
                }

                // SAFETY: we checked before.
                let code: ErrCode = unsafe { mem::transmute::<u8, ErrCode>(code as u8) };

                Ok(Code::Err(code))
            }
            'W' => {
                if code <= 0 || code as usize > WarnCode::VARIANT_COUNT {
                    return Err("invalid warning code");
                }

                // SAFETY: we checked before.
                let code: WarnCode = unsafe { mem::transmute::<u8, WarnCode>(code as u8) };

                Ok(Code::Warn(code))
            }
            _ => Err("unknown kind of diagnostic code"),
        }
    }
}

/// A diagnostic message.
#[derive(Debug, Clone)]
pub struct Message {
    pub level: Level,
    pub msg: String,
}

/// The style of the label.
#[derive(Debug, Clone)]
pub enum LabelStyle {
    Primary,
    Secondary,
}

/// A label describing a region of code in a diagnostic.
#[derive(Debug, Clone)]
pub struct Label {
    pub style: LabelStyle,
    pub msg: String,
    pub span: Span,
}

impl Label {
    /// Create a primary label
    pub fn primary(span: Span) -> Label {
        Label {
            style: LabelStyle::Primary,
            msg: String::new(),
            span,
        }
    }

    /// Create a secondary label
    pub fn secondary(span: Span) -> Label {
        Label {
            style: LabelStyle::Secondary,
            msg: String::new(),
            span,
        }
    }

    /// Attach a message to a label
    pub fn with_message(mut self, msg: impl ToString) -> Label {
        self.msg = msg.to_string();
        self
    }
}

/// Trait implemented by diagnostic helper structs.
pub trait Diagnostic {
    /// Convert to a diagnostic.
    fn into_diag(self, dcx: &DiagCtxt) -> Diag;
}

/// The main part of a diagnostic.
#[derive(Debug, Clone)]
pub struct Diag {
    pub(crate) level: Level,
    pub code: Option<Code>,
    pub title: String,
    pub span: MultiSpan,
    pub children: Vec<Subdiag>,
    pub messages: Vec<Message>,
    pub emitted_at: DiagEmitLoc,
}

impl Diag {
    /// Set the diagnostic's code.
    pub fn with_code(mut self, code: impl Into<Code>) -> Diag {
        self.code = Some(code.into());
        self
    }

    /// Set the diagnostic's message.
    pub fn with_title(mut self, message: impl Display) -> Diag {
        self.title = message.to_string();
        self
    }

    /// Push a label in the multispan of this diagnostic.
    ///
    /// N.B: each span must have the same `FileId`.
    pub fn with_label(mut self, label: Label) -> Diag {
        self.span.spans.push(label);
        self
    }

    /// Extend the labels of this diagnostic with the provided iterator
    pub fn with_labels_iter(mut self, iter: impl IntoIterator<Item = Label>) -> Diag {
        self.span.spans.extend(iter);
        self
    }

    /// Append a message to the diagnostic.
    pub fn with_message(mut self, level: Level, message: impl Display) -> Diag {
        self.messages.push(Message {
            level,
            msg: message.to_string(),
        });
        self
    }

    /// Append many message to the diagnostic.
    pub fn with_message_iter(mut self, iter: impl IntoIterator<Item = Message>) -> Diag {
        self.messages.extend(iter);
        self
    }

    /// Append many help messages
    pub fn with_help_iter(self, iter: impl IntoIterator<Item = String>) -> Diag {
        self.with_message_iter(iter.into_iter().map(|msg| Message {
            level: Level::Help,
            msg,
        }))
    }

    /// Append an help message to the diagnostic.
    pub fn with_help(self, message: impl Display) -> Diag {
        self.with_message(Level::Help, message)
    }

    /// Append an note message to the diagnostic.
    pub fn with_note(self, message: impl Display) -> Diag {
        self.with_message(Level::Note, message)
    }

    /// Append a sub diagnostic to this diagnostic.
    pub fn subdiag(mut self, sub: impl Into<Subdiag>) -> Diag {
        self.children.push(sub.into());
        self
    }
}

impl Diagnostic for Diag {
    fn into_diag(self, _: &DiagCtxt) -> Diag {
        self
    }
}

/// A "sub"-diagnostic, the child of a diagnostic.
#[derive(Debug, Clone)]
pub struct Subdiag {
    pub level: Level,
    pub message: String,
    pub span: MultiSpan,
}

bitflags! {
    /// Flags of the diagnostic context.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DiagCtxtFlags: u8 {
        /// Do we track the location of where the diagnostic was emitted?
        const TRACK_DIAGNOSTICS = 0b0000_0001;
        /// Can we emit diagnostics?
        const EMIT_WARNINGS = 0b0000_0010;
    }
}

#[derive(Debug, Clone)]
pub struct DiagCtxtInner {
    /// the diagnostics
    diags: Vec<Diag>,
    /// count of errors emitted
    errors: usize,
    /// count of warnings emitted
    warnings: usize,
    /// count of other severity diagnostics emitted (should be zero most of the
    /// time).
    other: usize,
    /// list of emitted error codes, used to be able to have `muonc --explain
    /// <errcode>`
    emitted_err_code: IndexSet<ErrCode>,
    /// the source map.
    sm: Arc<SourceMap>,
    /// configuration flags.
    flags: DiagCtxtFlags,
}

/// Diagnostic was guaranteed to be reported to the user.
#[derive(Debug, PartialEq, Eq)]
// NB. there is a private ZST field so that you can construct DiagGuaranteed only in this crate.
pub struct DiagGuaranteed(pub(crate) ());

impl DiagGuaranteed {
    /// Cannot recover from the error.
    pub fn cant_rec<T>(self) -> ReResult<T> {
        Err(Recovered::No(self))
    }

    /// Recover from the error with the default value of `T`.
    pub fn recover<T: Default>(self) -> ReResult<T> {
        self.recover_with(<T as Default>::default())
    }

    /// Recovered from the error.
    ///
    /// # Note
    ///
    /// If you want to recover with the `Default::default()` value use `rec`.
    pub fn recover_with<T>(self, val: T) -> ReResult<T> {
        Err(Recovered::Yes(val, self))
    }

    /// Discards the guarantee.
    #[inline]
    pub fn discard(self) {}
}

/// Diagnostic context.
#[derive(Clone)]
pub struct DiagCtxt {
    inner: Arc<RwLock<DiagCtxtInner>>,
}

impl DiagCtxt {
    /// Create a new diagnostic context with the provided source map.
    pub fn new(sm: Arc<SourceMap>, flags: DiagCtxtFlags) -> DiagCtxt {
        DiagCtxt {
            inner: Arc::new(RwLock::new(DiagCtxtInner {
                diags: Vec::new(),
                errors: 0,
                warnings: 0,
                other: 0,
                emitted_err_code: IndexSet::new(),
                sm,
                flags,
            })),
        }
    }

    /// Create a new empty diagnostic with the provided level.
    pub fn diag(&self, level: Level) -> Diag {
        Diag {
            level,
            code: None,
            title: String::new(),
            span: MultiSpan::new(),
            children: Vec::new(),
            messages: Vec::new(),
            emitted_at: DiagEmitLoc::NOWHERE,
        }
    }

    /// Returns true if we emitted at least one error.
    #[inline]
    pub fn failed(&self) -> bool {
        self.with_inner(|this| this.errors != 0)
            .expect("failed to access the diagnostic context")
    }

    /// Returns the summary message.
    #[inline]
    pub fn summary(&self, pkg_name: Symbol) -> Option<String> {
        self.with_inner(|this| {
            if this.errors > 0 {
                Some(format!(
                    "compilation of `{}` failed due to {} error{} and {} warning{}",
                    pkg_name,
                    this.errors,
                    pluralize(this.errors),
                    this.warnings,
                    pluralize(this.warnings)
                ))
            } else if this.warnings > 0 {
                Some(format!(
                    "compilation of `{}` succeeded but {} warning{} emitted.",
                    pkg_name,
                    this.warnings,
                    pluralize(this.warnings)
                ))
            } else {
                None
            }
        })
        .flatten()
    }

    /// Emit a diagnostic
    #[track_caller]
    pub fn emit(&self, diag: impl Diagnostic) -> DiagGuaranteed {
        let mut diag = diag.into_diag(self);
        let caller_loc = Location::caller();

        self.with_inner_mut(|this| {
            match diag.level {
                Level::Error => this.errors += 1,
                Level::Warning => this.errors += 1,
                _ => this.other += 1,
            }

            let can_debug_diag = diag.emitted_at != DiagEmitLoc::__NEVER_DEBUG_INFO;

            if diag.emitted_at == DiagEmitLoc::NOWHERE && can_debug_diag {
                diag.emitted_at = DiagEmitLoc::from(caller_loc);
            }

            if let Some(Code::Err(errcode)) = diag.code {
                this.emitted_err_code.insert(errcode);
            }

            let diag = if this.flags.contains(DiagCtxtFlags::TRACK_DIAGNOSTICS) && can_debug_diag {
                // TODO: make `DEBUG:` be purple.
                let msg = format!(
                    "this diagnostic was emitted in {file}, at {line}:{column}",
                    file = diag.emitted_at.file,
                    line = diag.emitted_at.line,
                    column = diag.emitted_at.col
                );

                diag.with_message(Level::Debug, msg)
            } else {
                diag
            };

            this.diags.push(diag);

            DiagGuaranteed(())
        })
        .expect("unable to lock the diagnostic context")
    }

    /// Render the emitted diagnostics with the `annotate_snippets` backend.
    pub fn render(&self) {
        let inner = self
            .inner
            .read()
            .expect("unable to lock the diagnostic context");

        let mut renderer = crate::renderer::annotate_snippets::AnnotateRenderer::new();
        renderer.init(&inner.diags, &inner.sm);
        eprintln!("{}", renderer.render());
    }

    /// Returns the 5 first error code that have been emitted and `true` if there is more than 5.
    pub fn err_codes(&self) -> (Vec<ErrCode>, bool) {
        self.with_inner(|this| {
            let codes = this.emitted_err_code.iter().take(5).copied().collect();
            let more = this.emitted_err_code.len() > 5;

            (codes, more)
        })
        .expect("unable to lock the diagnostic context")
    }

    /// Returns `true` if we emitted at least one diagnostic
    pub fn is_empty(&self) -> bool {
        self.with_inner(|this| this.diags.is_empty())
            .expect("unable to lock the diagnostic context")
    }

    /// Returns `Some(guarantee)` if we emitted a diagnostic, `None` otherwise.
    #[inline]
    pub fn has_emitted(&self) -> Option<DiagGuaranteed> {
        (!self.is_empty()).then_some(DiagGuaranteed(()))
    }

    /// Access the inner diagnostic context.
    #[inline]
    pub fn with_inner<F, R>(&self, f: F) -> Option<R>
    where
        F: FnOnce(&DiagCtxtInner) -> R,
    {
        let inner = self.inner.read().ok()?;

        Some(f(&inner))
    }

    /// Mutable `DiagCtxt::with_inner`.
    #[inline]
    pub fn with_inner_mut<F, R>(&self, f: F) -> Option<R>
    where
        F: FnOnce(&mut DiagCtxtInner) -> R,
    {
        let mut inner = self.inner.write().ok()?;

        Some(f(&mut inner))
    }
}

impl fmt::Debug for DiagCtxt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.with_inner(|this| {
            let mut dbg = String::new();
            if f.alternate() {
                write!(dbg, "{:#?}", this)?;
            } else {
                write!(dbg, "{:?}", this)?;
            }

            write!(f, "DiagCtxt {}", &dbg[14..])
        }) {
            Some(r) => r,
            None => f
                .debug_struct("DiagCtxt")
                .field("locked", &true)
                .finish_non_exhaustive(),
        }
    }
}

/// The recoverability of an error, with a guarantee that the diagnostic was
/// emitted.
#[derive(Debug, PartialEq, Eq)]
pub enum Recovered<T> {
    /// The error is recoverable and returned a result
    Yes(T, DiagGuaranteed),
    /// The error is irrecoverable.
    No(DiagGuaranteed),
}

/// A result that may have recovered from its failure.
pub type ReResult<T> = Result<T, Recovered<T>>;

mod private {
    pub trait Sealed {}

    impl<T> Sealed for super::ReResult<T> {}
}

/// Extension to the `ReResult<T>` type.
pub trait ReResultExtension<T>: private::Sealed + Sized {
    /// Maps a `ReResult<T>` to a `ReResult<U>`, both the `Ok(_)` and the
    /// `Err(Recovered::Yes(val, _))`.
    fn re_map<U>(self, f: impl FnOnce(T) -> U) -> ReResult<U>;

    /// Turns `&ReResult<T>` into `ReResult<&T>`.
    fn re_ref(&self) -> ReResult<&T>;

    /// Turns `&ReResult<T>` into `ReResult<&<T as Deref>::Target>`
    fn re_deref(&self) -> ReResult<&<T as Deref>::Target>
    where
        T: Deref;

    /// Turns `ReResult<T>` into `Result<T, DiagGuaranteed>`, it will return
    /// `Ok(val)` if it was `Err(Recovered::Yes(val, _))`.
    fn dere(self) -> Result<T, DiagGuaranteed>;

    /// Like `RES.dere().unwrap_or_else(op)`.
    fn dere_or(self, op: impl FnOnce() -> T) -> T;

    /// Discards a `ReResult<T>`, use it instead of `_ = reresult;` when:
    /// you don't care about the `T` value of the ReResult and don't want the
    /// guarantee.
    #[inline(always)]
    fn discard(self) {
        _ = self;
    }
}

impl<T> ReResultExtension<T> for ReResult<T> {
    fn re_map<U>(self, f: impl FnOnce(T) -> U) -> ReResult<U> {
        match self {
            Ok(val) => Ok(f(val)),
            Err(Recovered::Yes(val, guarantee)) => Err(Recovered::Yes(f(val), guarantee)),
            Err(Recovered::No(guarantee)) => Err(Recovered::No(guarantee)),
        }
    }

    fn re_ref(&self) -> ReResult<&T> {
        // NB. we don't use the guarantee of the previous one because it's
        // behind a reference and DiagGuaranteed doesn't implement Copy or Clone.
        match self {
            Ok(val) => Ok(val),
            Err(Recovered::Yes(val, _)) => Err(Recovered::Yes(val, DiagGuaranteed(()))),
            Err(Recovered::No(_)) => Err(Recovered::No(DiagGuaranteed(()))),
        }
    }

    fn re_deref(&self) -> ReResult<&<T as Deref>::Target>
    where
        T: Deref,
    {
        self.re_ref().re_map(Deref::deref)
    }

    fn dere(self) -> Result<T, DiagGuaranteed> {
        match self {
            Ok(val) | Err(Recovered::Yes(val, _)) => Ok(val),
            Err(Recovered::No(guarantee)) => Err(guarantee),
        }
    }

    fn dere_or(self, op: impl FnOnce() -> T) -> T {
        match self.dere() {
            Ok(t) => t,
            Err(_) => op(),
        }
    }
}

/// Like `?` but only for `ReResult<T>`, and returns the value even if its
/// `Err(Recovered::Yes(..))`, and propagates to a function with a `ReResult<U>`
/// return type.
#[macro_export]
macro_rules! tri {
    ($res:expr) => {
        match $res {
            Ok(val) => val,
            Err($crate::Recovered::Yes(val, _)) => val,
            Err($crate::Recovered::No(guarantee)) => return Err($crate::Recovered::No(guarantee)),
        }
    };
    ($res:expr, default: $default:expr) => {
        match $res {
            Ok(val) => val,
            Err($crate::Recovered::Yes(val, _)) => val,
            Err($crate::Recovered::No(guarantee)) => $default,
        }
    };
}

/// *`E___`* -- feature not implemented
#[derive(Debug, Clone)]
pub struct FeatureNotImplemented {
    /// name of the feature
    pub feature_name: String,
    /// text under primary label
    pub label_text: String,
    /// the location of the thing not implemented
    pub primary: Span,
    /// location of the call to `feature_todo!` macro, because it can be
    /// different from where we emit it.
    pub emit_loc: DiagEmitLoc,
}

impl FeatureNotImplemented {
    /// Create a new feature not implemented diagnostic error.
    #[track_caller]
    pub fn new(
        name: impl ToString,
        label_text: impl ToString,
        primary: Span,
    ) -> FeatureNotImplemented {
        FeatureNotImplemented {
            feature_name: name.to_string(),
            label_text: label_text.to_string(),
            primary: primary,
            emit_loc: DiagEmitLoc::from(Location::caller()),
        }
    }
}

impl Diagnostic for FeatureNotImplemented {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        let mut diag = dcx
            .diag(Level::Error)
            .with_title(format!(
                "the feature '{}', is not yet implemented",
                self.feature_name
            ))
            .with_label(Label::primary(self.primary).with_message(self.label_text));
        diag.emitted_at = self.emit_loc;

        diag
    }
}
