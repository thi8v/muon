//! Diagnostics emitted by the Muon Lexer.

use muonc_errors::prelude::*;
use muonc_span::Span;

/// `E0001` -- unknown token
#[derive(Debug, Clone)]
pub struct UnknownToken {
    pub c: char,
    pub primary: Span,
}

impl Diagnostic for UnknownToken {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::UnknownToken)
            .with_title(format!("unknwon start of token: {:?}", self.c))
            .with_label(Label::primary(self.primary))
    }
}

/// `E0002` -- unterminated block comment
#[derive(Debug, Clone)]
pub struct UnterminatedBlockComment {
    pub primary: Span,
}

impl Diagnostic for UnterminatedBlockComment {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::UnterminatedBlockComment)
            .with_title("unterminated block comment")
            .with_label(Label::primary(self.primary))
    }
}

/// `E0003` -- unknown character escape
#[derive(Debug, Clone)]
pub struct UnknownCharacterEscape {
    pub es: char,
    pub primary: Span,
    pub lit_span: Span,
}

impl Diagnostic for UnknownCharacterEscape {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::UnknownCharacterEscape)
            .with_title(format!("unknown character escape: {}", self.es))
            .with_label(Label::primary(self.primary))
            .with_label(Label::secondary(self.lit_span).with_message("in this literal"))
        // Diagnostic::error()
        //     .with_code(ErrorCode::UnknownCharacterEscape)
        //     .with_message(format!("unknown character escape: {}", self.es))
        //     .with_label(Label::primary(self.loc.fid, self.loc))
    }
}

/// `E0004` -- too many codepoints in a character literal
#[derive(Debug, Clone)]
pub struct TooManyCodepointsInCharLiteral {
    pub primary: Span,
}

impl Diagnostic for TooManyCodepointsInCharLiteral {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::TooManyCodepointsInCharLiteral)
            .with_title(
                "too many characters in a character literal, can only contain one codepoint",
            )
            .with_note("if you want to write a string literal use double quotes: \"")
            .with_label(Label::primary(self.primary))
    }
}

/// `E0005` -- empty character literal
#[derive(Debug, Clone)]
pub struct EmptyCharLiteral {
    pub primary: Span,
}

impl Diagnostic for EmptyCharLiteral {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::EmptyCharLiteral)
            .with_title("empty character literal")
            .with_label(
                Label::primary(self.primary).with_message("expected one codepoint but found zero"),
            )
    }
}

/// `E0006` -- early reach of the end of file
#[derive(Debug, Clone)]
pub struct ReachedEof {
    pub primary: Span,
}

impl Diagnostic for ReachedEof {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::ReachedEof)
            .with_title("reached end of file too early")
            .with_label(Label::primary(self.primary))
    }
}

/// `E0007` -- not enough hex digits in hexadecimal escape sequence
#[derive(Debug, Clone)]
pub struct NotEnoughHexDigits {
    pub primary: Span,
}

impl Diagnostic for NotEnoughHexDigits {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::NotEnoughHexDigits)
            .with_title("not enough hexadecimal digits in escape sequence")
            .with_label(Label::primary(self.primary))
    }
}

/// `E0008` -- unterminated string literal
#[derive(Debug, Clone)]
pub struct UnterminatedStringLiteral {
    /// location of the unterminated string literal
    pub primary: Span,
}

impl Diagnostic for UnterminatedStringLiteral {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::UnterminatedStringLiteral)
            .with_title("unterminated string literal")
            .with_label(Label::primary(self.primary))
    }
}

/// `E0009` -- invalid digit in number
#[derive(Debug, Clone)]
pub struct InvalidDigitInNumber {
    /// the invalid character
    pub c: char,
    /// location of the invalid digit
    pub primary: Span,
    /// location of the integer until the error
    pub int_span: Span,
}

impl Diagnostic for InvalidDigitInNumber {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::InvalidDigitNumber)
            .with_title(format!("invalid digit in integer literal: {}", self.c))
            .with_label(Label::primary(self.primary))
            .with_label(Label::secondary(self.int_span).with_message("in this integer"))
    }
}

/// `E0010` -- too large integer literal
#[derive(Debug, Clone)]
pub struct TooLargeIntegerLiteral {
    /// location of the too large integer to fit in 128 bits
    pub primary: Span,
}

impl Diagnostic for TooLargeIntegerLiteral {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::TooLargeIntegerLiteral)
            .with_title("integer literal is too large")
            .with_label(Label::primary(self.primary))
            .with_note(format!("integer exceeds the limit of `{}`", u128::MAX))
    }
}

#[derive(Debug, Clone)]
pub enum InvalidUnicodeNote {
    ExpectedOpeningBrace,
    EmptyUnicode,
    TooBig,
    ExpectedClosingBrace,
    MustNotBeASurrogate,
}

impl InvalidUnicodeNote {
    pub fn as_str(&self) -> &str {
        match self {
            Self::ExpectedOpeningBrace => "expected '{' after '\\u'",
            Self::EmptyUnicode => "this escape must have at least one hex digit",
            Self::TooBig => "this hex number doesn't fit in 32 bits",
            Self::ExpectedClosingBrace => "expected '}' at the end of the unicode escape",
            Self::MustNotBeASurrogate => "unicode escape must not be a surrogate",
        }
    }
}

/// `E0011` -- invalid unicode escape sequence
#[derive(Debug, Clone)]
pub struct InvalidUnicodeEscape {
    pub note: InvalidUnicodeNote,
    pub primary: Span,
}

impl Diagnostic for InvalidUnicodeEscape {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::InvalidUnicodeEscape)
            .with_title("invalid unicode escape")
            .with_label(Label::primary(self.primary).with_message(self.note.as_str()))
    }
}

/// `E0012` -- expected exponent part
#[derive(Debug, Clone)]
pub struct ExpectedExponentPart {
    pub found: char,
    pub primary: Span,
    pub float_span: Span,
}

impl Diagnostic for ExpectedExponentPart {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::ExpectedExponentPart)
            .with_title(format!(
                "expected exponent part of hexadecimal floating point literal, but found {:?}",
                self.found
            ))
            .with_label(Label::primary(self.primary))
            .with_label(Label::secondary(self.float_span))
    }
}

/// `E0013` -- no digits in a non decimal
#[derive(Debug, Clone)]
pub struct NoDigitsInANonDecimal {
    pub primary: Span,
}

impl Diagnostic for NoDigitsInANonDecimal {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::NoDigitsInANonDecimal)
            .with_title("no digits found after the base")
            .with_label(Label::primary(self.primary))
    }
}
