//! Diagnostics emitted by the parser.

use muonc_errors::prelude::*;
use muonc_span::{Span, symbol::Symbol};
use muonc_token::{ExpTokenSet, Token, TokenType};
use muonc_utils::{list_fmt, suggest_similar};

use crate::directive::Directive;

/// `EXXXX` -- expected token
#[derive(Debug, Clone)]
pub struct ExpectedToken {
    /// what token was expected?
    expected: Vec<String>,
    /// what was found instead of the expected token
    found: TokenType,
    /// semicolon info.
    semi_span: Option<Span>,
    /// location of the found token
    primary: Span,
}

impl ExpectedToken {
    /// Empty expected token, used when the expected are added later.
    pub const EMPTY: [String; 0] = [];

    /// Create a new ExpectedToken diag.
    pub fn new<I: IntoIterator<Item = S>, S: ToString>(expected: I, found: Token) -> ExpectedToken {
        ExpectedToken {
            expected: expected.into_iter().map(|s| s.to_string()).collect(),
            found: found.tt,
            semi_span: None,
            primary: found.span,
        }
    }

    pub fn add_expects(mut self, expects: ExpTokenSet) -> Self {
        self.expected
            .extend(expects.iter().map(|tr| tr.to_string()));
        self
    }

    pub fn add_semi(&mut self, semi_span: Span) {
        self.semi_span = Some(semi_span);
    }

    fn fmt_msg(&self) -> String {
        let len = self.expected.len();
        assert_ne!(len, 0, "must have at least one expected token");

        let expected = list_fmt(&self.expected);

        format!("expected {}, found {}", expected, self.found)
    }
}

impl Diagnostic for ExpectedToken {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_title(self.fmt_msg())
            .with_label({
                let mut label = Label::primary(self.primary);

                if self.semi_span.is_some() {
                    label.msg = format!("unexpected {}", self.found);
                }

                label
            })
            .with_labels_iter(
                self.semi_span
                    .map(|span| Label::secondary(span).with_message("add `;` after this token")),
            )
    }
}

/// `E0014` -- mutability qualifier used where not permitted
#[derive(Debug, Clone)]
pub struct MutQualifierNotPermitted {
    pub primary: Span,
}

impl Diagnostic for MutQualifierNotPermitted {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::MutQualifierNotPermitted)
            .with_title("mutability qualifiers are not permitted here")
            .with_label(Label::primary(self.primary))
            .with_help("remove the mutability qualifier")
    }
}

/// `E0015` -- visibility qualifier used where not permitted
#[derive(Debug, Clone)]
pub struct VisQualifierNotPermitted {
    pub primary: Span,
}

impl Diagnostic for VisQualifierNotPermitted {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::VisQualifierNotPermitted)
            .with_title("visibility qualifiers are not permitted here")
            .with_label(Label::primary(self.primary))
            .with_help("remove the visibility qualifier")
    }
}

/// `E0016` -- invalid abi
#[derive(Debug, Clone)]
pub struct InvalidAbi {
    pub abi: Symbol,
    pub primary: Span,
}

impl Diagnostic for InvalidAbi {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::InvalidAbi)
            .with_title(format!("invalid ABI, found: `{}`", self.abi))
            .with_label(Label::primary(self.primary))
            .with_note("`Muon`, `C` are the supported calling conventions")
    }
}

/// `E0017` -- malformed if expr
#[derive(Debug, Clone)]
pub struct MalformedIfExpr {
    pub kind: MalformedIfKind,
    pub primary: Span,
}

/// Kind of if expression malformedness
#[derive(Debug, Clone)]
pub enum MalformedIfKind {
    BlockElseIfExpr,
}

impl MalformedIfKind {
    pub fn help_msg(&self) -> &'static str {
        match self {
            MalformedIfKind::BlockElseIfExpr => {
"the 'else' branch of an 'if' expression whose 'then' branch is a block must be either:
  - a block
  - or an 'if' expression whose 'then' branch is a block"
            }
        }
    }
}

impl Diagnostic for MalformedIfExpr {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::MalformedIfExpr)
            .with_title("malformed if expression")
            .with_label(Label::primary(self.primary))
            .with_help(self.kind.help_msg())
    }
}

/// `EXXXX` -- unknown directive
#[derive(Debug, Clone)]
pub struct UnknownDirective {
    pub name: Symbol,
    pub primary: Span,
}

impl Diagnostic for UnknownDirective {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_title(format!("unknown directive '{}'", self.name))
            .with_label(Label::primary(self.primary))
            .with_help_iter(
                suggest_similar(self.name, Directive::DIRECTIVE_NAMES.iter().copied())
                    .map(|word| format!("a directive with a similar name exists: '{word}'")),
            )
    }
}
