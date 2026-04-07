//! Diagnostic emited at the HIR stage of Muonc.

use std::path::PathBuf;

use muonc_errors::{WarnCode, prelude::*};
use muonc_span::prelude::*;

/// `E0018` -- module file path error
#[derive(Debug, Clone)]
pub enum ModuleFilePathErr {
    BothFiles {
        name: Symbol,
        paths: [PathBuf; 2],
        primary: Span,
    },
    NoFiles {
        name: Symbol,
        paths: [PathBuf; 2],
        primary: Span,
    },
}

impl Diagnostic for ModuleFilePathErr {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        match self {
            Self::BothFiles {
                name,
                paths,
                primary,
            } => dcx
                .diag(Level::Error)
                .with_code(ErrCode::ModuleFilePathErr)
                .with_title(format!(
                    "file for module '{name}' found at both '{}' and '{}'",
                    paths[0].display(),
                    paths[1].display()
                ))
                .with_help("remove the ambiguity by deleting one of the candidate files.")
                .with_label(Label::primary(primary)),
            Self::NoFiles {
                name,
                paths,
                primary,
            } => dcx
                .diag(Level::Error)
                .with_code(ErrCode::ModuleFilePathErr)
                .with_title(format!("file not found for module '{name}'"))
                .with_label(Label::primary(primary))
                .with_help(format!(
                    "to create the module '{name}', create the file '{}' or '{}'",
                    paths[0].display(),
                    paths[1].display()
                )),
        }
    }
}

/// `W0001` -- shadowing a label
#[derive(Debug, Clone)]
pub struct WLabelShadowed {
    /// the label name
    pub name: Symbol,
    /// span of the label definition that is shadowed
    pub first_decl: Span,
    /// span of the label declaration that shadows the first one
    pub primary: Span,
}

impl Diagnostic for WLabelShadowed {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Warning)
            .with_code(WarnCode::LabelShadowed)
            .with_title(format!(
                "label name `{}` shadows a label name that is already in scope",
                self.name
            ))
            .with_label(
                Label::primary(self.primary)
                    .with_message(format!("label `{}` already in scope", self.name)),
            )
            .with_label(Label::secondary(self.first_decl).with_message("the shadowed label"))
            .with_help("you should rename one of the labels, it will make the code more readable")
    }
}

/// `E0019` -- use of undefined label
#[derive(Debug, Clone)]
pub struct UseOfUndefinedLabel {
    pub name: Symbol,
    pub primary: Span,
}

impl Diagnostic for UseOfUndefinedLabel {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::UseOfUndefinedLabel)
            .with_title(format!("use of undefined label '{}'", self.name))
            .with_label(Label::primary(self.primary))
    }
}

/// `E0020` -- label keyword outside loop or block
#[derive(Debug, Clone)]
pub struct LabelKwOutsideLoopOrBlock {
    pub kw: Symbol,
    pub primary: Span,
}

impl Diagnostic for LabelKwOutsideLoopOrBlock {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::LabelKwOutsideLoopOrBlock)
            .with_title(format!(
                "'{}' outside of a loop or a labeled block",
                self.kw
            ))
            .with_label(Label::primary(self.primary))
    }
}

/// `E0021` -- break with value unsupported
#[derive(Debug, Clone)]
pub struct BreakWithValueUnsupported {
    pub wher: Symbol,
    pub expr_span: Span,
    pub break_span: Span,
    pub def_span: Span,
}

impl Diagnostic for BreakWithValueUnsupported {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::BreakWithValueUnsupported)
            .with_title(format!("'break' from a {} with a value", self.wher))
            .with_label(
                Label::primary(self.expr_span)
                    .with_message("can only 'break' with a value on a labeled block or a 'loop'"),
            )
            .with_label(Label::secondary(self.break_span))
            .with_label(
                Label::secondary(self.def_span).with_message(format!("from this {}", self.wher)),
            )
    }
}

/// `E0022` -- can't continue a block
#[derive(Debug, Clone)]
pub struct CantContinueABlock {
    pub primary: Span,
    pub block_span: Span,
}

impl Diagnostic for CantContinueABlock {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::CantContinueABlock)
            .with_title("a block can't be 'continue'd")
            .with_label(Label::primary(self.primary))
            .with_label(Label::secondary(self.block_span))
            .with_help("you might want to use a 'while', 'for' or 'loop' instead.")
    }
}

/// `E0023` -- not found in scope
#[derive(Debug, Clone)]
pub struct NotFoundInScope {
    /// the path "rendered"
    pub name: String,
    /// span of the segment that made the resolution fail.
    pub seg_span: Span,
    /// span of the entire path
    pub path_span: Span,
    /// a similar name/seg existed in the current scope.
    pub similar: Option<(Symbol, Symbol)>,
}

impl Diagnostic for NotFoundInScope {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::NotFoundInScope)
            .with_title(format!("cannot find '{}' in the current scope", self.name))
            .with_label(Label::primary(self.seg_span))
            .with_label(Label::secondary(self.path_span))
            .with_help_iter(self.similar.map(|(similar, what)| {
                format!("there is a {what} `{similar}` with a similar name")
            }))
    }
}

/// `E0024` -- ambiguous name
#[derive(Debug, Clone)]
pub struct AmbiguousName {
    pub name: String,
    /// span of the name used ambiguously
    pub primary: Span,
    /// the previous defs, `.0` is what it is: `primitive type`, `local`,
    /// `function definition`... and `.1` is the span of the definition if any.
    pub defs: Vec<(Symbol, Option<Span>)>,
}

impl Diagnostic for AmbiguousName {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::AmbiguousName)
            .with_title(format!("ambiguous name '{}'", self.name))
            .with_label(Label::primary(self.primary))
            .with_subdiag_iter(self.defs.iter().map(|(what, span)| {
                let mut multi_span = MultiSpan::new();

                if let Some(span) = span {
                    multi_span.push_span(Label::primary(*span));
                }

                Subdiag {
                    level: Level::Note,
                    message: format!(
                        ".. defined {}as a {what}",
                        if span.is_some() { "here " } else { "" }
                    ),
                    span: multi_span,
                }
            }))
    }
}

/// `E0025` -- name defined multiple times
#[derive(Debug, Clone)]
pub struct NameDefinedMultipleTimes {
    /// name defined multiple times
    pub name: Symbol,
    /// span of the new definition
    pub new_span: Span,
    /// span of the previous definition
    pub old_span: Span,
}

impl Diagnostic for NameDefinedMultipleTimes {
    fn into_diag(self, dcx: &DiagCtxt) -> Diag {
        dcx.diag(Level::Error)
            .with_code(ErrCode::NameDefinedMultipleTimes)
            .with_title(format!(
                "the name '{}' is defined multiple times",
                self.name
            ))
            .with_label(
                Label::primary(self.new_span)
                    .with_message(format!("defined '{}' a second time here", self.name)),
            )
            .with_label(
                Label::secondary(self.old_span)
                    .with_message(format!("defined here for the first time")),
            )
    }
}
