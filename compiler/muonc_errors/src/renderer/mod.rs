//! Diagnostic renderer abstraction.

use crate::*;

pub mod annotate_snippets;

/// Diagnostic renderer.
pub trait Renderer<'diag> {
    /// Initializes the renderer with the provided diagnostics.
    fn init(&mut self, diags: &'diag [Diag], sm: &'diag Arc<SourceMap>);

    /// Render the result to a string.
    fn render(&mut self) -> String;
}
