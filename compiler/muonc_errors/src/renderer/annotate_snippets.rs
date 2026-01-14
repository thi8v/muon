//! [annotate_snippets] backend [Renderer] for [`Diagnostic`]s
//!
//! [Renderer]: crate::renderer::Renderer
//! [`Diagnostic`]: crate::Diagnostic

use std::sync::Arc;

use annotate_snippets::{Annotation, AnnotationKind, Group, Renderer as AsRenderer, Snippet};
use muonc_span::source::SourceMap;

use crate::{Code, MultiSpan, renderer::Renderer};

/// [annotate_snippets] backend Renderer.
#[derive(Debug, Clone)]
pub struct AnnotateRenderer<'dcx> {
    inner: AsRenderer,
    reports: Vec<Group<'dcx>>,
}

impl<'dcx> AnnotateRenderer<'dcx> {
    /// Create a new annotate snippets renderer.
    pub fn new() -> AnnotateRenderer<'dcx> {
        AnnotateRenderer {
            inner: AsRenderer::styled(),
            reports: Vec::new(),
        }
    }

    fn level(lvl: crate::Level) -> annotate_snippets::Level<'dcx> {
        match lvl {
            crate::Level::Error => annotate_snippets::Level::ERROR,
            crate::Level::Warning => annotate_snippets::Level::WARNING,
            crate::Level::Info => annotate_snippets::Level::INFO,
            crate::Level::Note => annotate_snippets::Level::NOTE,
            crate::Level::Help => annotate_snippets::Level::HELP,
        }
    }

    fn intern_diag(
        &mut self,
        level: crate::Level,
        message: &'dcx str,
        code: Option<crate::Code>,
        multispan: &'dcx MultiSpan,
        sm: &'dcx Arc<SourceMap>,
    ) -> Group<'dcx> {
        let title = Self::level(level).primary_title(message);

        let title = match code {
            Some(Code::Err(err)) => title.id(err.to_string()),
            Some(Code::Warn(warn)) => title.id(warn.to_string()),
            None => title,
        };

        if let Some((span, _)) = multispan.first() {
            let fid = span.fid;
            let path = sm.get_path(fid).as_os_str().to_str().unwrap();
            let src = sm.get_src(fid);

            title.element(Snippet::source(src).path(path).annotations(
                multispan.iter().enumerate().map(|(i, (span, label))| {
                    debug_assert_eq!(
                        span.fid, fid,
                        "The file ids must be the same in this multi span"
                    );

                    let kind = if i == 0 {
                        AnnotationKind::Primary
                    } else {
                        AnnotationKind::Context
                    };

                    kind.span(span.to_parts().1).label(label.as_deref())
                }),
            ))
        } else {
            title.elements(None::<Snippet<Annotation>>)
        }
    }

    fn intern(&mut self, diag: &'dcx crate::Diag, sm: &'dcx Arc<SourceMap>) {
        let primary = self.intern_diag(diag.level, &diag.message, diag.code, &diag.span, sm);

        self.reports.push(primary);

        for subdiag in &diag.children {
            let child = self.intern_diag(subdiag.level, &subdiag.message, None, &subdiag.span, sm);

            self.reports.push(child);
        }
    }
}

impl<'dcx> Renderer<'dcx> for AnnotateRenderer<'dcx> {
    fn init(&mut self, diags: &'dcx [crate::Diag], sm: &'dcx Arc<SourceMap>) {
        for diag in diags {
            self.intern(diag, &sm);
        }
    }

    fn render(&mut self) -> String {
        self.inner.render(&self.reports)
    }
}
