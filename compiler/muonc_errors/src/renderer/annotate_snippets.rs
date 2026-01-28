//! [annotate_snippets] backend [Renderer] for [`Diagnostic`]s
//!
//! [Renderer]: crate::renderer::Renderer
//! [`Diagnostic`]: crate::Diagnostic

use std::sync::Arc;

use annotate_snippets::{Annotation, AnnotationKind, Group, Renderer as AsRenderer, Snippet};
use muonc_span::source::SourceMap;

use crate::{Code, MultiSpan, renderer::Renderer};

type OwnedReport<'dcx> = Vec<Group<'dcx>>;

/// [annotate_snippets] backend Renderer.
#[derive(Debug, Clone)]
pub struct AnnotateRenderer<'dcx> {
    inner: AsRenderer,
    reports: Vec<OwnedReport<'dcx>>,
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
            crate::Level::Debug => annotate_snippets::Level::INFO.with_name("DEBUG"),
        }
    }

    fn intern_diag(
        &mut self,
        level: crate::Level,
        message: &'dcx str,
        code: Option<crate::Code>,
        multispan: &'dcx MultiSpan,
        messages: &'dcx [crate::Message],
        sm: &'dcx Arc<SourceMap>,
    ) -> Group<'dcx> {
        let title = Self::level(level).primary_title(message);

        let title = match code {
            Some(Code::Err(err)) => title.id(err.to_string()),
            Some(Code::Warn(warn)) => title.id(warn.to_string()),
            None => title,
        };

        let report = if let Some(crate::Label { span, .. }) = multispan.first() {
            let fid = span.fid;
            let path = sm.ref_path(fid).as_os_str().to_str().unwrap();
            let src = sm.ref_src(fid);

            title.element(
                Snippet::source(src)
                    .path(path)
                    .annotations(multispan.iter().map(|crate::Label { style, msg, span }| {
                        debug_assert_eq!(
                            span.fid, fid,
                            "The file ids must be the same in this multi span"
                        );

                        let kind = match style {
                            crate::LabelStyle::Primary => AnnotationKind::Primary,
                            crate::LabelStyle::Secondary => AnnotationKind::Context,
                        };

                        kind.span(span.to_parts().1).label(msg)
                    })),
            )
        } else {
            title.elements(None::<Snippet<Annotation>>)
        };

        report.elements(
            messages
                .iter()
                .map(|msg| Self::level(msg.level).message(&msg.msg)),
        )
    }

    fn intern(&mut self, diag: &'dcx crate::Diag, sm: &'dcx Arc<SourceMap>) {
        let primary = self.intern_diag(
            diag.level,
            &diag.title,
            diag.code,
            &diag.span,
            &diag.messages,
            sm,
        );

        let mut report = vec![primary];

        for subdiag in &diag.children {
            let child = self.intern_diag(
                subdiag.level,
                &subdiag.message,
                None,
                &subdiag.span,
                &[],
                sm,
            );

            report.push(child);
        }

        self.reports.push(report);
    }
}

impl<'dcx> Default for AnnotateRenderer<'dcx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'dcx> Renderer<'dcx> for AnnotateRenderer<'dcx> {
    fn init(&mut self, diags: &'dcx [crate::Diag], sm: &'dcx Arc<SourceMap>) {
        for diag in diags {
            self.intern(diag, sm);
        }
    }

    fn render(&mut self) -> String {
        let mut res = String::new();

        for (i, report) in self.reports.iter().enumerate() {
            if i != 0 {
                // print a little separation between different diagnostics
                res.push_str("\n\n");
            }

            res.push_str(&self.inner.render(report));
        }

        res
    }
}
