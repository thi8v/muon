//! Session of compilation.

use std::{
    fmt,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use muonc_errors::{DiagCtxt, DiagCtxtFlags, DiagEmitLoc};
use muonc_span::{
    source::{FileLoader, SourceMap},
    symbol::Symbol,
};

use crate::target::TargetTriple;

/// Session of a compilation.
#[derive(Debug)]
pub struct Session {
    /// Target's target triple.
    pub target: TargetTriple,
    /// Host target.
    pub host: TargetTriple,
    /// Timings of the compilation sessions.
    pub timings: Mutex<Timings>,
    /// Name of the package.
    pub pkg_name: Symbol,
    /// Do we track the location of creation of diagnostics?
    pub track_diagnostics: bool,
    /// The source maps.
    pub sm: Arc<SourceMap>,
    /// The diagnostic context.
    pub dcx: DiagCtxt,
}

impl Session {
    /// Compute the total duration of the timings.
    pub fn set_total_timings(&self) {
        let mut timings = self.timings.lock().expect("unable to lock the timings");
        timings.set_total();
    }

    /// Add `dt` duration to the `lexer` timings.
    ///
    /// N.B: this is used to add the lexing and parsing time of the nested
    /// files.
    pub fn add_lexer_dt(&self, dt: Duration) {
        let mut timings = self.timings.lock().expect("unable to lock the timings");
        timings.add_lexer(dt);
    }

    /// Same as `Session::add_lexer_dt`
    pub fn add_parser_dt(&mut self, dt: Duration) {
        let mut timings = self.timings.lock().expect("unable to lock the timings");
        timings.add_parser(dt);
    }

    /// Set the elapsed time of the `setup`.
    pub fn elapsed_setup(&self) {
        let instant = Instant::now();
        let mut timings = self.timings.lock().expect("unable to lock the timings");

        timings.setup = instant - timings.last_instant;
        timings.last_instant = instant;
    }

    /// Set the elapsed time of the `lexer`.
    pub fn elapsed_lexer(&self) {
        let instant = Instant::now();
        let mut timings = self.timings.lock().expect("unable to lock the timings");

        timings.lexer = instant - timings.last_instant;
        timings.last_instant = instant;
    }

    /// Set the elapsed time of the `parser`.
    pub fn elapsed_parser(&self) {
        let instant = Instant::now();
        let mut timings = self.timings.lock().expect("unable to lock the timings");

        timings.parser = instant - timings.last_instant;
        timings.last_instant = instant;
    }

    /// Emit the summary diagnostic if any.
    pub fn emit_summary(&self) {
        use muonc_errors::prelude::*;

        if let Some(summary) = self.dcx.summary(self.pkg_name) {
            let lvl = if self.dcx.failed() {
                Level::Error
            } else {
                Level::Info
            };

            let (codes, more) = self.dcx.err_codes();

            let dots = if more { " ..." } else { "" };

            let diag = self.dcx.diag(lvl).with_title(summary);

            let mut summary_diag = if codes.is_empty() {
                diag
            } else {
                diag.with_note(format!(
                    "Some errors have detailed documentation: {}{}, try 'muonc --explain {}'",
                    codes
                        .iter()
                        .map(|code| code.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    dots,
                    codes.first().expect("have at least one code??")
                ))
            };

            // tell the dcx we never want the debug infos.
            summary_diag.emitted_at = DiagEmitLoc::__NEVER_DEBUG_INFO;

            self.dcx.emit(summary_diag);
        }
    }
}

/// Make a new compilation session.
pub fn mk_session(
    target: TargetTriple,
    pkg_name: Symbol,
    track_diagnostics: bool,
    loader: impl FileLoader + 'static,
    initial: Instant,
) -> Arc<Session> {
    let timings = Timings::new(initial);
    let sm = Arc::new(SourceMap::new(loader));
    let mut flags = DiagCtxtFlags::empty();

    if track_diagnostics {
        flags |= DiagCtxtFlags::TRACK_DIAGNOSTICS;
    }

    Arc::new(Session {
        target,
        host: TargetTriple::host(),
        timings: Mutex::new(timings),
        pkg_name,
        track_diagnostics,
        sm: sm.clone(),
        dcx: DiagCtxt::new(sm, flags),
    })
}

/// Timings of the compiler.
#[derive(Debug, Clone)]
pub struct Timings {
    last_instant: Instant,
    /// Duration of the setup.
    setup: Duration,
    /// Duration of lexing.
    lexer: Duration,
    /// Duration of paring.
    parser: Duration,
    /// Total duration.
    total: Duration,
}

macro_rules! elapsed_fn {
    ($fn:ident, $name:ident) => {
        #[doc = concat!("Set the elapsed time of `", stringify!($name), "`.")]
        pub fn $fn(&mut self) {
            self.$name = self.last_instant.elapsed();
            self.last_instant = Instant::now();
        }
    };
}

impl Timings {
    /// Create a new timings record with `initial` as the instant where we start
    /// to setup the compiler.
    pub fn new(initial: Instant) -> Self {
        Timings {
            last_instant: initial,
            setup: Duration::ZERO,
            lexer: Duration::ZERO,
            parser: Duration::ZERO,
            total: Duration::ZERO,
        }
    }

    elapsed_fn!(elapsed_setup, setup);
    elapsed_fn!(elapsed_lexer, lexer);
    elapsed_fn!(elapsed_parser, parser);

    /// Compute the total time.
    pub fn set_total(&mut self) {
        self.total = self.setup + self.lexer + self.parser;
    }

    /// Add `dt` duration to the `lexer` timings.
    ///
    /// N.B: this is used to add the lexing and parsing time of the nested
    /// files.
    pub fn add_lexer(&mut self, dt: Duration) {
        self.lexer += dt;
    }

    /// Same as `Timings::add_lexer`
    pub fn add_parser(&mut self, dt: Duration) {
        self.parser += dt;
    }
}

impl fmt::Display for Timings {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Timings {
            last_instant: _,
            setup,
            lexer,
            parser,
            total,
        } = self.clone();

        writeln!(f, " Timings:")?;
        writeln!(f, "   setup: {}", humantime::format_duration(setup))?;
        writeln!(f, "   lexer: {}", humantime::format_duration(lexer))?;
        writeln!(f, "  parser: {}", humantime::format_duration(parser))?;
        writeln!(f, "=  Total: {}", humantime::format_duration(total))?;

        Ok(())
    }
}
