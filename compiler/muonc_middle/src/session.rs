//! Session of compilation.

use std::{
    fmt,
    sync::Arc,
    time::{Duration, Instant},
};

use muonc_errors::{DiagCtxt, DiagCtxtFlags};
use muonc_span::source::{FileLoader, SourceMap};

use crate::target::TargetTriple;

/// Session of a compilation.
#[derive(Debug, Clone)]
pub struct Session {
    /// Target's target triple.
    pub target: TargetTriple,
    /// Host target.
    pub host: TargetTriple,
    /// Timings of the compilation sessions.
    pub timings: Timings,
    /// Name of the package.
    pub pkg_name: String,
    /// Do we track the location of creation of diagnostics?
    pub track_diagnostics: bool,
    /// The source maps.
    pub sm: Arc<SourceMap>,
    /// The diagnostic context.
    pub dcx: DiagCtxt,
}

/// Make a new compilation session.
pub fn mk_session(
    target: TargetTriple,
    pkg_name: String,
    track_diagnostics: bool,
    loader: impl FileLoader + 'static,
) -> Session {
    let sm = Arc::new(SourceMap::new(loader));
    let mut flags = DiagCtxtFlags::empty();

    if track_diagnostics {
        flags |= DiagCtxtFlags::TRACK_DIAGNOSTICS;
    }

    Session {
        target,
        host: TargetTriple::host(),
        timings: Timings::default(),
        pkg_name,
        track_diagnostics,
        sm: sm.clone(),
        dcx: DiagCtxt::new(sm, flags),
    }
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

impl Default for Timings {
    fn default() -> Self {
        Timings {
            last_instant: Instant::now(),
            setup: Duration::ZERO,
            lexer: Duration::ZERO,
            parser: Duration::ZERO,
            total: Duration::ZERO,
        }
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
