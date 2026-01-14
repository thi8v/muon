//! Muon is a general-purpose programming language, that compile AOT to machine code,
//! used to create maintanable, reusable and optimized software.

use std::{
    backtrace::{Backtrace, BacktraceStatus},
    panic,
    path::PathBuf,
    process::abort,
    thread,
};

use clap::{ArgAction, Parser as ArgParser, ValueEnum};
use muonc_middle::{
    kv::{KeyValue, KvPair},
    session::mk_session,
    target::TargetTriple,
};
use muonc_span::source::FsFileLoader;
use thiserror::Error;

mod build {
    include!(concat!(env!("OUT_DIR"), "/shadow.rs"));
}

/// Implements `FromStr` for any type that implements `ValueEnum`.
/// The error type is `String`.
macro_rules! from_value_enum {
    ($ty:ty) => {
        impl std::str::FromStr for $ty {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <$ty as clap::ValueEnum>::from_str(s, false).map_err(|e| e.to_string())
            }
        }
    };
}

#[derive(ArgParser, Debug)]
#[command(
    about = "Compiler for the Muon Programming Language.",
    disable_version_flag = true,
    override_usage = "muonc [OPTIONS] <INPUT>"
)]
pub struct MuonCli {
    /// Specify the name of the orb being built, defaults to the input file
    /// name with the extension
    #[arg(short = 'o', long)]
    output: Option<PathBuf>,

    /// The root file of the package to build. (required)
    input: Option<PathBuf>,

    /// Debug options, type `muonc -D help` for some help.
    #[arg(short = 'D', value_name = "KEY=VALUE")]
    debug: Vec<KvPair>,

    /// Build for the given target triplet, type `muonc --target help` for more
    /// details
    #[arg(long)]
    target: Option<TargetTriple>,

    /// Name of the package, defaults to the input file name with the extension
    #[arg(long)]
    pkg_name: Option<String>,

    /// Print version info and exit
    #[arg(short = 'V', long, action = ArgAction::SetTrue)]
    version: bool,

    /// Verbosity flag
    #[arg(short = 'v', long, action = ArgAction::SetTrue)]
    verbose: bool,
}

/// Compilation stages.
#[derive(Debug, Clone, ValueEnum)]
pub enum CompStage {
    Lexer,
    Parser,
}

from_value_enum!(CompStage);

/// Compilation results.
#[derive(Debug, Clone, ValueEnum)]
pub enum CompResults {
    Inputfile,
    TokenStream,
    Ast,
}

from_value_enum!(CompResults);

// / Debug options
#[derive(Default, Debug, KeyValue)]
#[kv(name = "debug", short = 'D')]
pub struct DebugOptions {
    #[kv(help = "Halt the compilation at a specified stage:
* lexer
* parser
...")]
    pub halt: Option<CompStage>,
    #[kv(help = "Print the timings in a summary, of all stages of the compiler. [default: false]")]
    pub timings: bool,
    #[kv(help = "Prints to the standard error, one or more of:
* inputfile
* token-stream
* ast
...")]
    pub print: Vec<CompResults>,
    #[kv(
        help = "Track the location of the creation of the diagnostic in the compiler.",
        default = "false"
    )]
    pub track_diagnostics: bool,
}

#[derive(Debug, Error)]
pub enum CliError {
    #[error("no input file")]
    NoInputFile,
    #[error(transparent)]
    ClapError(#[from] clap::Error),
    #[error("{0}")]
    InvalidKv(String),
}

pub fn run() -> Result<(), CliError> {
    panic::set_hook(Box::new(|panic_info| {
        let thread = thread::current();
        let backtrace = Backtrace::capture();
        eprintln!("{}\n", panic_info);

        match backtrace.status() {
            BacktraceStatus::Captured => {
                if let Some(name) = thread.name() {
                    eprintln!("thread '{}'\n{}", name, backtrace);
                    eprintln!();
                } else {
                    eprintln!("{}", backtrace);
                    eprintln!();
                }
            }
            BacktraceStatus::Disabled => eprintln!(
                "note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace"
            ),
            BacktraceStatus::Unsupported => eprintln!("note: backtrace is not supported."),
            status => {
                eprintln!("unknown backtrace status, {status:?}");
                abort()
            }
        }
        eprintln!("BUG: internal compiler error: unexpected panic.");
        eprintln!(
            "  = note: we would appreciate a bug report on https://github.com/thi8v/muon/issues/new",
        );
        eprintln!(
            "  = note: muonc {version} ({commit} {date})",
            version = env!("CARGO_PKG_VERSION"),
            commit = build::SHORT_COMMIT,
            date = build::COMMIT_DATE
        );
    }));

    let args = MuonCli::try_parse()?;

    let host = TargetTriple::host();

    if args.version {
        eprintln!(
            "muonc {version} ({commit} {date})",
            version = env!("CARGO_PKG_VERSION"),
            commit = build::SHORT_COMMIT,
            date = &build::COMMIT_DATE[..10]
        );

        if args.verbose {
            eprintln!("host: {}", host);
            eprintln!("commit-hash: {}", build::COMMIT_HASH);
            eprintln!("commit-date: {}", build::COMMIT_DATE);
            eprintln!("rustc-version: {}", build::RUST_VERSION);
            eprintln!("rustc-toolchain: {}", build::RUST_CHANNEL);
        }

        return Ok(());
    }

    if args.debug.iter().any(|f| matches!(f, KvPair::Help)) {
        DebugOptions::print_kv_help();

        return Ok(());
    }

    let debug_opts = DebugOptions::from_kv_map(&args.debug).map_err(CliError::InvalidKv)?;

    let Some(input) = args.input else {
        return Err(CliError::NoInputFile);
    };

    let pkg_name = args.pkg_name.unwrap_or_else(|| {
        input
            .with_extension("")
            .file_name()
            .unwrap()
            .to_string_lossy()
            .to_string()
    });

    // TODO: check that pkg_name can be an identifier.

    let sess = mk_session(
        args.target.unwrap_or(host),
        pkg_name,
        debug_opts.track_diagnostics,
        // true,
        FsFileLoader,
    );

    use muonc_errors::{ErrCode, Level};
    use muonc_span::span;

    let fid = sess.sm.register("./playground.mu");

    let diag = sess
        .dcx
        .diag(Level::Error)
        .with_code(ErrCode::UnknownToken)
        .with_message("ZEBI")
        .with_span(span(0usize, 10usize, fid), String::from("LABEL"))
        .with_span(span(2usize, 4usize, fid), String::from("ANOTHER LABEL"));

    sess.dcx.emit(diag);

    dbg!(&sess);

    sess.dcx.render();

    Ok(())
}
