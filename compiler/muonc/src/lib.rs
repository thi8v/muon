//! Muon is a general-purpose programming language, that compile AOT to machine code,
//! used to create maintanable, reusable and optimized software.

use std::{
    backtrace::{Backtrace, BacktraceStatus},
    io::{self, stderr},
    panic,
    path::PathBuf,
    process::{ExitCode, abort},
    sync::{Arc, OnceLock},
    thread,
    time::Instant,
};

use clap::{ArgAction, ColorChoice, Parser as ArgParser, ValueEnum};
use muonc_hir::{lowering::LoweringCtx, resolve::Resolver};
use termimad::MadSkin;
use thiserror::Error;

use muonc_errors::prelude::*;
use muonc_lexer::Lexer;
use muonc_middle::{
    kv::{KeyValue, KvPair},
    session::{Session, mk_session},
    target::TargetTriple,
};
use muonc_parser::Parser;
use muonc_span::{
    FileId,
    source::FsFileLoader,
    symbol::{Symbol, force_eval_global_interner},
};
use muonc_utils::pretty::PrettyDump;

mod build {
    // NOTE: it is a manual implementation of the call to the `shadow_rs!` macro
    // because i don't want the `build` mod to be public.
    include!(concat!(env!("OUT_DIR"), "/shadow.rs"));
}

pub static COLOR_CHOICE: OnceLock<ColorChoice> = OnceLock::new();

/// converts clap color choice to termcolor's
pub fn color_choice_converter(choice: ColorChoice) -> termcolor::ColorChoice {
    match choice {
        ColorChoice::Auto => termcolor::ColorChoice::Auto,
        ColorChoice::Always => termcolor::ColorChoice::Always,
        ColorChoice::Never => termcolor::ColorChoice::Never,
    }
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
    override_usage = "muonc [OPTIONS] <INPUT>",
    color = if cfg!(debug_assertions) { ColorChoice::Always } else { ColorChoice::Auto },
)]
pub struct MuonCli {
    /// Specify the name of the package being built, defaults to the input file
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

    /// Explain an error code like `E0001` or a warning like `W0001`.
    #[arg(long)]
    explain: Option<muonc_errors::Code>,

    /// Coloring.
    #[arg(long, value_name = "WHEN", default_value_t = ColorChoice::Auto)]
    color: ColorChoice,

    /// Print version info and exit
    #[arg(short = 'V', long, action = ArgAction::SetTrue)]
    version: bool,

    /// Verbosity flag
    #[arg(short = 'v', long, action = ArgAction::SetTrue)]
    verbose: bool,
}

/// Compilation stages.
#[derive(Debug, Clone, ValueEnum, PartialEq, Eq, Hash)]
pub enum CompStage {
    Lexer,
    Parser,
    Hir,
}

from_value_enum!(CompStage);

/// Compilation results.
#[derive(Debug, Clone, ValueEnum, PartialEq)]
pub enum CompResults {
    Inputfile,
    TokenStream,
    Ast,
    Hir,
}

from_value_enum!(CompResults);

/// Debug options
#[derive(Default, Debug, KeyValue)]
#[kv(name = "debug", short = 'D')]
pub struct DebugOptions {
    #[kv(help = "Halt the compilation at a specified stage:
* lexer
* parser
...")]
    pub halt: Option<CompStage>,
    #[kv(
        help = "Print the timings in a summary, of all stages of the compiler.",
        default = "false"
    )]
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

impl DebugOptions {
    /// Does the options contains this compile result to print?
    pub fn contains_print(&self, res: CompResults) -> bool {
        self.print.contains(&res)
    }

    /// Does the options contains this compile stage to halt?
    pub fn contains_halt(&self, stage: CompStage) -> bool {
        self.halt.as_ref().is_some_and(|val| *val == stage)
    }
}

#[derive(Debug, Error)]
pub enum CliError {
    #[error("no input file")]
    NoInputFile,
    #[error(transparent)]
    ClapError(#[from] clap::Error),
    #[error("{0}")]
    InvalidKv(String),
    #[error("the package name {0:?} cannot be an identifier.")]
    NonIdentPkgName(String),
    #[error("{0}: {1}")]
    Io(PathBuf, io::Error),
    #[error("build failed({failed}), you SHOULD NEVER see this message.")]
    BuildFailed {
        guarantee: DiagGuaranteed,
        failed: bool,
    },
}

impl CliError {
    /// Returns `true` if the cli error is [`BuildFailed`].
    ///
    /// [`BuildFailed`]: CliError::BuildFailed
    #[must_use]
    pub fn is_build_failed(&self) -> bool {
        matches!(self, Self::BuildFailed { .. })
    }
}

/// Exit code used by muonc to tell that the build failed.
pub fn exit_code_build_fail() -> ExitCode {
    ExitCode::from(0x69)
}

pub fn explain(code: muonc_errors::Code) {
    let docs = code.get_docs();
    let skin = MadSkin::default();

    skin.print_text(docs);
}

pub fn run() -> Result<(), CliError> {
    let initial = Instant::now();

    // 1. setup everything and make the compilation session.
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
            version = build::PKG_VERSION,
            commit = build::SHORT_COMMIT,
            date = build::COMMIT_DATE
        );
    }));

    let args = MuonCli::try_parse()?;

    COLOR_CHOICE
        .set(args.color)
        .expect("COLOR_CHOICE must be uninitialized at this point");

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
            eprintln!("branch: {}", build::BRANCH);
            eprintln!("build-channel: {}", build::BUILD_RUST_CHANNEL);
            eprintln!("rustc-version: {}", build::RUST_VERSION);
            eprintln!("rustc-toolchain: {}", build::RUST_CHANNEL);
        }

        return Ok(());
    }

    if args.debug.iter().any(|f| matches!(f, KvPair::Help)) {
        DebugOptions::print_kv_help();

        return Ok(());
    }

    if let Some(code2explain) = args.explain {
        explain(code2explain);
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

    // force the global interner to be evaluated here and not later.
    force_eval_global_interner();

    let pkg = Symbol::intern(&pkg_name);

    if !pkg.can_identifier() {
        return Err(CliError::NonIdentPkgName(pkg_name));
    }

    let sess = mk_session(
        args.target.unwrap_or(host),
        pkg,
        debug_opts.track_diagnostics,
        FsFileLoader,
        initial,
    );

    let res = build(sess.clone(), input, &debug_opts);

    sess.set_total_timings();

    if debug_opts.timings {
        let should_print = match res {
            Err(ref e) => e.is_build_failed(),
            Ok(_) => true,
        };

        if should_print {
            eprint!("\n{}", sess.timings.lock().unwrap());
        }
    }

    res
}

fn build(sess: Arc<Session>, input: PathBuf, debug_opts: &DebugOptions) -> Result<(), CliError> {
    let builderr = |guarantee: DiagGuaranteed| -> Result<(), CliError> {
        sess.emit_summary();
        sess.dcx.render();

        Err(CliError::BuildFailed {
            guarantee,
            failed: sess.dcx.failed(),
        })
    };

    // use this closure to return early and check if we emitted diags and return
    // the appropriate thing.
    let check_dcx = || -> Result<(), CliError> {
        match sess.dcx.has_emitted() {
            Some(guarantee) => builderr(guarantee),
            None => Ok(()),
        }
    };

    // 2. register the source code file of the root module.
    let root_fid = sess
        .sm
        .try_register(&input)
        .map_err(|err| CliError::Io(input, err))?;

    debug_assert_eq!(root_fid, FileId::ROOT_MODULE);

    //    maybe print the source code
    if debug_opts.contains_print(CompResults::Inputfile) {
        eprintln!(
            "/* source code of {} */",
            sess.sm.ref_path(root_fid).display()
        );
        eprintln!("{}", sess.sm.ref_src(root_fid));
    }

    sess.elapsed_setup();

    // 3. lexes the root file
    let mut lexer = Lexer::new(sess.sm.ref_src(root_fid), sess.clone(), root_fid);
    let tokenstream = match lexer.produce().dere() {
        Ok(ts) => ts,
        Err(guarantee) => return builderr(guarantee),
    };

    //    maybe print the token stream
    if debug_opts.contains_print(CompResults::TokenStream) {
        eprintln!("/* token stream */");
        tokenstream
            .fmt(&mut stderr(), sess.sm.ref_src(root_fid))
            .expect("couldn't pretty print the token stream");
    }

    sess.elapsed_lexer();

    //    maybe halt the compilation here
    if debug_opts.contains_halt(CompStage::Lexer) {
        return check_dcx();
    }

    // 4. parses the root file
    let mut parser = Parser::new(tokenstream, sess.clone());
    let ast = match parser.produce().dere() {
        Ok(ast) => ast,
        Err(guarantee) => return builderr(guarantee),
    };

    //    maybe print the token stream
    if debug_opts.contains_print(CompResults::Ast) {
        eprintln!("/* ast */");
        ast.dump(&());
        eprintln!();
    }

    sess.elapsed_parser();

    //    maybe halt the compilation here
    if debug_opts.contains_halt(CompStage::Parser) {
        return check_dcx();
    }

    // 5. HIR, AST => HIR
    let mut lowerctx = LoweringCtx::new(sess.clone());

    let mut hir = match lowerctx.produce(ast).dere() {
        Ok(hir) => hir,
        Err(guarantee) => return builderr(guarantee),
    };

    let mut resolver = Resolver::new(&mut hir, sess.dcx.clone());

    match resolver.resolve().dere() {
        Ok(()) => {}
        Err(guarantee) => return builderr(guarantee),
    }

    if debug_opts.contains_print(CompResults::Hir) {
        eprintln!("/* hir */");
        hir.dump(&muonc_hir::pretty::PkgDumper);
        eprintln!();
    }

    sess.elapsed_hir();

    //    maybe halt the compilation here
    if debug_opts.contains_halt(CompStage::Hir) {
        return check_dcx();
    }

    check_dcx()
}
