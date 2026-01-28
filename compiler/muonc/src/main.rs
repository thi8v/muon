use std::{io::Write, process::ExitCode};

use muonc::CliError;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

fn main() -> ExitCode {
    match muonc::run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(CliError::BuildFailed { guarantee, failed }) => {
            // get rid of the guarantee
            _ = guarantee;

            if failed {
                muonc::exit_code_build_fail()
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            let mut out = StandardStream::stderr(ColorChoice::Auto);

            out.set_color(ColorSpec::new().set_bold(true)).unwrap();
            write!(out, "muonc: ").unwrap();
            out.reset().unwrap();

            if let CliError::ClapError(err) = e {
                err.print().unwrap();
            } else {
                out.set_color(
                    ColorSpec::new()
                        .set_fg(Some(Color::Red))
                        .set_bold(true)
                        .set_intense(true),
                )
                .unwrap();
                write!(out, "error: ").unwrap();
                out.reset().unwrap();
                writeln!(out, "{e}").unwrap();
            }

            ExitCode::FAILURE
        }
    }
}
