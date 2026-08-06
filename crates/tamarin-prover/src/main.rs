//! Binary entry-point for the Rust `tamarin-prover` port.
//!
//! Stays small: parse argv → dispatch to [`tamarin_prover::run::run`]
//! → translate errors into a stderr message + non-zero exit code.
//!
//! Uses `mimalloc` as the global allocator, matching every other
//! tamarin entry-point in the workspace (`maude_prof`, `dump_proof`,
//! the `oracle_solver` test harness).  On wireguard.spthy's
//! `exists_session` the switch cuts ~4s off the prove loop versus
//! glibc malloc — the prover allocates millions of small Term/Subst
//! nodes during graph search and slab/region allocators are dramatically
//! cheaper for that churn pattern.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::io::Write;
use std::process::ExitCode;

use tamarin_prover::cli::{CliError, Subcommand};

/// Stand in for GHC's top-level exception handler, which prints an uncaught
/// `ErrorCall` as `tamarin-prover: ` ++ `displayException` (the message plus
/// its `HasCallStack` frame) on stderr and exits 1.
///
/// A few HS `error`s live below the port's error-returning layers, in code
/// whose callers cannot carry a `Result` (`Term.fAppAC`, Raw.hs:120).  Those
/// sites panic with a payload [`tamarin_term::term::hs_error_text`] recognises;
/// everything else keeps Rust's own panic report.
fn install_hs_error_panic_hook() {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(
        move |info| match tamarin_term::term::hs_error_text(info.payload()) {
            Some(text) => {
                let mut err = std::io::stderr().lock();
                // GHC's laziness defers these errors past progress markers
                // the eager port has not printed yet; the batch loop parks
                // the pending lines for exactly that span (see
                // `run::take_deferred_hs_error_markers`).
                if let Some(markers) = tamarin_prover::run::take_deferred_hs_error_markers() {
                    let _ = write!(err, "{markers}");
                }
                let _ = writeln!(err, "tamarin-prover: {text}");
                let _ = err.flush();
                std::process::exit(1);
            }
            None => default_hook(info),
        },
    ));
}

fn main() -> ExitCode {
    install_hs_error_panic_hook();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = match tamarin_prover::parse_args(&raw) {
        Ok(a) => a,
        Err(CliError::UnknownFlag(m)) => {
            // cmdargs rejects the command line before `defaultMain` dispatches
            // (Console.hs:362-372): the bare message goes to stderr, nothing to
            // stdout, no help block, rc 1.
            eprintln!("{m}");
            return ExitCode::from(1);
        }
        Err(e) => {
            // HS-faithful: rc=1 for usage errors (CmdArgs's default).
            eprintln!("error: {}\n", e);
            eprintln!("{}", tamarin_prover::cli::help_text(Subcommand::Batch));
            return ExitCode::from(1);
        }
    };
    match tamarin_prover::run(&args) {
        Ok(0) => ExitCode::SUCCESS,
        Ok(n) => ExitCode::from(n.try_into().unwrap_or(1)),
        Err(e) => {
            // HS-faithful: rc=1 for runtime errors.
            eprintln!("error: {}", e);
            ExitCode::from(1)
        }
    }
}
