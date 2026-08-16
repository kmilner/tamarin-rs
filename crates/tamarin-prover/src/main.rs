// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

/// Does this panic payload come from a `print!`/`println!` whose write to a
/// closed stdout failed?
///
/// `std::io::stdio` panics with exactly this message rather than returning the
/// error, so a reader that leaves early (`tamarin-prover --parse-only x.spthy
/// | head -0`) would turn a normal run into a Rust panic report and rc 101.
/// GHC treats the same `EPIPE` as a non-event: `flushStdHandles` swallows it
/// and `runMainIO` still exits 0 with an empty stderr.  (`--help`/`--version`
/// never reach this: clap prints them itself and swallows write errors.)
fn is_stdout_broken_pipe(payload: &(dyn std::any::Any + Send)) -> bool {
    let msg = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied());
    msg.is_some_and(|m| m.starts_with("failed printing to stdout") && m.contains("Broken pipe"))
}

/// Stand in for GHC's top-level exception handler, which prints an uncaught
/// `ErrorCall` as `tamarin-prover: ` ++ `displayException` (the message plus
/// its `HasCallStack` frame) on stderr and exits 1.
///
/// A few HS `error`s live below the port's error-returning layers, in code
/// whose callers cannot carry a `Result` (`Term.fAppAC`, Raw.hs:120).  Those
/// sites panic with a payload [`tamarin_term::term::hs_error_text`] recognises;
/// a closed stdout is recognised by [`is_stdout_broken_pipe`]; everything else
/// keeps Rust's own panic report.
fn install_hs_error_panic_hook() {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if is_stdout_broken_pipe(info.payload()) {
            // GHC's shape: nothing on either stream, exit 0.
            std::process::exit(0);
        }
        match tamarin_term::term::hs_error_text(info.payload()) {
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
        }
    }));
}

fn main() -> ExitCode {
    install_hs_error_panic_hook();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    // clap renders its own usage errors (stderr, exit 2) and handles
    // `--help`/`--version` (stdout, exit 0) inside `exit()`.
    let args = tamarin_prover::parse_args(&raw).unwrap_or_else(|e| e.exit());
    match tamarin_prover::run(&args) {
        Ok(0) => ExitCode::SUCCESS,
        Ok(n) => ExitCode::from(n.try_into().unwrap_or(1)),
        Err(e) => {
            // rc=1 for runtime errors (matching the oracle, whose run
            // failures also exit 1 — this is output the run-parity
            // differentials do compare).
            eprintln!("error: {}", e);
            ExitCode::from(1)
        }
    }
}
