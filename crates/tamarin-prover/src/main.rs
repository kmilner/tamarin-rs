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

use std::process::ExitCode;

fn main() -> ExitCode {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = match tamarin_prover::parse_args(&raw) {
        Ok(a) => a,
        Err(e) => {
            // HS-faithful: rc=1 for usage errors (CmdArgs's default).
            eprintln!("error: {}\n", e);
            eprintln!("{}", tamarin_prover::cli::help_text());
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
