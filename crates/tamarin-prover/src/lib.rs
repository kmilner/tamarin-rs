//! Top-level library for the `tamarin-prover` binary (Rust port).
//!
//! The binary at `src/main.rs` is intentionally thin — it parses argv,
//! dispatches to [`run::run`], and translates errors / exit codes.
//! Everything testable lives here so the CLI surface can be exercised
//! from integration tests without spawning a subprocess.

pub mod cli;
pub mod run;

pub use cli::{parse_args, Args, CliError, Subcommand};
pub use run::{run, FileResult, LemmaResult, LemmaVerdict, RunError};
