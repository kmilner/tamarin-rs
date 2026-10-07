//! Ensure upstream sources exist before compiling tests that embed Haskell files.
#![allow(clippy::disallowed_macros)] // Cargo build directives.

fn main() {
    println!(
        "cargo:rerun-if-changed={}/lib/term/src/Term/Term/Raw.hs",
        tamarin_build::UPSTREAM_DIR
    );
}
