//! Ensure upstream sources exist before compiling tests that embed Haskell files.
#![allow(clippy::disallowed_macros)] // Cargo build directives.

fn main() {
    println!(
        "cargo:rerun-if-changed={}/lib/term/src/Term/Term/Raw.hs",
        tamarin_build::UPSTREAM_DIR
    );
    if std::env::var_os("CARGO_FEATURE_LEAN_UNIFICATION").is_some() {
        // Read the fixtures and generate coverage queries from exactly the
        // solver revision Cargo linked. Lake's output lives in its OUT_DIR.
        let lean = std::env::var("DEP_TAMARIN_ALGEBRA_LEAN_DIR")
            .expect("tamarin-algebra-sys must expose its Lake directory");
        println!("cargo:rustc-env=TAMARIN_ALGEBRA_LEAN_DIR={lean}");
    }
}
