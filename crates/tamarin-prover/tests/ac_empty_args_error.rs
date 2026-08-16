// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code parity for `fAppAC`'s empty-argument-list
//! rejection (`error "Term.fAppAC: empty argument list"`, Raw.hs:120).
//!
//! Declaring an AC symbol and then applying it to no arguments — `functions:
//! f/2 [AC]` with a term `f()` — reaches that `error`.  It is a GHC `error`,
//! not a `Result`: the exception escapes every layer, GHC's top-level handler
//! prints `tamarin-prover: ` plus the message and its `HasCallStack` frame,
//! and the process exits 1 with no stdout.  The port raises it as a marked
//! panic that the binary's hook renders the same way (a Rust panic would
//! print a `thread 'main' panicked at …` report and exit 101).
//!
//! The oracle is lazy and does not force the term until the close pipeline,
//! so its stderr carries three more `[Theory …]` progress lines (`Theory
//! translated`, `No Deconstruction Chain checks started`, `… ended` — only
//! the first under `--no-ndc`) before the error.  The port builds terms
//! eagerly during elaboration; the batch loop parks those pending marker
//! lines for the panic hook to replay (`run::take_deferred_hs_error_markers`),
//! so the whole death sequence is byte-identical, as is the exit code.

mod common;

use common::maude_available;

/// A theory whose only rule applies a binary AC symbol to nothing.
const AC_EMPTY_THEORY: &str = "theory ACEmpty begin\n\n\
     functions: f/2 [AC]\n\n\
     rule R:\n  [ ] --[ ]-> [ Out(f()) ]\n\n\
     end\n";

/// The GHC top-level handler's stderr for the Raw.hs:120:20 `error`, verbatim
/// from the pinned oracle.  The package id is build-specific and is refreshed
/// at a submodule bump together with `tamarin-term`'s copy of it.
const ORACLE_TAIL: &str = "tamarin-prover: Term.fAppAC: empty argument list\n\
     CallStack (from HasCallStack):\n  error, called at src/Term/Term/Raw.hs:120:20 in \
     tamarin-prover-term-1.13.0-HEWlVEyEBKAFHPl3i5M61g:Term.Term.Raw\n";

/// Run the binary on the theory with `extra` flags and return its stderr,
/// after the shared rc-1 / empty-stdout / no-Rust-panic assertions.
fn death_stderr(extra: &[&str]) -> String {
    let (code, stdout, stderr) = common::run_raw(
        "tamarin_prover_ac_empty",
        "ac_empty",
        AC_EMPTY_THEORY,
        extra,
    );

    // rc 1 (GHC's uncaught-exception code), not 101 (Rust's panic code).
    assert_eq!(code, 1, "exit code");
    assert!(
        stdout.is_empty(),
        "the oracle writes nothing to stdout; got {stdout:?}"
    );
    assert!(
        !stderr.contains("panicked at"),
        "the panic must be rendered GHC-style, not by Rust's hook; got:\n{stderr}"
    );
    stderr
}

#[test]
fn empty_ac_application_dies_with_the_hs_error_bytes_and_rc_1() {
    if !maude_available() {
        eprintln!("skipping: no maude binary found");
        return;
    }
    let stderr = death_stderr(&[]);
    // GHC forces the term only after translation and the NDC stage; the
    // deferred-marker replay must reproduce that exact sequence.
    let tail = format!(
        "[Theory ACEmpty] Theory loaded\n\
         [Theory ACEmpty] Theory translated\n\
         [Theory ACEmpty] No Deconstruction Chain checks started\n\
         [Theory ACEmpty] No Deconstruction Chain checks ended\n\
         {ORACLE_TAIL}"
    );
    assert!(
        stderr.ends_with(&tail),
        "stderr must end with the oracle's marker + error sequence; got:\n{stderr}"
    );
}

#[test]
fn no_ndc_suppresses_the_deconstruction_chain_markers_before_the_death() {
    if !maude_available() {
        eprintln!("skipping: no maude binary found");
        return;
    }
    let stderr = death_stderr(&["--no-ndc"]);
    let tail = format!(
        "[Theory ACEmpty] Theory loaded\n\
         [Theory ACEmpty] Theory translated\n\
         {ORACLE_TAIL}"
    );
    assert!(
        stderr.ends_with(&tail),
        "stderr must end with the oracle's marker + error sequence; got:\n{stderr}"
    );
    assert!(
        !stderr.contains("Deconstruction"),
        "--no-ndc must suppress the NDC markers, matching the oracle; got:\n{stderr}"
    );
}
