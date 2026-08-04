// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, beschmi, jdreier, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term/Raw.hs, src/Main/Mode/Batch.hs

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
//! Known residual: the oracle is lazy and does not force the term until after
//! the theory is translated, so its stderr carries three more `[Theory …]`
//! progress lines (`Theory translated`, `No Deconstruction Chain checks
//! started`, `… ended`) before the error.  The port builds terms eagerly
//! during elaboration and dies right after `Theory loaded`.  Everything from
//! the error line on is byte-identical, as is the exit code.

use std::process::Command;

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

fn maude_available() -> bool {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return std::path::Path::new(&p).exists();
    }
    ["/usr/local/bin/maude", "/usr/bin/maude"]
        .iter()
        .any(|c| std::path::Path::new(c).exists())
}

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

#[test]
fn empty_ac_application_dies_with_the_hs_error_bytes_and_rc_1() {
    if !maude_available() {
        eprintln!("skipping: no maude binary found");
        return;
    }
    let dir = std::env::temp_dir().join("tamarin_prover_ac_empty");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("ac_empty.spthy");
    std::fs::write(&path, AC_EMPTY_THEORY).expect("write theory");

    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd.arg(&path).output().expect("spawn tamarin-rs");

    // rc 1 (GHC's uncaught-exception code), not 101 (Rust's panic code).
    assert_eq!(out.status.code(), Some(1), "exit code");
    assert!(
        out.stdout.is_empty(),
        "the oracle writes nothing to stdout; got {:?}",
        String::from_utf8_lossy(&out.stdout)
    );
    let stderr = String::from_utf8(out.stderr).expect("utf-8 stderr");
    assert!(
        stderr.ends_with(ORACLE_TAIL),
        "stderr must end with the oracle's error block; got:\n{stderr}"
    );
    // No Rust panic report anywhere.
    assert!(
        !stderr.contains("panicked at"),
        "the panic must be rendered GHC-style, not by Rust's hook; got:\n{stderr}"
    );
    // The progress marker the port does reach still precedes it.
    assert!(
        stderr.contains("[Theory ACEmpty] Theory loaded\n"),
        "got:\n{stderr}"
    );
}
