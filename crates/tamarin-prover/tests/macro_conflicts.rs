// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end diagnostics and exit codes for `macro` rejections.
//!
//! A macro whose name conflicts with the signature is a structured parser
//! error: batch mode writes the source-labelled diagnostic to stderr, exits 1,
//! and writes no stdout. The non-conflicting control loads successfully.
//!
//! Haskell implements two of these checks with escaping GHC exceptions. Rust
//! deliberately maps them to the same stable structured diagnostic surface as
//! ordinary parser failures, without compiler-specific call stacks.
//!
//! The oracle emits the `maude tool:` banner and, once a theory parses, the
//! `[Theory X] …` markers on stderr even under `--quiet` (the flag is
//! registered but never read — TheoryLoader.hs:159-163, 414-416).  The
//! expectations below are its `--quiet` stderr minus the three banner lines,
//! whose maude path and version are machine-local.

mod common;

use common::{maude_arg, maude_available, strip_maude_banner};
use tamarin_prover::{parse_args, run};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_macro_conflicts";

/// Load `src` IN-PROCESS through `parse_args` + `run`, returning the exit
/// code. Used where only the code matters.
fn run_theory(stem: &str, src: &str) -> i32 {
    let dir = std::env::temp_dir().join(TMP_DIR);
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(format!("{stem}.spthy"));
    std::fs::write(&path, src).expect("write theory");
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend(["--quiet", path.to_str().unwrap()]);
    let args = parse_args(&argv.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("args");
    run(&args).expect("run")
}

/// Run the built binary on `src` and return `(exit code, stderr minus the
/// maude banner)`.
///
/// `--quiet` suppresses nothing HS emits, so the remaining stderr is the
/// oracle's: the `[Theory …]` markers for a theory that loads, or the failure
/// text for one that does not.
fn run_binary(stem: &str, src: &str) -> (i32, String) {
    let (code, _, stderr) = common::run_raw(TMP_DIR, stem, src, &["--quiet"]);
    (code, strip_maude_banner(&stderr))
}

fn assert_diagnostic(stderr: &str, expected: &[&str]) {
    for text in expected {
        assert!(stderr.contains(text), "missing {text:?} in:\n{stderr}");
    }
    assert!(
        !stderr.contains("CallStack"),
        "unexpected GHC details:\n{stderr}"
    );
}

/// The seven `traceM` markers a theory that loads, translates and closes
/// writes to stderr: TheoryLoader.hs:451, 496, 581, 594, 696 and
/// CloseRule.hs:383, 386.  `--quiet` leaves every one of them in place.
fn theory_markers(name: &str) -> String {
    [
        "Theory loaded",
        "Theory translated",
        "No Deconstruction Chain checks started",
        "No Deconstruction Chain checks ended",
        "Derivation checks started",
        "Derivation checks ended",
        "Theory closed",
    ]
    .iter()
    .map(|m| format!("[Theory {name}] {m}\n"))
    .collect()
}

/// A macro named after one of the nine `reservedBuiltins`
/// (Theory/Text/Parser/Term.hs:74-86) produces a structured diagnostic.
#[test]
fn reserved_macro_name_prints_a_diagnostic_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "reserved",
        "theory MacroRB begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_diagnostic(
        &stderr,
        &[
            "error[parse]: Reserved builtin used in macro",
            "builtin function `exp` is reserved",
        ],
    );
}

/// Two arguments that are the same full `LVar` produce a duplicate diagnostic;
/// differing sorts keep them apart and the theory loads.
#[test]
fn duplicate_macro_arguments_print_a_diagnostic_and_exit_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "dup_args",
        "theory MacroDA begin\nmacros: m(x, x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_diagnostic(
        &stderr,
        &[
            "error[parse]: Duplicate macro argument",
            "macro argument `x` is listed more than once",
        ],
    );

    let (code, stderr) = run_binary(
        "dup_args_ok",
        "theory MacroDA begin\nmacros: m(x, x:pub) = x\nend\n",
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, theory_markers("MacroDA"));
}

/// A macro named after a user function aborts the load with exit 1, while the
/// same theory under a fresh macro name loads with exit 0.
#[test]
fn conflicting_macro_name_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    assert_eq!(
        run_theory(
            "conflict",
            "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n"
        ),
        1
    );
    assert_eq!(
        run_theory(
            "control",
            "theory MacroCF begin\nfunctions: f/1\nmacros: m(x) = x\nend\n"
        ),
        0
    );
}
