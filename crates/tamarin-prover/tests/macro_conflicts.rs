// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code behavior for `macro`'s rejections.
//!
//! HS `macro` `fail`s on a name the signature already carries
//! (Theory/Text/Parser/Macro.hs:43-44).  The port raises
//! `ParseError::ConflictingDeclarations` (macro context), rendered as a
//! codespan diagnostic on stderr — exit 1, no stdout.
//!
//! The two GHC `error`s of Theory/Text/Parser/Macro.hs:34-38 are
//! non-backtrackable rejections in HS; the port raises the reserved-name one
//! as `ParseError::UsedReservedBuiltin` and the duplicate-argument one as
//! `ParseError::DuplicateMacroArg`, both rendered as codespan diagnostics
//! instead of the `tamarin-prover: ` prefix and `HasCallStack` frame.  Those
//! go through the binary, since only a spawned process shows the stderr
//! bytes.
//!
//! The oracle emits the `maude tool:` banner and, once a theory parses, the
//! `[Theory X] …` markers on stderr even under `--quiet` (the flag is
//! registered but never read — TheoryLoader.hs:159-163, 414-416).  The marker
//! expectation below is its `--quiet` stderr minus the three banner lines,
//! whose maude path and version are machine-local.

mod common;

use common::{maude_arg, maude_available, strip_maude_banner};
use tamarin_prover::{parse_args, run};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_macro_conflicts";

/// Load `src` IN-PROCESS through `parse_args` + `run`, returning the exit
/// code.  Used where only the code matters — the rejection itself is pinned
/// in `crates/tamarin-parser/tests/macro_conflicts.rs`.
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
/// `[Theory …]` markers for a theory that loads, or the diagnostic for one
/// that does not.
fn run_binary(stem: &str, src: &str) -> (i32, String) {
    let (code, _, stderr) = common::run_raw(TMP_DIR, stem, src, &["--quiet"]);
    (code, strip_maude_banner(&stderr))
}

/// Assert the death shape of a fatal parse rejection: every `label` appears
/// in the diagnostic, the GHC `CallStack` frame does not.
fn assert_fatal_diagnostic(stderr: &str, labels: &[&str]) {
    for label in labels {
        assert!(
            stderr.contains(label),
            "expected `{label}` in the diagnostic:\n{stderr}"
        );
    }
    assert!(
        !stderr.contains("CallStack"),
        "the GHC CallStack frame must not be rendered:\n{stderr}"
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

/// A macro named after one of the nine `reservedBuiltins` (Theory/Text/Parser/Term.hs:74-86)
/// aborts with the rejection of Theory/Text/Parser/Macro.hs:34-35, exit 1.
#[test]
fn reserved_macro_name_prints_diagnostic_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "reserved",
        "theory MacroRB begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_fatal_diagnostic(
        &stderr,
        &["reserved builtin function `exp` was used in a macro"],
    );
}

/// Two arguments that are the same full `LVar` abort with the rejection of
/// Theory/Text/Parser/Macro.hs:37-38; differing sorts keep them apart and the theory loads.
#[test]
fn duplicate_macro_arguments_print_diagnostic_and_exit_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "dup_args",
        "theory MacroDA begin\nmacros: m(x, x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_fatal_diagnostic(
        &stderr,
        &[
            "duplicate macro argument `x`",
            "first occurrence of argument `x`",
        ],
    );

    let (code, stderr) = run_binary(
        "dup_args_ok",
        "theory MacroDA begin\nmacros: m(x, x:pub) = x\nend\n",
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, theory_markers("MacroDA"));
}

/// A macro named after a user function aborts the load with exit 1 (HS
/// `die`, Batch.hs:235), while the same theory under a fresh macro name
/// loads with exit 0.  The diagnostic labels both declarations.
#[test]
fn conflicting_macro_name_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "conflict",
        "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_fatal_diagnostic(
        &stderr,
        &[
            "conflicting macro declaration for `f`",
            "first declaration of `f`",
        ],
    );
    assert_eq!(
        run_theory(
            "control",
            "theory MacroCF begin\nfunctions: f/1\nmacros: m(x) = x\nend\n"
        ),
        0
    );
}

/// A macro named after a symbol a `builtins:` entry merged aborts the same
/// way, and the "first declaration" label sits on that entry's name — the
/// diagnostic quotes the `builtins:` line, not the `macros:` line alone.  HS
/// prints only `Conflicting name for macro h` (Theory/Text/Parser/Macro.hs:44)
/// with no first site; the label is the port's own.
#[test]
fn a_builtin_symbol_conflict_labels_the_builtins_entry() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "builtin_symbol",
        "theory MacroCH begin\nbuiltins: hashing\nmacros: h(x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_fatal_diagnostic(
        &stderr,
        &[
            "conflicting macro declaration for `h`",
            "first declaration of `h`",
            "builtins: hashing",
        ],
    );
    // The label is on line 2, where the entry is; the rejection on line 3.
    let label_line = stderr
        .lines()
        .position(|l| l.contains("first declaration of `h`"))
        .expect("the first-declaration label is rendered");
    let builtins_line = stderr
        .lines()
        .position(|l| l.contains("builtins: hashing"))
        .expect("the builtins entry is quoted");
    assert_eq!(
        label_line,
        builtins_line + 1,
        "the label must sit under the `builtins:` line:\n{stderr}"
    );
}
