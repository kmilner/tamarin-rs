// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code parity for `macro`'s rejections.
//!
//! HS `macro` `fail`s on a name the signature already carries
//! (Theory/Text/Parser/Macro.hs:43-44); batch mode's `handleError` `die`s on
//! the resulting `ParserError` (Main/Mode/Batch.hs:235) — parsec frame on
//! stderr, exit 1, no stdout.  The pinned oracle (Git revision ef3f0468)
//! exits 1 on the conflicting theory below with stderr body
//! `"…" (line 4, column 1):\nunexpected "e"\nexpecting "."\nConflicting name
//! for macro f`, and loads the non-conflicting control with exit 0; the
//! stderr bytes themselves are pinned in
//! `crates/tamarin-parser/tests/macro_conflicts.rs` (`run` prints exactly
//! `ParseError::with_source(<in_file>)`).
//!
//! The two GHC `error`s of Theory/Text/Parser/Macro.hs:34-38 never become a `ParserError`: the
//! exception escapes to GHC's runtime, which prints `tamarin-prover: ` plus
//! the message and the `HasCallStack` frame and exits 1.  Those go through the
//! binary, since only a spawned process shows the stderr bytes.
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
/// code.  Used where only the code matters — the stderr bytes of the parsec
/// `die` are pinned in `crates/tamarin-parser/tests/macro_conflicts.rs`.
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

/// The stderr GHC's top-level handler writes for a `macro` `error` raised at
/// `Macro.hs:<site>` — the pinned oracle prints exactly these three lines
/// after its maude banner.
fn ghc_stderr(message: &str, site: &str) -> String {
    format!(
        "tamarin-prover: {message}\nCallStack (from HasCallStack):\n  error, called at \
         src/Theory/Text/Parser/Macro.hs:{site} in \
         tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP:Theory.Text.Parser.Macro\n"
    )
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
/// aborts with the GHC `error` of Theory/Text/Parser/Macro.hs:34-35 — no parsec frame, no
/// `SourcePos` header, exit 1.
#[test]
fn reserved_macro_name_prints_ghc_error_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "reserved",
        "theory MacroRB begin\nbuiltins: diffie-hellman\nmacros: exp(x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_eq!(
        stderr,
        ghc_stderr(
            "`\"exp\"` is a reserved function name for builtins.",
            "35:15"
        )
    );
}

/// Two arguments that are the same full `LVar` abort with the GHC `error` of
/// Theory/Text/Parser/Macro.hs:37-38; differing sorts keep them apart and the theory loads.
#[test]
fn duplicate_macro_arguments_print_ghc_error_and_exit_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "dup_args",
        "theory MacroDA begin\nmacros: m(x, x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_eq!(
        stderr,
        ghc_stderr("\"m\" have two arguments with the same name.", "38:15")
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
/// loads with exit 0.
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
