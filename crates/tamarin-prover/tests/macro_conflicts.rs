// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, jdreier, charlie-j, ValentinYuri, racoucho1u,
//   and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Macro.hs, src/Main/Mode/Batch.hs

//! End-to-end stderr / exit-code parity for `macro`'s rejections.
//!
//! HS `macro` `fail`s on a name the signature already carries
//! (Theory/Text/Parser/Macro.hs:43-44); batch mode's `handleError` `die`s on
//! the resulting `ParserError` (Main/Mode/Batch.hs:234) — parsec frame on
//! stderr, exit 1, no stdout.  The pinned oracle (Git revision ef3f0468)
//! exits 1 on the conflicting theory below with stderr body
//! `"…" (line 4, column 1):\nunexpected "e"\nexpecting "."\nConflicting name
//! for macro f`, and loads the non-conflicting control with exit 0; the
//! stderr bytes themselves are pinned in
//! `crates/tamarin-parser/tests/macro_conflicts.rs` (`run` prints exactly
//! `ParseError::with_source(<in_file>)`).
//!
//! The two GHC `error`s of Macro.hs:34-38 never become a `ParserError`: the
//! exception escapes to GHC's runtime, which prints `tamarin-prover: ` plus
//! the message and the `HasCallStack` frame and exits 1.  Those go through the
//! binary, since only a spawned process shows the stderr bytes.
//!
//! The oracle emits the `maude tool:` banner and, once a theory parses, the
//! `[Theory X] …` markers on stderr even under `--quiet` (the flag is
//! registered but never read — TheoryLoader.hs:159-163, 414-416).  The
//! expectations below are its `--quiet` stderr minus the three banner lines,
//! whose maude path and version are machine-local.

use std::process::Command;

use tamarin_prover::{parse_args, run};

fn maude_available() -> bool {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return std::path::Path::new(&p).exists();
    }
    for c in ["/usr/local/bin/maude", "/usr/bin/maude"] {
        if std::path::Path::new(c).exists() {
            return true;
        }
    }
    false
}

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

fn run_theory(name: &str, src: &str) -> i32 {
    let dir = std::env::temp_dir().join("tamarin_prover_macro_conflicts");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(name);
    std::fs::write(&path, src).expect("write theory");
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend(["--quiet", path.to_str().unwrap()]);
    let args = parse_args(&argv.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("args");
    run(&args).expect("run")
}

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it (Console.hs:150-155).  The path comes from `--with-maude` and the
/// version from the local maude, so only their presence is portable.
fn strip_maude_banner(stderr: &str) -> String {
    let rest = stderr
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("maude tool: '") || l.starts_with(" checking "))
        .collect::<String>();
    assert_ne!(
        rest, stderr,
        "expected a `maude tool:` banner on stderr; got:\n{stderr}"
    );
    rest
}

/// Run the built binary on `src` and return `(exit code, stderr minus the
/// maude banner)`.
///
/// `--quiet` suppresses nothing HS emits, so the remaining stderr is the
/// oracle's: the `[Theory …]` markers for a theory that loads, or the failure
/// text for one that does not.
fn run_binary(name: &str, src: &str) -> (i32, String) {
    let dir = std::env::temp_dir().join("tamarin_prover_macro_conflicts");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(name);
    std::fs::write(&path, src).expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd
        .arg("--quiet")
        .arg(&path)
        .output()
        .expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        strip_maude_banner(&String::from_utf8(out.stderr).expect("utf-8 stderr")),
    )
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

/// A macro named after one of the nine `reservedBuiltins` (Term.hs:74-86)
/// aborts with the GHC `error` of Macro.hs:34-35 — no parsec frame, no
/// `SourcePos` header, exit 1.
#[test]
fn reserved_macro_name_prints_ghc_error_and_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "reserved.spthy",
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
/// Macro.hs:37-38; differing sorts keep them apart and the theory loads.
#[test]
fn duplicate_macro_arguments_print_ghc_error_and_exit_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let (code, stderr) = run_binary(
        "dup_args.spthy",
        "theory MacroDA begin\nmacros: m(x, x) = x\nend\n",
    );
    assert_eq!(code, 1);
    assert_eq!(
        stderr,
        ghc_stderr("\"m\" have two arguments with the same name.", "38:15")
    );

    let (code, stderr) = run_binary(
        "dup_args_ok.spthy",
        "theory MacroDA begin\nmacros: m(x, x:pub) = x\nend\n",
    );
    assert_eq!(code, 0, "stderr: {stderr}");
    assert_eq!(stderr, theory_markers("MacroDA"));
}

/// A macro named after a user function aborts the load with exit 1 (HS
/// `die`, Batch.hs:234), while the same theory under a fresh macro name
/// loads with exit 0.
#[test]
fn conflicting_macro_name_exits_1() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    assert_eq!(
        run_theory(
            "conflict.spthy",
            "theory MacroCF begin\nfunctions: f/1\nmacros: f(x) = x\nend\n"
        ),
        1
    );
    assert_eq!(
        run_theory(
            "control.spthy",
            "theory MacroCF begin\nfunctions: f/1\nmacros: m(x) = x\nend\n"
        ),
        0
    );
}
