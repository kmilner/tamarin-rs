// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, jdreier, charlie-j, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Term.hs, src/Main/Mode/Batch.hs

//! End-to-end stderr / exit-code behavior for `naryOpApp`'s reserved-builtin
//! rejection inside `equations:` (Theory/Text/Parser/Term.hs:90-92).
//!
//! HS raises this as a GHC `error` (not a parsec failure).  The port raises
//! it as `ParseError::Abort` — a non-backtrackable parse failure — which the
//! binary renders as a codespan diagnostic on stderr and exits 1 with no
//! stdout.  The HS message text survives as the diagnostic's label/note; the
//! `CallStack (from HasCallStack)` frame does not.

use std::process::Command;

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

/// Run the built binary on `src`; return `(exit code, stderr, stdout len)`.
fn run_binary(name: &str, src: &str) -> (i32, String, usize) {
    let dir = std::env::temp_dir().join("tamarin_prover_eqn_reserved");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join(name);
    std::fs::write(&path, src).expect("write theory");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    if let Some(a) = maude_arg() {
        cmd.arg(a);
    }
    let out = cmd.arg(&path).output().expect("spawn tamarin-rs");
    (
        out.status.code().expect("exit code"),
        String::from_utf8(out.stderr).expect("utf-8 stderr"),
        out.stdout.len(),
    )
}

/// Assert the death shape shared by both probes: exit 1, empty stdout, the
/// HS rejection message in the diagnostic, no GHC `CallStack` frame.
fn assert_reserved_death(code: i32, stderr: &str, stdout_len: usize, name: &str) {
    assert_eq!(code, 1);
    assert_eq!(stdout_len, 0, "no stdout on an aborting parse error");
    assert!(
        stderr.contains(&format!(
            "`\"{name}\"` is a reserved function name for builtins."
        )),
        "expected the reserved-builtin message in the diagnostic:\n{stderr}"
    );
    assert!(
        !stderr.contains("CallStack"),
        "the GHC CallStack frame must not be rendered:\n{stderr}"
    );
}

/// `exp` applied inside an equation (probe p22).
#[test]
fn applied_reserved_name_in_equations_dies_with_diagnostic() {
    let (code, stderr, stdout_len) = run_binary(
        "p22_eqn_reserved.spthy",
        "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n",
    );
    assert_reserved_death(code, &stderr, stdout_len, "exp");
}

/// A BARE reserved name in an equation operand aborts too — `naryOpApp`'s
/// check runs on the identifier before anything else (probe p47).
#[test]
fn bare_reserved_name_in_equations_dies_with_diagnostic() {
    let (code, stderr, stdout_len) = run_binary(
        "p47_eqn_bare_reserved.spthy",
        "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n",
    );
    assert_reserved_death(code, &stderr, stdout_len, "mun");
}
