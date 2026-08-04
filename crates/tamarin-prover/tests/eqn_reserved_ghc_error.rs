// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, meiersi, jdreier, charlie-j, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Text/Parser/Term.hs, src/Main/Mode/Batch.hs

//! End-to-end stderr / exit-code parity for `naryOpApp`'s reserved-builtin
//! rejection inside `equations:` (Theory/Text/Parser/Term.hs:90-92).
//!
//! The rejection is a GHC `error`, not a parsec failure: the exception
//! escapes the parser run, GHC's top-level handler prints `tamarin-prover: `
//! plus the message and the `HasCallStack` frame, and the process exits 1
//! with no stdout.  The pinned oracle (Git revision ef3f0468) produces
//! exactly the bytes below (probes p22/p47 of the lookup-arity matrix),
//! after its machine-local `maude tool:` banner.

use std::process::Command;

/// `--with-maude=PATH` from the `MAUDE_PATH` env override, when set.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines
/// that follow it — their path and version are machine-local.
fn strip_maude_banner(stderr: &str) -> String {
    stderr
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("maude tool: '") || l.starts_with(" checking "))
        .collect::<String>()
}

/// Run the built binary on `src`; return `(exit code, stderr minus banner,
/// stdout length)`.
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
        strip_maude_banner(&String::from_utf8(out.stderr).expect("utf-8 stderr")),
        out.stdout.len(),
    )
}

/// The GHC top-level handler's stderr for the Term.hs:92:9 `error`.
fn ghc_stderr(name: &str) -> String {
    format!(
        "tamarin-prover: `\"{name}\"` is a reserved function name for builtins.\n\
         CallStack (from HasCallStack):\n  error, called at \
         src/Theory/Text/Parser/Term.hs:92:9 in \
         tamarin-prover-theory-1.13.0-8wixYaxm5uHCGl2uEzaKzP:Theory.Text.Parser.Term\n"
    )
}

/// `exp` applied inside an equation (probe p22).
#[test]
fn applied_reserved_name_in_equations_dies_with_callstack() {
    let (code, stderr, stdout_len) = run_binary(
        "p22_eqn_reserved.spthy",
        "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n",
    );
    assert_eq!(code, 1);
    assert_eq!(stderr, ghc_stderr("exp"));
    assert_eq!(stdout_len, 0, "no stdout on a GHC error");
}

/// A BARE reserved name in an equation operand aborts too — `naryOpApp`'s
/// check runs on the identifier before anything else (probe p47).
#[test]
fn bare_reserved_name_in_equations_dies_with_callstack() {
    let (code, stderr, stdout_len) = run_binary(
        "p47_eqn_bare_reserved.spthy",
        "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n",
    );
    assert_eq!(code, 1);
    assert_eq!(stderr, ghc_stderr("mun"));
    assert_eq!(stdout_len, 0, "no stdout on a GHC error");
}
