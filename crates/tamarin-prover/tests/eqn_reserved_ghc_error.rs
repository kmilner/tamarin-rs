// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end diagnostics for `naryOpApp`'s reserved-builtin
//! rejection inside `equations:` (Theory/Text/Parser/Term.hs:90-92).
//!
//! Haskell raises a GHC exception here. The port converts it into the same
//! semantic parser-error surface used for ordinary failures, without exposing
//! a compiler-version-specific call stack.

mod common;

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it — their path and version are machine-local.
///
/// Unlike [`common::strip_maude_banner`] this does NOT assert the banner was
/// there: these two runs are not guarded on maude being available, and the
/// stderr below is asserted in FULL, so a bannerless run still compares the
/// whole stream rather than passing vacuously.
fn strip_maude_banner(stderr: &str) -> String {
    stderr
        .split_inclusive('\n')
        .skip_while(|l| l.starts_with("maude tool: '") || l.starts_with(" checking "))
        .collect::<String>()
}

/// Run the built binary on `src`; return `(exit code, stderr minus banner,
/// stdout length)`.
fn run_binary(stem: &str, src: &str) -> (i32, String, usize) {
    let (code, stdout, stderr) = common::run_raw("tamarin_prover_eqn_reserved", stem, src, &[]);
    (code, strip_maude_banner(&stderr), stdout.len())
}

fn assert_reserved_diagnostic(code: i32, stderr: &str, stdout_len: usize, name: &str) {
    assert_eq!(code, 1);
    assert_eq!(stdout_len, 0, "no stdout on a parser error");
    assert!(
        stderr.contains("error: Reserved builtin used in term")
            && stderr.contains(&format!("builtin function `{name}` is reserved")),
        "unexpected stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("CallStack"),
        "unexpected GHC details:\n{stderr}"
    );
}

/// `exp` applied inside an equation (probe p22).
#[test]
fn applied_reserved_name_in_equations_has_a_diagnostic() {
    let (code, stderr, stdout_len) = run_binary(
        "p22_eqn_reserved",
        "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n",
    );
    assert_reserved_diagnostic(code, &stderr, stdout_len, "exp");
}

/// A BARE reserved name in an equation operand aborts too — `naryOpApp`'s
/// check runs on the identifier before anything else (probe p47).
#[test]
fn bare_reserved_name_in_equations_has_a_diagnostic() {
    let (code, stderr, stdout_len) = run_binary(
        "p47_eqn_bare_reserved",
        "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n",
    );
    assert_reserved_diagnostic(code, &stderr, stdout_len, "mun");
}
