// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end stderr / exit-code behavior for `naryOpApp`'s reserved-builtin
//! rejection inside `equations:` (Theory/Text/Parser/Term.hs:90-92).
//!
//! HS raises this as a GHC `error` (not a parsec failure).  The port raises
//! it as `ParseError::UsedReservedBuiltin`, which the binary renders as a
//! codespan diagnostic naming the symbol on stderr and exits 1 with no
//! stdout.  The GHC `CallStack (from HasCallStack)` frame is not rendered.

mod common;

/// Drop the `maude tool: '<path>'` line and the ` checking …: OK.` lines that
/// follow it — their path and version are machine-local.
///
/// Unlike [`common::strip_maude_banner`] this does NOT assert the banner was
/// there: these two runs are not guarded on maude being available.  The
/// assertions below name the diagnostic's own text, so a run without maude
/// fails rather than passing vacuously.
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

/// Assert the death shape shared by both probes: exit 1, empty stdout, the
/// reserved-builtin diagnostic naming the symbol, no GHC `CallStack` frame.
fn assert_reserved_death(code: i32, stderr: &str, stdout_len: usize, name: &str) {
    assert_eq!(code, 1);
    assert_eq!(stdout_len, 0, "no stdout on an aborting parse error");
    assert!(
        stderr.contains("Reserved builtin function in equation")
            && stderr.contains(&format!(
                "reserved builtin function `{name}` was used in an equation"
            )),
        "expected the reserved-builtin diagnostic:\n{stderr}"
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
        "p22_eqn_reserved",
        "theory T\nbegin\n\nequations: exp(x, y) = x\n\nend\n",
    );
    assert_reserved_death(code, &stderr, stdout_len, "exp");
}

/// A BARE reserved name in an equation operand aborts too — `naryOpApp`'s
/// check runs on the identifier before anything else (probe p47).
#[test]
fn bare_reserved_name_in_equations_dies_with_diagnostic() {
    let (code, stderr, stdout_len) = run_binary(
        "p47_eqn_bare_reserved",
        "theory T\nbegin\n\nfunctions: f/1\n\nequations: f(x) = mun\n\nend\n",
    );
    assert_reserved_death(code, &stderr, stdout_len, "mun");
}
