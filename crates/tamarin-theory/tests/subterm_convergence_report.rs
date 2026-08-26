// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins HS `checkEquationsSubtermConvergence` (Wellformedness.hs:1222-1232)
//! and its `isUserMarkedConvergent` guard (Wellformedness.hs:1211-1214, read
//! at :1285).
//!
//! The check reads `thyEquations = S.toList (stRules sig)`, so it runs off the
//! elaborated signature.  The parser sets `eqConvergent = convergent` on EVERY
//! `equations` block (Theory/Text/Parser/Signature.hs:232-243, see line 242),
//! which is last-write-wins: a `[convergent]` block LAST suppresses the whole
//! report, a regular block last does not.
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_theory::wellformedness::equations::subterm_convergence_report;

/// The report the load pipelines emit last (`wellformedness::check_wellformedness`'s
/// closing member), as its single entry's message, or `None` when the check
/// stays silent.
fn message(src: &str) -> Option<String> {
    let parsed = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let mut errs = subterm_convergence_report(&elaborated.signature.maude_sig);
    assert!(errs.len() <= 1, "expected at most one entry, got {errs:?}");
    let entry = errs.pop()?;
    assert_eq!(entry.topic, "Subterm Convergence Warning");
    Some(entry.message)
}

/// A non-subterm-convergent equation renders as `sep [nest 2 lhs, "=" <-> rhs]`
/// inside `prettyWfErrorReport`'s own `nest 2` (Wellformedness.hs:118-125, see
/// line 122), so four leading spaces, and the pair-headed rhs prints in angle
/// form.  Oracle: `    ff(x, y) = <x, y>`.
#[test]
fn pair_headed_terms_render_in_angle_form() {
    let msg = message(
        "theory T begin functions: ff/2 equations: ff(x,y) = pair(x,y) \
            rule Test: [ ] --[ ]-> [] end",
    )
    .expect("the equation is not subterm convergent");
    assert!(msg.contains("\n    ff(x, y) = <x, y>\n"), "report: {msg:?}");
}

/// `equations [convergent]` as the LAST equations block suppresses the whole
/// report, even with a non-convergent regular block present.
#[test]
fn global_convergent_guard_suppresses_the_report() {
    assert_eq!(
        message(
            "theory T begin functions: f/1, g/1, a/0, b/0 \
                equations: f(x) = g(x) \
                equations [convergent]: g(y) = a end",
        ),
        None,
    );
}

/// A `[convergent]` block FIRST followed by a regular block LAST leaves the
/// flag false, so the non-convergent equation is reported.
#[test]
fn a_regular_block_last_leaves_the_report_on() {
    let msg = message(
        "theory T begin functions: f/1, g/1, a/0, b/0 \
            equations [convergent]: g(y) = a \
            equations: f(x) = g(x) end",
    )
    .expect("the trailing regular block clears the convergent flag");
    assert!(msg.contains("f(x) = g(x)"), "report: {msg:?}");
}
