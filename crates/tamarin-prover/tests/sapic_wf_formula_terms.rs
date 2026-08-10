// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pins HS's "Formula terms" (`checkTerms`) coverage of the restrictions
//! SAPIC's `let … else` lowering generates.
//!
//! HS runs its single `checkWellformedness` pass on the TRANSLATED theory
//! (`checkTranslatedTheory`, TheoryLoader.hs:559-565), so `formulaReports`'
//! `annFormulas` (Wellformedness.hs:1006-1015) includes the `Restr_<rule>_<i>`
//! restrictions minted while lowering a `let` pattern's `else` branch.  Those
//! carry the branch's right-hand side verbatim, so a reducible symbol there —
//! `exp` in `<<'a'^'b', 'b'>, 'c'>` — is an offender and must be reported.
//!
//! The expected bytes below are the pinned oracle's (Git revision ef3f0468)
//! output for `tests/fixtures/sapic_else_branch_exp.spthy`.

mod common;

use common::{fixture, maude_available, run_binary};

/// The oracle's wf block for the fixture, as a line list so the blank-ish
/// separator line (two spaces, HS `$--$`) survives verbatim.
const EXPECTED_WF_BLOCK: &[&str] = &[
    "/*",
    "WARNING: the following wellformedness checks failed!",
    "",
    "Formula terms",
    "=============",
    "",
    "  Restriction `Restr_letpqrabbc_2__1' uses terms of the wrong form:",
    "    `pair(pair(exp('a','b'),'b'),'c')'",
    "  ",
    "  The only allowed terms are public constants and bound node and",
    "  message variables. If you encounter free message variables, then",
    "  you might have forgotten a #-prefix. Sort prefixes can only be",
    "  dropped where this is unambiguous. Moreover, reducible function",
    "  symbols are disallowed.",
    "*/",
];

#[test]
fn sapic_else_branch_restriction_reports_formula_terms() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }

    let in_path = fixture("sapic_else_branch_exp.spthy");
    let out_dir = std::env::temp_dir().join("tamarin_prover_sapic_wf");
    std::fs::create_dir_all(&out_dir).expect("mkdir out_dir");
    let out_path = out_dir.join("sapic_else_branch_exp_out.spthy");

    // `-o`/`--output` is a cmdargs `flagOpt` whose value must be ATTACHED
    // (Batch.hs:44-84, see line 76).
    let output_arg = format!("--output={}", out_path.to_str().unwrap());
    let (code, _, stderr) = run_binary(&["--quiet", &output_arg], &[&in_path]);
    assert_eq!(
        code, 0,
        "expected exit code 0, got {code}; stderr:\n{stderr}"
    );

    let body = std::fs::read_to_string(&out_path).expect("output written");
    let expected = EXPECTED_WF_BLOCK.join("\n");
    assert!(
        body.contains(&expected),
        "wf report must carry the oracle's `Formula terms` block for the \
         generated else-branch restriction.\nexpected:\n{}\ngot:\n{}",
        expected,
        body
    );
}
