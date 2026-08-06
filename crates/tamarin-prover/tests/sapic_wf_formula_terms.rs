// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Tools/Wellformedness.hs,
//   src/Main/Mode/Batch.hs, src/Main/TheoryLoader.hs

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

use std::path::PathBuf;

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
/// Without the flag the prover probes bare `maude` on PATH (HS-faithful),
/// which is absent on CI runners.
fn maude_arg() -> Option<String> {
    std::env::var("MAUDE_PATH")
        .ok()
        .map(|p| format!("--with-maude={p}"))
}

fn fixture(name: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("tests");
    p.push("fixtures");
    p.push(name);
    p
}

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
    let maude = maude_arg();
    let mut argv: Vec<&str> = maude.as_deref().into_iter().collect();
    argv.extend(["--quiet", &output_arg, in_path.to_str().unwrap()]);
    let args = parse_args(&argv.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse");
    let code = run(&args).expect("run");
    assert_eq!(code, 0, "expected exit code 0, got {}", code);

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
