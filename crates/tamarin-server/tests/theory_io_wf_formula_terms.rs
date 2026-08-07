// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `Formula terms` (`checkTerms`) coverage of SAPIC-generated restrictions on
//! the WEB load path — the twin of the batch `--prove` pin in
//! `crates/tamarin-prover/tests/sapic_wf_formula_terms.rs`.
//!
//! HS runs ONE `checkWellformedness` pass, over the `OpenTranslatedTheory`
//! (Wellformedness.hs:1270-1286, driven by `checkTranslatedTheory`,
//! TheoryLoader.hs:559-565 and fed by `closeTheory`, TheoryLoader.hs:726-728).
//! The interactive server shares that loader, so `formulaReports`' `annFormulas`
//! (Wellformedness.hs:1006-1015) sees the `Restr_<rule>_<i>` restrictions minted
//! while lowering a `let` pattern's `else` branch, exactly as the batch mode
//! does.  Those restrictions carry the branch's right-hand side verbatim, so a
//! reducible symbol there — `exp` in `<<'a'^'b','b'>,'c'>` — is an offender.
//!
//! The expected bytes are the pinned oracle's (Git revision ef3f0468) wf block
//! for `tests/fixtures/sapic_else_branch_exp.spthy`; the web report renders
//! through the same `format_wf_block` the batch output uses, and the block is
//! byte-identical at the web render width.
//!
//! Maude-backed: skipped when no Maude binary is available.

use std::path::PathBuf;

use tamarin_server::theory_io;

/// Locate the Maude binary (`MAUDE_PATH` env override, else the common
/// install paths).  `None` skips the Maude-backed test below.
fn maude_bin_path() -> Option<String> {
    std::env::var("MAUDE_PATH").ok().or_else(|| {
        for c in [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "/usr/bin/maude",
        ] {
            if std::path::Path::new(c).exists() {
                return Some(c.to_string());
            }
        }
        None
    })
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sapic_else_branch_exp.spthy")
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
fn web_load_reports_formula_terms_for_sapic_else_restriction() {
    let Some(maude) = maude_bin_path() else {
        eprintln!("no maude binary found; skipping");
        return;
    };
    // The process-wide setup `serve` applies, so the report renders at the web
    // width every HTTP response uses.
    tamarin_server::init_process_globals();
    // `derivcheck_timeout = 0` skips the dynamic derivation checks, matching
    // the `--derivcheck-timeout=0` oracle probe (HS `compare derivChecks 0`
    // returns `Just []` on EQ, TheoryLoader.hs:578-579), so the report holds
    // the static checks only.
    let entry = theory_io::load_from_path(&fixture(), &maude, 0).expect("fixture loads");

    assert!(
        entry.wf_report.iter().any(|e| e.topic == "Formula terms"),
        "the load-path report must carry the `Formula terms` entry for the \
         restriction SAPIC's `let … else` lowering generates; topics present: {:?}",
        entry
            .wf_report
            .iter()
            .map(|e| e.topic.as_str())
            .collect::<Vec<_>>(),
    );

    // Same renderer as the batch `/* WARNING … */` comment (`format_wf_block`),
    // which the source/message routes emit and `make_wf_errors_html` reuses for
    // the header banner — so the block is byte-comparable with the oracle's.
    let block = tamarin_theory::pretty_theory::format_wf_block(&entry.wf_report);
    assert_eq!(block, EXPECTED_WF_BLOCK.join("\n"));
}
