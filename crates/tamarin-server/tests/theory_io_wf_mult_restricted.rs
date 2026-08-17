// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `Multiplication restriction of rules` (`multRestrictedReport`) on the WEB
//! load path, and the raw `<`/`>` its rule dump puts through
//! `makeWfErrorsHtml`'s banner.
//!
//! HS runs ONE `checkWellformedness` pass, over the `OpenTranslatedTheory`
//! (Wellformedness.hs:1270-1286), which the interactive server shares with the
//! batch mode — so the check has to be spliced on both load paths, not only in
//! `run.rs`.
//!
//! `makeWfErrorsHtml` (src/Web/Handler.hs:469-475) feeds the report through
//! `renderHtmlDoc (htmlDoc …)`, and `htmlDoc = HtmlDoc` (Html.hs:96-97) only
//! WRAPS the already-built plain `Doc`: the escaping `Document (HtmlDoc d)`
//! instance (Html.hs:102-105) never runs, so `postprocessHtmlDoc`
//! (Html.hs:157-162) is the whole transformation and a pair term's angle
//! brackets reach the browser unescaped.
//!
//! The expected bytes are the pinned oracle's (Git revision ef3f0468) wf block
//! for `tests/fixtures/mult_restricted_pair.spthy`.

use std::path::PathBuf;

use tamarin_server::theory_io;

/// A path that cannot start a Maude process.  The report below comes from
/// the static wellformedness pass.  The load runs that pass before it needs
/// a Maude handle.  The load therefore skips the best-effort Maude block,
/// and this test needs no external program.  A run of this comparison under
/// a real Maude gives the same bytes.  The test skips nothing when the
/// binary is absent.  A skipped test would pass without comparing anything.
const NO_MAUDE: &str = "/nonexistent/maude-for-test";

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("mult_restricted_pair.spthy")
}

/// The oracle's wf block for the fixture, as a line list so the two-space
/// separator lines (`nest 2` over HS's `text ""`) survive verbatim.
const EXPECTED_WF_BLOCK: &[&str] = &[
    "/*",
    "WARNING: the following wellformedness checks failed!",
    "",
    "Multiplication restriction of rules",
    "===================================",
    "",
    "  The following rule is not multiplication restricted:",
    "    rule (modulo E) R2:",
    "       [ In( fst(x) ), Fr( ~a ), Fr( ~b ) ]",
    "      --[ Go( x ) ]->",
    "       [ Out( <x, (~a*~b)> ) ]",
    "  ",
    "  After replacing reducible function symbols in lhs with variables:",
    "    rule (modulo E) R2:",
    "       [ In( x.1 ), Fr( ~a ), Fr( ~b ) ]",
    "      --[ Go( x ) ]->",
    "       [ Out( <x, (~a*~b)> ) ]",
    "  ",
    "    Terms with multiplication:  (~a*~b)",
    "    Variables that occur only in rhs:  x",
    "*/",
];

#[test]
fn web_load_reports_multiplication_restriction_unescaped_in_the_banner() {
    // The process-wide setup `serve` applies, so every renderer runs at the
    // web width the HTTP responses use.
    tamarin_server::init_process_globals();
    // `derivcheck_timeout = 0` skips the dynamic derivation checks, matching
    // the `--derivcheck-timeout=0` oracle probe.
    let entry = theory_io::load_from_path(&fixture(), NO_MAUDE, 0).expect("fixture loads");

    assert!(
        entry
            .wf_report
            .iter()
            .any(|e| e.topic == "Multiplication restriction of rules"),
        "the web load-path report must carry the multiplication-restriction \
         entry; topics present: {:?}",
        entry
            .wf_report
            .iter()
            .map(|e| e.topic.as_str())
            .collect::<Vec<_>>(),
    );

    let block = tamarin_theory::pretty_theory::format_wf_block(&entry.wf_report);
    assert_eq!(block, EXPECTED_WF_BLOCK.join("\n"));

    // `makeWfErrorsHtml`'s banner keeps the body's characters as they are —
    // only leading spaces (`&nbsp;`) and line breaks (`<br/>`) are rewritten.
    let banner = &entry.errors_html;
    assert!(
        banner.contains("[ Out( <x, (~a*~b)> ) ]"),
        "banner must carry the pair term's angle brackets raw: {banner}"
    );
    assert!(
        !banner.contains("&lt;") && !banner.contains("&gt;"),
        "banner must not entity-escape the report body: {banner}"
    );
}
