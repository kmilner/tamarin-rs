// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Tools/Wellformedness.hs,
//   lib/utils/src/Text/PrettyPrint/Html.hs, src/Web/Handler.hs

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
    let Some(maude) = maude_bin_path() else {
        eprintln!("no maude binary found; skipping");
        return;
    };
    // The process-wide setup `serve` applies, so every renderer runs at the
    // web width the HTTP responses use.
    tamarin_server::init_process_globals();
    // `derivcheck_timeout = 0` skips the dynamic derivation checks, matching
    // the `--derivcheck-timeout=0` oracle probe.
    let entry = theory_io::load_from_path(&fixture(), &maude, 0).expect("fixture loads");

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
