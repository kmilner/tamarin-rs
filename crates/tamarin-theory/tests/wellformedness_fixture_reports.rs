//! Byte-pins the WELLFORMEDNESS REPORT each `tests/wellformedness_fixtures/`
//! theory produces, against the pinned oracle's own `/* WARNING … */` block.
//!
//! The two parser-side harnesses (`tamarin-parser`'s `tests/wellformedness.rs`
//! and its `examples/wellformedness_fixtures.rs` differential runner) can only
//! reach `tamarin_parser::wf::check_theory`, so they compare TOPIC NAMES and
//! must drop the two topics that exist only after elaboration
//! (`Formula terms`, `Multiplication restriction of rules`).  Three fixtures —
//! `formula_unguarded`, `multiplication_in_rule_lhs`, `quantifier_wrong_sort` —
//! pin nothing else, so on the parser side they survive being replaced by an
//! empty `theory X begin end`.  This harness closes that hole from the crate
//! where the post-elaboration checks live, and while it is here it holds every
//! other fixture to its full report bytes rather than to a topic subset.
//!
//! The pipeline below is the four `tamarin_theory::translated_wf` entry points
//! in the order both production drivers call them — `run.rs`'s batch loop and
//! `tamarin_server::theory_io`'s web load — so this is a third caller of that
//! shared module rather than a hand-copy of either driver.  Two production
//! stages are deliberately absent, and [`render_report`] asserts the first
//! cannot apply:
//!
//! * the SAPIC / accountability translation `run.rs` runs between the
//!   `swap_subterm_convergence_report` and `splice_translated_wf_reports`
//!   calls — no fixture declares a process, which the render asserts; and
//! * the Maude-backed `Message Derivation Checks` and `Rule variants` blocks
//!   the batch driver splices afterwards.  Four expectation files therefore
//!   carry an `# omits:` line naming the derivation-check section the oracle
//!   prints and this pipeline does not — the same asymmetry `expected.txt`
//!   documents for the topic-level harnesses.
//!
//! Expected bytes live one file per fixture in
//! `tests/wellformedness_fixtures/reports/<fixture>.report`, each opening with
//! `#` provenance lines that [`expectation_body`] strips and
//! [`every_report_declares_an_oracle_provenance`] holds to naming the oracle.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

/// Fixtures with no `.report` expectation, each with the reason it has none.
///
/// Both diff-theory checks these three trip render a deliberately
/// best-effort body: `wf::left_right_rule_report` (wf.rs:2562-2574) and
/// `wf::reserved_prefix_report` (wf.rs:1489-1505) each carry a comment saying
/// the faithful HS body needs `prettyProtoRuleE` / HughesPJ `wrappedText`,
/// which the parser crate cannot reach, and that no corpus input exercises
/// the path.  Their bytes are consequently NOT the oracle's, so a pin here
/// would fix a divergence in place instead of pinning upstream.  Each keeps a
/// parser-reachable topic in `expected.txt` (`Left rule`, `Right rule`,
/// `Reserved prefixes`), so gutting one of these three still reddens the
/// parser-side harness.
const NO_REPORT_EXPECTATION: &[(&str, &str)] = &[
    (
        "diff_left_right_mismatch",
        "`Left rule` body is a documented best-effort divergence",
    ),
    (
        "diff_reserved_prefix",
        "`Reserved prefixes` body is a documented best-effort divergence",
    ),
    (
        "diff_right_rule_mismatch",
        "`Right rule` body is a documented best-effort divergence",
    ),
];

/// Minimum number of pinned reports, so mass truncation of the expectation
/// directory fails loudly even though [`report_roster_is_complete`] accepts
/// any matched pair.
const MIN_REPORTS: usize = 18;

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests")
        .join("wellformedness_fixtures")
}

fn reports_dir() -> PathBuf {
    fixtures_dir().join("reports")
}

/// The `.spthy` stems in the fixture directory.
fn fixture_stems() -> BTreeSet<String> {
    stems(&fixtures_dir(), "spthy")
}

/// The `.report` stems in the expectation directory.
fn report_stems() -> BTreeSet<String> {
    stems(&reports_dir(), "report")
}

fn stems(dir: &Path, ext: &str) -> BTreeSet<String> {
    fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.expect("directory entry").path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some(ext))
        .map(|p| p.file_stem().unwrap().to_string_lossy().into_owned())
        .collect()
}

/// Run one fixture through the theory-level wellformedness pipeline and
/// render the `/* WARNING … */` block the batch driver would print.
fn render_report(name: &str) -> String {
    let path = fixtures_dir().join(format!("{name}.spthy"));
    let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_theory(&src, &["diff"]).unwrap_or_else(|e| panic!("{name}: parse: {e}"));

    let mut report = tamarin_theory::translated_wf::pre_translation_wf_report(&parsed);
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed)
        .unwrap_or_else(|e| panic!("{name}: elaborate: {}", e.message));
    assert!(
        !elaborated.is_sapic,
        "{name}: declares a process, but this harness omits the SAPIC/accountability \
         translation stage `run.rs` runs before `splice_translated_wf_reports`, so its \
         report would be missing the generated rules' findings",
    );
    let maude_sig = elaborated.signature.maude_sig.clone();
    tamarin_theory::translated_wf::swap_subterm_convergence_report(&mut report, &maude_sig);
    tamarin_theory::translated_wf::splice_translated_wf_reports(
        &parsed,
        &elaborated,
        &maude_sig,
        &mut report,
    );
    format_wf_block(&report)
}

/// The leading `#` provenance lines of an expectation file.
fn provenance(text: &str) -> Vec<&str> {
    text.lines().take_while(|l| l.starts_with('#')).collect()
}

/// An expectation file's body: everything after the leading `#` provenance
/// lines, with the file's single trailing newline removed (`format_wf_block`
/// ends at `*/`).
fn expectation_body(text: &str) -> String {
    let body: String = text
        .lines()
        .skip_while(|l| l.starts_with('#'))
        .map(|l| format!("{l}\n"))
        .collect();
    body.strip_suffix('\n').unwrap_or(&body).to_string()
}

#[test]
fn every_fixture_report_matches_its_pinned_block() {
    let dir = reports_dir();
    let stems = report_stems();
    assert!(!stems.is_empty(), "no .report expectations loaded");
    for name in &stems {
        let path = dir.join(format!("{name}.report"));
        let text =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let expected = expectation_body(&text);
        // A fixture that stopped tripping any check would render
        // `format_wf_block`'s "All wellformedness checks were successful."
        // line; refuse to pin that, so an expectation file cannot be
        // regenerated into one that compares nothing.
        assert!(
            expected.starts_with("/*\nWARNING: the following wellformedness checks failed!\n"),
            "{name}.report does not pin a failing wellformedness block:\n{expected}",
        );
        assert_eq!(
            render_report(name),
            expected,
            "{name}: rendered wellformedness block differs from {}",
            path.display(),
        );
    }
}

/// Every fixture is either pinned here or listed with a reason, and every
/// pin/exclusion names a fixture that exists.
#[test]
fn report_roster_is_complete() {
    let fixtures = fixture_stems();
    let reports = report_stems();
    let excluded: BTreeSet<String> = NO_REPORT_EXPECTATION
        .iter()
        .map(|(n, _)| (*n).to_string())
        .collect();

    let unpinned: Vec<_> = fixtures
        .difference(&reports)
        .filter(|n| !excluded.contains(*n))
        .collect();
    assert!(
        unpinned.is_empty(),
        "{unpinned:?}.spthy have no .report expectation and no NO_REPORT_EXPECTATION entry, \
         so their report bytes are unpinned",
    );
    let orphaned: Vec<_> = reports.difference(&fixtures).collect();
    assert!(
        orphaned.is_empty(),
        "{orphaned:?}.report pin fixtures that have no .spthy file",
    );
    let stale: Vec<_> = excluded.difference(&fixtures).collect();
    assert!(
        stale.is_empty(),
        "NO_REPORT_EXPECTATION lists {stale:?}, which have no .spthy file",
    );
    let both: Vec<_> = excluded.intersection(&reports).collect();
    assert!(
        both.is_empty(),
        "{both:?} are both pinned and excused — drop the NO_REPORT_EXPECTATION entry",
    );
    assert!(
        reports.len() >= MIN_REPORTS,
        "expected ≥{MIN_REPORTS} pinned reports, got {}",
        reports.len(),
    );
}

/// Every expectation file states where its bytes came from, and names the
/// oracle when it does: a `.report` regenerated from the port would pin the
/// port against itself and pass while comparing nothing upstream.
#[test]
fn every_report_declares_an_oracle_provenance() {
    let dir = reports_dir();
    for name in report_stems() {
        let path = dir.join(format!("{name}.report"));
        let text =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let lines = provenance(&text);
        let source = lines
            .iter()
            .find_map(|l| l.strip_prefix("# source:"))
            .unwrap_or_else(|| panic!("{name}.report has no `# source:` provenance line"));
        assert!(
            source.contains("oracle"),
            "{name}.report is pinned against `{}`, not the oracle",
            source.trim(),
        );
    }
}
