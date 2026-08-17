//! This harness compares the complete wellformedness report of each
//! `tests/wellformedness_fixtures/` theory, byte for byte.  The reference is
//! the pinned oracle's own `/* WARNING … */` block.
//!
//! There are two parser-side harnesses: `tamarin-parser`'s
//! `tests/wellformedness.rs` and its `examples/wellformedness_fixtures.rs`
//! differential runner.  Both can only reach
//! `tamarin_parser::wf::check_theory`.  They therefore compare topic names,
//! and they must drop the two topics that exist only after elaboration
//! (`Formula terms`, `Multiplication restriction of rules`).  Three fixtures
//! pin nothing else: `formula_unguarded`, `multiplication_in_rule_lhs` and
//! `quantifier_wrong_sort`.  If you replace one of those three with an empty
//! `theory X begin end`, the parser-side harnesses still pass.  This harness
//! closes that hole from the crate that holds the post-elaboration checks.  It
//! also compares the full report bytes of every other fixture, rather than a
//! subset of the topics.
//!
//! The pipeline below calls the four `tamarin_theory::translated_wf` entry
//! points in the order that both production drivers call them.  Those drivers
//! are `run.rs`'s batch loop and `tamarin_server::theory_io`'s web load.  This
//! harness is therefore a third caller of that shared module, not a hand-copy
//! of either driver.  Two production stages are deliberately absent, and
//! [`render_report`] asserts that the first one cannot apply:
//!
//! * the SAPIC / accountability translation that `run.rs` runs between the
//!   `swap_subterm_convergence_report` and `splice_translated_wf_reports`
//!   calls.  No fixture declares a process, and the render asserts this.
//! * the Maude-backed `Message Derivation Checks` and `Rule variants` blocks
//!   that the batch driver splices afterwards.  Four expectation files
//!   therefore carry an `# omits:` line.  That line names the derivation-check
//!   section that the oracle prints and this pipeline does not.
//!   `expected.txt` documents the same asymmetry for the topic-level
//!   harnesses.
//!
//! The expected bytes live in one file per fixture, at
//! `tests/wellformedness_fixtures/reports/<fixture>.report`.  Each file opens
//! with `#` provenance lines.  [`expectation_body`] strips those lines, and
//! [`every_report_declares_an_oracle_provenance`] requires them to name the
//! oracle.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

/// Fixtures with no `.report` expectation, each with the reason it has none.
///
/// These three fixtures trip two diff-theory checks, and both checks render a
/// deliberately best-effort body.  `wf::left_right_rule_report`
/// (wf.rs:2562-2574) and `wf::reserved_prefix_report` (wf.rs:1489-1505) each
/// carry a comment.  Those comments say the faithful HS bodies need
/// `prettyProtoRuleE` and HughesPJ `wrappedText`, which the parser crate
/// cannot reach.  They also say that no corpus input exercises the path.  The
/// bytes of these two checks are therefore not the oracle's.  A pin here would
/// fix a divergence in place instead of pinning upstream.  Each of the three
/// fixtures keeps a topic in `expected.txt` that the parser side can reach
/// (`Left rule`, `Right rule`, `Reserved prefixes`).  If you empty one of the
/// three, the parser-side harness still fails.
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

/// The minimum number of pinned reports.  [`report_roster_is_complete`]
/// accepts any matched pair, so it alone cannot detect a mass truncation of
/// the expectation directory.  This floor fails the test as soon as the
/// number of pinned reports drops below it.
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

/// Runs one fixture through the theory-level wellformedness pipeline.  It
/// returns the `/* WARNING … */` block that the batch driver prints.
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

/// An expectation file's body.  The body is everything after the leading `#`
/// provenance lines.  This function also removes the file's single trailing
/// newline, because `format_wf_block` ends at `*/`.
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
        // A fixture that trips no check renders `format_wf_block`'s
        // "All wellformedness checks were successful." line.  This assertion
        // refuses to pin that line.  An expectation file therefore cannot be
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

/// Every fixture is either pinned here or listed with a reason.  Every pin and
/// every exclusion names a fixture that exists.
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

/// Every expectation file states where its bytes come from, and the source it
/// names is the oracle.  A `.report` regenerated from the port would pin the
/// port against itself.  Such a file passes without comparing anything against
/// upstream.
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
