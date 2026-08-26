//! This harness compares the complete wellformedness report of each
//! `tests/wellformedness_fixtures/` theory, byte for byte.  The reference is
//! the pinned oracle's own `/* WARNING … */` block.
//!
//! The `examples/wellformedness_fixtures.rs` differential runner compares
//! topic names only, and four fixtures list a single topic:
//! `formula_unguarded`, `multiplication_in_rule_lhs`, `non_subterm_equation`
//! and `quantifier_wrong_sort`.  This harness compares the full report bytes
//! of every fixture instead, so a fixture cannot be hollowed out and still
//! pass.  It also holds that runner's `expected.txt` roster to the fixture
//! directory, in [`expected_txt_lists_every_fixture`].
//!
//! The pipeline below calls `tamarin_theory::wellformedness::check_wellformedness`
//! the way both production callers call it.  Those callers are `run.rs`'s
//! batch loop and `tamarin_server::theory_io`'s web load.  This harness is
//! therefore a third caller of that shared module, not a hand-copy of either
//! caller.  Two production stages are deliberately absent, and
//! [`render_report`] asserts that the first one cannot apply:
//!
//! * the SAPIC / accountability translation both drivers run before the pass.
//!   No fixture declares a process, and the render asserts this.
//! * the Maude-backed `Message Derivation Checks` and `Rule variants` blocks
//!   that the batch loop splices afterwards.  Four expectation files
//!   therefore carry an `# omits:` line.  That line names the derivation-check
//!   section that the oracle prints and this pipeline does not.
//!   `expected.txt` documents the same asymmetry for the differential
//!   runner.
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
/// returns the `/* WARNING … */` block that the batch loop prints.
fn render_report(name: &str) -> String {
    let path = fixtures_dir().join(format!("{name}.spthy"));
    let src = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_theory(&src, &["diff"]).unwrap_or_else(|e| panic!("{name}: parse: {e}"));

    let elaborated = tamarin_theory::elaborate::elaborate(&parsed)
        .unwrap_or_else(|e| panic!("{name}: elaborate: {}", e.message));
    assert!(
        !elaborated.is_sapic,
        "{name}: declares a process, but this harness omits the SAPIC/accountability \
         translation stage both drivers run before the wellformedness pass, so its \
         report would be missing the generated rules' findings",
    );
    format_wf_block(&tamarin_theory::wellformedness::check_wellformedness(
        &elaborated,
        None,
    ))
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

/// Every fixture pins its rendered block against the oracle, and every pin
/// names a fixture that exists.
#[test]
fn report_roster_is_complete() {
    let fixtures = fixture_stems();
    let reports = report_stems();

    let unpinned: Vec<_> = fixtures.difference(&reports).collect();
    assert!(
        unpinned.is_empty(),
        "{unpinned:?}.spthy have no .report expectation, so their report bytes are unpinned",
    );
    let orphaned: Vec<_> = reports.difference(&fixtures).collect();
    assert!(
        orphaned.is_empty(),
        "{orphaned:?}.report pin fixtures that have no .spthy file",
    );
    assert!(
        reports.len() >= MIN_REPORTS,
        "expected ≥{MIN_REPORTS} pinned reports, got {}",
        reports.len(),
    );
}

/// The fixture names `tests/wellformedness_fixtures/expected.txt` carries:
/// `positive` holds the names of its expectation lines, `negative` the names
/// of its `#!` lines.
struct ExpectedNames {
    positive: BTreeSet<String>,
    negative: BTreeSet<String>,
}

/// Reads the names out of `expected.txt`.  A `#!<name> [oracle-flags] :
/// <topics>` line is a negative expectation, every other `#` line is a
/// comment, and any other line is a positive expectation.  A line that lists
/// no topics compares nothing in the differential runner, so it fails here.
fn expected_names() -> ExpectedNames {
    let path = fixtures_dir().join("expected.txt");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut names = ExpectedNames {
        positive: BTreeSet::new(),
        negative: BTreeSet::new(),
    };
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let (body, negative) = match line.strip_prefix("#!") {
            Some(rest) => (rest.trim(), true),
            None if line.starts_with('#') => continue,
            None => (line, false),
        };
        let Some((lhs, rhs)) = body.split_once(':') else {
            continue;
        };
        let Some(name) = lhs.split_whitespace().next() else {
            continue;
        };
        assert!(
            rhs.split(',').any(|t| !t.trim().is_empty()),
            "{name}: {} line lists no topics, so it compares nothing",
            if negative { "`#!`" } else { "expected.txt" },
        );
        if negative {
            names.negative.insert(name.to_string());
        } else {
            names.positive.insert(name.to_string());
        }
    }
    names
}

/// The differential runner drives the fixtures from `expected.txt`.  A
/// `.spthy` file that no line names goes unchecked there, and a `#!` negative
/// pin whose fixture no positive line lists is enforced against nothing.
#[test]
fn expected_txt_lists_every_fixture() {
    let names = expected_names();
    let fixtures = fixture_stems();

    let unlisted: Vec<_> = fixtures.difference(&names.positive).collect();
    assert!(
        unlisted.is_empty(),
        "{unlisted:?}.spthy have no expected.txt line, so the differential runner skips them",
    );
    let missing: Vec<_> = names.positive.difference(&fixtures).collect();
    assert!(
        missing.is_empty(),
        "expected.txt lists {missing:?}, which have no .spthy file",
    );
    let orphaned: Vec<_> = names.negative.difference(&names.positive).collect();
    assert!(
        orphaned.is_empty(),
        "`#!` negative pins for fixtures expected.txt does not list: {orphaned:?}",
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
