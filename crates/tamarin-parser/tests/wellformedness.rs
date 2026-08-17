// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration test for the fixtures in `tests/wellformedness_fixtures/`.
//! Each fixture must parse.  It must make `wf::check_theory` emit every
//! topic that its `expected.txt` line lists.  It must not make
//! `wf::check_theory` emit any topic that a `#!` line records as absent.
//! Nothing here runs `tamarin-prover`, so this test works offline.  The
//! differential runner (`cargo run -p tamarin-parser --example
//! wellformedness_fixtures`) compares the same file against the oracle.
//!
//! The comparison must not pass while it compares nothing.  Three cases are
//! each a failure.  The first is a `.spthy` file that no `expected.txt` line
//! mentions.  The second is a `#!` line for a fixture that no positive line
//! lists.  The third is a fixture that has neither a parser-level expected
//! topic nor a forbidden one.  This test still cannot see a fixture that has
//! lost its content while its `#!` negatives stay satisfiable.  An empty
//! theory emits no topic, so it triggers no negative.  `tamarin-theory`'s
//! `tests/wellformedness_fixture_reports.rs` covers that case from the crate
//! that holds the post-elaboration checks.  It compares the complete
//! rendered report of each fixture against the bytes of the oracle.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, wf};

/// The two topics that `wf::check_theory` cannot produce.  HS `checkTerms`
/// needs the elaborated `MaudeSig` to classify a funsym as reducible or
/// irreducible.  `multRestrictedReport` (Wellformedness.hs:1108-1113) needs
/// the irreducible symbols of `abstractRule` and the HughesPJ rule renderer.
/// Their ports therefore live in `tamarin_theory::check_terms` and
/// `tamarin_theory::mult_restricted`, and `tamarin_theory::translated_wf`
/// splices them in after elaboration.  The tests of those modules
/// (`tamarin-theory/tests/mult_restricted_report.rs`) and the corpus wf gate
/// cover these two topics.  The parser-only comparison here drops them from
/// the positive side.
const POST_ELABORATION_TOPICS: [&str; 2] = ["Formula terms", "Multiplication restriction of rules"];

/// The minimum size of the roster.  [`fixture_roster_is_complete`] accepts
/// any pair of a file and a line.  This bound is therefore what makes the
/// test fail when the corpus loses most of its fixtures.
const MIN_FIXTURES: usize = 20;

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests")
        .join("wellformedness_fixtures")
}

/// The comparison of topic titles ignores the whitespace around a title.  HS
/// keeps a trailing space in the source literal of the LHS-usage title, and a
/// leading space in ` Formula guardedness`.  A comma-separated `expected.txt`
/// entry can hold neither space, because the parse `trim`s its fields.
fn norm(topic: &str) -> String {
    topic.trim().to_string()
}

#[derive(Debug)]
struct Fixture {
    name: String,
    is_diff: bool,
    /// The topics that `wf::check_theory` must emit.  The test compares
    /// subsets.  A fixture may emit more topics, and that is not a failure.
    expected: BTreeSet<String>,
    /// The topics that it must not emit.  These come from the `#!` lines.
    /// They catch a false positive, as `expected` catches a missing report.
    forbidden: BTreeSet<String>,
}

struct Corpus {
    fixtures: Vec<Fixture>,
    /// The `#!` names that have no positive `expected.txt` line.  Nothing
    /// enforces these expectations.
    unlisted_negatives: Vec<String>,
}

/// Parse `expected.txt`.  A `#!<name> [flags] : <topics>` line is a negative
/// expectation.  Every other `#` line is a comment.  Any other line is a
/// positive expectation.
fn load_corpus() -> Corpus {
    let dir = fixtures_dir();
    let text = fs::read_to_string(dir.join("expected.txt")).expect("expected.txt missing");
    let mut fixtures: Vec<Fixture> = Vec::new();
    let mut negatives: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
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
        let mut parts = lhs.split_whitespace();
        let Some(name) = parts.next() else {
            continue;
        };
        let is_diff = parts.any(|f| f == "--diff");
        let topics: BTreeSet<String> = rhs.split(',').map(norm).filter(|s| !s.is_empty()).collect();
        assert!(
            !topics.is_empty(),
            "{}: {} line lists no topics, so it compares nothing",
            name,
            if negative { "`#!`" } else { "expected.txt" }
        );
        if negative {
            negatives
                .entry(name.to_string())
                .or_default()
                .extend(topics);
        } else {
            fixtures.push(Fixture {
                name: name.to_string(),
                is_diff,
                expected: topics,
                forbidden: BTreeSet::new(),
            });
        }
    }
    for fx in fixtures.iter_mut() {
        if let Some(topics) = negatives.remove(&fx.name) {
            fx.forbidden = topics;
        }
    }
    Corpus {
        fixtures,
        unlisted_negatives: negatives.into_keys().collect(),
    }
}

/// The stems of the `.spthy` files in the fixture directory.
fn fixture_files() -> BTreeSet<String> {
    fs::read_dir(fixtures_dir())
        .expect("fixture dir")
        .map(|e| e.expect("directory entry").path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("spthy"))
        .map(|p| p.file_stem().unwrap().to_string_lossy().into_owned())
        .collect()
}

#[test]
fn every_fixture_parses_and_matches() {
    let corpus = load_corpus();
    assert!(!corpus.fixtures.is_empty(), "no fixtures loaded");
    let dir = fixtures_dir();
    let mut failures = Vec::new();
    for fx in &corpus.fixtures {
        let path = dir.join(format!("{}.spthy", fx.name));
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("missing fixture file: {}", path.display()));
        let mut thy = match parse_theory(&src, &["diff"]) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("PARSE  {}: {}", fx.name, e));
                continue;
            }
        };
        if fx.is_diff {
            thy.is_diff = true;
        }
        let topics: BTreeSet<String> = wf::topics(&wf::check_theory(&thy))
            .into_iter()
            .map(|s| norm(&s))
            .collect();
        let mut expected = fx.expected.clone();
        for topic in POST_ELABORATION_TOPICS {
            expected.remove(topic);
        }
        if expected.is_empty() && fx.forbidden.is_empty() {
            failures.push(format!(
                "VACUOUS {}: every expected topic is post-elaboration ({:?}), and no `#!` line \
                 pins one as absent, so this fixture asserts only that the file parses. Restore \
                 a parser-level expectation or add a `#!` line.",
                fx.name, POST_ELABORATION_TOPICS
            ));
        }
        if !expected.is_subset(&topics) {
            let missing: Vec<_> = expected.difference(&topics).collect();
            failures.push(format!(
                "TOPIC  {}: missing {:?} (got {:?})",
                fx.name, missing, topics
            ));
        }
        let reported: Vec<_> = fx.forbidden.intersection(&topics).collect();
        if !reported.is_empty() {
            failures.push(format!(
                "NEG    {}: reported {:?}, which this fixture pins as NOT emitted",
                fx.name, reported
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Nothing checks a `.spthy` file that no `expected.txt` line mentions.
/// Nothing enforces a `#!` line for a fixture that `expected.txt` does not
/// list.
#[test]
fn fixture_roster_is_complete() {
    let corpus = load_corpus();
    let listed: BTreeSet<String> = corpus.fixtures.iter().map(|f| f.name.clone()).collect();
    let on_disk = fixture_files();
    let unlisted: Vec<_> = on_disk.difference(&listed).collect();
    assert!(
        unlisted.is_empty(),
        "{:?}.spthy have no expected.txt line, so nothing checks them",
        unlisted
    );
    let missing_files: Vec<_> = listed.difference(&on_disk).collect();
    assert!(
        missing_files.is_empty(),
        "expected.txt lists {:?}, which have no .spthy file",
        missing_files
    );
    assert!(
        corpus.unlisted_negatives.is_empty(),
        "`#!` negative expectations for fixtures expected.txt does not list: {:?}",
        corpus.unlisted_negatives
    );
    assert!(
        listed.len() >= MIN_FIXTURES,
        "expected ≥{} fixtures, got {}",
        MIN_FIXTURES,
        listed.len()
    );
}
