// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Integration test: every fixture in `tests/wellformedness_fixtures/` must
//! (a) parse, (b) make `wf::check_theory` emit every topic its `expected.txt`
//! line lists, and (c) NOT make it emit any topic a `#!` line pins as absent.
//! Nothing here shells out to `tamarin-prover`, so it runs offline; the
//! differential runner (`cargo run -p tamarin-parser --example
//! wellformedness_fixtures`) holds the same file to the oracle.
//!
//! The comparison refuses to pass while comparing nothing: a `.spthy` no
//! `expected.txt` line mentions, a `#!` line for a fixture no positive line
//! lists, and a fixture left with neither a parser-level expected topic nor a
//! forbidden one are each a failure.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, wf};

/// The two topics `wf::check_theory` cannot produce: HS `checkTerms` needs
/// the elaborated `MaudeSig` for reducible/irreducible funsym
/// classification, and `multRestrictedReport` (Wellformedness.hs:1108-1113)
/// needs `abstractRule`'s irreducible symbols plus the HughesPJ rule
/// renderer, so their ports live in `tamarin_theory::check_terms` /
/// `tamarin_theory::mult_restricted` and are spliced post-elaboration by
/// `tamarin_theory::translated_wf`.  They are covered by those modules' own
/// tests (`tamarin-theory/tests/mult_restricted_report.rs`) and by the corpus
/// wf gate; the parser-only comparison here drops them from the positive
/// side.
const POST_ELABORATION_TOPICS: [&str; 2] = ["Formula terms", "Multiplication restriction of rules"];

/// Minimum roster size, so mass truncation of the corpus fails loudly even
/// though [`fixture_roster_is_complete`] accepts any file/line pair.
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

/// Topic titles compare modulo surrounding whitespace: HS carries a
/// source-literal trailing space on the LHS-usage title and a leading one on
/// ` Formula guardedness`, neither of which a comma-separated `expected.txt`
/// entry can hold — its fields are `trim`ed on parse.
fn norm(topic: &str) -> String {
    topic.trim().to_string()
}

#[derive(Debug)]
struct Fixture {
    name: String,
    is_diff: bool,
    /// Topics `wf::check_theory` must emit (subset check: a fixture may
    /// legitimately emit more).
    expected: BTreeSet<String>,
    /// Topics it must NOT emit — the `#!` lines, which catch a false
    /// positive the way `expected` catches a missing report.
    forbidden: BTreeSet<String>,
}

struct Corpus {
    fixtures: Vec<Fixture>,
    /// `#!` names with no positive `expected.txt` line: pins nothing enforces.
    unlisted_negatives: Vec<String>,
}

/// Parse `expected.txt`.  `#!<name> [flags] : <topics>` is a negative
/// expectation; every other `#` line is a comment; anything else is a
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

/// The `.spthy` file stems present in the fixture directory.
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

/// A `.spthy` no `expected.txt` line mentions is a fixture nothing checks,
/// and a `#!` line for an unlisted fixture is a pin nothing enforces.
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
