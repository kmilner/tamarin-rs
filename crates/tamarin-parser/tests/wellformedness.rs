//! Integration test: every fixture in `tests/wellformedness_fixtures/`
//! must (a) parse and (b) cause our wf checker to emit every topic
//! listed in `expected.txt`. This test does NOT shell out to
//! `tamarin-prover` so it runs offline.

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, wf};

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()
        .parent().unwrap()
        .join("tests")
        .join("wellformedness_fixtures")
}

#[derive(Debug)]
struct Fixture {
    name: String,
    is_diff: bool,
    expected: BTreeSet<String>,
}

fn load_fixtures() -> Vec<Fixture> {
    let dir = fixtures_dir();
    let expected = fs::read_to_string(dir.join("expected.txt"))
        .expect("expected.txt missing");
    let mut out = Vec::new();
    for line in expected.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        let (lhs, rhs) = match line.split_once(':') { Some(p) => p, None => continue };
        let mut parts = lhs.split_whitespace();
        let name = parts.next().expect("fixture name");
        let mut is_diff = false;
        for f in parts { if f == "--diff" { is_diff = true; } }
        let expected_topics: BTreeSet<String> = rhs
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        out.push(Fixture {
            name: name.to_string(),
            is_diff,
            expected: expected_topics,
        });
    }
    out
}

#[test]
fn every_fixture_parses_and_matches() {
    let fixtures = load_fixtures();
    assert!(!fixtures.is_empty(), "no fixtures loaded");
    let dir = fixtures_dir();
    let mut failures = Vec::new();
    for fx in &fixtures {
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
        if fx.is_diff { thy.is_diff = true; }
        // Normalise trailing whitespace: some HS wellformedness titles
        // carry a source-literal trailing space (e.g.
        // "...not in any right-hand-side "), which the comma-separated
        // `expected.txt` cannot represent because its entries are
        // `.trim()`-ed when parsed.  Compare titles modulo trailing space.
        let topics: BTreeSet<String> = wf::topics(&wf::check_theory(&thy))
            .into_iter()
            .map(|s| s.trim_end().to_string())
            .collect();
        // The "Formula terms" check (HS `checkTerms`) needs the elaborated
        // `MaudeSig` for reducible/irreducible funsym classification, so it
        // lives in `tamarin_theory::check_terms` and runs post-elaboration
        // (wired in `tamarin-prover`'s `run.rs`) — NOT in the parser-level
        // `check_theory`.  It is covered by `check_terms`'s own unit tests
        // and the corpus raw-diff sweep.  Drop it from this parser-only
        // comparison so the fixtures that exercise it aren't spuriously
        // failed here.
        let mut expected = fx.expected.clone();
        expected.remove("Formula terms");
        if !expected.is_subset(&topics) {
            let missing: Vec<_> = expected.difference(&topics).collect();
            failures.push(format!(
                "TOPIC  {}: missing {:?} (got {:?})", fx.name, missing, topics));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn fixture_count_is_at_least_twenty() {
    // Guards against accidentally truncating the corpus.
    let fxs = load_fixtures();
    assert!(fxs.len() >= 20, "expected ≥20 fixtures, got {}", fxs.len());
}
