//! Run the wellformedness fixture corpus against:
//!
//!   1. Our parser — every fixture must parse without error.
//!   2. Our Rust wellformedness checker — the topics it emits must include
//!      every expected topic from `expected.txt`, and none of that fixture's
//!      `#!` negative expectations.
//!   3. Tamarin (binary) — the same two comparisons against what
//!      `tamarin-prover` actually emits, confirming we're shooting at the
//!      right targets.
//!
//! The run ends with an explicit `VERDICT:` line and exits nonzero on any
//! failure.  It also refuses to pass while comparing nothing: an empty
//! fixture roster, a `.spthy` no `expected.txt` line mentions, a line that
//! lists no topics, an oracle that fails to launch, and a fixture whose
//! step-2 expectations all vanish into [`POST_ELABORATION_TOPICS`] are each a
//! failure — the last one unless the fixture is on
//! [`EMPTY_RUST_EXPECTATION_ALLOWLIST`] *and* carries negative expectations
//! for step 2 to compare instead.
//!
//! Usage:  cargo run -p tamarin-parser --example wellformedness_fixtures \
//!           [-- <fixtures-dir>]
//!
//! Pass `--no-tamarin` to skip the Tamarin oracle pass (e.g. on systems
//! without the binary installed).

// Example/dev tool: prints fixture results to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, wf};

mod common;
use common::run_tamarin;

/// The two topics the parser-level `wf::check_theory` cannot produce: both HS
/// checks need the elaborated `MaudeSig` (reducible-funsym classification,
/// and `abstractRule`'s irreducible symbols), so their ports live in
/// `tamarin_theory::check_terms` / `tamarin_theory::mult_restricted` and run
/// post-elaboration.  Step 2 drops them; step 3 still holds the oracle to
/// them.
const POST_ELABORATION_TOPICS: [&str; 2] = ["Formula terms", "Multiplication restriction of rules"];

/// Fixtures whose step-2 expectation set is EMPTY once
/// [`POST_ELABORATION_TOPICS`] are removed, each with the reason it stays.
///
/// A fixture that empties and is NOT listed here fails the run: "the file
/// parses" is not a wellformedness expectation.  A listed fixture that stops
/// emptying fails too, so an entry cannot outlive its reason.  And every
/// entry must carry `#!` negative expectations in `expected.txt`, so step 2
/// compares *something* for it.
///
/// Step 2 still cannot separate the real content of a listed fixture from an
/// empty theory.  Neither of the two emits a negative topic.
/// `tests/wellformedness_fixture_reports.rs` in `tamarin-theory` can make
/// that separation.  It runs each fixture through the post-elaboration
/// checks.  It then compares the complete rendered report against
/// `tests/wellformedness_fixtures/reports/`.
const EMPTY_RUST_EXPECTATION_ALLOWLIST: &[(&str, &str)] = &[
    (
        "formula_unguarded",
        "pins `Formula terms` alone (the lemma's free `#i`); HS `checkTerms` \
         is post-elaboration in the port",
    ),
    (
        "multiplication_in_rule_lhs",
        "pins `Multiplication restriction of rules` alone; HS \
         `multRestrictedReport` is post-elaboration in the port",
    ),
    (
        "quantifier_wrong_sort",
        "pins `Formula terms` alone; the oracle's second topic here, \
         ` Formula guardedness`, is post-elaboration in the port too and \
         cannot be pinned in a file the parser-only harness also reads",
    ),
];

/// Topic titles compare modulo surrounding whitespace: HS carries a
/// source-literal trailing space on the LHS-usage title and a leading one on
/// ` Formula guardedness`, neither of which a comma-separated `expected.txt`
/// entry can hold — its fields are `trim`ed on parse.
fn norm(topic: &str) -> String {
    topic.trim().to_string()
}

fn pct(n: usize, total: usize) -> f64 {
    100.0 * n as f64 / total.max(1) as f64
}

/// One positive `expected.txt` line.
struct Fixture {
    name: String,
    flags: Vec<String>,
    expected: BTreeSet<String>,
}

fn main() {
    let args = env::args().skip(1);
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests")
        .join("wellformedness_fixtures");
    let mut run_tamarin_oracle = true;
    let mut positional: Vec<String> = Vec::new();
    for a in args {
        match a.as_str() {
            "--no-tamarin" => run_tamarin_oracle = false,
            other => positional.push(other.to_string()),
        }
    }
    if let Some(a) = positional.into_iter().next() {
        dir = PathBuf::from(a);
    }
    let tamarin = env::var("TAMARIN").unwrap_or_else(|_| "tamarin-prover".into());

    let expected_path = dir.join("expected.txt");
    let expected = fs::read_to_string(&expected_path)
        .unwrap_or_else(|_| panic!("missing expected.txt at {}", expected_path.display()));

    let mut fail_lines: Vec<String> = Vec::new();
    let mut fixtures: Vec<Fixture> = Vec::new();
    let mut negatives: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    // Parse `expected.txt`.  `#!<name> : <topics>` is a negative-expectation
    // directive; every other `#` line is a comment.  Negatives ride inside a
    // comment on purpose — the parser-only harness
    // `crates/tamarin-parser/tests/wellformedness.rs` reads the same file and
    // treats every non-`#` line as positive expectations.
    for line in expected.lines() {
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
        let flags: Vec<String> = parts.map(str::to_string).collect();
        let topics: BTreeSet<String> = rhs.split(',').map(norm).filter(|s| !s.is_empty()).collect();
        if topics.is_empty() {
            fail_lines.push(format!(
                "SYNTAX {}: {} line lists no topics, so it compares nothing",
                name,
                if negative { "`#!`" } else { "expected.txt" }
            ));
        }
        if negative {
            negatives
                .entry(name.to_string())
                .or_default()
                .extend(topics);
        } else {
            fixtures.push(Fixture {
                name: name.to_string(),
                flags,
                expected: topics,
            });
        }
    }

    // Roster: a `.spthy` no line mentions is a fixture nothing checks, and a
    // `#!` line for an unlisted fixture is a pin nothing enforces.
    let listed: BTreeSet<&str> = fixtures.iter().map(|f| f.name.as_str()).collect();
    let dir_entries =
        fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {}", dir.display(), e));
    let mut on_disk: BTreeSet<String> = BTreeSet::new();
    for entry in dir_entries {
        let path = entry.expect("directory entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("spthy") {
            on_disk.insert(path.file_stem().unwrap().to_string_lossy().into_owned());
        }
    }
    for name in on_disk.iter().filter(|n| !listed.contains(n.as_str())) {
        fail_lines.push(format!(
            "ROSTER {}.spthy: no expected.txt line, so nothing checks it",
            name
        ));
    }
    for name in negatives.keys().filter(|n| !listed.contains(n.as_str())) {
        fail_lines.push(format!(
            "ROSTER {}: `#!` negative expectations for a fixture expected.txt does not list",
            name
        ));
    }

    let mut total = 0usize;
    let mut parser_ok = 0usize;
    let mut rust_wf_match = 0usize;
    let mut topics_match = 0usize;
    let mut negatives_checked = 0usize;
    let mut allowlisted_hit: Vec<(&str, &str)> = Vec::new();

    for fx in &fixtures {
        let name = fx.name.as_str();
        total += 1;

        let path = dir.join(format!("{}.spthy", name));
        let src =
            fs::read_to_string(&path).unwrap_or_else(|_| panic!("missing {}", path.display()));

        // 1. Our parser must accept the fixture.
        let mut thy = match parse_theory(&src, &["diff"]) {
            Ok(t) => {
                parser_ok += 1;
                t
            }
            Err(e) => {
                fail_lines.push(format!("PARSE  {}: {}", name, e));
                continue;
            }
        };
        // Override is_diff if the fixture is flagged --diff. Our parser
        // doesn't auto-detect diff mode (Tamarin uses a separate
        // entry point), so we surface it from the fixture metadata.
        if fx.flags.iter().any(|f| f == "--diff") {
            thy.is_diff = true;
        }

        // 2. Our Rust wf checker must emit every expected topic and none of
        // the fixture's negative pins.  [`POST_ELABORATION_TOPICS`] are
        // dropped from the positive side; step 3 still verifies them.
        let rust_topics: BTreeSet<String> = wf::topics(&wf::check_theory(&thy))
            .into_iter()
            .map(|s| norm(&s))
            .collect();
        let mut rust_expected = fx.expected.clone();
        for topic in POST_ELABORATION_TOPICS {
            rust_expected.remove(topic);
        }
        let negative = negatives.get(name).cloned().unwrap_or_default();
        negatives_checked += negative.len();

        let allowed: Option<&str> = EMPTY_RUST_EXPECTATION_ALLOWLIST
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, reason)| *reason);
        match (rust_expected.is_empty(), allowed) {
            (true, None) => fail_lines.push(format!(
                "VACUOUS {}: every expected topic is post-elaboration ({:?}), so step 2 \
                 asserts only that the file parses. Restore a parser-level expectation, \
                 or add an EMPTY_RUST_EXPECTATION_ALLOWLIST entry with a reason.",
                name, POST_ELABORATION_TOPICS
            )),
            (true, Some(_)) if negative.is_empty() => fail_lines.push(format!(
                "VACUOUS {}: allowlisted with an empty step-2 expectation set but carrying \
                 no `#!` negative expectations, so step 2 still compares nothing.",
                name
            )),
            (true, Some(reason)) => allowlisted_hit.push((name, reason)),
            (false, Some(_)) => fail_lines.push(format!(
                "STALE  {}: on EMPTY_RUST_EXPECTATION_ALLOWLIST, but its step-2 expectation \
                 set is no longer empty ({:?}) — drop the allowlist entry.",
                name, rust_expected
            )),
            (false, None) => {}
        }

        if rust_expected.is_subset(&rust_topics) {
            rust_wf_match += 1;
        } else {
            let missing: Vec<_> = rust_expected.difference(&rust_topics).collect();
            fail_lines.push(format!(
                "RUST   {}: missing {:?} (got: {:?})",
                name, missing, rust_topics
            ));
        }
        let reported: Vec<_> = negative.intersection(&rust_topics).collect();
        if !reported.is_empty() {
            fail_lines.push(format!(
                "RUSTNEG {}: our checker reported {:?}, which this fixture pins as NOT emitted",
                name, reported
            ));
        }

        // 3. (Optional) Tamarin must emit the expected topics and none of the
        // negative pins.
        if run_tamarin_oracle {
            match run_tamarin(&tamarin, &path, &fx.flags) {
                None => fail_lines.push(format!(
                    "ORACLE {}: `{}` failed to launch — point $TAMARIN at the pinned binary, \
                     or pass --no-tamarin to run steps 1 and 2 alone",
                    name, tamarin
                )),
                Some(topics) => {
                    let actual: BTreeSet<String> = topics.iter().map(|s| norm(s)).collect();
                    if actual.is_empty() {
                        fail_lines.push(format!(
                            "ORACLE {}: `{}` emitted no wellformedness topics at all",
                            name, tamarin
                        ));
                    }
                    if fx.expected.is_subset(&actual) {
                        topics_match += 1;
                    } else {
                        let missing: Vec<_> = fx.expected.difference(&actual).collect();
                        fail_lines.push(format!(
                            "TOPICS {}: missing {:?} (actual: {:?})",
                            name, missing, actual
                        ));
                    }
                    let reported: Vec<_> = negative.intersection(&actual).collect();
                    if !reported.is_empty() {
                        fail_lines.push(format!(
                            "TOPICSNEG {}: `{}` reported {:?}, which this fixture pins as NOT \
                             emitted",
                            name, tamarin, reported
                        ));
                    }
                }
            }
        }
    }

    if total == 0 {
        fail_lines.push(format!(
            "EMPTY  {}: lists no fixtures — the run compared nothing",
            expected_path.display()
        ));
    }

    println!("Fixtures total:   {}", total);
    println!(
        "Parsed OK:        {} ({:.0}%)",
        parser_ok,
        pct(parser_ok, total)
    );
    println!(
        "Rust wf match:    {} ({:.0}%)",
        rust_wf_match,
        pct(rust_wf_match, total)
    );
    if run_tamarin_oracle {
        println!(
            "Tamarin match:    {} ({:.0}%)",
            topics_match,
            pct(topics_match, total)
        );
    }
    println!(
        "Negative pins:    {} across {} fixture(s)",
        negatives_checked,
        negatives.len()
    );
    if !allowlisted_hit.is_empty() {
        println!(
            "\nStep-2 expectation set empty (allowlisted; checked by their `#!` \
             negatives and by step 3):"
        );
        for (name, reason) in &allowlisted_hit {
            println!("  {}: {}", name, reason);
        }
    }
    if !fail_lines.is_empty() {
        println!("\nFailures:");
        for l in &fail_lines {
            println!("  {}", l);
        }
    }
    let bad = fail_lines.len();
    println!(
        "\nVERDICT: {} ({} fixture(s), {} failure(s))",
        if bad == 0 { "PASS" } else { "FAIL" },
        total,
        bad
    );
    if bad != 0 {
        std::process::exit(1);
    }
}
