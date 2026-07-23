//! Run the wellformedness fixture corpus against:
//!
//!   1. Our parser — every fixture must parse without error.
//!   2. Our Rust wellformedness checker — the topics it emits must
//!      include every expected topic from `expected.txt`.
//!   3. Tamarin (binary) — the expected topics must also be a subset of
//!      what `tamarin-prover` actually emits, confirming we're shooting
//!      at the right targets.
//!
//! Usage:  cargo run -p tamarin-parser --example wellformedness_fixtures \
//!           [-- <fixtures-dir>]
//!
//! Pass `--no-tamarin` to skip the Tamarin oracle pass (e.g. on systems
//! without the binary installed).

// Example/dev tool: prints fixture results to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, wf};

mod common;
use common::run_tamarin;

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

    let mut total = 0usize;
    let mut parser_ok = 0usize;
    let mut rust_wf_match = 0usize;
    let mut topics_match = 0usize;
    let mut fail_lines: Vec<String> = Vec::new();

    for line in expected.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (lhs, rhs) = match line.split_once(':') {
            Some(p) => p,
            None => continue,
        };
        let mut parts = lhs.split_whitespace();
        let name = match parts.next() {
            Some(n) => n,
            None => continue,
        };
        let mut flags: Vec<String> = Vec::new();
        for f in parts {
            flags.push(f.to_string());
        }
        let expected_topics: BTreeSet<String> = rhs
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();

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
        if flags.iter().any(|f| f == "--diff") {
            thy.is_diff = true;
        }

        // 2. Our Rust wf checker must emit every expected topic. Same
        // comparison semantics as tests/wellformedness.rs: titles compare
        // modulo trailing space (some HS titles carry a source-literal
        // trailing space that comma-separated expected.txt cannot hold),
        // and "Formula terms" (HS `checkTerms`) is excluded — it needs the
        // elaborated MaudeSig, so it lives in `tamarin_theory::check_terms`
        // post-elaboration rather than the parser-level `check_theory`;
        // step 3 still verifies it against the tamarin binary.
        let rust_topics: BTreeSet<String> = wf::topics(&wf::check_theory(&thy))
            .into_iter()
            .map(|s| s.trim_end().to_string())
            .collect();
        let mut rust_expected = expected_topics.clone();
        rust_expected.remove("Formula terms");
        if rust_expected.is_subset(&rust_topics) {
            rust_wf_match += 1;
        } else {
            let missing: Vec<_> = rust_expected.difference(&rust_topics).collect();
            fail_lines.push(format!(
                "RUST   {}: missing {:?} (got: {:?})",
                name, missing, rust_topics
            ));
        }

        // 3. (Optional) Tamarin must emit the expected topics.
        if run_tamarin_oracle {
            let actual = run_tamarin(&tamarin, &path, &flags).unwrap_or_default();
            if expected_topics.is_subset(&actual) {
                topics_match += 1;
            } else {
                let missing: Vec<_> = expected_topics.difference(&actual).collect();
                fail_lines.push(format!(
                    "TOPICS {}: missing {:?} (actual: {:?})",
                    name, missing, actual
                ));
            }
        }
    }

    println!("Fixtures total:   {}", total);
    println!(
        "Parsed OK:        {} ({:.0}%)",
        parser_ok,
        100.0 * parser_ok as f64 / total.max(1) as f64
    );
    println!(
        "Rust wf match:    {} ({:.0}%)",
        rust_wf_match,
        100.0 * rust_wf_match as f64 / total.max(1) as f64
    );
    if run_tamarin_oracle {
        println!(
            "Tamarin match:    {} ({:.0}%)",
            topics_match,
            100.0 * topics_match as f64 / total.max(1) as f64
        );
    }
    if !fail_lines.is_empty() {
        println!("\nFailures:");
        for l in fail_lines {
            println!("  {}", l);
        }
        std::process::exit(1);
    }
}
