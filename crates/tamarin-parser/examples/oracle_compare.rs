//! Oracle harness: for each `.spthy` file, run `tamarin-prover
//! --parse-only` and compare structural counts (theory name, rules,
//! lemmas, restrictions) against our Rust parser.
//!
//! Usage:  cargo run -p tamarin-parser --example oracle_compare -- [<root>]
//!         [--limit N] [--filter STR]

// Example/dev tool: prints comparison results to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use tamarin_parser::{ast, parse_theory};

mod common;
use common::{collect_spthy, corpus_root};

#[derive(Debug, Default, Clone)]
struct Counts {
    name: String,
    rules: usize,
    lemmas: usize,
    restrictions: usize,
}

fn main() {
    let mut args = env::args().skip(1);
    let mut root = corpus_root();
    let mut limit: Option<usize> = None;
    let mut filter: Option<String> = None;
    let mut tamarin_path = "tamarin-prover".to_string();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--limit" => limit = args.next().and_then(|s| s.parse().ok()),
            "--filter" => filter = args.next(),
            "--tamarin" => tamarin_path = args.next().unwrap_or(tamarin_path),
            other if other.starts_with("--") => {
                eprintln!("unknown flag: {}", other);
                std::process::exit(2);
            }
            other => root = PathBuf::from(other),
        }
    }

    let mut files = collect_spthy(&root);

    if let Some(f) = &filter {
        files.retain(|p| p.to_string_lossy().contains(f));
    }
    if let Some(n) = limit {
        files.truncate(n);
    }

    let mut total = 0usize;
    let mut both_parse = 0usize;
    let mut equal = 0usize;
    let mut diff_examples = Vec::new();
    let mut tamarin_failed = 0usize;
    let mut ours_failed = 0usize;

    for path in files.iter() {
        total += 1;
        let src = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        // Tamarin oracle.
        let tamarin = match run_tamarin(&tamarin_path, path) {
            Some(c) => c,
            None => {
                tamarin_failed += 1;
                continue;
            }
        };
        let our = match parse_theory(&src, &["diff"]) {
            Ok(t) => count_ours(&t),
            Err(_) => {
                ours_failed += 1;
                continue;
            }
        };
        both_parse += 1;
        if structural_equal(&tamarin, &our) {
            equal += 1;
        } else if diff_examples.len() < 10 {
            diff_examples.push((path.clone(), tamarin.clone(), our));
        }
    }

    println!("Files scanned:           {}", total);
    println!("Tamarin parse failures:  {}", tamarin_failed);
    println!("Our parse failures:      {}", ours_failed);
    println!("Both parsed:             {}", both_parse);
    println!(
        "Structurally equal:      {} ({:.1}%)",
        equal,
        100.0 * equal as f64 / both_parse.max(1) as f64
    );

    if !diff_examples.is_empty() {
        println!("\nDifferences (showing up to 10):");
        for (p, t, o) in diff_examples.iter() {
            println!("  {}", p.display());
            println!(
                "    tamarin: name={:?} rules={} lemmas={} restrictions={}",
                t.name, t.rules, t.lemmas, t.restrictions
            );
            println!(
                "    ours:    name={:?} rules={} lemmas={} restrictions={}",
                o.name, o.rules, o.lemmas, o.restrictions
            );
        }
    }
}

/// Run `tamarin-prover --parse-only` on a file and extract structural
/// counts. Returns None on any failure (tamarin not found, file rejected,
/// etc.).
fn run_tamarin(tamarin: &str, path: &std::path::Path) -> Option<Counts> {
    let output = Command::new(tamarin)
        .arg("--parse-only")
        .arg(path)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    parse_tamarin_output(&stdout)
}

/// Parse the textual output of `tamarin-prover --parse-only` to extract
/// structural counts.
fn parse_tamarin_output(s: &str) -> Option<Counts> {
    let mut c = Counts::default();
    let mut name = None;
    for line in s.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("theory ") {
            // first occurrence is the theory header
            if name.is_none() {
                let n = rest.split_whitespace().next().unwrap_or("");
                name = Some(n.to_string());
            }
        } else if line.starts_with("rule ") || line.starts_with("rule (") {
            c.rules += 1;
        } else if line.starts_with("lemma ") {
            c.lemmas += 1;
        } else if line.starts_with("restriction ") {
            c.restrictions += 1;
        }
    }
    name.map(|n| {
        c.name = n;
        c
    })
}

fn count_ours(t: &ast::Theory) -> Counts {
    let mut c = Counts {
        name: t.name.clone(),
        ..Default::default()
    };
    for it in &t.items {
        match it {
            ast::TheoryItem::Rule(_) | ast::TheoryItem::IntrRule(_) => c.rules += 1,
            ast::TheoryItem::Lemma(_) => c.lemmas += 1,
            ast::TheoryItem::Restriction(_) | ast::TheoryItem::LegacyAxiom(_) => {
                c.restrictions += 1
            }
            _ => {}
        }
    }
    c
}

fn structural_equal(a: &Counts, b: &Counts) -> bool {
    a.name == b.name
        && a.rules == b.rules
        && a.lemmas == b.lemmas
        && a.restrictions == b.restrictions
}
