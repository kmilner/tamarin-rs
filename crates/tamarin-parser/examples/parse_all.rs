//! Walks an examples directory, parses every `.spthy` file, and reports
//! pass/fail counts.
//!
//! Usage:  cargo run -p tamarin-parser --example parse_all -- <root>
//!
//! With `--list-fail` it prints the first error of each failing file.

// Example/dev tool: reports pass/fail counts to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

use tamarin_parser::{parse_theory, Message};
use walkdir::WalkDir;

mod common;
use common::corpus_root;

/// A representative message string for failure-category bucketing.  The
/// `ParseError` holds a parsec-style message list, so join the message
/// strings for classification purposes.
fn error_key_source(e: &tamarin_parser::ParseError) -> String {
    e.messages
        .iter()
        .map(|m| match m {
            Message::SysUnExpect(s)
            | Message::UnExpect(s)
            | Message::Expect(s)
            | Message::Message(s) => s.as_str(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() {
    let mut args = env::args().skip(1);
    let mut root = corpus_root();
    let mut list_fail = false;
    let mut limit: Option<usize> = None;
    let mut filter: Option<String> = None;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--list-fail" => list_fail = true,
            "--limit" => limit = args.next().and_then(|s| s.parse().ok()),
            "--filter" => filter = args.next(),
            other if other.starts_with("--") => {
                eprintln!("unknown flag: {}", other);
                std::process::exit(2);
            }
            other => root = PathBuf::from(other),
        }
    }

    let mut total = 0usize;
    let mut ok = 0usize;
    let mut failed: Vec<(PathBuf, String)> = Vec::new();
    let mut failure_reasons: BTreeMap<String, usize> = BTreeMap::new();

    for entry in WalkDir::new(&root).follow_links(false) {
        let entry = match entry { Ok(e) => e, Err(_) => continue };
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("spthy") { continue; }
        if let Some(f) = &filter {
            if !path.to_string_lossy().contains(f) { continue; }
        }
        if let Some(n) = limit {
            if total >= n { break; }
        }
        let src = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        total += 1;
        match parse_theory(&src, &["diff"]) {
            Ok(_) => { ok += 1; }
            Err(e) => {
                let key = classify(&error_key_source(&e));
                *failure_reasons.entry(key).or_insert(0) += 1;
                failed.push((path.to_path_buf(), format!("{}", e)));
            }
        }
    }

    println!("Parsed {} / {} ({:.1}%)",
        ok, total, 100.0 * ok as f64 / total.max(1) as f64);

    println!("\nTop failure categories:");
    let mut reasons: Vec<_> = failure_reasons.iter().collect();
    reasons.sort_by(|a, b| b.1.cmp(a.1));
    for (msg, n) in reasons.iter().take(15) {
        println!("  {:5}  {}", n, msg);
    }

    if list_fail {
        println!("\nFailing files (out of {}):", failed.len());
        for (p, e) in failed.iter() {
            println!("  {}", p.display());
            println!("    {}", e);
        }
    }
}

fn classify(msg: &str) -> String {
    // Trim location-specific bits to bucket failures by reason.
    let msg = msg.split(" (near:").next().unwrap_or(msg);
    msg.to_string()
}
