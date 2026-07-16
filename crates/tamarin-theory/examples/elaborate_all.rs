//! Walks `examples/`, parses each `.spthy` and runs elaboration. Reports
//! how many files we can carry through parser → typed Theory.

// Example/dev tool: reports elaboration results to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::env;
use std::fs;
use std::path::PathBuf;

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::{elaborate, elaborate_with_diagnostics};

mod common;
use common::{collect_spthy, corpus_root};

fn main() {
    let root = env::args().nth(1).map(PathBuf::from).unwrap_or_else(corpus_root);

    let files = collect_spthy(&root);

    let verbose = env::var("VERBOSE").is_ok();
    let mut total = 0;
    let mut parse_ok = 0;
    let mut elab_ok = 0;
    let mut sample_diags: Vec<String> = Vec::new();
    let mut total_lemmas = 0u64;
    let mut total_restrictions = 0u64;
    let mut guarded_lemmas = 0u64;
    let mut guarded_restrictions = 0u64;
    let mut files_with_no_guard_diags = 0u64;
    let mut errors_by_kind: std::collections::BTreeMap<String, usize> = Default::default();

    for path in &files {
        total += 1;
        let src = match fs::read_to_string(path) { Ok(s) => s, _ => continue };
        let p = match parse_theory(&src, &["diff"]) {
            Ok(t) => { parse_ok += 1; t }
            Err(_) => continue,
        };
        match elaborate_with_diagnostics(&p) {
            Ok((t, diags)) => {
                elab_ok += 1;
                let n_lem = t.lemmas().count() as u64;
                let n_res = t.restrictions().count() as u64;
                total_lemmas += n_lem;
                total_restrictions += n_res;
                let mut bad_lem = 0u64;
                let mut bad_res = 0u64;
                for d in &diags {
                    if d.item.starts_with("Lemma") { bad_lem += 1; }
                    else { bad_res += 1; }
                }
                guarded_lemmas += n_lem.saturating_sub(bad_lem);
                guarded_restrictions += n_res.saturating_sub(bad_res);
                if diags.is_empty() { files_with_no_guard_diags += 1; }
                if verbose && !diags.is_empty() && sample_diags.len() < 30 {
                    for d in &diags {
                        sample_diags.push(format!("{}: {} → {}",
                            path.display(), d.item, d.message));
                    }
                }
            }
            Err(e) => {
                let _ = elaborate(&p); // for stats parity
                let key = first_phrase(&e.message);
                *errors_by_kind.entry(key).or_insert(0) += 1;
            }
        }
    }
    println!("Files:                  {}", total);
    println!("Parsed:                 {} ({:.1}%)", parse_ok, 100.0 * parse_ok as f64 / total.max(1) as f64);
    println!("Elaborated:             {} ({:.1}%)", elab_ok, 100.0 * elab_ok as f64 / total.max(1) as f64);
    println!("Files with 0 guard diag {} ({:.1}%)",
        files_with_no_guard_diags,
        100.0 * files_with_no_guard_diags as f64 / elab_ok.max(1) as f64);
    println!("Lemmas:                 {} ({} guarded, {:.1}%)",
        total_lemmas, guarded_lemmas,
        100.0 * guarded_lemmas as f64 / total_lemmas.max(1) as f64);
    println!("Restrictions:           {} ({} guarded, {:.1}%)",
        total_restrictions, guarded_restrictions,
        100.0 * guarded_restrictions as f64 / total_restrictions.max(1) as f64);
    if !sample_diags.is_empty() {
        println!("\nSample guardedness diagnostics:");
        for d in sample_diags.iter().take(30) {
            println!("  {}", d);
        }
    }
    if !errors_by_kind.is_empty() {
        let mut sorted: Vec<_> = errors_by_kind.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        println!("\nElaboration error categories:");
        for (k, n) in sorted.iter().take(15) {
            println!("  {:5}  {}", n, k);
        }
    }
}

fn first_phrase(s: &str) -> String {
    s.split('`').next().unwrap_or(s).trim().to_string()
}
