//! Quick proof-tree dumper for an HS-vs-Rust shape comparison.
//!
//! Usage: `cargo run --example dump_proof -- <theory.spthy> <lemma>`

// Example/dev tool: dumps the proof tree to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use tamarin_theory::prove::prove_lemma;
use tamarin_theory::proof_skeleton::render;

mod common;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: dump_proof <theory.spthy> <lemma>");
        std::process::exit(2);
    }
    let theory_path = &args[1];
    let lemma = &args[2];

    let (parsed, _elaborated, maude) = common::load_theory_with_maude(theory_path);

    let root = prove_lemma(&parsed, lemma, maude, 500).expect("prove");
    let steps = count_steps(&root);
    eprintln!("=== {} proof tree (status={:?}, children={}, steps={}) ===",
        lemma, root.status, root.children.len(), steps);
    println!("{}", render(&root));
}

fn count_steps(node: &tamarin_theory::constraint::solver::search::ProofNode) -> usize {
    1 + node.children.values().map(count_steps).sum::<usize>()
}
