//! Census of the stored proof skeletons in the examples tree: how many
//! lemmas carry one, how many of those the proof parser turns into a
//! structured tree, and which `GoalSpec` kind each `solve(...)` step of
//! those trees carries.  The kind table is the population the goal
//! grammar, the replay matcher and the goal printer work on; the 432-file
//! prove and pretty gates reach a small fraction of it, so a change to any
//! of the three is measured against this table first.
//!
//! Diff lemmas are tallied in their own row and asserted on nowhere: a
//! diff proof is written in the `rule-equivalence` / `backward-search` /
//! `step( ... )` grammar, which `parse_proof_tree` does not accept, so
//! every such skeleton is `tree: None` and none of the `solve(...)` text
//! inside one becomes a `GoalSpec`.  The diff skeletons that do carry a
//! tree are the bare `by sorry` ones.
//!
//! A `tree_none` of zero over the regular lemmas is what makes the strict
//! grammar safe: every stored step is a method `proof_method` reads and
//! every stored goal one `Parser::goal` accepts.
//!
//! The load and `--parse-only` sweeps that widen the net beyond the gate
//! corpus run over the files this grep lists, so their list stays
//! reproducible:
//!
//! ```text
//! grep -rlE '(^|[^A-Za-z0-9_])(solve\(|qed|SOLVED)' tamarin-prover/examples --include='*.spthy'
//! ```

use crate::test_corpus::{beyond_budget, corpus_root, parse_file, rel, spthy_files};
use rayon::prelude::*;
use std::path::Path;
use std::time::Instant;
use tamarin_parser::ast as p;

/// Tallies over one group of lemmas — the regular ones, or the diff ones.
#[derive(Default)]
struct Census {
    /// Files with at least one lemma of the group carrying a skeleton.
    files: usize,
    /// Lemmas carrying a proof skeleton.
    skeletons: usize,
    /// Skeletons `try_proof_skeleton` left without a structured tree.
    tree_none: usize,
    /// Proof steps across the structured trees.
    steps: usize,
    /// `solve(...)` steps by `GoalSpec` kind.
    action: usize,
    premise: usize,
    chain: usize,
    split: usize,
    disj: usize,
    subterm: usize,
}

/// The column headers of [`Census::row`], in its order.
const COLUMNS: &str = "  group    files skeletons tree_none    steps   action  premise    chain    split     disj  subterm";

impl Census {
    fn add(&mut self, o: &Census) {
        self.files += usize::from(o.skeletons > 0);
        self.skeletons += o.skeletons;
        self.tree_none += o.tree_none;
        self.steps += o.steps;
        self.action += o.action;
        self.premise += o.premise;
        self.chain += o.chain;
        self.split += o.split;
        self.disj += o.disj;
        self.subterm += o.subterm;
    }

    fn row(&self, group: &str) -> String {
        format!(
            "  {group:7} {:6} {:9} {:9} {:8} {:8} {:8} {:8} {:8} {:8} {:8}",
            self.files,
            self.skeletons,
            self.tree_none,
            self.steps,
            self.action,
            self.premise,
            self.chain,
            self.split,
            self.disj,
            self.subterm,
        )
    }

    fn count_skeleton(&mut self, skel: &p::ProofSkeleton) {
        self.skeletons += 1;
        match &skel.tree {
            Some(tree) => self.count_tree(tree),
            None => self.tree_none += 1,
        }
    }

    fn count_tree(&mut self, tree: &p::ParsedProofTree) {
        self.steps += 1;
        if let p::ParsedMethod::SolveGoal(goal) = &tree.method {
            match goal {
                p::GoalSpec::Action { .. } => self.action += 1,
                p::GoalSpec::Premise { .. } => self.premise += 1,
                p::GoalSpec::Chain { .. } => self.chain += 1,
                p::GoalSpec::Split { .. } => self.split += 1,
                p::GoalSpec::Disj { .. } => self.disj += 1,
                p::GoalSpec::Subterm { .. } => self.subterm += 1,
            }
        }
        for (_, sub) in &tree.cases {
            self.count_tree(sub);
        }
    }
}

/// What the census records for one file.
#[derive(Default)]
struct FileCensus {
    regular: Census,
    diff: Census,
    /// The file is one of `test_corpus::BEYOND_BUDGET`.
    skipped_listed: bool,
    /// Neither parse of the file produced a theory.
    unparsed: bool,
    /// The file carries a skeleton, and lifting its embedded restrictions
    /// or elaborating it failed.
    unelaborated: bool,
}

fn file_census(path: &Path, root: &Path) -> FileCensus {
    let mut rep = FileCensus::default();
    if beyond_budget(path, root) {
        rep.skipped_listed = true;
        return rep;
    }
    let Some(parsed) = parse_file(path) else {
        rep.unparsed = true;
        return rep;
    };
    for item in &parsed.items {
        match item {
            p::TheoryItem::Lemma(lem) => {
                if let Some(skel) = &lem.proof {
                    rep.regular.count_skeleton(skel);
                }
            }
            p::TheoryItem::DiffLemma(lem) => {
                if let Some(skel) = &lem.proof {
                    rep.diff.count_skeleton(skel);
                }
            }
            _ => {}
        }
    }
    if rep.regular.skeletons + rep.diff.skeletons == 0 {
        return rep;
    }
    // The step the production drivers run between the parse and any reader
    // of a stored goal.
    let elaborated = matches!(
        std::panic::catch_unwind(|| crate::elaborate::elaborate(&parsed).is_ok()),
        Ok(true)
    );
    rep.unelaborated = !elaborated;
    rep
}

#[test]
fn corpus_stored_proof_census() {
    let root = corpus_root();
    if !root.is_dir() {
        if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
            eprintln!("stored proofs: root {} missing, skipped", root.display());
            return;
        }
        panic!(
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
    }
    let files = spthy_files(&root);
    let start = Instant::now();
    // The parser recurses along the input, so the workers get the 64 MiB
    // stacks the CLI parses on (run.rs).
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool");
    let reports: Vec<FileCensus> = pool.install(|| {
        files
            .par_iter()
            .map(|path| file_census(path, &root))
            .collect()
    });
    let mut regular = Census::default();
    let mut diff = Census::default();
    let mut skipped_listed = 0usize;
    let mut unparsed = 0usize;
    let mut unelaborated = Vec::new();
    for (rep, path) in reports.iter().zip(&files) {
        regular.add(&rep.regular);
        diff.add(&rep.diff);
        skipped_listed += usize::from(rep.skipped_listed);
        unparsed += usize::from(rep.unparsed);
        if rep.unelaborated {
            unelaborated.push(rel(path, &root).display().to_string());
        }
    }
    eprintln!(
        "stored proofs: files={} skipped_listed={skipped_listed} unparsed={unparsed} \
         unelaborated={} wall={:?}",
        files.len(),
        unelaborated.len(),
        start.elapsed()
    );
    eprintln!("{COLUMNS}");
    eprintln!("{}", regular.row("regular"));
    eprintln!("{}", diff.row("diff"));
    for name in &unelaborated {
        eprintln!("UNELABORATED {name}");
    }

    assert!(
        regular.skeletons > 0,
        "no stored proof skeleton found under {}",
        root.display()
    );
    // A skeleton without a tree, or a step the replay walker cannot name,
    // sends its whole lemma to the auto-prover instead of replaying it.
    assert_eq!(
        regular.tree_none, 0,
        "regular lemmas with an unparsed proof"
    );
    // No stored goal of a regular lemma is a subterm split.
    assert_eq!(regular.subterm, 0, "stored subterm goals");
    for (kind, n) in [
        ("action", regular.action),
        ("premise", regular.premise),
        ("chain", regular.chain),
        ("split", regular.split),
        ("disj", regular.disj),
    ] {
        assert!(n > 0, "no stored {kind} goal to exercise");
    }
    // Every stored goal reaches its readers through an elaborated theory.
    assert!(
        unelaborated.is_empty(),
        "{} files carry a stored proof and do not elaborate: {:#?}",
        unelaborated.len(),
        unelaborated.iter().take(20).collect::<Vec<_>>()
    );
}
