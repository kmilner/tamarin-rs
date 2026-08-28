//! Load ladder shared by the whole-corpus integration audits.
#![allow(dead_code)]

#[path = "../../src/test_corpus_common.rs"]
mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;
use tamarin_theory::theory::Theory;

pub use common::{beyond_budget, corpus_root, parse_file, rel, spthy_files};

/// The corpus root and its `.spthy` files, with an explicit opt-out when the
/// examples submodule is unavailable.
pub fn corpus_files(label: &str) -> Option<(PathBuf, Vec<PathBuf>)> {
    let root = corpus_root();
    if !root.is_dir() {
        if std::env::var("TAM_ALLOW_NO_CORPUS").as_deref() == Ok("1") {
            eprintln!("{label}: root {} missing, skipped", root.display());
            return None;
        }
        panic!(
            "corpus root {} missing; set TAM_ALLOW_NO_CORPUS=1 to skip",
            root.display()
        );
    }
    let files = spthy_files(&root);
    Some((root, files))
}

/// A pool whose workers have the same 64 MiB stacks as the web renderer.
pub fn deep_pool() -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool")
}

/// Why a file dropped out of the load ladder.
#[derive(Clone, PartialEq)]
pub enum LoadSkip {
    Listed,
    Parse,
    Elab,
}

fn elaborate_parsed(parsed: &p::Theory) -> Result<Theory, LoadSkip> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tamarin_theory::elaborate::elaborate(parsed).ok()
    }))
    .ok()
    .flatten()
    .ok_or(LoadSkip::Elab)
}

/// Run one file through the load ladder once per integration-test process.
pub fn load_elaborated(path: &Path, root: &Path) -> Result<Arc<Theory>, LoadSkip> {
    if beyond_budget(path, root) {
        return Err(LoadSkip::Listed);
    }
    type Entry = Arc<OnceLock<Result<Arc<Theory>, LoadSkip>>>;
    static CACHE: OnceLock<Mutex<BTreeMap<PathBuf, Entry>>> = OnceLock::new();
    let entry = {
        let mut cache = CACHE
            .get_or_init(|| Mutex::new(BTreeMap::new()))
            .lock()
            .unwrap();
        Arc::clone(
            cache
                .entry(path.to_path_buf())
                .or_insert_with(|| Arc::new(OnceLock::new())),
        )
    };
    entry
        .get_or_init(|| {
            let parsed = parse_file(path).ok_or(LoadSkip::Parse)?;
            elaborate_parsed(&parsed).map(Arc::new)
        })
        .clone()
}

/// Fail rather than silently shrinking a corpus comparison.
pub fn assert_corpus_covered(reached: usize, files: usize) {
    assert!(
        reached * 20 >= files * 19,
        "only {reached} of {files} files reached the comparison"
    );
}
