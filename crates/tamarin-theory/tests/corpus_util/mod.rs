//! Load ladder shared by the whole-corpus integration audits.
#![allow(dead_code)]

#[path = "../../src/test_corpus_common.rs"]
mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;
use tamarin_theory::theory::Theory;

pub use common::{
    beyond_budget, corpus_root, parse_file, rel, spthy_files, EXPECTED_LOAD_SKIPS, SKIP_ELAB,
    SKIP_LISTED, SKIP_PARSE,
};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LoadSkip {
    Listed,
    Parse,
    Elab,
}

impl LoadSkip {
    pub fn reason(self) -> &'static str {
        match self {
            LoadSkip::Listed => SKIP_LISTED,
            LoadSkip::Parse => SKIP_PARSE,
            LoadSkip::Elab => SKIP_ELAB,
        }
    }
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

/// Require the exact reviewed set of files that may stop before an audit.
/// A percentage floor lets a new rejection silently replace a repaired one;
/// comparing `(path, reason)` rows makes every change to coverage explicit.
pub fn assert_expected_skips<'a>(
    root: &Path,
    observed: impl IntoIterator<Item = (&'a Path, &'static str)>,
    expected: &[(&str, &str)],
) {
    let mut actual: Vec<(String, &'static str)> = observed
        .into_iter()
        .map(|(path, reason)| (rel(path, root).display().to_string(), reason))
        .collect();
    actual.sort();
    let mut expected: Vec<(String, &str)> = expected
        .iter()
        .map(|(path, reason)| ((*path).to_owned(), *reason))
        .collect();
    expected.sort();
    assert_eq!(actual, expected, "corpus skip ledger changed");
}
