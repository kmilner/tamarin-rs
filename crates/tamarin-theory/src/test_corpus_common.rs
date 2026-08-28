//! Corpus discovery and parsing shared by this crate's unit and integration
//! test binaries. Each binary gets its own process-local cache, but both
//! compile this implementation.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;

/// Examples beyond the corpus tests' budget. The accountability lemmas of
/// this family grow geometrically with the session count.
pub const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// The examples tree, or the override in `CORPUS_ROOT`.
pub fn corpus_root() -> PathBuf {
    std::env::var("CORPUS_ROOT").map_or_else(
        |_| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples"),
        PathBuf::from,
    )
}

/// `path` relative to the corpus root, as reports name it.
pub fn rel<'a>(path: &'a Path, root: &Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

/// Every `.spthy` file under `root`, in path order.
pub fn spthy_files(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<_> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .map(|entry| entry.into_path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "spthy"))
        .collect();
    files.sort();
    files
}

/// Whether [`BEYOND_BUDGET`] lists `path`.
pub fn beyond_budget(path: &Path, root: &Path) -> bool {
    BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref())
}

/// Read and parse one example file once per test process, resolving includes
/// against its directory and retrying diff-operator theories with `-D=diff`.
pub fn parse_file(path: &Path) -> Option<Arc<p::Theory>> {
    type Entry = Arc<OnceLock<Option<Arc<p::Theory>>>>;
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
            let src = std::fs::read_to_string(path).ok()?;
            let base = path.parent().map(Path::to_path_buf);
            std::panic::catch_unwind(|| {
                tamarin_parser::parser::parse_theory_with_base(&src, &[], base.clone())
                    .or_else(|_| {
                        tamarin_parser::parser::parse_theory_with_base(&src, &["diff"], base)
                    })
                    .ok()
                    .map(Arc::new)
            })
            .ok()
            .flatten()
        })
        .clone()
}
