//! The examples-tree walker this crate's corpus tests share: the corpus
//! root, the file list, the budget list and the parse step each of those
//! tests starts from.  The corpus nets under `tests/` use the same walker
//! from `tests/corpus_util/mod.rs`, which crate privacy keeps separate
//! from this one.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;

/// Examples beyond the corpus tests' budget, reported as `skipped_listed`:
/// the accountability lemmas of the mixvote multi-session family grow
/// geometrically with the session count, so a session-4 lemma takes minutes
/// through the renders of `corpus_lnformula_doc_matches_ast_printer` and
/// session 5 overflows the stack.  Neither file is in the prove or pretty
/// gate corpus (scripts/parity_corpus.txt) and neither carries a stored
/// proof.
pub(crate) const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// The examples tree, or the override in `CORPUS_ROOT`.
pub(crate) fn corpus_root() -> PathBuf {
    if let Ok(root) = std::env::var("CORPUS_ROOT") {
        return PathBuf::from(root);
    }
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
}

/// `path` relative to the corpus root, as the listing and the report name it.
pub(crate) fn rel<'a>(path: &'a Path, root: &Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

/// Every `.spthy` file under `root`, in path order.
pub(crate) fn spthy_files(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.extension().is_some_and(|x| x == "spthy"))
        .collect();
    files.sort();
    files
}

/// Whether [`BEYOND_BUDGET`] lists `path`.
pub(crate) fn beyond_budget(path: &Path, root: &Path) -> bool {
    BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref())
}

/// Read and parse one example file, resolving its `#include`s against its
/// own directory.  `None` when the read fails, when neither parse succeeds
/// or when the parser panics.  A diff-operator theory is parsed again with
/// the `diff` define, the way `-D=diff` enables the operator on the CLI.
pub(crate) fn parse_file(path: &Path) -> Option<Arc<p::Theory>> {
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

/// Elaborate a cached parse once per path. Concurrent corpus tests share the
/// result, including a stable description of an elaboration failure or panic.
pub(crate) fn elaborate_file(path: &Path) -> Result<Arc<crate::theory::Theory>, Arc<str>> {
    type Outcome = Result<Arc<crate::theory::Theory>, Arc<str>>;
    type Entry = Arc<OnceLock<Outcome>>;
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
            let parsed = parse_file(path).ok_or_else(|| Arc::from("parse failed"))?;
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::elaborate::elaborate(&parsed)
            })) {
                Ok(Ok(theory)) => Ok(Arc::new(theory)),
                Ok(Err(error)) => Err(Arc::from(error.message)),
                Err(_) => Err(Arc::from("elaboration panicked")),
            }
        })
        .clone()
}
