//! The examples-tree walker the corpus nets in this directory share: the
//! corpus root, the file list, the budget list and the load ladder each net
//! starts from.  The in-crate corpus nets use the same walker from
//! `src/test_corpus.rs`, which crate privacy keeps separate from this one.
//! Each test binary uses the subset it needs, so the unused remainder is
//! allowed per binary.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};
use tamarin_parser::ast as p;
use tamarin_theory::theory::Theory;

/// Examples beyond the corpus nets' budget, reported as a listed skip: the
/// accountability lemmas of the mixvote multi-session family grow
/// geometrically with the session count.  Neither file is in the prove or
/// pretty gate corpus (scripts/parity_corpus.txt).
pub const BEYOND_BUDGET: &[&str] = &[
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-4-fixed.spthy",
    "sapic/deprecated/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session-5-fixed.spthy",
];

/// Whether [`BEYOND_BUDGET`] lists `path`.
pub fn beyond_budget(path: &Path, root: &Path) -> bool {
    BEYOND_BUDGET.contains(&rel(path, root).to_string_lossy().as_ref())
}

/// The examples tree, or the override in `CORPUS_ROOT`.
pub fn corpus_root() -> PathBuf {
    if let Ok(root) = std::env::var("CORPUS_ROOT") {
        return PathBuf::from(root);
    }
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
}

/// `path` relative to the corpus root, as the report names it.
pub fn rel<'a>(path: &'a Path, root: &Path) -> &'a Path {
    path.strip_prefix(root).unwrap_or(path)
}

/// Every `.spthy` file under `root`, in path order.
pub fn spthy_files(root: &Path) -> Vec<PathBuf> {
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

/// The corpus root and its `.spthy` files.  `None` when the root is missing
/// and `TAM_ALLOW_NO_CORPUS=1` allows the skip; `label` names the net in the
/// skip line.
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

/// A pool whose workers can take the parser's, the translations' and the
/// Doc builders' recursion along the input; the web server renders on
/// 64 MiB tokio threads (run.rs), so the workers get the same stacks.
pub fn deep_pool() -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build()
        .expect("rayon pool")
}

/// Read and parse one example file, resolving its `#include`s against its
/// own directory.  `None` when the read fails, when neither parse succeeds
/// or when the parser panics.  A diff-operator theory is parsed again with
/// the `diff` define, the way `-D=diff` enables the operator on the CLI.
pub fn parse_file(path: &Path) -> Option<p::Theory> {
    let src = std::fs::read_to_string(path).ok()?;
    let base = path.parent().map(Path::to_path_buf);
    let parsed = std::panic::catch_unwind(|| {
        tamarin_parser::parser::parse_theory_with_base(&src, &[], base.clone())
            .or_else(|_| tamarin_parser::parser::parse_theory_with_base(&src, &["diff"], base))
            .ok()
    });
    parsed.ok().flatten()
}

/// Why a file dropped out of the load ladder.
#[derive(Clone, PartialEq)]
pub enum LoadSkip {
    /// The file is one of [`BEYOND_BUDGET`].
    Listed,
    /// The read failed, neither parse succeeded, or the parser panicked.
    Parse,
    /// Elaboration failed or panicked.
    Elab,
}

/// Elaborate a parsed theory, the step the driver runs after the parse; a
/// failure or a panic in it is [`LoadSkip::Elab`].
pub fn elaborate_parsed(parsed: &p::Theory) -> Result<Theory, LoadSkip> {
    let elab = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tamarin_theory::elaborate::elaborate(parsed).ok()
    }));
    match elab {
        Ok(Some(elab)) => Ok(elab),
        _ => Err(LoadSkip::Elab),
    }
}

/// Run one file through the load ladder once per integration-test process.
/// Concurrent audits share a per-path `OnceLock`, so parsing and elaboration
/// are single-flight without serialising different files.
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

/// A comparison over the corpus is a net only while it covers the tree: a
/// change that makes a stage of the load ladder reject files has to fail
/// here instead of shrinking the comparison.  The tree has 19 parser
/// rejects in 1037 files.
pub fn assert_corpus_covered(reached: usize, files: usize) {
    assert!(
        reached * 20 >= files * 19,
        "only {reached} of {files} files reached the comparison"
    );
}
