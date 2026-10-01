//! Shared helpers for the tamarin-parser dev example binaries: corpus-root
//! resolution and `.spthy` collection.
//!
//! Lives in `examples/common/` (a subdirectory, so cargo does not treat it
//! as an example target); each example pulls it in with `mod common;`.
//! Individual examples use only a subset of these helpers, so each is
//! marked `#[allow(dead_code)]`.

use std::path::{Path, PathBuf};

#[allow(dead_code)]
pub fn corpus_root() -> PathBuf {
    tamarin_test_support::corpus_root()
}

/// Collect every `.spthy` file under `root`, sorted by path.
#[allow(dead_code)]
pub fn collect_spthy(root: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spthy"))
        .map(|e| e.path().to_path_buf())
        .collect();
    files.sort();
    files
}
