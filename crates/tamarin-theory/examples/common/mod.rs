//! Shared setup for the dev example binaries: read → parse → elaborate a
//! theory file and boot a Maude handle on its full signature, plus
//! corpus-root resolution and `.spthy` collection for the corpus walkers.
//!
//! Lives in `examples/common/` (a subdirectory, so cargo does not treat it
//! as an example target); each example pulls it in with `mod common;`.
//! Individual examples use only a subset of these helpers, so each is
//! marked `#[allow(dead_code)]`.

use std::path::{Path, PathBuf};

use tamarin_term::maude_proc::MaudeHandle;

/// The examples corpus root: `$CORPUS_ROOT` if set, else the
/// `tamarin-prover/examples/` directory in the submodule, relative to this
/// crate's manifest.
#[allow(dead_code)]
pub fn corpus_root() -> PathBuf {
    std::env::var("CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
        })
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

/// Read, parse, and elaborate `theory_path`, then start Maude on the
/// elaborated signature (`$MAUDE_PATH` overrides the binary, else `maude`
/// on `PATH`).  The elaborated signature carries the full `MaudeSig`
/// (aenc/pk/user-declared symbols); booting Maude on the default sig would
/// leave those symbols unparseable and corrupt any downstream unification.
#[allow(dead_code)]
pub fn load_theory_with_maude(
    theory_path: &str,
) -> (
    tamarin_parser::ast::Theory,
    tamarin_theory::theory::Theory,
    MaudeHandle,
) {
    let source = std::fs::read_to_string(theory_path).expect("read theory");
    let parsed = tamarin_parser::parse_theory(&source, &[]).expect("parse theory");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude_path = std::env::var("MAUDE_PATH").unwrap_or_else(|_| "maude".to_string());
    let maude = MaudeHandle::start(&maude_path, elaborated.signature.maude_sig.clone())
        .expect("start maude");
    (parsed, elaborated, maude)
}
