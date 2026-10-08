// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Embed Git revision and build timestamp for `--version` and the
//! `Generated from:` footer of emitted theories.

// Cargo build directives use println!.
#![allow(clippy::disallowed_macros)]

use std::path::{Path, PathBuf};
use std::process::Command;

fn git(root: &Path, args: &[&str]) -> Option<String> {
    Command::new("git")
        .current_dir(root)
        // Metadata inspection must not refresh the index we watch below:
        // that would cause an unnecessary rebuild on the next Cargo run.
        .env("GIT_OPTIONAL_LOCKS", "0")
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
}

fn is_repository_root(root: &Path) -> bool {
    git(root, &["rev-parse", "--show-toplevel"])
        .and_then(|path| Path::new(&path).canonicalize().ok())
        .is_some_and(|path| path == root)
}

fn watch_git_inputs(root: &Path) {
    // Resolve Git's real paths: in a worktree .git is a file, and refs live
    // in the common repository. Watching refs also catches packing/unpacking.
    for name in ["HEAD", "index", "refs", "packed-refs"] {
        if let Some(path) = git(root, &["rev-parse", "--git-path", name]) {
            let path = root.join(path);
            if path.exists() {
                println!("cargo:rerun-if-changed={}", path.display());
            }
        }
    }
    // Explicit watches replace Cargo's default source scan. Watch workspace
    // sources individually to refresh the dirty marker without scanning target/.
    if let Some(files) = git(
        root,
        &[
            "ls-files",
            "--cached",
            "--others",
            "--exclude-standard",
            "-z",
        ],
    ) {
        for file in files.split('\0').filter(|file| !file.is_empty()) {
            let path = root.join(file);
            // Upstream tracks dangling .cabal-sandbox symlinks. They are not
            // source inputs; watching them makes fresh builds appear stale.
            if path.is_symlink() && !path.exists() {
                continue;
            }
            if path.is_dir() {
                // A tracked directory is a submodule; watch its source and
                // Git metadata without including its ignored build outputs.
                if is_repository_root(&path) {
                    watch_git_inputs(&path);
                }
            } else {
                // Watch deleted paths to catch restoration without an index
                // change, at the cost of repeat builds while they remain absent.
                println!("cargo:rerun-if-changed={}", path.display());
            }
        }
    }
}

fn main() {
    let root =
        PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo manifest directory"))
            .join("../..")
            .canonicalize()
            .expect("workspace directory");
    // Archives inside another repository must not inherit its revision.
    let repository = is_repository_root(&root);
    // Git revision (full sha + branch).
    let mut rev = repository
        .then(|| git(&root, &["rev-parse", "HEAD"]))
        .flatten()
        .unwrap_or_else(|| "unknown".to_string());
    // Rust build identity is separate from the upstream compatibility version.
    let mut rust_version: String = rev.chars().take(7).collect();
    let branch = repository
        .then(|| git(&root, &["rev-parse", "--abbrev-ref", "HEAD"]))
        .flatten()
        .unwrap_or_else(|| "unknown".to_string());

    // Match HS gitVersion (Console.hs): untracked files count as dirty, and
    // generated-theory provenance preserves its "uncommited" spelling.
    // The short Rust identity uses the conventional -dirty suffix.
    let dirty = repository
        && git(&root, &["status", "--porcelain"]).is_some_and(|status| !status.is_empty());
    if dirty {
        rev.push_str(" (with uncommited changes)");
        rust_version.push_str("-dirty");
    }

    // UTC build time. Parity checks ignore this line; unlike HS compileTime
    // (Console.hs), this format omits sub-second precision.
    let ts = Command::new("date")
        .args(["-u", "+%Y-%m-%d %H:%M:%S UTC"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=TAMARIN_GIT_REV={}", rev);
    println!("cargo:rustc-env=TAMARIN_RS_VERSION={}", rust_version);
    println!("cargo:rustc-env=TAMARIN_GIT_BRANCH={}", branch);
    println!("cargo:rustc-env=TAMARIN_BUILD_TIMESTAMP={}", ts);
    if repository {
        watch_git_inputs(&root);
    }
}
