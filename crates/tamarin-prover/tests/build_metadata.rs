//! Exercise the real build script in tiny offline Cargo workspaces. These
//! checks must rebuild: inspecting an already-built binary cannot catch stale
//! Cargo build-script metadata after source edits or Git operations.

use std::path::{Path, PathBuf};
use std::process::Command;

struct Fixture {
    dir: PathBuf,
    root: PathBuf,
}

fn command(cwd: &Path, program: &str, args: &[&str]) -> String {
    let output = Command::new(program)
        .current_dir(cwd)
        .args(args)
        .output()
        .expect("run fixture command");
    assert!(
        output.status.success(),
        "{program} {args:?}:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

impl Fixture {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "tamarin_build_metadata_{name}_{}",
            std::process::id()
        ));
        std::fs::create_dir(&dir).unwrap();
        let root = dir.join("source");
        let src = root.join("crates/tamarin-prover/src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"crates/tamarin-prover\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        std::fs::write(root.join(".gitignore"), "/target/\n").unwrap();
        std::fs::write(
            root.join("sibling.rs"),
            "// another workspace crate's source\n",
        )
        .unwrap();
        std::fs::write(
            src.parent().unwrap().join("Cargo.toml"),
            "[package]\nname = \"metadata-fixture\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        std::fs::write(
            src.join("main.rs"),
            "fn main() { println!(\"{}\", env!(\"TAMARIN_RS_VERSION\")); }\n",
        )
        .unwrap();
        std::fs::write(
            src.parent().unwrap().join("build.rs"),
            include_str!("../build.rs"),
        )
        .unwrap();
        command(&root, env!("CARGO"), &["generate-lockfile", "--offline"]);
        Self { dir, root }
    }

    fn git(&self, args: &[&str]) -> String {
        command(&self.root, "git", args)
    }

    fn init_git(root: &Path) {
        command(root, "git", &["init", "-q"]);
        command(root, "git", &["config", "user.name", "Metadata test"]);
        command(
            root,
            "git",
            &["config", "user.email", "metadata@example.invalid"],
        );
        command(root, "git", &["config", "commit.gpgsign", "false"]);
        command(root, "git", &["add", "."]);
        command(root, "git", &["commit", "-qm", "fixture"]);
    }

    fn version(&self) -> String {
        command(
            &self.root,
            env!("CARGO"),
            &[
                "run",
                "--quiet",
                "--offline",
                "--target-dir",
                self.root.join("target").to_str().unwrap(),
            ],
        )
    }

    fn assert_cached(&self) {
        let executable = self.root.join("target/debug/metadata-fixture");
        let before = std::fs::metadata(&executable).unwrap().modified().unwrap();
        self.version();
        assert_eq!(
            std::fs::metadata(executable).unwrap().modified().unwrap(),
            before,
            "a no-op build must reuse its binary"
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

#[test]
fn version_refreshes_after_source_edits_restores_and_commits() {
    let f = Fixture::new("refresh");
    Fixture::init_git(&f.root);
    // Both packed-refs and a loose current branch ref must exist: an absent
    // watched file can otherwise accidentally force every build to rerun.
    f.git(&["pack-refs", "--all"]);
    f.git(&["commit", "--allow-empty", "-qm", "loose ref"]);
    let hash = f.git(&["rev-parse", "HEAD"])[..7].to_string();
    assert_eq!(f.version(), hash);
    for file in ["crates/tamarin-prover/src/main.rs", "sibling.rs"] {
        let path = f.root.join(file);
        let original = std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path, format!("{original}\n// local edit\n")).unwrap();
        assert_eq!(f.version(), format!("{hash}-dirty"), "{file}");
        f.assert_cached();
        f.git(&["restore", file]);
        assert_eq!(f.version(), hash, "restored {file}");
        f.assert_cached();
    }
    f.git(&["commit", "--allow-empty", "-qm", "next version"]);
    assert_eq!(f.version(), &f.git(&["rev-parse", "HEAD"])[..7]);
    f.assert_cached();
}

#[test]
fn source_archive_does_not_adopt_parent_repository_version() {
    let f = Fixture::new("archive");
    assert_eq!(f.version(), "unknown");
    // Same source archive, now surrounded by an unrelated parent repository.
    Fixture::init_git(&f.dir);
    command(
        &f.root,
        env!("CARGO"),
        &[
            "clean",
            "--target-dir",
            f.root.join("target").to_str().unwrap(),
        ],
    );
    assert_eq!(f.version(), "unknown");
}

#[cfg(unix)]
#[test]
fn dangling_tracked_symlink_does_not_invalidate_a_fresh_build() {
    let f = Fixture::new("dangling_symlink");
    // Upstream tracks lib/utils/.cabal-sandbox, whose target is normally absent.
    std::os::unix::fs::symlink("missing-cabal-sandbox", f.root.join(".cabal-sandbox")).unwrap();
    Fixture::init_git(&f.root);
    assert_eq!(f.version(), &f.git(&["rev-parse", "HEAD"])[..7]);
    let gate = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/gate_common.sh");
    let executable = f.root.join("target/debug/metadata-fixture");
    command(
        &f.root,
        "bash",
        &[
            "-c",
            "unset ALLOW_STALE_BIN; source \"$1\"; rs_stale_check \"$2\" \"$3\"",
            "check",
            gate.to_str().unwrap(),
            executable.to_str().unwrap(),
            f.root.to_str().unwrap(),
        ],
    );
    f.assert_cached();
}

#[test]
fn worktree_version_refreshes_after_commit() {
    let mut f = Fixture::new("worktree");
    Fixture::init_git(&f.root);
    let worktree = f.dir.join("worktree");
    f.git(&["worktree", "add", "--detach", worktree.to_str().unwrap()]);
    f.root = worktree;
    assert_eq!(f.version(), &f.git(&["rev-parse", "HEAD"])[..7]);
    f.git(&["commit", "--allow-empty", "-qm", "worktree version"]);
    assert_eq!(f.version(), &f.git(&["rev-parse", "HEAD"])[..7]);
}
