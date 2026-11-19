//! Process-boundary tests: native-only must not even probe a Maude executable.

use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Fixture {
    dir: PathBuf,
}

impl Fixture {
    fn new(theory: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tamarin-native-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("input.spthy"), theory).unwrap();
        // The marker is a shell builtin, so it works even with an empty PATH.
        let trap = dir.join("maude");
        std::fs::write(
            &trap,
            format!(
                "#!/bin/sh\nprintf called > '{}'/called\nexit 91\n",
                dir.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&trap, std::fs::Permissions::from_mode(0o755)).unwrap();
        Self { dir }
    }

    fn command(&self) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
        cmd.arg("--algebra-backend=native-only")
            .arg(format!("--with-maude={}", self.dir.join("maude").display()))
            .arg("--processors=2")
            .arg("--maude-processes=4")
            .env("PATH", "")
            .env_remove("TAM_RS_NO_LEAN_UNIFY")
            .env_remove("TAM_RS_VERIFY_LEAN_UNIFY")
            .env_remove("TAM_RS_VERIFY_REDUCE_NF");
        cmd
    }

    fn run(&self, args: &[&str]) -> Output {
        let output = self
            .command()
            .args(args)
            .arg(self.dir.join("input.spthy"))
            .output()
            .unwrap();
        assert!(
            !self.dir.join("called").exists(),
            "native-only invoked Maude"
        );
        output
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

const SIMPLE: &str = include_str!("fixtures/native_pairing.spthy");

#[cfg(feature = "lean-unification")]
#[test]
fn native_parse_only_never_probes_or_starts_maude() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.run(&["--parse-only"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(stdout.contains("NativePairing"), "{stdout}");
    assert!(!stderr.contains("Maude tool:"), "{stderr}");
}

#[cfg(feature = "lean-unification")]
#[test]
fn pairing_and_bilinear_proofs_complete_without_probing_or_starting_maude() {
    let nested = SIMPLE.replace(
        "rule Emit:",
        "rule NestedProjection:\n  [In(x)] --[ Seen(fst(snd(x))) ]-> []\n\nrule Emit:",
    );
    for (theory, lemma) in [
        (nested.as_str(), "reachable"),
        (SIMPLE, "reachable"),
        (
            include_str!("fixtures/native_joint_projections.spthy"),
            "projected",
        ),
        (
            include_str!("fixtures/native_commutative.spthy"),
            "recorded",
        ),
    ] {
        let fixture = Fixture::new(theory);
        let output = fixture.run(&["--prove"]);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stdout}\n{stderr}");
        assert!(
            stdout.contains(&format!("{lemma} (exists-trace): verified (2 steps)")),
            "{stdout}"
        );
        assert!(
            stdout.contains("Maude version not used (native-only)"),
            "{stdout}"
        );
        assert!(!stderr.contains("Maude tool:"), "{stderr}");
    }
}

#[cfg(feature = "lean-unification")]
#[test]
fn unsupported_theory_fails_without_publishing_proofs_or_output_files() {
    // Two rules for the same redex give distinct irreducible observations.
    let fixture = Fixture::new(&SIMPLE.replace(
        "rule Emit:",
        "functions: pick/1\nequations: pick(<x,y>) = x, pick(<x,y>) = y\n\nrule Pick:\n  [In(x)] --[ Seen(pick(x)) ]-> []\n\nrule Emit:",
    ));
    let out_path = fixture.dir.join("result.spthy");
    let output = fixture.run(&["--prove", &format!("--output={}", out_path.display())]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stdout}\n{stderr}");
    assert!(
        stderr.contains("native-only backend does not support"),
        "{stderr}"
    );
    assert!(!stdout.contains("verified"), "{stdout}");
    assert!(
        !out_path.exists(),
        "unsupported analysis published an output file"
    );
}

#[cfg(feature = "lean-unification")]
#[test]
fn conflicting_oracle_switch_fails_before_any_tool_probe() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture
        .command()
        .env("TAM_RS_VERIFY_LEAN_UNIFY", "1")
        .arg(fixture.dir.join("input.spthy"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("incompatible with TAM_RS_VERIFY_LEAN_UNIFY"));
    assert!(!fixture.dir.join("called").exists());
}

#[cfg(feature = "lean-unification")]
#[test]
fn interactive_native_mode_is_explicitly_rejected_without_probing() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.run(&["interactive"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("interactive and installation self-tests are not yet supported"));
}

#[cfg(not(feature = "lean-unification"))]
#[test]
fn native_mode_requires_the_lean_feature_before_probing() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.run(&["--prove"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("require a build with --features lean-unification"));
}

#[cfg(feature = "lean-unification")]
#[test]
fn multiset_proof_and_output_complete_without_any_maude_process() {
    let fixture = Fixture::new(include_str!("fixtures/lean_unification.spthy"));
    let out_path = fixture.dir.join("result.spthy");
    let output = fixture.run(&["--prove", &format!("--output={}", out_path.display())]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    for lemma in ["reachable", "conjunction_reachable"] {
        assert!(
            stdout.contains(&format!("{lemma} (exists-trace): verified (4 steps)")),
            "{stdout}"
        );
    }
    let theory = std::fs::read_to_string(out_path).unwrap();
    assert!(
        theory.contains("Maude version not used (native-only)"),
        "{theory}"
    );
    assert!(!stderr.contains("Maude tool:"), "{stderr}");
}

#[cfg(feature = "lean-unification")]
#[test]
fn declared_constructors_proof_completes_without_maude() {
    let fixture = Fixture::new(include_str!("fixtures/native_constructors.spthy"));
    let output = fixture.run(&["--prove"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(
        stdout.contains("reachable (exists-trace): verified"),
        "{stdout}"
    );
}

#[cfg(feature = "lean-unification")]
#[test]
fn cancellation_proves_the_only_possible_residual_without_maude() {
    let fixture = Fixture::new(include_str!("fixtures/native_cancellation.spthy"));
    let output = fixture.run(&["--prove"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(
        stdout.contains("reachable (exists-trace): verified (3 steps)"),
        "{stdout}"
    );
    assert!(
        stdout.contains("only_residual (all-traces): verified (3 steps)"),
        "{stdout}"
    );
}

#[cfg(feature = "lean-unification")]
#[test]
fn protocol_can_select_the_shared_witness_branch_without_maude() {
    let fixture = Fixture::new(include_str!("fixtures/native_shared_offset.spthy"));
    let output = fixture.run(&["--prove"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(
        stdout.contains("shared_reachable (exists-trace): verified (3 steps)"),
        "{stdout}"
    );
}
