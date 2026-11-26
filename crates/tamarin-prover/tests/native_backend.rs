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
        self.command_on("native-only")
    }

    fn command_on(&self, backend: &str) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
        cmd.arg(format!("--algebra-backend={backend}"))
            .arg(format!("--with-maude={}", self.dir.join("maude").display()))
            .arg("--processors=2")
            .arg("--maude-processes=4")
            .env("PATH", "")
            .env_remove("TAM_RS_NATIVE_REFERENCE")
            .env_remove("TAM_RS_NATIVE_REFERENCE_VARIANTS")
            .env_remove("TAM_RS_VARIANT_CHECK_WORK")
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
fn reference_proves_mixed_subterm_and_reducible_ground_equations_with_dh() {
    let fixture = Fixture::new(include_str!("fixtures/native_mixed_subterms.spthy"));
    let output = fixture
        .command()
        .env("TAM_RS_NATIVE_REFERENCE", "1")
        .args(["--processors", "1"])
        .arg("--prove")
        .arg(fixture.dir.join("input.spthy"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("recovered (exists-trace): verified"),
        "{stdout}"
    );
    assert!(!stdout.contains("wellformedness check failed"), "{stdout}");
    assert!(!fixture.dir.join("called").exists());
}

#[cfg(feature = "lean-unification")]
#[test]
fn user_equation_chain_and_pairing_prove_both_traces_without_maude() {
    let fixture = Fixture::new(include_str!("fixtures/native_user_equations_pairing.spthy"));
    for (reference, variants) in [("0", "0"), ("0", "1"), ("1", "0")] {
        let output = fixture
            .command()
            .env("TAM_RS_NATIVE_REFERENCE", reference)
            .env("TAM_RS_NATIVE_REFERENCE_VARIANTS", variants)
            .arg("--prove")
            .arg(fixture.dir.join("input.spthy"))
            .output()
            .unwrap();
        assert!(!fixture.dir.join("called").exists());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        for lemma in ["specialized", "open_case"] {
            assert!(
                stdout.contains(&format!("{lemma} (exists-trace): verified")),
                "{stdout}"
            );
        }
        assert!(!stdout.contains("wellformedness check failed"), "{stdout}");
    }
}

/// Native-only uses the families of the Rust variant solvers only after the
/// Lean certificate checker accepted them: they count as proved on a table
/// the certifier accepts and as assumed on any other table, and never as
/// native Rust. A family that does not fit in the checker's work bound fails
/// the run instead of being used, and the bound changes no result otherwise.
#[cfg(feature = "lean-unification")]
#[test]
fn rust_variants_are_checked_and_count_as_proved_or_assumed() {
    for (theory, origin) in [
        (include_str!("fixtures/native_dh_agreement.spthy"), "proved"),
        (
            include_str!("fixtures/native_user_equations_pairing.spthy"),
            "assumed",
        ),
    ] {
        let fixture = Fixture::new(theory);
        let run = |work: Option<&str>| {
            let mut command = fixture.command();
            if let Some(work) = work {
                command.env("TAM_RS_VARIANT_CHECK_WORK", work);
            }
            let output = command
                .env("TAM_MAUDE_CACHE_STATS", "1")
                .args(["--processors", "1"])
                .arg("--prove")
                .arg(fixture.dir.join("input.spthy"))
                .output()
                .unwrap();
            assert!(!fixture.dir.join("called").exists());
            let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            let results: Vec<String> = stdout
                .lines()
                .filter(|line| line.contains("(exists-trace)") || line.contains("(all-traces)"))
                .map(str::to_owned)
                .collect();
            // Fresh and cached answers by origin, and the families a Rust
            // solver proposed, summed over the sessions of the run.
            let mut seen = std::collections::BTreeMap::new();
            let mut proposed = 0;
            for line in stderr.lines() {
                if let Some(row) = line.strip_prefix("[ALGEBRA_PROVENANCE] variants fresh: ") {
                    for cell in row.split(' ') {
                        if let Some((name, count)) = cell.split_once('=') {
                            *seen.entry(name.to_owned()).or_insert(0u64) +=
                                count.parse::<u64>().unwrap();
                        }
                    }
                } else if let Some(row) = line.strip_prefix("[VARIANT_ROUTES] proposer=") {
                    proposed += row.split(' ').next().unwrap().parse::<u64>().unwrap();
                }
            }
            (output.status.success(), results, seen, proposed, stderr)
        };
        let (ok, results, seen, proposed, stderr) = run(None);
        assert!(ok, "{stderr}");
        assert!(!results.is_empty(), "{stderr}");
        assert!(proposed > 0, "{stderr}");
        assert!(seen[origin] > 0, "{seen:?}");
        assert_eq!(seen["native_rust"], 0, "{seen:?}");

        // Without a bound the checker accepts the same families.
        let (ok, unbounded, seen, _, stderr) = run(Some("0"));
        assert!(ok, "{stderr}");
        assert_eq!(unbounded, results);
        assert_eq!(seen["native_rust"], 0, "{seen:?}");

        // A bound of one position admits no family of these theories.
        let (ok, refused, _, _, stderr) = run(Some("1"));
        assert!(!ok, "{stderr}");
        assert!(refused.is_empty(), "{refused:?}");
        assert!(
            stderr.contains("variants not certified: out of budget"),
            "{stderr}"
        );
    }

    let fixture = Fixture::new(SIMPLE);
    let output = fixture
        .command()
        .env("TAM_RS_VARIANT_CHECK_WORK", "some")
        .arg("--prove")
        .arg(fixture.dir.join("input.spthy"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("TAM_RS_VARIANT_CHECK_WORK"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(feature = "lean-unification")]
#[test]
fn ac_marker_variant_preserves_the_reachable_trace() {
    let fixture = Fixture::new(include_str!("fixtures/native_ac_marker_trace.spthy"));
    let output = fixture.run(&["--prove"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    // Initial, Combine and Observe are a concrete witness under the bare equation.
    assert!(
        stdout.contains("possible (exists-trace): verified"),
        "{stdout}"
    );
    assert!(
        stdout.contains("impossible (all-traces): falsified - found trace"),
        "{stdout}"
    );
}

/// Rules whose variants no specialised solver covers: a destructor or an
/// inverse above an exponentiation or an exclusive-or of two received
/// messages. Native-only used to hand these to a Lean search that did not
/// return. Folding variant narrowing proposes the families, the certificate
/// checker accepts them, and the proofs are those of the Maude backend.
#[cfg(feature = "lean-unification")]
#[test]
fn folded_rule_variants_prove_the_traces_without_maude() {
    for theory in [
        include_str!("fixtures/native_folded_decryption.spthy"),
        include_str!("fixtures/native_folded_projection.spthy"),
        include_str!("fixtures/native_folded_inverse.spthy"),
    ] {
        let fixture = Fixture::new(theory);
        let output = fixture
            .command()
            .env("TAM_MAUDE_CACHE_STATS", "1")
            .env("TAM_DBG_VARIANTS", "1")
            .arg("--prove")
            .arg(fixture.dir.join("input.spthy"))
            .output()
            .unwrap();
        assert!(!fixture.dir.join("called").exists());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stdout}\n{stderr}");
        assert!(
            stdout.contains("reachable (exists-trace): verified (4 steps)"),
            "{stdout}"
        );
        // The family of the rule came from the folding proposer and no
        // family from an export that is used without the checker.
        assert!(stderr.contains("[variants] solver fold"), "{stderr}");
        assert!(!stderr.contains("solver checked_export"), "{stderr}");
        let mut unchecked = 0;
        for line in stderr.lines() {
            if let Some(row) = line.strip_prefix("[VARIANT_ROUTES] ") {
                for cell in row.split(' ') {
                    if let Some(count) = cell.strip_prefix("checked_export=") {
                        unchecked += count.parse::<u64>().unwrap();
                    }
                }
            } else if let Some(row) = line.strip_prefix("[ALGEBRA_PROVENANCE] variants fresh: ") {
                assert!(row.contains("assumed=0 native_rust=0"), "{line}");
            }
        }
        assert_eq!(unchecked, 0, "{stderr}");
    }
}

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
        .env("TAM_RS_VERIFY_REDUCE_NF", "1")
        .arg(fixture.dir.join("input.spthy"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("incompatible with TAM_RS_VERIFY_REDUCE_NF"));
    assert!(!fixture.dir.join("called").exists());
}

/// The installation self-test compares against a Maude installation, so
/// native-only refuses it before probing anything. Interactive mode is
/// supported: `crates/tamarin-server/tests/routes_native_backend.rs` and
/// `scripts/interactive_backend_check.sh` drive it.
#[cfg(feature = "lean-unification")]
#[test]
fn native_installation_self_test_is_explicitly_rejected_without_probing() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.command().arg("test").output().unwrap();
    assert!(!fixture.dir.join("called").exists());
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("the installation self-test is not yet supported"));
}

#[cfg(not(feature = "lean-unification"))]
#[test]
fn native_mode_requires_the_lean_feature_before_probing() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.run(&["--prove"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("requires a build with --features lean-unification"));
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

/// Parallel search shares the native session among its jobs. What it prints
/// must not depend on how many workers there are, or on which job computed
/// an answer first: one worker and eight give the same proofs.
#[cfg(feature = "lean-unification")]
#[test]
fn stdout_is_the_same_for_one_worker_and_for_many() {
    for theory in [
        include_str!("fixtures/native_dh_agreement.spthy"),
        include_str!("fixtures/native_ac_marker_trace.spthy"),
        include_str!("fixtures/native_shared_exponent.spthy"),
        include_str!("fixtures/native_user_equations_pairing.spthy"),
        include_str!("fixtures/lean_unification.spthy"),
    ] {
        let fixture = Fixture::new(theory);
        let prove = |workers: &str| {
            let output = fixture.run(&["--processors", workers, "--prove"]);
            let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(output.status.success(), "{stdout}\n{stderr}");
            assert!(stdout.contains("summary of summaries"), "{stdout}");
            stdout
                .lines()
                .filter(|line| !line.contains("processing time"))
                .map(|line| format!("{line}\n"))
                .collect::<String>()
        };
        let serial = prove("1");
        for _ in 0..3 {
            assert_eq!(prove("8"), serial);
        }
    }
}

/// What a run printed and how it ended, without the line that times it.
#[cfg(feature = "lean-unification")]
fn outcome(output: &Output) -> (Option<i32>, String, String) {
    let stdout = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| !line.contains("processing time"))
        .map(|line| format!("{line}\n"))
        .collect();
    let error = String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|line| line.starts_with("error:"))
        .map(|line| format!("{line}\n"))
        .collect();
    (output.status.code(), stdout, error)
}

/// A failed algebra query belongs to the search job that ran into it. The
/// case `Hard` runs out of budget, and a search on one worker never visits
/// it: `Easy` comes first and is solved. On eight workers `Hard` is started
/// beside `Easy`, fails while it is still wanted, and is discarded once
/// `Easy` is solved. Its failure must go with it, so that the run ends as
/// it does on one worker.
#[cfg(feature = "lean-unification")]
#[test]
fn a_discarded_search_job_takes_its_failure_with_it() {
    let fixture = Fixture::new(include_str!("fixtures/native_budget_speculative.spthy"));
    for budget in ["4000000", "100000"] {
        let prove = |workers: &str| {
            let output = fixture
                .command()
                .env("TAM_RS_ALGEBRA_SEARCH_WORK", budget)
                .args(["--processors", workers, "--prove"])
                .arg(fixture.dir.join("input.spthy"))
                .output()
                .unwrap();
            outcome(&output)
        };
        let serial = prove("1");
        assert_eq!(serial.0, Some(0), "{serial:?}");
        assert!(
            serial.1.contains("reach (exists-trace): verified"),
            "{serial:?}"
        );
        for _ in 0..5 {
            assert_eq!(prove("8"), serial, "budget {budget}");
        }
    }
}

/// The counterpart: the case that runs out of budget is the first one, so a
/// search on one worker visits it and fails. Eight workers must fail with
/// the same error and print the same, however the job that failed and the
/// jobs beside it are scheduled.
#[cfg(feature = "lean-unification")]
#[test]
fn a_failure_on_the_path_of_the_search_fails_every_number_of_workers() {
    let fixture = Fixture::new(include_str!("fixtures/native_budget_required.spthy"));
    for budget in ["4000000", "100000"] {
        let prove = |workers: &str| {
            let output = fixture
                .command()
                .env("TAM_RS_ALGEBRA_SEARCH_WORK", budget)
                .args(["--processors", workers, "--prove"])
                .arg(fixture.dir.join("input.spthy"))
                .output()
                .unwrap();
            outcome(&output)
        };
        let serial = prove("1");
        assert_eq!(serial.0, Some(1), "{serial:?}");
        assert!(serial.2.contains("out of budget"), "{serial:?}");
        assert!(!serial.1.contains("verified"), "{serial:?}");
        for _ in 0..5 {
            assert_eq!(prove("8"), serial, "budget {budget}");
        }
    }
}

/// The native backend hands what the Maude backend sends to Maude to the
/// proved exports. It never probes or starts Maude, and prints what
/// native-only prints, but for the line that names the backend.
#[cfg(feature = "lean-unification")]
#[test]
fn native_prints_what_native_only_prints_without_maude() {
    for theory in [
        include_str!("fixtures/native_dh_agreement.spthy"),
        include_str!("fixtures/native_shared_exponent.spthy"),
        include_str!("fixtures/native_cancellation.spthy"),
        SIMPLE,
    ] {
        let fixture = Fixture::new(theory);
        let prove = |backend: &str| {
            let output = fixture
                .command_on(backend)
                .args(["--processors=1", "--prove"])
                .arg(fixture.dir.join("input.spthy"))
                .output()
                .unwrap();
            assert!(
                !fixture.dir.join("called").exists(),
                "{backend} invoked Maude"
            );
            let (code, stdout, stderr) = outcome(&output);
            assert_eq!(code, Some(0), "{backend}: {stdout}\n{stderr}");
            stdout
                .lines()
                .filter(|line| !line.contains("processing time"))
                .map(|line| line.replace("not used (native)", "not used (native-only)"))
                .collect::<Vec<_>>()
        };
        let native = prove("native");
        assert!(native.iter().any(|line| line.contains("verified")));
        assert_eq!(native, prove("native-only"));
    }
}

/// Native is refused for the installation self-test, as native-only is.
#[cfg(feature = "lean-unification")]
#[test]
fn native_installation_self_test_is_rejected_without_probing() {
    let fixture = Fixture::new(SIMPLE);
    let output = fixture.command_on("native").arg("test").output().unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("native supports batch"));
    assert!(!fixture.dir.join("called").exists());
}
