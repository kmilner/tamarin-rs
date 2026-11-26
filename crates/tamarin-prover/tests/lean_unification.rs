//! Exercise the native backend through actual protocol proof search.
#![cfg(feature = "lean-unification")]

mod common;

use std::process::Command;

fn run(backend: &str) -> (String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    command
        .arg(if backend == "proved-only" {
            "--with-maude=/nonexistent".to_owned()
        } else {
            common::maude_arg().expect("Maude oracle")
        })
        .arg(format!("--algebra-backend={backend}"))
        .arg("--prove")
        .arg(common::fixture("lean_unification.spthy"))
        .arg("--processors=2")
        .arg("--maude-processes=2")
        .env("TAM_MAUDE_CACHE_STATS", "1")
        .env_remove("TAM_RS_NATIVE_REFERENCE")
        .env_remove("TAM_RS_VARIANT_CHECK_WORK")
        .env_remove("TAM_RS_VERIFY_REDUCE_NF");
    let output = command.output().expect("run prover");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{stdout}\n{stderr}");
    (stdout, stderr)
}

fn lean_calls(stderr: &str) -> u64 {
    stderr
        .lines()
        .filter_map(|line| line.split_once("lean_unify="))
        .map(|(_, count)| count.trim().parse::<u64>().expect("Lean counter"))
        .sum()
}

/// The answers of `command` that `[ALGEBRA_PROVENANCE]` attributes to
/// `origin`, fresh and cached, over every session of the run.
fn provenance(stderr: &str, command: &str, origin: &str) -> u64 {
    let prefix = format!("[ALGEBRA_PROVENANCE] {command} fresh: ");
    let key = format!("{origin}=");
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix(prefix.as_str()))
        .flat_map(|row| row.split_whitespace())
        .filter_map(|cell| cell.strip_prefix(key.as_str()))
        .map(|count| count.parse::<u64>().expect("provenance count"))
        .sum()
}

#[test]
fn proved_only_proof_rests_on_the_proved_exports_and_matches_maude() {
    if !common::maude_available() {
        return;
    }
    let (native_stdout, native_stderr) = run("proved-only");
    let (maude_stdout, maude_stderr) = run("maude");
    assert!(
        native_stdout
            .lines()
            .any(|line| line.contains("conjunction_reachable") && line.contains("verified")),
        "{native_stdout}"
    );
    assert_eq!(
        comparable_proof(&native_stdout),
        comparable_proof(&maude_stdout)
    );
    assert!(lean_calls(&native_stderr) > 0, "{native_stderr}");
    assert_eq!(lean_calls(&maude_stderr), 0, "{maude_stderr}");
    // Every unification and every match of the native run is the answer of
    // one proved export, or of the tuple unpacker composed with one.
    assert!(
        provenance(&native_stderr, "unify", "proved") > 0,
        "{native_stderr}"
    );
    for command in ["unify", "match"] {
        for origin in ["assumed", "shared_rust", "maude"] {
            assert_eq!(
                provenance(&native_stderr, command, origin),
                0,
                "{command} {origin}: {native_stderr}"
            );
        }
    }
    // No reduction of the native run is a Rust shortcut.
    assert_eq!(provenance(&native_stderr, "reduce", "shared_rust"), 0);
    for command in ["unify", "match", "reduce", "variants"] {
        assert_eq!(provenance(&native_stderr, command, "maude"), 0);
        assert_eq!(provenance(&maude_stderr, command, "proved"), 0);
    }
    assert!(provenance(&maude_stderr, "unify", "maude") > 0);
}

fn comparable_proof(stdout: &str) -> String {
    common::normalize_stdout(stdout)
        .lines()
        .filter(|line| !line.starts_with("Maude version "))
        .map(|line| format!("{line}\n"))
        .collect()
}

/// How much of the proved-only output a test compares with Maude's. The
/// native backend spells the witnesses of a unifier and lists a family of
/// variants as the Maude backend does, so the whole output is the same
/// wherever no unification is left to the AC engine. Where it is, the proved
/// unifier may list its complete family in another order than Maude and
/// number the engine's witnesses differently, which renames variables and
/// renumbers cases. The verdicts cannot differ.
#[derive(Clone, Copy)]
enum Parity {
    /// The whole output.
    Output,
    /// Each lemma's verdict and step count.
    Summary,
}

fn assert_parity(parity: Parity, actual: &str, reference: &str, context: &str) {
    let summary = |stdout: &str| {
        stdout
            .lines()
            .map(str::trim)
            .filter(|line| line.contains(" (all-traces): ") || line.contains(" (exists-trace): "))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    match parity {
        Parity::Output => assert_eq!(
            comparable_proof(actual),
            comparable_proof(reference),
            "{context}"
        ),
        Parity::Summary => assert_eq!(summary(actual), summary(reference), "{context}"),
    }
}

fn assert_native_parity(fixture: &str, expected: &[&str]) {
    assert_fixture_parity(fixture, expected, Parity::Output);
}

fn assert_fixture_parity(fixture: &str, expected: &[&str], parity: Parity) {
    if !common::maude_available() {
        return;
    }
    let mut outputs = Vec::new();
    for backend in ["proved-only", "maude"] {
        let output = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .arg(format!("--algebra-backend={backend}"))
            .arg(if backend == "proved-only" {
                "--with-maude=/nonexistent".to_owned()
            } else {
                common::maude_arg().unwrap()
            })
            .arg("--prove")
            .arg("--processors=2")
            .arg("--maude-processes=2")
            .arg(common::fixture(fixture))
            .env_remove("TAM_RS_VERIFY_REDUCE_NF")
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(output.status.success(), "{backend}: {stdout}\n{stderr}");
        for verdict in expected {
            assert!(stdout.contains(verdict), "{stdout}");
        }
        outputs.push(stdout);
    }
    assert_parity(parity, &outputs[0], &outputs[1], fixture);
}

/// A unifier witness once reused the name of the lemma variable `x`, which is
/// in the constraint system but not in the XOR query, and proved-only then
/// reported the false lemma verified and the true one falsified.
#[test]
fn witnesses_stay_distinct_from_system_variables_outside_the_query() {
    // The XOR engine's witnesses are numbered differently in the trace.
    assert_fixture_parity(
        "native_witness_scope.spthy",
        &[
            "flip (all-traces): falsified - found trace (4 steps)",
            "sanity (exists-trace): verified (4 steps)",
        ],
        Parity::Summary,
    );
}

#[test]
fn native_pairing_proof_matches_maude() {
    assert_native_parity(
        "native_pairing.spthy",
        &["reachable (exists-trace): verified (2 steps)"],
    );
}

#[test]
fn joint_projection_variants_and_proof_match_maude() {
    assert_native_parity(
        "native_joint_projections.spthy",
        &["projected (exists-trace): verified (2 steps)"],
    );
}

#[test]
fn nested_user_rules_preserve_the_input_and_twice_rewritten_value() {
    assert_native_parity(
        "native_nested_rule_variants.spthy",
        &["nested_value (exists-trace): verified"],
    );
}

#[test]
fn cancellation_below_free_constructors_preserves_the_protocol_proof() {
    assert_native_parity(
        "native_free_variant_context.spthy",
        &["cancelled (exists-trace): verified (3 steps)"],
    );
}

#[test]
fn dh_exchange_commutes_the_two_secret_exponents_without_maude() {
    assert_native_parity(
        "native_dh_agreement.spthy",
        &[
            "completes (exists-trace): verified (2 steps)",
            "same_key (all-traces): verified (2 steps)",
        ],
    );
}

#[test]
fn bilinear_derivation_check_and_proof_match_maude() {
    assert_native_parity(
        "native_commutative.spthy",
        &["recorded (exists-trace): verified (2 steps)"],
    );
}

#[test]
fn native_multiset_proof_matches_maude() {
    assert_native_parity(
        "lean_unification.spthy",
        &[
            "reachable (exists-trace): verified (4 steps)",
            "conjunction_reachable (exists-trace): verified (4 steps)",
        ],
    );
}

#[test]
fn nested_ac_restriction_preserves_both_trace_verdicts() {
    assert_native_parity(
        "native_nested_ac_guard.spthy",
        &[
            "allowed (exists-trace): verified (2 steps)",
            "excluded (all-traces): verified (1 steps)",
        ],
    );
}

#[test]
fn native_declared_constructors_match_maude() {
    assert_native_parity(
        "native_constructors.spthy",
        &["reachable (exists-trace): verified"],
    );
}

#[test]
fn native_cancellation_proof_matches_maude() {
    assert_native_parity(
        "native_cancellation.spthy",
        &[
            "reachable (exists-trace): verified (3 steps)",
            "only_residual (all-traces): verified (3 steps)",
        ],
    );
}

#[test]
fn shared_offset_proof_matches_maude() {
    assert_native_parity(
        "native_shared_offset.spthy",
        &[
            "either_branch (exists-trace): verified (3 steps)",
            "reachable (exists-trace): verified (3 steps)",
            "shared_reachable (exists-trace): verified (3 steps)",
        ],
    );
}

fn assert_corpus_proof(example: &str, verdicts: &[&str]) {
    assert_corpus_parity(example, verdicts, Parity::Output);
}

fn run_corpus(example: &str, backend: &str, args: &[&str]) -> (String, String) {
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tamarin-prover/examples")
        .join(example);
    run_model(&example, backend, args)
}

fn run_model(example: &std::path::Path, backend: &str, args: &[&str]) -> (String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .env_remove("TAM_RS_VARIANT_CHECK_WORK")
        .arg(format!("--algebra-backend={backend}"))
        .arg(if backend == "proved-only" {
            "--with-maude=/nonexistent".to_string()
        } else {
            common::maude_arg().unwrap()
        })
        .args(["--processors=1", "--maude-processes=1"])
        .args(args)
        .arg(example)
        .env("TAM_DBG_MAUDE_IO", "1")
        .env_remove("TAM_DBG_MAUDE_IO_FILTER")
        .env_remove("TAM_RS_VERIFY_REDUCE_NF")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{stdout}\n{stderr}");
    (stdout, stderr)
}

#[test]
fn dh_message_deduction_preserves_sources_and_the_full_proof_without_maude() {
    assert_corpus_proof(
        "thesis-benedikt/running-examples/DH_Message_Deduction.spthy",
        &["key_deducible (exists-trace): verified (5 steps)"],
    );
}

#[test]
fn received_dh_powers_preserve_sources_and_full_proofs_without_maude() {
    assert_corpus_proof(
        "cav13/DH_example.spthy",
        &[
            "Accept_Secret (all-traces): verified (9 steps)",
            "Accept_Secret_Counter (all-traces): falsified - found trace (7 steps)",
        ],
    );
    assert_corpus_parity(
        "csf12/SignedDH_PFS.spthy",
        &["Perfect_Forward_Secrecy (all-traces): verified (39 steps)"],
        Parity::Output,
    );
    assert_corpus_parity(
        "csf12/STS_MAC.spthy",
        &[
            "KI_Perfect_Forward_Secrecy_I (all-traces): falsified - found trace (12 steps)",
            "KI_Perfect_Forward_Secrecy_R (all-traces): falsified - found trace (13 steps)",
        ],
        Parity::Output,
    );
}

#[test]
fn naxos_joint_variants_preserve_sources_and_the_full_proof_without_maude() {
    for (example, verdict, parity) in [
        (
            "csf12/NAXOS_eCK.spthy",
            "eCK_key_secrecy (all-traces): verified (134 steps)",
            Parity::Output,
        ),
        (
            "ake/dh/NAXOS_eCK.spthy",
            "eCK_key_secrecy (all-traces): verified (136 steps)",
            Parity::Output,
        ),
        (
            "ake/dh/NAXOS_eCK_PFS.spthy",
            "eCK_PFS_key_secrecy (all-traces): falsified - found trace (15 steps)",
            Parity::Output,
        ),
    ] {
        assert_corpus_parity(example, &[verdict], parity);
    }
}

#[test]
fn received_base_towers_preserve_group_dh_rule_variants_without_maude() {
    if !common::maude_available() {
        return;
    }
    let example = "experiments/A-GDH2.spthy";
    let (reference, _) = run_corpus(example, "maude", &[]);
    let (actual, _) = run_corpus(example, "proved-only", &[]);
    assert!(reference.contains("variants (modulo AC)"));
    assert!(actual.contains("variants (modulo AC)"));
    assert_parity(Parity::Output, &actual, &reference, example);
}

#[test]
fn shared_exponents_preserve_group_dh_rules_and_sources_without_maude() {
    if !common::maude_available() {
        return;
    }
    let example = "sp14/GDH.spthy";
    for (args, expected, parity) in [
        (&[][..], "rule (modulo E) RecvOthers", Parity::Output),
        (
            &["--precompute-only"][..],
            "Refined sources: 11 cases",
            Parity::Output,
        ),
        (
            &["-D=executable2", "--prove=key_reachable_2", "--bound=12"][..],
            "key_reachable_2 (exists-trace): analysis incomplete (87 steps)",
            Parity::Output,
        ),
    ] {
        let (reference, _) = run_corpus(example, "maude", args);
        let (native, _) = run_corpus(example, "proved-only", args);
        assert!(reference.contains(expected), "{reference}");
        assert_parity(parity, &native, &reference, example);
    }
}

#[test]
fn group_dh_two_party_reachability_finds_the_reference_trace_without_maude() {
    if !common::maude_available() {
        return;
    }
    let args = ["-D=executable2", "--prove=key_reachable_2", "--bound=20"];
    let example = "sp14/GDH.spthy";
    let (reference, _) = run_corpus(example, "maude", &args);
    let (native, calls) = run_corpus(example, "proved-only", &args);
    assert!(!calls.contains("[maude>]"));
    for output in [&reference, &native] {
        assert!(output.contains("key_reachable_2 (exists-trace): verified (20 steps)"));
        assert!(output.contains("SOLVED // trace found"));
    }
    assert_parity(Parity::Output, &native, &reference, example);
}

#[test]
fn shared_exponent_can_become_the_unit_before_or_after_multiplication() {
    assert_native_parity(
        "native_shared_exponent.spthy",
        &[
            "unit_before (exists-trace): verified (3 steps)",
            "cancels_after (exists-trace): verified (3 steps)",
        ],
    );
}

#[test]
fn flattening_a_received_tower_preserves_the_proof() {
    assert_fixture_parity(
        "native_positive_tower.spthy",
        &[
            "reachable (exists-trace): verified (3 steps)",
            "tower (all-traces): verified (2 steps)",
        ],
        Parity::Output,
    );
}

#[test]
fn uniform_power_towers_and_received_powers_preserve_um_three_pass_proofs() {
    assert_corpus_parity(
        "ake/dh/UM_three_pass_combined_fixed.spthy",
        &[
            "key_agreement_reachable (exists-trace): verified (14 steps)",
            "CK_secure_UM3 (all-traces): verified (482 steps)",
            "CK_secure (all-traces): verified (142 steps)",
        ],
        Parity::Output,
    );
}

#[test]
fn rigid_context_matches_preserve_um_one_pass_proofs() {
    assert_corpus_parity(
        "ake/dh/UM_one_pass_fix.spthy",
        &[
            "key_agreement_reachable (exists-trace): verified (10 steps)",
            "CK_secure (all-traces): verified (174 steps)",
        ],
        Parity::Output,
    );
}

#[test]
fn yubikey_multiset_preserves_sources_and_all_six_proofs_without_maude() {
    assert_corpus_parity(
        "csf26-ac/fast/Yubikey_multiset.spthy",
        &[
            "transitivity (all-traces): verified (2 steps)",
            "Login_reachable (exists-trace): verified (9 steps)",
            "slightly_weaker_invariant (all-traces): verified (419 steps)",
            "no_replay (all-traces): verified (8 steps)",
            "injective_correspondance (all-traces): verified (11 steps)",
            "Login_invalidates_smaller_counters (all-traces): verified (1 steps)",
        ],
        Parity::Output,
    );
}

/// Sources agree with Maude exactly and the proofs up to `parity`, and
/// proved-only sends no command to Maude.
fn assert_corpus_parity(example: &str, verdicts: &[&str], parity: Parity) {
    if !common::maude_available() {
        return;
    }
    let run = |backend: &str, action: &str| {
        let (stdout, stderr) = run_corpus(example, backend, &[action]);
        let commands = stderr
            .lines()
            .filter(|line| line.starts_with("[maude>]"))
            .count();
        (stdout, commands)
    };
    let (reference, baseline) = run("maude", "--precompute-only");
    assert!(reference.contains("Refined sources:"), "{reference}");
    assert!(baseline > 0);
    let (native, calls) = run("proved-only", "--precompute-only");
    assert_eq!(native, reference);
    assert_eq!(calls, 0);
    let (reference, _) = run("maude", "--prove");
    for &verdict in verdicts {
        assert!(reference.contains(verdict), "{reference}");
    }
    let (actual, calls) = run("proved-only", "--prove");
    assert_eq!(calls, 0, "proved-only proof sent a command to Maude");
    assert_parity(parity, &actual, &reference, example);
}

#[test]
fn fresh_xor_corpus_preserves_sources_and_complete_proof_trees() {
    for (example, verdict) in [
        (
            "features/xor/xor.spthy",
            "Secret (all-traces): falsified - found trace (4 steps)",
        ),
        (
            "features/xor/xorplusdh.spthy",
            "Secret (all-traces): falsified - found trace (4 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor0.spthy",
            "crworks (exists-trace): verified (6 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor1.spthy",
            "secrecybroken (all-traces): falsified - found trace (4 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor2.spthy",
            "secrecybroken (all-traces): falsified - found trace (5 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor3.spthy",
            "secrecybroken (all-traces): falsified - found trace (12 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor-basic.spthy",
            "secrecybroken (all-traces): falsified - found trace (19 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor4.spthy",
            "secrecybroken (all-traces): falsified - found trace (11 steps)",
        ),
        (
            "features/xor/basicfunctionality/xor5.spthy",
            "secrecybroken (all-traces): falsified - found trace (16 steps)",
        ),
    ] {
        assert_corpus_parity(example, &[verdict], Parity::Output);
    }
    assert_corpus_parity(
        "features/xor/basicfunctionality/testConstructor.spthy",
        &[
            "secret1 (all-traces): falsified - found trace (11 steps)",
            "secret2 (all-traces): falsified - found trace (10 steps)",
            "secret3 (all-traces): falsified - found trace (11 steps)",
        ],
        Parity::Output,
    );
}

#[test]
fn crxor_preserves_sources_and_all_three_proofs_without_maude() {
    assert_crxor_parity("features/xor/CRxor.spthy");
}

#[test]
fn declared_ac_crxor_preserves_sources_and_all_three_proofs_without_maude() {
    assert_crxor_parity("csf26-ac/fast/CRxor.spthy");
}

#[test]
fn ch07_preserves_sources_and_all_five_proof_trees_without_maude() {
    let example = "features/xor/CH07.spthy";
    let (sources, log) = run_corpus(example, "proved-only", &["--precompute-only"]);
    assert!(!log.contains("[maude>]"), "{log}");
    for kind in ["Raw", "Refined"] {
        assert!(
            sources.contains(&format!(
                "{kind} sources: 11 cases, deconstructions complete"
            )),
            "{sources}"
        );
    }
    if common::maude_available() {
        let (reference, _) = run_corpus(example, "maude", &["--precompute-only"]);
        assert_eq!(sources, reference);
    }
    let (proof, log) = run_corpus(example, "proved-only", &["--prove"]);
    assert!(!log.contains("[maude>]"), "{log}");
    if common::maude_available() {
        let (reference, _) = run_corpus(example, "maude", &["--prove"]);
        assert_parity(Parity::Output, &proof, &reference, example);
    }
    for verdict in [
        "recentalive_tag (all-traces): falsified - found trace (11 steps)",
        "recentalive_reader (all-traces): verified (23 steps)",
        "noninjectiveagreement_tag (all-traces): verified (19 steps)",
        "noninjectiveagreement_reader (all-traces): verified (15 steps)",
        "executable (exists-trace): verified (12 steps)",
    ] {
        assert!(proof.contains(verdict), "{proof}");
    }
}

/// `line` without the index of each variable: `x.2` and `#vk.6` become `x`
/// and `#vk`. Only a `.` between a name and digits is an index.
fn without_variable_indices(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(at) = rest.find('.') {
        let (head, tail) = rest.split_at(at);
        out.push_str(head);
        let digits = tail[1..].bytes().take_while(u8::is_ascii_digit).count();
        let named = head
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || c == '_');
        if named && digits != 0 {
            rest = &tail[1 + digits..];
        } else {
            out.push('.');
            rest = &tail[1..];
        }
    }
    out.push_str(rest);
    out
}

fn assert_crxor_parity(example: &str) {
    let (sources, log) = run_corpus(example, "proved-only", &["--precompute-only"]);
    assert!(!log.contains("[maude>]"), "{log}");
    for expected in [
        "Raw sources: 7 cases, deconstructions complete",
        "Refined sources: 7 cases, deconstructions complete",
    ] {
        assert!(sources.contains(expected), "{sources}");
    }
    let (proof, log) = run_corpus(example, "proved-only", &["--prove"]);
    assert!(!log.contains("[maude>]"), "{log}");
    for verdict in [
        "alive (all-traces): verified (364 steps)",
        "recentalive_tag (all-traces): falsified - found trace (11 steps)",
        "executable (exists-trace): verified (10 steps)",
    ] {
        assert!(proof.contains(verdict), "{proof}");
    }
    if common::maude_available() {
        let (reference, _) = run_corpus(example, "maude", &["--precompute-only"]);
        assert_eq!(sources, reference);
        let (reference, _) = run_corpus(example, "maude", &["--prove"]);
        // The xor unifications of this theory are left to the AC engine. The
        // proved unifier numbers that engine's witnesses in another order
        // than Maude, so the proofs agree as trees, case for case and goal
        // for goal, up to the indices of their variables.
        let tree = |stdout: &str| {
            comparable_proof(stdout)
                .lines()
                .map(without_variable_indices)
                .collect::<Vec<_>>()
        };
        assert_eq!(tree(&proof), tree(&reference));
    }
}

#[test]
fn nslpk_xor_responder_preserves_sources_and_the_complete_reachability_proof() {
    if !common::maude_available() {
        return;
    }
    // Isolate the responder reachability lemma and its ten source cases.
    let corpus = include_str!("../../../tamarin-prover/examples/features/xor/NSLPK3xor.spthy");
    let (prefix, _) = corpus.split_once("\nrule I_2:").unwrap();
    let theory = format!(
        "{prefix}\nlemma responder_reachable:\n  exists-trace \"Ex ni m #i. IN_R_1_ni(ni,m) @ i\"\nend\n"
    );
    let path =
        std::env::temp_dir().join(format!("tamarin-nslpk-xor-r1-{}.spthy", std::process::id()));
    std::fs::write(&path, theory).unwrap();
    for (args, expected) in [
        (&[][..], "rule (modulo E) R_1:"),
        (&["--precompute-only"][..], "Refined sources: 10 cases"),
        (
            &["--prove"][..],
            "responder_reachable (exists-trace): verified (5 steps)",
        ),
    ] {
        let (reference, _) = run_model(&path, "maude", args);
        assert!(reference.contains(expected), "{reference}");
        let (actual, log) = run_model(&path, "proved-only", args);
        assert!(!log.contains("[maude>]"), "{log}");
        assert_eq!(comparable_proof(&actual), comparable_proof(&reference));
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn nslpk_xor_preserves_sources_and_all_four_proofs_without_maude() {
    let example = "features/xor/NSLPK3xor.spthy";
    let (theory, log) = run_corpus(example, "proved-only", &[]);
    assert!(!log.contains("[maude>]"), "{log}");
    let (_, initiator) = theory.split_once("rule (modulo AC) I_2:").unwrap();
    let (initiator, rest) = initiator.split_once("*/").unwrap();
    assert!(rest.contains("rule (modulo E) R_2:"));
    let (_, variants) = initiator.split_once("variants (modulo AC)").unwrap();
    let numbers: Vec<usize> = variants
        .lines()
        .filter_map(|line| line.trim_start().split_once(". ")?.0.parse().ok())
        .collect();
    assert_eq!(numbers, (1..=7).collect::<Vec<_>>());
    let (sources, log) = run_corpus(example, "proved-only", &["--precompute-only"]);
    assert!(!log.contains("[maude>]"), "{log}");
    assert!(
        sources.contains("Refined sources: 11 cases, deconstructions complete"),
        "{sources}"
    );
    let (proof, log) = run_corpus(example, "proved-only", &["--prove"]);
    assert!(!log.contains("[maude>]"), "{log}");
    for verdict in [
        "types (all-traces): falsified - found trace (12 steps)",
        "nonce_secrecy (all-traces): falsified - found trace (11 steps)",
        "injective_agree (all-traces): falsified - found trace (13 steps)",
        "session_key_setup_possible (exists-trace): verified (6 steps)",
    ] {
        assert!(proof.contains(verdict), "{proof}");
    }
    if common::maude_available() {
        let (reference, _) = run_corpus(example, "maude", &["--precompute-only"]);
        assert_eq!(comparable_proof(&sources), comparable_proof(&reference));
        let (reference, _) = run_corpus(example, "maude", &["--prove"]);
        // The rule listing above the first lemma uses different variant witness names.
        let lemmas =
            |out: &str| comparable_proof(out.split_once("lemma types [sources]").unwrap().1);
        assert_eq!(lemmas(&proof), lemmas(&reference));
    }
}

#[test]
fn nslpk_preserves_sources_and_proof_without_maude_variant_calls() {
    assert_corpus_proof(
        "classic/NSLPK3.spthy",
        &["nonce_secrecy (all-traces): verified"],
    );
}

#[test]
fn tls_handshake_preserves_the_complete_sources_and_all_three_proofs() {
    assert_corpus_parity(
        "classic/TLS_Handshake.spthy",
        &["session_key_secrecy (all-traces): verified"],
        Parity::Output,
    );
}

#[test]
fn minimal_multiset_preserves_the_complete_proof_after_cancellation() {
    assert_corpus_proof(
        "features/multiset/minimal_multiset.spthy",
        &["Reachable (exists-trace): verified (4 steps)"],
    );
}

#[test]
fn number_subterms_preserves_the_probe_warning_and_all_eleven_proofs() {
    assert_corpus_proof(
        "features/multiset/NumberSubtermTests.spthy",
        &[
            "Reserved names",
            "Rule `InOut' contains facts with reserved names",
            "SnatChain (all-traces): verified (2 steps)",
            "SnegRecurse (all-traces): verified (2 steps)",
            "SnegACRecurse (all-traces): verified (2 steps)",
            "Sneg (all-traces): verified (2 steps)",
            "Sinvalid (all-traces): verified (2 steps)",
            "Schain (all-traces): verified (2 steps)",
            "SRecurse (all-traces): verified (2 steps)",
            "SACRecurse (all-traces): verified (2 steps)",
            "testEqual (all-traces): verified (2 steps)",
            "arityOneDeduction (all-traces): verified (2 steps)",
            "antiCharlie (all-traces): verified (2 steps)",
        ],
    );
}

#[test]
fn counter_preserves_all_four_proof_trees_without_maude() {
    assert_corpus_proof(
        "features/multiset/counter.spthy",
        &[
            "counters_linear_order (all-traces): verified (31 steps)",
            "counter_start (all-traces): verified (7 steps)",
            "counter_increases (all-traces): verified (5 steps)",
            "lesser_senc_secret (all-traces): verified (18 steps)",
        ],
    );
}

#[test]
fn user_rule_narrowing_requires_the_same_key_in_both_arguments() {
    assert_native_parity(
        "native_open_narrowing.spthy",
        &[
            "shared_key_branch (exists-trace): verified (3 steps)",
            "mismatched_keys (all-traces): verified (2 steps)",
        ],
    );
}

#[test]
fn bilinear_pairings_preserve_sources_and_all_four_protocol_verdicts() {
    for (model, first, second) in [
        (
            "ake/bilinear/Joux.spthy",
            "session_key_establish (exists-trace): verified (28 steps)",
            "Session_Key_Secrecy_PFS (all-traces): verified (22 steps)",
        ),
        (
            "ake/bilinear/Scott.spthy",
            "key_agreement_reachable (exists-trace): verified (10 steps)",
            "key_secrecy (all-traces): verified (452 steps)",
        ),
    ] {
        let (sources, log) = run_corpus(model, "proved-only", &["--precompute-only"]);
        assert!(!log.contains("[maude>]"), "{log}");
        for kind in ["Raw", "Refined"] {
            assert!(
                sources.contains(&format!(
                    "{kind} sources: 12 cases, deconstructions complete"
                )),
                "{sources}"
            );
        }
        let (proof, log) = run_corpus(model, "proved-only", &["--prove"]);
        assert!(!log.contains("[maude>]"), "{log}");
        assert!(proof.contains(first) && proof.contains(second), "{proof}");
        if common::maude_available() {
            let (oracle_sources, _) = run_corpus(model, "maude", &["--precompute-only"]);
            assert_eq!(sources, oracle_sources);
            let (oracle_proof, _) = run_corpus(model, "maude", &["--prove"]);
            assert!(
                oracle_proof.contains(first) && oracle_proof.contains(second),
                "{oracle_proof}"
            );
            // The same cases, numbered in the order of the proved unifier's arms.
            assert_parity(Parity::Summary, &proof, &oracle_proof, model);
        }
    }
}

/// Prove `fixture` on `backend` with one worker and return stdout and stderr.
fn prove_fixture(backend: &str, fixture: &str, extra: &[&str]) -> (String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    command
        .arg(if backend == "proved-only" {
            "--with-maude=/nonexistent".to_owned()
        } else {
            common::maude_arg().expect("Maude oracle")
        })
        .arg(format!("--algebra-backend={backend}"))
        .args(extra)
        .arg("--processors=1")
        .arg("--prove")
        .arg(common::fixture(fixture))
        .env_remove("TAM_MAUDE_CACHE_STATS")
        .env_remove("TAM_RS_NATIVE_REFERENCE")
        .env_remove("TAM_RS_NATIVE_REFERENCE_VARIANTS")
        .env_remove("TAM_RS_VARIANT_CHECK_WORK")
        .env_remove("TAM_RS_VERIFY_REDUCE_NF");
    let output = command.output().expect("run prover");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "{stdout}\n{stderr}");
    (stdout, stderr)
}

/// The line a proved-only run prints when the Lean certifier did not accept
/// the theory's rewrite table. The wording is stable; scripts match on it.
const ASSUMED_CONVERGENT: &str = "note: the equational theory's convergence was not certified \
     by the proved checker; results assume the user-specified equations are convergent, \
     as Maude-based Tamarin also assumes";

fn assumed_convergent_lines(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.contains("convergence was not certified"))
        .collect()
}

/// A proved-only run whose rewrite table the certifier did not accept says
/// so once per theory, on stderr, before the first lemma is attempted, and
/// leaves stdout alone. `--quiet` drops the line like every Rust-side
/// diagnostic.
#[test]
fn uncertified_user_equations_are_reported_as_assumed_convergent_once() {
    let fixture = "native_user_equations_pairing.spthy";
    let (stdout, stderr) = prove_fixture("proved-only", fixture, &[]);
    assert_eq!(
        assumed_convergent_lines(&stderr),
        [format!(
            "[Theory UserEquationsAndPairing] {ASSUMED_CONVERGENT}"
        )],
        "{stderr}"
    );
    let noted = stderr.find(ASSUMED_CONVERGENT).unwrap();
    let closed = stderr.find("Theory closed").expect("closed marker");
    assert!(noted < closed, "{stderr}");
    assert!(!stdout.contains("not certified"), "{stdout}");

    let (quiet_stdout, quiet_stderr) = prove_fixture("proved-only", fixture, &["--quiet"]);
    assert!(assumed_convergent_lines(&quiet_stderr).is_empty());
    assert_eq!(
        common::normalize_stdout(&stdout),
        common::normalize_stdout(&quiet_stdout)
    );
}

/// The built-in tables are certified outright, so a theory without user
/// equations never prints the line.
#[test]
fn certified_builtin_table_prints_no_assumed_convergent_line() {
    for fixture in ["native_dh_agreement.spthy", "lean_unification.spthy"] {
        let (_, stderr) = prove_fixture("proved-only", fixture, &[]);
        assert!(assumed_convergent_lines(&stderr).is_empty(), "{stderr}");
    }
}

/// Maude has no certifier and assumes convergence for every theory; it never
/// prints the line, and its stdout verdicts are those of the native run.
#[test]
fn maude_backend_never_prints_the_assumed_convergent_line() {
    if !common::maude_available() {
        return;
    }
    let fixture = "native_user_equations_pairing.spthy";
    let (maude_stdout, stderr) = prove_fixture("maude", fixture, &[]);
    assert!(assumed_convergent_lines(&stderr).is_empty(), "{stderr}");
    let (native_stdout, _) = prove_fixture("proved-only", fixture, &[]);
    let verdicts = |stdout: &str| -> Vec<String> {
        stdout
            .lines()
            .filter(|line| line.contains("(exists-trace):") || line.contains("(all-traces):"))
            .map(str::to_owned)
            .collect()
    };
    assert!(!verdicts(&maude_stdout).is_empty(), "{maude_stdout}");
    assert_eq!(verdicts(&maude_stdout), verdicts(&native_stdout));
}
