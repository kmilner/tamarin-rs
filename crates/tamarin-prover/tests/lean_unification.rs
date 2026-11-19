//! Exercise the native backend through actual protocol proof search.
#![cfg(feature = "lean-unification")]

mod common;

use std::process::Command;

fn run(disable_lean: bool) -> (String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
    command
        .arg(common::maude_arg().expect("Maude oracle"))
        .arg("--prove")
        .arg(common::fixture("lean_unification.spthy"))
        .env("TAM_MAUDE_CACHE_STATS", "1")
        .env("TAM_RS_VERIFY_LEAN_UNIFY", "1");
    command
        .arg(if disable_lean {
            "--algebra-backend=maude"
        } else {
            "--algebra-backend=hybrid"
        })
        .arg("--processors=2")
        .arg("--maude-processes=2")
        .env_remove("TAM_RS_NO_LEAN_UNIFY");
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

#[test]
fn protocol_proof_uses_lean_and_matches_maude() {
    if !common::maude_available() {
        return;
    }
    let (lean_stdout, lean_stderr) = run(false);
    let (maude_stdout, maude_stderr) = run(true);
    assert!(lean_stdout.contains("verified"), "{lean_stdout}");
    assert!(
        lean_stdout
            .lines()
            .any(|line| line.contains("conjunction_reachable") && line.contains("verified")),
        "{lean_stdout}"
    );
    assert_eq!(
        common::normalize_stdout(&lean_stdout),
        common::normalize_stdout(&maude_stdout)
    );
    assert!(lean_calls(&lean_stderr) > 0, "{lean_stderr}");
    assert_eq!(lean_calls(&maude_stderr), 0, "{maude_stderr}");
}

fn comparable_proof(stdout: &str) -> String {
    common::normalize_stdout(stdout)
        .lines()
        .filter(|line| !line.starts_with("Maude version "))
        .map(|line| format!("{line}\n"))
        .collect()
}

fn assert_native_parity(fixture: &str, expected: &[&str]) {
    if !common::maude_available() {
        return;
    }
    let mut outputs = Vec::new();
    for backend in ["native-only", "hybrid", "maude"] {
        let output = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
            .arg(format!("--algebra-backend={backend}"))
            .arg(if backend == "native-only" {
                "--with-maude=/nonexistent".to_owned()
            } else {
                common::maude_arg().unwrap()
            })
            .arg("--prove")
            .arg("--processors=2")
            .arg("--maude-processes=2")
            .arg(common::fixture(fixture))
            .env_remove("TAM_RS_NO_LEAN_UNIFY")
            .env_remove("TAM_RS_VERIFY_LEAN_UNIFY")
            .env_remove("TAM_RS_VERIFY_REDUCE_NF")
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(output.status.success(), "{backend}: {stdout}\n{stderr}");
        for verdict in expected {
            assert!(stdout.contains(verdict), "{stdout}");
        }
        outputs.push(comparable_proof(&stdout));
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_eq!(outputs[0], outputs[2]);
}

#[test]
fn native_pairing_proof_matches_maude_and_hybrid() {
    assert_native_parity(
        "native_pairing.spthy",
        &["reachable (exists-trace): verified (2 steps)"],
    );
}

#[test]
fn joint_projection_variants_and_proof_match_maude_and_hybrid() {
    assert_native_parity(
        "native_joint_projections.spthy",
        &["projected (exists-trace): verified (2 steps)"],
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
fn native_multiset_proof_matches_maude_and_hybrid() {
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
fn native_declared_constructors_match_maude_and_hybrid() {
    assert_native_parity(
        "native_constructors.spthy",
        &["reachable (exists-trace): verified"],
    );
}

#[test]
fn native_cancellation_proof_matches_maude_and_hybrid() {
    assert_native_parity(
        "native_cancellation.spthy",
        &[
            "reachable (exists-trace): verified (3 steps)",
            "only_residual (all-traces): verified (3 steps)",
        ],
    );
}

#[test]
fn shared_offset_proof_matches_maude_and_hybrid() {
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
    assert_corpus_parity(example, verdicts, true);
}

fn run_corpus(example: &str, backend: &str, args: &[&str]) -> (String, String) {
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tamarin-prover/examples")
        .join(example);
    run_model(&example, backend, args)
}

fn run_model(example: &std::path::Path, backend: &str, args: &[&str]) -> (String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"))
        .arg(format!("--algebra-backend={backend}"))
        .arg(if backend == "native-only" {
            "--with-maude=/nonexistent".to_string()
        } else {
            common::maude_arg().unwrap()
        })
        .args(["--processors=1", "--maude-processes=1"])
        .args(args)
        .arg(example)
        .env("TAM_DBG_MAUDE_IO", "1")
        .env_remove("TAM_DBG_MAUDE_IO_FILTER")
        .env_remove("TAM_RS_NO_LEAN_UNIFY")
        .env_remove("TAM_RS_VERIFY_LEAN_UNIFY")
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
    assert_corpus_proof(
        "csf12/SignedDH_PFS.spthy",
        &["Perfect_Forward_Secrecy (all-traces): verified (39 steps)"],
    );
    assert_corpus_proof(
        "csf12/STS_MAC.spthy",
        &[
            "KI_Perfect_Forward_Secrecy_I (all-traces): falsified - found trace (12 steps)",
            "KI_Perfect_Forward_Secrecy_R (all-traces): falsified - found trace (13 steps)",
        ],
    );
}

#[test]
fn naxos_joint_variants_preserve_sources_and_the_full_proof_without_maude() {
    for (example, verdict) in [
        (
            "csf12/NAXOS_eCK.spthy",
            "eCK_key_secrecy (all-traces): verified (134 steps)",
        ),
        (
            "ake/dh/NAXOS_eCK.spthy",
            "eCK_key_secrecy (all-traces): verified (136 steps)",
        ),
        (
            "ake/dh/NAXOS_eCK_PFS.spthy",
            "eCK_PFS_key_secrecy (all-traces): falsified - found trace (15 steps)",
        ),
    ] {
        assert_corpus_parity(example, &[verdict], false);
    }
}

#[test]
fn received_base_towers_preserve_group_dh_rule_variants_without_maude() {
    if !common::maude_available() {
        return;
    }
    let example = "experiments/A-GDH2.spthy";
    let (reference, _) = run_corpus(example, "maude", &[]);
    let (actual, _) = run_corpus(example, "native-only", &[]);
    assert!(reference.contains("variants (modulo AC)"));
    assert_eq!(comparable_proof(&actual), comparable_proof(&reference));
}

#[test]
fn shared_exponents_preserve_group_dh_rules_and_sources_without_maude() {
    if !common::maude_available() {
        return;
    }
    let example = "sp14/GDH.spthy";
    for (args, expected) in [
        (&[][..], "rule (modulo E) RecvOthers"),
        (&["--precompute-only"][..], "Refined sources: 11 cases"),
        (
            &["-D=executable2", "--prove=key_reachable_2", "--bound=12"][..],
            "key_reachable_2 (exists-trace): analysis incomplete (87 steps)",
        ),
    ] {
        let (reference, _) = run_corpus(example, "maude", args);
        let (native, _) = run_corpus(example, "native-only", args);
        assert!(reference.contains(expected), "{reference}");
        assert_eq!(comparable_proof(&native), comparable_proof(&reference));
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
    let (native, calls) = run_corpus(example, "native-only", &args);
    assert!(!calls.contains("[maude>]"));
    for output in [&reference, &native] {
        assert!(output.contains("key_reachable_2 (exists-trace): verified (20 steps)"));
        assert!(output.contains("SOLVED // trace found"));
    }
    // A local case number is an index into that backend's unifier list.
    // Compare the chosen goals, rule instances and trace through the whole proof.
    let trace = |output: &str| {
        comparable_proof(output)
            .lines()
            .map(|line| {
                if let Some((indent, n)) = line.split_once("case split_case_")
                    && indent.trim().is_empty()
                    && !n.is_empty()
                    && n.bytes().all(|b| b.is_ascii_digit())
                {
                    format!("{indent}case split_case")
                } else {
                    line.to_owned()
                }
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(trace(&native), trace(&reference));
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
    assert_native_parity(
        "native_positive_tower.spthy",
        &[
            "reachable (exists-trace): verified (3 steps)",
            "tower (all-traces): verified (2 steps)",
        ],
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
        false,
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
        false,
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
        true,
    );
}

fn assert_corpus_parity(example: &str, verdicts: &[&str], check_hybrid_offload: bool) {
    if !common::maude_available() {
        return;
    }
    let run = |backend: &str, action: &str| {
        let (stdout, stderr) = run_corpus(example, backend, &[action]);
        let commands = stderr
            .lines()
            .filter(|line| {
                line.starts_with("[maude>] get variants") || line.starts_with("[maude>] reduce ")
            })
            .count();
        (stdout, commands)
    };
    let (reference, baseline) = run("maude", "--precompute-only");
    let (actual, calls) = run("hybrid", "--precompute-only");
    assert!(reference.contains("Refined sources:"), "{reference}");
    assert_eq!(actual, reference);
    assert!(baseline > 0);
    if check_hybrid_offload {
        assert_eq!(
            calls, 0,
            "hybrid precomputation sent a variant or reduction query"
        );
    }
    let (native, calls) = run("native-only", "--precompute-only");
    assert_eq!(native, reference);
    assert_eq!(calls, 0);
    let (reference, _) = run("maude", "--prove");
    for &verdict in verdicts {
        assert!(reference.contains(verdict), "{reference}");
    }
    for backend in ["hybrid", "native-only"] {
        let (actual, calls) = run(backend, "--prove");
        if backend == "native-only" || check_hybrid_offload {
            assert_eq!(
                calls, 0,
                "{backend} proof sent a variant or reduction query"
            );
        }
        assert_eq!(comparable_proof(&actual), comparable_proof(&reference));
    }
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
        assert_corpus_parity(example, &[verdict], false);
    }
    assert_corpus_parity(
        "features/xor/basicfunctionality/testConstructor.spthy",
        &[
            "secret1 (all-traces): falsified - found trace (11 steps)",
            "secret2 (all-traces): falsified - found trace (10 steps)",
            "secret3 (all-traces): falsified - found trace (11 steps)",
        ],
        false,
    );
}

#[test]
fn crxor_preserves_sources_and_all_three_proofs_without_maude() {
    assert_crxor_parity("features/xor/CRxor.spthy", "case c_xor_case_1");
}

#[test]
fn declared_ac_crxor_preserves_sources_and_all_three_proofs_without_maude() {
    assert_crxor_parity("csf26-ac/fast/CRxor.spthy", "case c_xorr_case_1");
}

#[test]
fn ch07_preserves_sources_and_all_five_proof_trees_without_maude() {
    let example = "features/xor/CH07.spthy";
    let (sources, log) = run_corpus(example, "native-only", &["--precompute-only"]);
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
    let (proof, log) = run_corpus(example, "native-only", &["--prove"]);
    assert!(!log.contains("[maude>]"), "{log}");
    if common::maude_available() {
        let (reference, _) = run_corpus(example, "maude", &["--prove"]);
        assert_eq!(comparable_proof(&proof), comparable_proof(&reference));
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

fn assert_crxor_parity(example: &str, first_case: &str) {
    let (sources, log) = run_corpus(example, "native-only", &["--precompute-only"]);
    assert!(!log.contains("[maude>]"), "{log}");
    for expected in [
        "Raw sources: 7 cases, deconstructions complete",
        "Refined sources: 7 cases, deconstructions complete",
    ] {
        assert!(sources.contains(expected), "{sources}");
    }
    let (proof, log) = run_corpus(example, "native-only", &["--prove"]);
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
        // The terminal KU(~k) goals directly under the first AC case can print a
        // different fresh timepoint index. Keep the solved term and indentation.
        let tree = |stdout: &str| {
            let mut first_xor_case = false;
            comparable_proof(stdout)
                .lines()
                .map(|line| {
                    let under_case = first_xor_case;
                    first_xor_case = line.trim() == first_case;
                    if under_case
                        && let Some((prefix, tail)) = line.split_once("by solve( !KU( ~k ) @ #vk.")
                        && prefix.trim().is_empty()
                        && tail
                            .strip_suffix(" )")
                            .is_some_and(|id| id.parse::<u64>().is_ok())
                    {
                        format!("{prefix}by solve( !KU( ~k ) @ #vk )")
                    } else {
                        line.to_owned()
                    }
                })
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
        for backend in ["native-only", "hybrid"] {
            let (actual, log) = run_model(&path, backend, args);
            if backend == "native-only" {
                assert!(!log.contains("[maude>]"), "{log}");
            }
            assert_eq!(comparable_proof(&actual), comparable_proof(&reference));
        }
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
fn nslpk_xor_preserves_sources_and_all_four_proofs_without_maude() {
    let example = "features/xor/NSLPK3xor.spthy";
    let (theory, log) = run_corpus(example, "native-only", &[]);
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
    let (sources, log) = run_corpus(example, "native-only", &["--precompute-only"]);
    assert!(!log.contains("[maude>]"), "{log}");
    assert!(
        sources.contains("Refined sources: 11 cases, deconstructions complete"),
        "{sources}"
    );
    let (proof, log) = run_corpus(example, "native-only", &["--prove"]);
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
    assert_corpus_proof(
        "classic/TLS_Handshake.spthy",
        &["session_key_secrecy (all-traces): verified"],
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
