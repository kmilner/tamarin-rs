// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! End-to-end byte pins for the rule count of the `--precompute-only`
//! document, with and without `--auto-sources`.
//!
//! HS `prettyPrecomputation` prints `length (L.get crProtocol rules)`
//! (ClosedTheory.hs).  `crProtocol` carries one entry per
//! `ClosedProtoRule` of the closed theory plus the intruder rules that are
//! neither construction nor destruction rules (`closeRuleCache`,
//! CloseRule.hs).  When `--auto-sources` finds partial deconstructions
//! in the refined sources, `closeTheoryWithMaude` closes over `unfoldRules
//! items` (CloseRule.hs#closeTheoryWithMaude), and `unfoldRules` maps
//! `unfoldRuleVariants` over every rule item (CloseRule.hs), so a rule
//! whose AC variant is non-trivial contributes one `ClosedProtoRule` per
//! variant (`unfoldRuleVariants`, lib/theory/src/Rule.hs) rather than one
//! for the whole rule.
//!
//! These tests pin the oracle counts on [`THEORY`]: four closed protocol
//! rules without auto-sources and five with its unfolded variants.
//!
//! `--derivcheck-timeout=300` is on both runs because a derivation check that
//! times out adds a wellformedness entry, and `ppWf` (Batch.hs) puts
//! its WARNING line ahead of the stats.

mod common;

#[test]
fn auto_sources_preserves_supported_products_in_compiled_variant_actions() {
    if !common::maude_available() {
        return;
    }
    let source = r#"theory CoveredProductAutoSources begin
    builtins: diffie-hellman, symmetric-encryption
    rule Emit: [] --[Power(('g'^'a')^'b')]-> []
    variants
    rule (modulo AC) Emit___VARIANT_1:
      [] --[Power('g'^('a'*'b')),Added('a'*'b')]-> []
    rule Setup: [Fr(~k)] --> [!Key(~k)]
    rule Dec: [!Key(~k),In(x)] --[Dec(sdec(x,~k))]-> [Out(sdec(x,~k))]
    lemma witness: exists-trace "Ex x y #i. Power(x)@i & Added(y)@i"
    end"#;
    let (code, stdout, stderr) = common::run_raw(
        "tamarin_auto_sources_covered_product",
        "covered",
        source,
        &[
            "--auto-sources",
            "--prove=witness",
            "--bound=8",
            "--no-ndc",
            "--derivcheck-timeout=0",
            "--processors=1",
        ],
    );
    assert_eq!(code, 0, "{stderr}");
    assert!(
        stdout.contains("witness (exists-trace): verified (2 steps)"),
        "{stdout}"
    );
}

use common::{joined, maude_available};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_precompute_auto_sources";

/// `Dec` decrypts an incoming message under a stored key, so Maude gives it
/// two AC variants: the generic one and the one where the input is
/// `senc(m, ~k)`.  Its `Out(sdec(x, ~k))` conclusion leaves the refined
/// sources with partial deconstructions, the condition `--auto-sources` tests
/// using the preliminary cache of unfolded rules (`containsPartialDeconstructions`,
/// lib/theory/src/Rule.hs).
const THEORY: &str = "theory AutoSourcesUnfold\nbegin\n\n\
                      builtins: symmetric-encryption\n\n\
                      rule Setup:\n  [ Fr(~k) ] --> [ !Key(~k) ]\n\n\
                      rule Dec:\n  \
                      [ !Key(~k), In(x) ] --[ Dec(sdec(x, ~k)) ]-> \
                      [ Out(sdec(x, ~k)) ]\n\n\
                      lemma reach:\n  exists-trace \"Ex m #i. Dec(m) @ #i\"\n\nend\n";

#[test]
fn auto_sources_annotates_explicit_identity_members_and_replays() {
    if !maude_available() {
        return;
    }
    let source = r#"theory TrivialSource begin
    builtins: symmetric-encryption
    rule Start:
      [Fr(~k), Fr(~v)] --[Sent(~v)]-> [!Key(~k), Out(senc(<'tag',~v>,~k))]
    variants rule (modulo AC) Start___VARIANT_1:
      [Fr(~k), Fr(~v)] --[Sent(~v)]-> [!Key(~k), Out(senc(<'tag',~v>,~k))]
    rule Consume:
      [!Key(k), In(c)] --[Got(snd(sdec(c,k)))]-> [Out(snd(sdec(c,k)))]
    lemma witness: exists-trace "Ex x #i. Got(x)@i"
    end"#;
    let args = [
        "--prove",
        "--auto-sources",
        "--no-ndc",
        "--derivcheck-timeout=0",
        "--quit-on-warning",
        "--processors=1",
    ];
    let (code, stdout, stderr) = common::run_raw(TMP_DIR, "identity_member", source, &args);
    assert_eq!(code, 0, "{stderr}");
    // Saved replay drops contradiction-reason comments in both provers,
    // but must retain the executable annotations and both proof verdicts.
    let (code, replay, stderr) = common::run_raw(TMP_DIR, "identity_replay", &stdout, &args);
    assert_eq!(code, 0, "{stderr}");
    for output in [&stdout, &replay] {
        // Pinned pristine upstream a75fec7f verifies both in these steps.
        for verdict in [
            "witness (exists-trace): verified (4 steps)",
            "AUTO_typing (all-traces): verified (12 steps)",
        ] {
            assert!(output.contains(verdict), "{output}");
        }
    }
    fn start_member(output: &str) -> &str {
        output
            .split("rule (modulo AC) Start___VARIANT_1:")
            .nth(1)
            .expect("explicit identity member retained")
            .split("rule ")
            .next()
            .unwrap()
    }
    assert!(start_member(&stdout).contains("AUTO_OUT_"), "{stdout}");
    assert_eq!(start_member(&stdout), start_member(&replay));
}

/// Run the built binary on [`THEORY`] with `extra` flags, returning its raw
/// stdout.  The precompute document carries no build-info block, no
/// `analyzed:` line and no processing time, so its bytes need no
/// normalization.
fn precompute_stdout(stem: &str, extra: &[&str]) -> String {
    let (code, stdout, stderr) = common::run_raw(TMP_DIR, stem, THEORY, extra);
    assert_eq!(code, 0, "tamarin-rs exited {code}\nstderr:\n{stderr}");
    stdout
}

/// The two rule items close into two `ClosedProtoRule`s — `variantsProtoRule`
/// parks `Dec`'s two variants inside one of them (lib/theory/src/Rule.hs) —
/// plus the two intruder members of `crProtocol`.
#[test]
fn precompute_counts_the_closed_protocol_rules() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    assert_eq!(
        precompute_stdout("plain", &["--derivcheck-timeout=300", "--precompute-only"]),
        joined(&[
            "Multiset rewriting rules: 4",
            "Raw sources: 6 cases, 5 partial deconstructions left",
            "Refined sources: 6 cases, 5 partial deconstructions left",
        ])
    );
}

/// `--auto-sources` splits `Dec` into its two variants before the cache is
/// built, so the count rises by one and the refined sources close.
#[test]
fn precompute_counts_the_unfolded_variants_under_auto_sources() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    assert_eq!(
        precompute_stdout(
            "auto",
            &[
                "--derivcheck-timeout=300",
                "--precompute-only",
                "--auto-sources",
            ]
        ),
        joined(&[
            "Multiset rewriting rules: 5",
            "Raw sources: 6 cases, 5 partial deconstructions left",
            "Refined sources: 6 cases, deconstructions complete",
        ])
    );
}

/// Existing sources lemmas can disable automatic generation even when the
/// shared preliminary cache has raw chains. The public rules must then remain
/// folded, and refining the cache must not erase its raw chains.
#[test]
fn manual_sources_preserve_raw_chains_and_disable_unfolding() {
    if !maude_available() {
        return;
    }
    let source = r#"theory ManualSources begin
    builtins: symmetric-encryption
    rule Setup: [Fr(~k)] --> [!Key(~k)]
    rule Dec: [!Key(~k), In(x)] --[Dec(sdec(x,~k))]-> [Out(sdec(x,~k))]
    lemma manually_closed [sources]: "All x #i. Dec(x)@i ==> F"
    end"#;
    // Exact output from pristine upstream a75fec7f, in both modes.
    let expected = joined(&[
        "Multiset rewriting rules: 4",
        "Raw sources: 6 cases, 5 partial deconstructions left",
        "Refined sources: 6 cases, deconstructions complete",
    ]);
    for (stem, extra) in [
        ("manual_sources", vec![]),
        ("manual_sources_auto", vec!["--auto-sources"]),
    ] {
        let mut args = vec!["--precompute-only", "--derivcheck-timeout=0"];
        args.extend(extra);
        let (code, stdout, stderr) = common::run_raw(TMP_DIR, stem, source, &args);
        assert_eq!(code, 0, "{stderr}");
        assert_eq!(stdout, expected, "{stem}");
    }
}
