// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! End-to-end byte pins for the rule count of the `--precompute-only`
//! document, with and without `--auto-sources`.
//!
//! HS `prettyPrecomputation` prints `length (L.get crProtocol rules)`
//! (ClosedTheory.hs:553-575, see line 562).  `crProtocol` carries one entry per
//! `ClosedProtoRule` of the closed theory plus the intruder rules that are
//! neither construction nor destruction rules (`closeRuleCache`,
//! CloseRule.hs:402-436).  When `--auto-sources` finds partial deconstructions
//! in the refined sources, `closeTheoryWithMaude` closes over `unfoldRules
//! items` (CloseRule.hs:56-64, see line 58), and `unfoldRules` maps
//! `unfoldRuleVariants` over every rule item (CloseRule.hs:106-110), so a rule
//! whose AC variant is non-trivial contributes one `ClosedProtoRule` per
//! variant (`unfoldRuleVariants`, lib/theory/src/Rule.hs:63-78) rather than one
//! for the whole rule.
//!
//! No corpus file passes both flags, so neither the prove gate nor the pretty
//! gate reaches this count.  Both expectations below are verbatim oracle bytes
//! from the pinned v1.13.0 binary (Git revision ef3f0468) on [`THEORY`]; the
//! pair is the anti-vacuity statement that `--auto-sources` moves the count on
//! this theory, so a count that parks the unfolded variants under one entry
//! reads 4 twice and fails the second test alone.
//!
//! `--derivcheck-timeout=300` is on both runs because a derivation check that
//! times out adds a wellformedness entry, and `ppWf` (Batch.hs:244-247) puts
//! its WARNING line ahead of the stats.

mod common;

use common::{joined, maude_available};

/// The temp subdirectory this suite writes its theories to.
const TMP_DIR: &str = "tamarin_prover_precompute_auto_sources";

/// `Dec` decrypts an incoming message under a stored key, so Maude gives it
/// two AC variants: the generic one and the one where the input is
/// `senc(m, ~k)`.  Its `Out(sdec(x, ~k))` conclusion leaves the refined
/// sources with partial deconstructions, the condition `--auto-sources` tests
/// before it unfolds (`containsPartialDeconstructions`,
/// lib/theory/src/Rule.hs:89-94).
const THEORY: &str = "theory AutoSourcesUnfold\nbegin\n\n\
                      builtins: symmetric-encryption\n\n\
                      rule Setup:\n  [ Fr(~k) ] --> [ !Key(~k) ]\n\n\
                      rule Dec:\n  \
                      [ !Key(~k), In(x) ] --[ Dec(sdec(x, ~k)) ]-> \
                      [ Out(sdec(x, ~k)) ]\n\n\
                      lemma reach:\n  exists-trace \"Ex m #i. Dec(m) @ #i\"\n\nend\n";

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
/// parks `Dec`'s two variants inside one of them (lib/theory/src/Rule.hs:84) —
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
