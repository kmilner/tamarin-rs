// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--no-ndc` on the web load path.
//!
//! HS hands the interactive mode's `TheoryLoadOptions` to `withWebUI` as the
//! partially applied `loadTheory thyLoadOptions` (Interactive.hs:135), and
//! `addParamsOptions`' `addNdcOption` (TheoryLoader.hs:821-826) writes
//! `ndcCheck` — `not (argExists "no-ndc")` (TheoryLoader.hs:365-366) — into the
//! loaded theory's `_deductionChainCheck`.  `checkCloseIntrRule` reads that
//! field back and runs `prettyNDCcheck` only when it holds
//! (TheoryLoader.hs:513-519).  So a web load with the flag set must skip the
//! NDC pass exactly like the `--prove` batch load does.
//!
//! Both verdicts are pinned to the ef3f0468 oracle on the `NdcXorr` fixture,
//! whose `xorr` destructor group is the family the pass tags:
//!
//! ```text
//! $ tamarin-prover --no-ndc ndc_xorr.spthy
//! functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC]
//! $ tamarin-prover ndc_xorr.spthy
//! stderr: Function xorr has the NDC property.
//! functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC,NDC]
//! ```
//!
//! These tests need Maude.  They skip only when `TAM_ALLOW_NO_MAUDE=1` is set.
//!
//! Cost.  The load with the flag on takes about 8.3s under `--profile ci`.
//! That is the profile which `.github/workflows/ci.yml` runs.  The same load
//! takes about 56s under a plain debug build.  A measurement from a debug
//! build therefore states the CI cost seven times too high.  In both builds
//! this load is about 90% of the test time of this crate.  The cause is
//! `apply_ndc_check`, which runs one deduction proof for each chainable rule
//! pair.  The load with the flag off takes 40ms.  The cost comes from the
//! pass itself, not from the size of the fixture.  A smaller fixture would
//! need a new capture of both oracle verdicts above against a different
//! theory.

use std::path::PathBuf;

use tamarin_server::theory_io;
use tamarin_server::TheoryEntry;
use tamarin_test_support::require_maude_path;

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("ndc_xorr.spthy")
}

/// The `functions:` line of the loaded theory's signature — the header the web
/// message page's "Signature" section renders (`web_signature_block`), where
/// the NDC pass's tags surface as ` [AC,NDC]`.
fn functions_line(entry: &TheoryEntry) -> String {
    tamarin_theory::pretty_theory::web_signature_block(&entry.typed_theory.signature)
        .lines()
        .find(|l| l.starts_with("functions:"))
        .expect("signature block carries a functions: line")
        .to_string()
}

/// Destructor rules in the load-time intruder cache whose head symbol carries
/// the NDC tag.  Only the NDC pass sets it (`apply_ndc_check`'s `add_ndc`), and
/// the cache is what every `ProofContext` the theory builds consumes.
fn ndc_tagged_cache_rules(entry: &TheoryEntry) -> usize {
    entry
        .ndc_cache
        .as_ref()
        .expect("Maude booted, so the load stored an intruder cache")
        .iter()
        .filter(|r| match &r.info {
            tamarin_theory::rule::IntrRuleACInfo::DestrRule { funs, .. } => {
                funs.first().is_some_and(|f| f.is_ndc_fun_sym())
            }
            _ => false,
        })
        .count()
}

#[test]
fn ndc_check_flag_gates_the_web_load_ndc_pass() {
    let Some(maude) = require_maude_path() else {
        return;
    };
    // The process-wide setup `serve` applies, so the signature renders at the
    // web width the message page uses.
    tamarin_server::init_process_globals();
    let path = fixture();
    // `derivcheck_timeout = 0` skips the dynamic derivation checks, which this
    // test does not observe (HS `TheoryLoader.hs:578-579` skips them on EQ).
    let deriv_off = 0;

    // Flag absent — HS `ndcCheck = True` (TheoryLoader.hs:279), the pass runs.
    theory_io::set_ndc_check(true);
    let checked = theory_io::load_from_path(&path, &maude, deriv_off).expect("fixture loads");
    assert_eq!(
        functions_line(&checked),
        "functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC,NDC]",
    );
    assert!(
        ndc_tagged_cache_rules(&checked) > 0,
        "the pass tags the xorr destructor rules it found NDC",
    );

    // `--no-ndc` — HS's `else (sign, intrRules)` branch (TheoryLoader.hs:517):
    // no verdicts, no signature tags, cache in raw assembly order.
    theory_io::set_ndc_check(false);
    let skipped = theory_io::load_from_path(&path, &maude, deriv_off).expect("fixture loads");
    assert_eq!(
        functions_line(&skipped),
        "functions: fst/1, pair/2, snd/1, zeroo/0, xorr/2 [AC]",
    );
    assert_eq!(
        ndc_tagged_cache_rules(&skipped),
        0,
        "a skipped pass tags nothing",
    );

    // Back to the default every other load in this process expects.
    theory_io::set_ndc_check(true);
}
