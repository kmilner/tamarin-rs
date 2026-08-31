// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::pretty_theory::format_wf_block;

/// One rule and one `exists-trace` lemma named `good`, the probe the expected
/// bytes below come from.
const ONE_LEMMA: &str = "theory S8LemmaArgs\nbegin\n\
                         rule R: [ Fr(~x) ] --[ A(~x) ]-> [ Out(~x) ]\n\
                         lemma good:\n  exists-trace \"Ex x #i. A(x) @ #i\"\n\
                         end\n";

/// The elaborated theory for `src`, as a loader holds it before translation.
fn elaborated(src: &str) -> Theory {
    let parsed = tamarin_parser::parse_theory(src, &[]).expect("parse");
    crate::elaborate::elaborate(&parsed).expect("elaborate")
}

/// [`elaborated`] with the `--prove`/`--lemma` selection both drivers write
/// into the theory's options before the wellformedness pass runs.  `names` is
/// HS's `lemmaNames` (TheoryLoader.hs:326): the `--prove` values then the
/// `--lemma` values, each flag's values in reverse command-line order.
fn with_lemma_args(src: &str, names: &[&str]) -> Theory {
    let mut thy = elaborated(src);
    thy.options.lemmas_to_prove = names.iter().map(|s| (*s).to_string()).collect();
    thy
}

/// A theory with no `--prove`/`--lemma` value at all: HS's fold over an empty
/// `_lemmasToProve` finds nothing, so `null notProvedLemmas` returns the empty
/// report (Wellformedness.hs:1159).
#[test]
fn no_lemma_argument_reports_nothing() {
    assert!(check_if_lemmas_in_theory(&elaborated(ONE_LEMMA)).is_empty());
}

/// Bare `--prove` is HS's `lemmaArgsNames == [[]]` guard
/// (Wellformedness.hs:1158): the empty name means "prove everything", so the
/// check is skipped rather than reporting the empty string.
#[test]
fn bare_prove_argument_skips_the_check() {
    assert!(check_if_lemmas_in_theory(&with_lemma_args(ONE_LEMMA, &[""])).is_empty());
}

/// A trailing `*` matches by prefix (`lemmaChecker`,
/// Wellformedness.hs:1145-1147), so `go*` corresponds to `good`.
#[test]
fn prefix_argument_matches_a_lemma_by_prefix() {
    assert!(check_if_lemmas_in_theory(&with_lemma_args(ONE_LEMMA, &["go*"])).is_empty());
}

/// The whole `Check presence of the --prove/--lemma arguments in theory`
/// block, for two `--prove` values neither of which names a lemma.  Repeats of
/// one flag reach HS's report in CLI order: its `Arguments` list is built by
/// prepending (`addArg`, Console.hs:279-280) and `findNotProvedLemmas`
/// (Wellformedness.hs:1141) prepends again.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468) for this theory under
/// `--prove=aaa --prove=bbb --derivcheck-timeout=0`.
#[test]
fn unmatched_arguments_are_listed_in_cli_order() {
    let report = check_if_lemmas_in_theory(&with_lemma_args(ONE_LEMMA, &["bbb", "aaa"]));
    assert_eq!(
        format_wf_block(&report),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Check presence of the --prove/--lemma arguments in theory\n\
         =========================================================\n\n  \
         --> 'aaa', 'bbb' from arguments do(es) not correspond to a specified lemma in the theory \n*/"
    );
}

/// `findNotProvedLemmas`' `foldl` prepends, so it reverses `lemmaNames`, whose
/// two halves are the `--prove` values then the `--lemma` values: the report
/// lists the `--lemma` values first.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468) for this theory under
/// `--prove=aaa --lemma=bbb --derivcheck-timeout=0`.
#[test]
fn lemma_arguments_are_listed_before_prove_arguments() {
    let report = check_if_lemmas_in_theory(&with_lemma_args(ONE_LEMMA, &["aaa", "bbb"]));
    assert_eq!(
        format_wf_block(&report),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Check presence of the --prove/--lemma arguments in theory\n\
         =========================================================\n\n  \
         --> 'bbb', 'aaa' from arguments do(es) not correspond to a specified lemma in the theory \n*/"
    );
}

/// `--prove --lemma=good` mixes the empty name with a matching one, so the
/// `[[]]` guard does not fire and the empty name is reported on its own.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468) for this theory under
/// `--prove --lemma=good --derivcheck-timeout=0`.
#[test]
fn bare_prove_beside_a_named_lemma_reports_the_empty_name() {
    let report = check_if_lemmas_in_theory(&with_lemma_args(ONE_LEMMA, &["", "good"]));
    assert_eq!(
        format_wf_block(&report),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Check presence of the --prove/--lemma arguments in theory\n\
         =========================================================\n\n  \
         --> '' from arguments do(es) not correspond to a specified lemma in the theory \n*/"
    );
}

/// `reuse` on an `all-traces` lemma is what the attribute is for, so
/// `lemmaAttributeReport`'s guard (Wellformedness.hs:927-928) drops it.
#[test]
fn reuse_on_an_all_traces_lemma_is_not_reported() {
    let src = "theory S8Reuse begin\n\
               rule R: [ Fr(~x) ] --[ A(~x) ]-> [ Out(~x) ]\n\
               lemma one [reuse]:\n  all-traces \"All x #i. A(x) @ #i ==> T\"\n\
               end\n";
    assert!(lemma_attribute_report(&elaborated(src)).is_empty());
}

/// HS's list-monad `do` (Wellformedness.hs:925-932) yields ONE entry per
/// offending lemma, which is what the trailing
/// `WARNING: N wellformedness check failed!` line counts (`length rep`,
/// Batch.hs:246).  `prettyWfErrorReport` then prints the underlined topic once
/// and separates the two bodies with the two-space blank line
/// `intersperse (text "")` renders under `nest 2`.
///
/// Bytes are the pinned oracle's (Git revision ef3f0468) for
/// `scripts/divergence_fixtures/s8_two_reuse_exists_lemmas.spthy` under
/// `--derivcheck-timeout=0`.
#[test]
fn two_reuse_exists_lemmas_emit_two_entries() {
    let src = "theory S8TwoReuseExistsLemmas\nbegin\n\
               rule R: [ Fr(~x) ] --[ A(~x) ]-> [ Out(~x) ]\n\
               lemma one [reuse]:\n  exists-trace \"Ex x #i. A(x) @ #i\"\n\
               lemma two [reuse]:\n  exists-trace \"Ex y #j. A(y) @ #j\"\n\
               end\n";
    let report = lemma_attribute_report(&elaborated(src));
    assert_eq!(report.len(), 2, "one entry per offending lemma");
    assert_eq!(
        format_wf_block(&report),
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Lemma annotations\n=================\n\n  \
         Lemma `one': cannot reuse 'exists-trace' lemmas\n  \n  \
         Lemma `two': cannot reuse 'exists-trace' lemmas\n*/"
    );
}
