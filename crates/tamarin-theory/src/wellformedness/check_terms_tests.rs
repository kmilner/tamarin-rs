// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_parser::parse_theory;

/// The `Formula terms` findings for `src`: the arm [`super::check_terms`]
/// contributes to [`super::super::formulas::formula_reports`], HS's
/// `formulaReports` loop (Wellformedness.hs:1003), over the elaborated
/// theory the load pipelines check.
fn check_terms_report(src: &str) -> Vec<WfError> {
    let thy = parse_theory(src, &[]).expect("parse");
    let elab = crate::elaborate::elaborate(&thy).expect("elaborate");
    super::super::formulas::formula_reports(&elab)
        .into_iter()
        .filter(|e| e.topic == "Formula terms")
        .collect()
}

#[test]
fn private_nullary_function_is_allowed() {
    // secretF reproducer: `f/0 [private]`, lemma `All #i. K(f) @ i ==> F`.
    let src = "theory T begin\n\
               functions: f/0 [private]\n\
               lemma secretF:\n  \"All #i. K(f) @ i ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert!(report.is_empty(), "expected no offenders, got {:?}", report);
}

#[test]
fn reducible_destructor_is_offender() {
    // type_assertion-style: `snd`/`sdec` are reducible destructors.
    let src = "theory T begin\n\
               builtins: symmetric-encryption\n\
               lemma L:\n\
                 \"All x #i. K(x) @ i ==> Ex body key #j #k. \
                   K(body) @ j & key = snd(sdec(body, key)) & j < i & k < i\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(report.len(), 1, "expected one Formula-terms block");
    let msg = &report[0].message;
    assert!(
        msg.contains("`snd(sdec(Bound 3,Bound 2))'"),
        "offender rendering mismatch:\n{}",
        msg
    );
}

/// The offender spelling is HS's `Show (Term a)` (Term/Term/Raw.hs:227-237)
/// over `VTerm Name (BVar LVar)`, not `prettyTerm`: a nested application
/// stays prefix with comma-separated arguments and no space, a bound
/// variable is the derived `Show (BVar v)` constructor plus its De Bruijn
/// index, and a free one carries `Show LVar`'s sort sigil.
///
/// Oracle bytes (ef3f0468, probes S3/S3_offender_show.spthy).
#[test]
fn offender_text_matches_the_haskell_show() {
    let src = "theory T begin\n\
               builtins: symmetric-encryption\n\
               lemma Nested:\n\
                 \"All x #i. K(x) @ i ==> Ex body key #j #k. \
                   K(body) @ j & key = snd(sdec(body, key)) & j < i & k < i\"\n\
               lemma FreeTimepoint:\n  \"All #j. K('c') @ i ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(
        report.len(),
        2,
        "one block per offending lemma: {:?}",
        report
    );
    one_offender(&report[..1], "`snd(sdec(Bound 3,Bound 2))'");
    one_offender(&report[1..], "`Free #i'");
}

#[test]
fn plain_protocol_lemma_no_offenders() {
    let src = "theory T begin\n\
               lemma L:\n  \"All x #i. K(x) @ i ==> Ex #j. K(x) @ j\"\n\
               end\n";
    assert!(check_terms_report(src).is_empty());
}

#[test]
fn public_constant_allowed() {
    let src = "theory T begin\n\
               lemma L:\n  \"All #i. K('c') @ i ==> F\"\n\
               end\n";
    assert!(check_terms_report(src).is_empty());
}

#[test]
fn unary_hash_with_surplus_args_is_allowed() {
    // `hashing` gives `h/1`.  Surface `h(x, y)` is folded to `h(<x, y>)`
    // (an irreducible `h/1` applied to a pair) at parse time in HS
    // (naryOpApp k==1) — so it is ALLOWED, not flagged as a reducible
    // `h/2`.  This is the alethea selectionphase root.
    let src = "theory T begin\n\
               builtins: hashing\n\
               lemma L:\n  \"All x y #i. K(h(x, y)) @ i ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert!(report.is_empty(), "expected no offenders, got {:?}", report);
}

#[test]
fn bare_message_use_does_not_bind_to_node_binder() {
    // A bare message-position use `x` must NOT bind to a `#x` node
    // binder of the same name+idx: HS's `LVar` Eq compares sort, and the
    // parser gives a bare message use the concrete sort `LSortMsg`,
    // so `quantify`'s `v == x` fails and the use stays `Free x`.
    //
    // Verified against the v1.13.0 binary on
    //   lemma L: "All #x. (K(x) @ #x) ==> F"
    // which prints `Lemma `L' uses terms of the wrong form: `Free x'`.
    let src = "theory T begin\n\
               lemma L:\n  \"All #x. (K(x) @ #x) ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(report.len(), 1, "expected one Formula-terms block");
    assert!(
        report[0].message.contains("`Free x'"),
        "bare use must stay Free (not bind to #x), got:\n{}",
        report[0].message
    );
}

#[test]
fn free_message_variable_is_offender() {
    // A msg var used but never quantified -> Free offender.
    let src = "theory T begin\n\
               lemma L:\n  \"All #i. K(x) @ i ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(report.len(), 1);
    assert!(
        report[0].message.contains("`Free x'"),
        "got: {}",
        report[0].message
    );
}

/// The one offender rendering of the single block `report` produced.
fn one_offender(report: &[WfError], want: &str) {
    assert_eq!(report.len(), 1, "expected one block, got {:?}", report);
    assert!(
        report[0].message.contains(want),
        "expected offender {}, got:\n{}",
        want,
        report[0].message
    );
}

#[test]
fn prefix_em_is_a_reducible_c_symbol_even_when_user_declared() {
    // `naryOpApp` routes the prefix spelling `em(…)` to `fAppC EMap` on
    // the WRITTEN NAME (Theory/Text/Parser/Term.hs:103), so a user
    // `functions: em/2` declaration beside `bilinear-pairing` does not
    // turn it into a NoEq symbol.  `C EMap` is subtracted from the
    // irreducible set by `bpReducibleFunSig`
    // (Term/Term/FunctionSymbols.hs:311-312,
    // Term/Maude/Signature.hs:120-124), so the enclosing `*` is an
    // offender even though `f/2`, `em/2` and `AC Mult` all look
    // irreducible by name.
    //
    // Oracle bytes (ef3f0468, probes S3/S3_user_em2_bp.spthy):
    //   Lemma `L1' uses terms of the wrong form:
    //     `Mult(f('g','h'),em('g','h'))'
    let src = "theory T begin\n\
               builtins: bilinear-pairing\n\
               functions: em/2, f/2\n\
               lemma L1:\n  \"All #i. Test(em('g', 'h') * f('g', 'h')) @ #i ==> F\"\n\
               end\n";
    one_offender(&check_terms_report(src), "`Mult(f('g','h'),em('g','h'))'");
}

#[test]
fn a_user_em_without_bilinear_pairing_is_an_ordinary_symbol() {
    // Without `bilinear-pairing` the theory has no `C EMap` operator, so
    // `term_to_vterm` keeps a user `em/2` a NoEq symbol
    // (`elaborate.rs`, which records why the port gates the arm HS keys
    // on the name alone).  The wellformedness check reads the same terms
    // the solver does, so the constructor `em/2` is irreducible here and
    // nothing is reported.
    let src = "theory T begin\n\
               builtins: diffie-hellman\n\
               functions: em/2, f/2\n\
               lemma L1:\n  \"All #i. Test(em('g', 'h') * f('g', 'h')) @ #i ==> F\"\n\
               end\n";
    assert!(check_terms_report(src).is_empty());
}

#[test]
fn em_written_as_alg_app_stays_a_noeq_symbol() {
    // `em{a}b` goes through `binaryAlgApp`, which has no `em` arm and
    // builds `fAppNoEq ("em", …)` (Theory/Text/Parser/Term.hs:108-121).
    // So it sorts among the NoEq symbols ("em" < "f") instead of after
    // them, unlike the prefix spelling above.
    //
    // Oracle bytes (ef3f0468, div2/algapp_em.spthy):
    //   `Mult(em('g','h'),f('g','h'))'
    let src = "theory T begin\n\
               builtins: bilinear-pairing\n\
               functions: f/2\n\
               lemma L1:\n  \"All #i. Test(em{'g'}'h' * f('g', 'h')) @ #i ==> F\"\n\
               end\n";
    one_offender(&check_terms_report(src), "`Mult(em('g','h'),f('g','h'))'");
}

#[test]
fn c_and_ac_arguments_sort_on_the_de_bruijn_form() {
    // `em(x, y)` sorts its two arguments AFTER `quantify` has replaced
    // them by De Bruijn indices, so the pair comes out ascending in the
    // INDEX (`Bound 1` before `Bound 2`) — the reverse of the source
    // order, in which `x` precedes `y`.  The enclosing `Mult` sorts its
    // NoEq operand ahead of the C operand.
    //
    // Oracle bytes (ef3f0468, div2/em_c_tier.spthy lemma L2):
    //     `Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))',
    //     `Mult(f(Bound 3,Bound 2),em(Bound 2,Bound 3))'
    let src = "theory T begin\n\
               builtins: bilinear-pairing\n\
               functions: f/2, aaa/2\n\
               lemma L2:\n  \"All x y #i. Test2(em(x, y) * aaa(x, y)) @ #i ==> \
                 Ex #j. Test(em(x, y) * f(x, y)) @ #j\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(report.len(), 1, "expected one block, got {:?}", report);
    assert!(
        report[0].message.contains(
            "`Mult(aaa(Bound 2,Bound 1),em(Bound 1,Bound 2))',\n    \
             `Mult(f(Bound 3,Bound 2),em(Bound 2,Bound 3))'"
        ),
        "got:\n{}",
        report[0].message
    );
}

#[test]
fn builtin_ac_arguments_are_flattened_and_sorted() {
    // `('b' ++ 'a') ++ ('c' XOR 'd')`: `fAppAC` splices the nested
    // `Union` node's arguments into the outer one and sorts the result,
    // so the two constants precede the `Xor` application.
    //
    // Oracle bytes (ef3f0468):
    //   `Union('a','b',Xor('c','d'))'
    let src = "theory T begin\n\
               builtins: xor, multiset\n\
               lemma L3:\n  \"All #i. Test(('b' ++ 'a') ++ ('c' XOR 'd')) @ #i ==> F\"\n\
               end\n";
    one_offender(&check_terms_report(src), "`Union('a','b',Xor('c','d'))'");
}

#[test]
fn user_ac_symbol_written_prefix_is_flattened_and_sorted() {
    // A `[AC]` symbol applied prefix is `fAppAC (ACfct …)` whatever the
    // written arity (Theory/Text/Parser/Term.hs:104-105), so the nested
    // `uac('z','a')` is spliced in and the whole list sorted.
    //
    // Oracle bytes (ef3f0468):
    //   Lemma `L1' ... `uac('a',red('b','a'))'
    //   Lemma `L2' ... `uac('a','z',red('b','c'))'
    let src = "theory T begin\n\
               functions: uac/2 [AC], red/2\n\
               equations: red(x, y) = x\n\
               lemma L1:\n  \"All #i. Test(uac(red('b','a'), 'a')) @ #i ==> F\"\n\
               lemma L2:\n  \"All #i. Test(uac(uac('z','a'), red('b','c'))) @ #i ==> F\"\n\
               end\n";
    let report = check_terms_report(src);
    assert_eq!(report.len(), 2, "expected two blocks, got {:?}", report);
    assert!(
        report[0].message.contains("`uac('a',red('b','a'))'"),
        "got:\n{}",
        report[0].message
    );
    assert!(
        report[1].message.contains("`uac('a','z',red('b','c'))'"),
        "got:\n{}",
        report[1].message
    );
}

#[test]
fn bare_free_variable_under_at_keeps_its_node_sort() {
    // `@ i` is parsed by `nodevar`, so the free `i` is an `LSortNode`
    // `LVar` and `Show LVar` prefixes it with `#`.
    //
    // Oracle bytes (ef3f0468): `Free #i'
    let src = "theory T begin\n\
               lemma L1:\n  \"All #j. K('c') @ i ==> F\"\n\
               end\n";
    one_offender(&check_terms_report(src), "`Free #i'");
}
