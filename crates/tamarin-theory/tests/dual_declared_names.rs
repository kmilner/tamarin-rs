// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the resolution of a DUAL-DECLARED name — one that is BOTH a
//! `NoEq` funsym of the full signature (user-declared or theory-contributed)
//! AND a user-declared `[AC]` symbol.
//!
//! HS resolves the prefix and `op{a}b` spellings of such a name through
//! `lookupArity` (Theory/Text/Parser/Term.hs:62-72), a list lookup over
//! `S.toList (userDefinedFunSyms maudeSig)` in which every `NoEqUser` sorts
//! before every `ACfctUser` (constructor order of `UserDefinedSym`,
//! Term/Term/FunctionSymbols.hs:146-147) — so the `NoEq` symbol wins those
//! spellings.  The INFIX spelling bypasses `lookupArity` entirely: `acterm`
//! (Term.hs:163-174) builds `fAppACfct` straight from `stACFunSyms`, so it
//! stays the AC symbol.  `nullaryApp` (Term.hs:158-163) still resolves a bare
//! nullary name to the `NoEq` constant.
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468)
//! for the same theories, plain no-prove load.

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::pretty_theory::{format_wf_block, web_proto_rules, web_signature_block};

/// The `rule (modulo E)` echoes of a theory's rules, with the AC-variant
/// annotation below each echo split off (its content depends on the variant
/// computation, not on term resolution).
fn rule_echoes(src: &str) -> Vec<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    // The load pipelines render with the theory's user-function bundle
    // installed (`set_user_funs_for_theory`), which the canonicalization the
    // rule printer runs reads through.
    let _guard = tamarin_theory::elaborate::set_user_funs_for_theory(&thy);
    let elaborated = elaborate(&thy).expect("elaborate");
    web_proto_rules(&thy, &elaborated)
        .into_iter()
        .map(|rule| match rule.split_once("\n\n  /*") {
            Some((echo, _annotation)) => echo.to_string(),
            None => rule,
        })
        .collect()
}

/// The rendered `/* WARNING … */` block the batch / web load pipelines print
/// for a theory's formula reports, or `None` when all arms stay silent.
fn wf_block(src: &str) -> Option<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = elaborate(&thy).expect("elaborate");
    let errs =
        tamarin_theory::formula_reports::formula_reports(&thy, &elaborated.signature.maude_sig);
    if errs.is_empty() {
        return None;
    }
    Some(format_wf_block(&errs))
}

/// The body HS wraps every Formula-terms offender in.
const OFFENDER_TAIL: &str = "\n  \n  \
     The only allowed terms are public constants and bound node and\n  \
     message variables. If you encounter free message variables, then\n  \
     you might have forgotten a #-prefix. Sort prefixes can only be\n  \
     dropped where this is unambiguous. Moreover, reducible function\n  \
     symbols are disallowed.";

/// `/* WARNING … */` block with ONE Formula-terms offender line per entry.
fn formula_terms_block(offenders: &[&str]) -> String {
    let mut out = String::from(
        "/*\nWARNING: the following wellformedness checks failed!\n\n\
         Formula terms\n\
         =============\n",
    );
    for (i, o) in offenders.iter().enumerate() {
        if i > 0 {
            // Two-space blank line between consecutive offender entries.
            out.push_str("\n  ");
        }
        out.push_str("\n  ");
        out.push_str(o);
        out.push_str(OFFENDER_TAIL);
    }
    out.push_str("\n*/");
    out
}

/// Prefix `f(…)` resolves to the NoEq symbol (rendered prefix, unflattened),
/// the infix spelling stays the AC symbol (rendered infix, flattened+sorted)
/// — side by side in one rule.  Oracle bytes: probe `p_infix`.
#[test]
fn prefix_resolves_noeq_while_infix_stays_ac() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2, red/2\n\
               equations: red(x, y) = x\n\n\
               rule R:\n\
               \x20 [ ] --[ A('a' f 'b'), B(f('a','b')) ]-> [ ]\n\n\
               rule R2:\n\
               \x20 [ In(f(x,y)) ] --> [ Out('a' f y) ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        [
            "rule (modulo E) R:\n   [ ] --[ A( ('a' f 'b') ), B( f('a', 'b') ) ]-> [ ]",
            "rule (modulo E) R2:\n   [ In( f(x, y) ) ] --> [ Out( ('a' f y) ) ]",
        ]
    );
}

/// `f{a}b` goes through the same `lookupArity` NoEq-first lookup
/// (`binaryAlgApp`, Theory/Text/Parser/Term.hs:108-121): NoEq for a dual
/// name.  Oracle bytes: probe `p_algapp2`.
#[test]
fn algapp_resolves_noeq_for_a_dual_name() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2\n\n\
               rule R:\n\
               \x20 [ ] --[ A(f{'a'}'b') ]-> [ ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        ["rule (modulo E) R:\n   [ ] --[ A( f('a', 'b') ) ]-> [ ]"]
    );
}

/// The control: with no NoEq symbol in the way, `myac{a}b` IS the AC symbol
/// and renders infix.  Oracle bytes: probe `p_algapp_pure_ac`.
#[test]
fn algapp_stays_ac_without_a_noeq_collision() {
    let src = "theory T begin\n\n\
               functions: myac/2 [AC]\n\n\
               rule R:\n\
               \x20 [ ] --[ A(myac{'a'}'b') ]-> [ ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        ["rule (modulo E) R:\n   [ ] --[ A( ('a' myac 'b') ) ]-> [ ]"]
    );
}

/// A bare nullary dual name resolves to the NoEq constant (`nullaryApp`,
/// Term.hs:158-163).  Oracle bytes: probe `p_nullary_rule`.
#[test]
fn a_bare_nullary_dual_name_stays_the_noeq_constant() {
    let src = "theory T begin\n\n\
               functions: g/2 [AC], g/0\n\n\
               rule R:\n\
               \x20 [ ] --[ D(g) ]-> [ ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        ["rule (modulo E) R:\n   [ ] --[ D( g ) ]-> [ ]"]
    );
}

/// Under `builtins: diffie-hellman` the theory-contributed NoEq `exp/2` wins
/// the prefix spelling of a dual-declared `exp`, and the resolved symbol IS
/// `expSym`, so HS `prettyTerm` renders it `'a'^'b'` (Term/Term.hs:310); the
/// infix spelling stays the AC symbol.  Oracle bytes: probes `probe2` (exp-ac)
/// and `p_exp_infix`.
#[test]
fn a_dual_declared_exp_prefix_renders_as_the_dh_caret() {
    let src = "theory T begin\n\n\
               builtins: diffie-hellman\n\
               functions: exp/2 [AC]\n\n\
               rule R:\n\
               \x20 [ ] --[ A(exp('a', 'b')) ]-> [ ]\n\n\
               rule R2:\n\
               \x20 [ ] --[ A('a' exp 'b') ]-> [ ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        [
            "rule (modulo E) R:\n   [ ] --[ A( 'a'^'b' ) ]-> [ ]",
            "rule (modulo E) R2:\n   [ ] --[ A( ('a' exp 'b') ) ]-> [ ]",
        ]
    );
}

/// The same `'a'^'b'` rendering for prefix `exp(…)` WITHOUT any `[AC]`
/// declaration — the resolution is by the full signature, not by the
/// collision.  Oracle bytes: probe `p_dh_prefix`.
#[test]
fn a_plain_dh_exp_prefix_renders_as_the_caret_too() {
    let src = "theory T begin\n\n\
               builtins: diffie-hellman\n\n\
               rule R:\n\
               \x20 [ ] --[ A(exp('a', 'b')) ]-> [ ]\n\n\
               end\n";
    assert_eq!(
        rule_echoes(src),
        ["rule (modulo E) R:\n   [ ] --[ A( 'a'^'b' ) ]-> [ ]"]
    );
}

/// The Formula-terms check classifies the resolved heads: the NoEq `f` (no
/// equations) is irreducible, so only the lemma whose ARGUMENT carries the
/// reducible `red` is flagged, and the nested prefix `f` stays unflattened
/// and unsorted in the offender.  Oracle bytes: probe `ac_noeq_collide`.
#[test]
fn formula_terms_classifies_the_noeq_head_by_its_own_reducibility() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2, red/2\n\
               equations: red(x, y) = x\n\n\
               lemma L1:\n\
               \x20 \"All #i. Test(f('b', red('c','d'))) @ #i ==> F\"\n\
               lemma L2:\n\
               \x20 \"All #i. Test(f(f('z','a'), 'b')) @ #i ==> F\"\n\n\
               end\n";
    assert_eq!(
        wf_block(src).expect("L1's reducible red argument must be reported"),
        formula_terms_block(&["Lemma `L1' uses terms of the wrong form: `f('b',red('c','d'))'"])
    );
}

/// The infix chain resolves to the AC symbol, which stays irreducible, so
/// only the reducible `red` ARGUMENT flags a lemma — and the offender renders
/// the flattened, sorted AC argument list.  Oracle bytes: probe `p_wf_infix`.
#[test]
fn formula_terms_classifies_the_infix_chain_as_the_ac_symbol() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2, red/2\n\
               equations: red(x, y) = x\n\n\
               lemma L1:\n\
               \x20 \"All #i. Test('a' f 'b') @ #i ==> F\"\n\
               lemma L2:\n\
               \x20 \"All #i. Test('a' f red('b','c')) @ #i ==> F\"\n\
               lemma L3:\n\
               \x20 \"All #i. Test(('a' f 'b') f 'c') @ #i ==> F\"\n\n\
               end\n";
    assert_eq!(
        wf_block(src).expect("L2's reducible red argument must be reported"),
        formula_terms_block(&["Lemma `L2' uses terms of the wrong form: `f('a',red('b','c'))'"])
    );
}

/// Under DH the resolved NoEq `exp` is REDUCIBLE (`dhReducibleFunSig`,
/// Term/Term/FunctionSymbols.hs:307-308), so every prefix/`^` use is flagged,
/// rendered prefix, unflattened and unsorted.  Oracle bytes: probe
/// `exp_ac_prefix`.
#[test]
fn formula_terms_flags_every_noeq_exp_use_under_dh() {
    let src = "theory T begin\n\n\
               builtins: diffie-hellman\n\
               functions: exp/2 [AC], red/2\n\
               equations: red(x, y) = x\n\n\
               lemma L1:\n\
               \x20 \"All #i. Test('a' ^ 'b') @ #i ==> F\"\n\
               lemma L2:\n\
               \x20 \"All #i. Test(exp('b', red('c','d'))) @ #i ==> F\"\n\
               lemma L3:\n\
               \x20 \"All #i. Test(exp('b', 'a') ^ 'c') @ #i ==> F\"\n\n\
               end\n";
    assert_eq!(
        wf_block(src).expect("all three exp uses must be reported"),
        formula_terms_block(&[
            "Lemma `L1' uses terms of the wrong form: `exp('a','b')'",
            "Lemma `L2' uses terms of the wrong form: `exp('b',red('c','d'))'",
            "Lemma `L3' uses terms of the wrong form: `exp(exp('b','a'),'c')'",
        ])
    );
}

/// An `equations:` LHS written prefix resolves to the NoEq symbol too: the
/// equation registers under NoEq `f` (making it reducible — the lemma is
/// flagged) and the signature echo prints it as `f(x, y) = x`, sorted among
/// the other subterm rules by the derived `Ord CtxtStRule`.  Oracle bytes:
/// probe `p_eq`.
#[test]
fn an_equation_over_the_dual_name_registers_under_the_noeq_symbol() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2\n\
               equations: f(x, y) = x\n\n\
               lemma L1:\n\
               \x20 \"All #i. Test(f('a','b')) @ #i ==> F\"\n\n\
               end\n";
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = elaborate(&thy).expect("elaborate");
    assert_eq!(
        web_signature_block(&elaborated.signature.maude_sig),
        "functions: f/2, fst/1, pair/2, snd/1, f/2 [AC]\n\
         equations: f(x, y) = x, fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    assert_eq!(
        wf_block(src).expect("the now-reducible NoEq f must be reported"),
        formula_terms_block(&["Lemma `L1' uses terms of the wrong form: `f('a','b')'"])
    );
}
