// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins `checkTerms`' irreducibility test when a user-declared `[AC]`
//! symbol shares its NAME with a reducible builtin.
//!
//! HS's `allowed` guard is on the whole `FunSym`:
//! ``FApp o args | o `S.member` irreducible`` (Wellformedness.hs:984).  A NoEq
//! head and an AC head are different `FunSym` constructors, so an irreducible
//! `AC (ACfct (name, _))` never makes a NoEq application of the same `name`
//! allowed.
//!
//! `builtins: diffie-hellman` plus `functions: exp/2 [AC]` separates the two.
//! `^` is parsed by `expterm` (Theory/Text/Parser/Term.hs:176) as `fAppExp`,
//! i.e. `fAppNoEq expSym` (Term/Term.hs:164), whatever the declaration says;
//! `dhReducibleFunSig = {NoEq expSym, NoEq invSym}`
//! (Term/Term/FunctionSymbols.hs:307-308) is subtracted from
//! `irreducibleFunSyms` (Term/Maude/Signature.hs:121-124), so that NoEq head
//! is REDUCIBLE and `'a' ^ 'b'` is an offender.  The user's
//! `AC (ACfct exp)` stays in the irreducible set at the same time — nothing
//! subtracts it — so an application of a user `[AC]` symbol is allowed.
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468).

use tamarin_parser::parse_theory;
use tamarin_theory::pretty_theory::format_wf_block;

/// The rendered `/* WARNING … */` block the batch / web load pipelines print
/// for a theory's formula reports, or `None` when all three arms stay silent.
fn wf_block(src: &str) -> Option<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = tamarin_theory::elaborate::elaborate(&thy).expect("elaborate");
    let errs = tamarin_theory::wellformedness::formulas::formula_reports(&elaborated);
    if errs.is_empty() {
        return None;
    }
    Some(format_wf_block(&errs))
}

/// The whole block a single `exp('a','b')` offender produces.  The line after
/// the offender carries HS's two-space body indent and nothing else.
const EXP_OFFENDER_BLOCK: &str = "/*\nWARNING: the following wellformedness checks failed!\n\n\
     Formula terms\n\
     =============\n\n  \
     Lemma `L' uses terms of the wrong form: `exp('a','b')'\n  \n  \
     The only allowed terms are public constants and bound node and\n  \
     message variables. If you encounter free message variables, then\n  \
     you might have forgotten a #-prefix. Sort prefixes can only be\n  \
     dropped where this is unambiguous. Moreover, reducible function\n  \
     symbols are disallowed.\n*/";

/// A `[AC]` declaration for the name `exp` leaves the builtin NoEq `exp/2`
/// reducible, so the `^` in the lemma is still reported.
#[test]
fn a_user_ac_exp_declaration_does_not_make_the_dh_exponentiation_allowed() {
    let src = "theory ExpAcProbe1\nbegin\n\
               builtins: diffie-hellman\n\
               functions: exp/2 [AC]\n\
               rule R: [ ] --[ A('a' ^ 'b') ]-> [ ]\n\
               lemma L:\n\
               \x20 exists-trace\n\
               \x20 \"Ex #i. A('a' ^ 'b') @ i\"\n\
               end\n";
    assert_eq!(
        wf_block(src).expect("the reducible exp/2 head must be reported"),
        EXP_OFFENDER_BLOCK
    );
}

/// The control: without the declaration the same lemma reports the same
/// offender, so the declaration changes nothing about the NoEq head.
#[test]
fn the_dh_exponentiation_reports_identically_without_the_declaration() {
    let src = "theory ExpAcProbe4\nbegin\n\
               builtins: diffie-hellman\n\
               rule R: [ ] --[ A('a' ^ 'b') ]-> [ ]\n\
               lemma L:\n\
               \x20 exists-trace\n\
               \x20 \"Ex #i. A('a' ^ 'b') @ i\"\n\
               end\n";
    assert_eq!(
        wf_block(src).expect("the reducible exp/2 head must be reported"),
        EXP_OFFENDER_BLOCK
    );
}

/// The other side of the split: an application of a user-declared `[AC]`
/// symbol is an irreducible AC head, and its public-constant arguments are
/// allowed, so the check stays silent.
#[test]
fn an_application_of_a_user_ac_symbol_stays_allowed() {
    let src = "theory ExpAcProbe3\nbegin\n\
               builtins: diffie-hellman\n\
               functions: myac/2 [AC]\n\
               rule R: [ ] --[ A(myac('a', 'b')) ]-> [ ]\n\
               lemma L:\n\
               \x20 exists-trace\n\
               \x20 \"Ex #i. A(myac('a', 'b')) @ i\"\n\
               end\n";
    assert_eq!(wf_block(src), None);
}
