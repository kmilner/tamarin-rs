// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the OPTIONS (privacy / constructability / NDC) each symbol of a
//! DUAL-DECLARED name carries when the two declarations disagree — e.g.
//! `functions: f/2 [AC, destructor, NDC], f/2`.
//!
//! HS keeps the two symbols in two different fields of the `MaudeSig`: the
//! `NoEqUser` one in `stFunSyms`, the `ACfctUser` one in `stACFunSyms`
//! (Term/Maude/Signature.hs:97-98), each with its own options tuple —
//! `function` builds the tuple from the attribute list of the declaration it
//! is parsing and never merges the two (Theory/Text/Parser/Signature.hs:
//! 183-225, see lines 220-225).
//!
//! Which orders load is decided by `function`'s conflict check
//! (Signature.hs:212-216), which looks the name up in `stFunSyms` ONLY:
//!
//! | declaration order              | options      | result                     |
//! |--------------------------------|--------------|----------------------------|
//! | `f/2 [AC] , f/2`               | any / any    | loads (AC never in the set)|
//! | `f/2 , f/2 [AC]`               | equal        | loads                      |
//! | `f/2 , f/2 [AC, …]`            | differing    | "conflicting arities/options" |
//! | `f/2 [AC] , f/2 [AC, …]`       | differing    | loads (two AC symbols)     |
//!
//! So EVERY differing-options dual pair that loads is AC-declaration-first,
//! and the two symbols must be resolved independently: the prefix and
//! `op{a}b` spellings take the `NoEq` one (`lookupArity`'s NoEq-first list
//! lookup, Theory/Text/Parser/Term.hs:62-72), the infix spelling takes the AC
//! one (`acterm`, Term.hs:163-168).
//!
//! The observable is the Maude operator name: `funSymEncodeAttr`
//! (Term/Maude/Parser.hs:76-88) folds privacy / constructability / AC-ness /
//! NDC into the four characters after the `tam` prefix, so a symbol resolved
//! with the OTHER declaration's options serialises to an operator the theory
//! module never declares — Maude then returns nothing for `get variants` and
//! the rule is reported as having none.
//!
//! Expected strings are the pinned oracle's bytes (Git revision ef3f0468) for
//! the same theories, plain no-prove load.

use tamarin_parser::ast as p;
use tamarin_parser::parse_theory;
use tamarin_term::function_symbols::{AcState, FunSym};
use tamarin_term::lterm::LNTerm;
use tamarin_term::maude_print::{fun_sym_encode_attr, pp_maude_ac_sym, pp_theory};
use tamarin_term::term::Term;
use tamarin_theory::elaborate::{elaborate, set_user_funs_for_theory, term_to_lnterm};
use tamarin_theory::pretty_theory::{web_proto_rules, web_signature_block};

/// The Maude operator name the head of `t` serialises to — `tam`, the
/// `funSymEncodeAttr` attribute block, then the symbol name (HS
/// `ppMaudeNoEqSym` / `ppMaudeACSym`, Term/Maude/Parser.hs:110-124).
fn head_maude_op(t: &LNTerm) -> String {
    match t {
        Term::App(FunSym::NoEq(s), _) => format!(
            "tam{}{}",
            fun_sym_encode_attr(s.privacy, s.constructability, AcState::NotAc, s.ndc),
            String::from_utf8_lossy(s.name)
        ),
        Term::App(FunSym::Ac(a), _) => String::from_utf8(pp_maude_ac_sym(*a)).unwrap(),
        other => panic!("expected a function application, got {other:?}"),
    }
}

/// The Maude operator name of every action-fact argument of rule `rule`, in
/// source order, resolved through the theory's own user-function bundle (the
/// same install the load pipelines perform).
fn action_arg_ops(src: &str, rule: &str) -> Vec<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    let _guard = set_user_funs_for_theory(&thy);
    let r = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) if r.name == rule => Some(r),
            _ => None,
        })
        .expect("rule present");
    r.actions
        .iter()
        .flat_map(|f| f.args.iter())
        .map(|t| head_maude_op(&term_to_lnterm(t).expect("term converts")))
        .collect()
}

/// The `functions:` / `equations:` echo plus the `fmod`-level operator
/// declarations of a theory's Maude module.
fn signature_and_module(src: &str) -> (String, String) {
    let thy = parse_theory(src, &[]).expect("parse");
    let elaborated = elaborate(&thy).expect("elaborate");
    (
        web_signature_block(&elaborated.signature.maude_sig),
        pp_theory(&elaborated.signature.maude_sig),
    )
}

/// Panics unless `module` declares an operator called `op`.  A resolved
/// symbol whose options came from the wrong declaration fails this: the
/// module only ever declares the two operators the two declarations name.
fn assert_module_declares(module: &str, op: &str) {
    assert!(
        module.contains(&format!("op {op} :")),
        "Maude module does not declare `{op}`:\n{module}"
    );
}

/// The `rule (modulo E)` echoes of a theory's rules, with the AC-variant
/// annotation below each echo split off (its content depends on the variant
/// computation, not on term resolution).
fn rule_echoes(src: &str) -> Vec<String> {
    let thy = parse_theory(src, &[]).expect("parse");
    let _guard = set_user_funs_for_theory(&thy);
    let elaborated = elaborate(&thy).expect("elaborate");
    web_proto_rules(&thy, &elaborated)
        .into_iter()
        .map(|rule| match rule.split_once("\n\n  /*") {
            Some((echo, _annotation)) => echo.to_string(),
            None => rule,
        })
        .collect()
}

/// `[destructor, NDC]` on the AC declaration must not reach the plain `f/2`:
/// the oracle echoes the two option tuples separately, and the prefix
/// spelling — which resolves NoEq — stays the default constructor operator.
///
/// Oracle bytes: probe `p_eqvar` (`functions: f/2 [AC, destructor, NDC],
/// f/2` + `equations: f(x, y) = x`), whose signature echo is
/// `functions: f/2, fst/1, pair/2, snd/1, f/2 [destructor,AC,NDC]` and whose
/// rule closes with `rule (modulo AC) R1: [ In( z ) ] --[ A( z ), B( ('a' f
/// z) ) ]-> [ Out( 'c' ) ]` — i.e. the NoEq `f` reduces, which it can only do
/// if its Maude operator is one the module declares.
#[test]
fn ac_declaration_attributes_do_not_reach_the_noeq_symbol() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC, destructor, NDC], f/2\n\
               equations: f(x, y) = x\n\n\
               rule R1:\n\
               \x20 [ In(z) ] --[ A(f(z,'b')), B('a' f z) ]-> [ Out(f('c', z)) ]\n\n\
               end\n";
    let (signature, module) = signature_and_module(src);
    assert_eq!(
        signature,
        "functions: f/2, fst/1, pair/2, snd/1, f/2 [destructor,AC,NDC]\n\
         equations: f(x, y) = x, fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    // `A(f(z,'b'))` is the NoEq `f`: public constructor, not NDC (`XCFU`).
    // `B('a' f z)` is the AC `f`: public destructor, NDC (`XDAN`).
    let ops = action_arg_ops(src, "R1");
    assert_eq!(ops, ["tamXCFUf", "tamXDANf"]);
    for op in &ops {
        assert_module_declares(&module, op);
    }
}

/// The mirror direction: `[private, destructor]` on the NoEq declaration must
/// not reach the AC symbol, whose declaration carries no attributes.
///
/// Oracle bytes: probe `p_privnoeq` (`functions: f/2 [AC], f/2 [private,
/// destructor]` + `equations: f(x, y) = x`), signature echo
/// `functions: f/2 [private,destructor], fst/1, pair/2, snd/1, f/2 [AC]`,
/// closing as `rule (modulo AC) R1: [ In( z ) ] --[ A( z ), B( ('a' f z) )
/// ]-> [ Out( <'c', ('x' f z)> ) ]`.
#[test]
fn noeq_declaration_attributes_do_not_reach_the_ac_symbol() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2 [private, destructor]\n\
               equations: f(x, y) = x\n\n\
               rule R1:\n\
               \x20 [ In(z) ] --[ A(f(z,'b')), B('a' f z) ]-> [ Out(f('c', z)) ]\n\n\
               end\n";
    let (signature, module) = signature_and_module(src);
    assert_eq!(
        signature,
        "functions: f/2 [private,destructor], fst/1, pair/2, snd/1, f/2 [AC]\n\
         equations: f(x, y) = x, fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    // NoEq `f`: private destructor, not NDC (`PDFU`).  AC `f`: public
    // constructor, not NDC (`XCAU`).
    let ops = action_arg_ops(src, "R1");
    assert_eq!(ops, ["tamPDFUf", "tamXCAUf"]);
    for op in &ops {
        assert_module_declares(&module, op);
    }
}

/// `[NDC-diff]` on the NoEq declaration and nothing on the AC one: the two
/// NDC states are independent, and the NDC state is the FOURTH attribute
/// character, so a conflated pair would still pick a declared-looking but
/// wrong operator.
///
/// Oracle bytes: probe `o12` (`functions: f/2 [AC], f/2 [NDC-diff]`), whose
/// signature echo is
/// `functions: f/2 [NDC-diff], fst/1, pair/2, snd/1, f/2 [AC]`.
#[test]
fn ndc_diff_is_kept_per_declaration() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2 [NDC-diff]\n\n\
               rule R1:\n\
               \x20 [ ] --[ A(f('a','b')), B('a' f 'b') ]-> [ ]\n\n\
               end\n";
    let (signature, module) = signature_and_module(src);
    assert_eq!(
        signature,
        "functions: f/2 [NDC-diff], fst/1, pair/2, snd/1, f/2 [AC]\n\
         equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    // NoEq `f`: public constructor, IsNDCDiff (`XCFD`).  AC `f`: public
    // constructor, NotNDC (`XCAU`).
    let ops = action_arg_ops(src, "R1");
    assert_eq!(ops, ["tamXCFDf", "tamXCAUf"]);
    for op in &ops {
        assert_module_declares(&module, op);
    }
}

/// A `[private]` `[AC]` declaration of `exp` under `builtins:
/// diffie-hellman` leaves the theory-contributed NoEq `exp` untouched, so the
/// prefix spelling is still THE DH `expSym` and `prettyTerm` renders it
/// `'a'^'b'` (Term/Term.hs:310).  Reading privacy off the AC declaration
/// would make it a different symbol and drop the caret rendering.
///
/// Oracle bytes: probe `p_expac`, signature echo
/// `functions: fst/1, pair/2, snd/1, exp/2 [private,AC]`, rule echo
/// `rule (modulo E) R1: [ ] --[ A( 'a'^'b' ), B( ('a' exp 'b') ) ]-> [ ]`.
#[test]
fn an_ac_only_private_exp_leaves_the_dh_exp_alone() {
    let src = "theory T begin\n\n\
               builtins: diffie-hellman\n\
               functions: exp/2 [AC, private]\n\n\
               rule R1:\n\
               \x20 [ ] --[ A(exp('a','b')), B('a' exp 'b') ]-> [ ]\n\n\
               end\n";
    let (signature, module) = signature_and_module(src);
    assert_eq!(
        signature,
        "builtins: diffie-hellman\n\
         functions: fst/1, pair/2, snd/1, exp/2 [private,AC]\n\
         equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    assert_eq!(
        rule_echoes(src),
        ["rule (modulo E) R1:\n   [ ] --[ A( 'a'^'b' ), B( ('a' exp 'b') ) ]-> [ ]"]
    );
    // `expSym` is `("exp",(2,Public,Constructor,NotNDC))`
    // (Term/Term/FunctionSymbols.hs:251), i.e. `XCFU`; the AC `exp` is the
    // private constructor `PCAU`.
    let ops = action_arg_ops(src, "R1");
    assert_eq!(ops, ["tamXCFUexp", "tamPCAUexp"]);
    for op in &ops {
        assert_module_declares(&module, op);
    }
}

/// Two `[AC]` declarations of one name with differing options is the one
/// same-name pair HS admits WITHOUT a `NoEq` symbol involved: both symbols
/// enter `stACFunSyms` (the conflict check reads `stFunSyms` only).  The
/// resolved infix symbol must be one the module declares.
///
/// Oracle bytes: probe `p_dupac` (`functions: f/2 [AC], f/2 [AC, private]`),
/// signature echo `functions: fst/1, pair/2, snd/1, f/2 [private,AC], f/2
/// [AC]` — both symbols survive, and the rule echo `B( ('a' f 'b') )` is the
/// same for either, so the oracle does not distinguish which one the infix
/// spelling binds.
#[test]
fn duplicate_ac_declarations_resolve_to_a_declared_operator() {
    let src = "theory T begin\n\n\
               functions: f/2 [AC], f/2 [AC, private]\n\n\
               rule R1:\n\
               \x20 [ ] --[ B('a' f 'b') ]-> [ ]\n\n\
               end\n";
    let (signature, module) = signature_and_module(src);
    assert_eq!(
        signature,
        "functions: fst/1, pair/2, snd/1, f/2 [private,AC], f/2 [AC]\n\
         equations: fst(<x.1, x.2>) = x.1, snd(<x.1, x.2>) = x.2"
    );
    let ops = action_arg_ops(src, "R1");
    assert_module_declares(&module, &ops[0]);
    // The bundle keeps the least symbol by `Ord ACfctSym`, which is the order
    // `lookupArity`'s `lookup` over the ascending `S.toList` sees first
    // (Theory/Text/Parser/Term.hs:62-72); `Private < Public`
    // (Term/Term/FunctionSymbols.hs:111-112), so the private one wins.
    assert_eq!(ops, ["tamPCAUf"]);
}
