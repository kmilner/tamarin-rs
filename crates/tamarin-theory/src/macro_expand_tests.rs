// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_parser::parse_theory;

fn parse(src: &str) -> p::Theory {
    parse_theory(src, &[]).expect("parse")
}

#[test]
fn bare_nullary_macro_name_expands() {
    // HS `nullaryApp` (Theory/Text/Parser/Term.hs:151,158-163) parses a BARE arity-0 macro
    // name as a 0-ary application, so `konst` and `konst()` are the
    // same call.  A sorted/indexed variable of the same name is NOT
    // a call.
    let src = "theory T begin\n\
            builtins: hashing\n\
            macros: konst() = h('seed')\n\
            rule R: [ In(konst) ] --[ M(konst.1, konst:pub) ]-> [ ]\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    // Premise In(konst) → In(h('seed')).
    assert!(
        matches!(&rule.premises[0].args[0],
            p::Term::App(n, args) if n == "h" && args.len() == 1),
        "got {:?}",
        rule.premises[0].args[0]
    );
    // konst.1 (indexed) and konst:pub (sorted) stay variables.
    assert!(
        matches!(&rule.actions[0].args[0],
            p::Term::Var(v) if v.name == "konst" && v.idx == 1),
        "got {:?}",
        rule.actions[0].args[0]
    );
    assert!(
        matches!(&rule.actions[0].args[1],
            p::Term::Var(v) if v.name == "konst"
                && v.sort != p::SortHint::Untagged),
        "got {:?}",
        rule.actions[0].args[1]
    );
}

#[test]
fn simple_term_macro_replaces_call() {
    // macro `id(x) = x`; call `id(a)` → `a`.
    let src = "theory T begin\n\
            macros: id(x) = x\n\
            rule R: [ In(id(a)) ] --> [ ]\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    // Premise was In(id(a)); after expansion: In(a).
    let arg = &rule.premises[0].args[0];
    assert!(
        matches!(arg, p::Term::Var(v) if v.name == "a"),
        "got {:?}",
        arg
    );
}

#[test]
fn nested_macro_is_re_expanded() {
    // hashdec(x, y) = h(decrypt(x, y)); decrypt(x, y) = adec(x, y).
    // Expanding hashdec(a, b) should produce h(adec(a, b)).
    let src = "theory T begin\n\
            builtins: hashing, asymmetric-encryption\n\
            macros: decrypt(x, y) = adec(x, y), hashdec(x, y) = h(decrypt(x, y))\n\
            rule R: [ In(hashdec(a, b)) ] --> [ ]\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    let arg = &rule.premises[0].args[0];
    // Expected: App("h", [App("adec", [Var(a), Var(b)])])
    if let p::Term::App(h_name, h_args) = arg {
        assert_eq!(h_name, "h");
        assert_eq!(h_args.len(), 1);
        if let p::Term::App(adec_name, adec_args) = &h_args[0] {
            assert_eq!(adec_name, "adec");
            assert_eq!(adec_args.len(), 2);
        } else {
            panic!("expected adec, got {:?}", h_args[0]);
        }
    } else {
        panic!("expected h(...), got {:?}", arg);
    }
}

#[test]
fn macro_in_lemma_formula_expands() {
    // Lemma uses a macro that wraps Action(A(m(x))).
    let src = "theory T begin\n\
            macros: m(x) = x\n\
            rule R: [ In(x) ] --[ A(m(x)) ]-> [ ]\n\
            lemma L: exists-trace \"Ex x #i. A(m(x)) @ #i\"\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let lemma = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Lemma(l) => Some(l),
            _ => None,
        })
        .unwrap();
    // The Action atom's fact's arg should be Var(x) (not App("m", [Var(x)])).
    fn check(f: &p::Formula) {
        match &f.kind {
            p::FormulaKind::Exists(_, body) => check(body),
            p::FormulaKind::And(a, b) => {
                check(a);
                check(b);
            }
            p::FormulaKind::Atom(p::Atom::Action(fact, _)) => {
                assert!(
                    matches!(&fact.args[0], p::Term::Var(v) if v.name == "x"),
                    "got {:?}",
                    fact.args[0]
                );
            }
            _ => {}
        }
    }
    check(&lemma.formula);
}

#[test]
fn macro_with_pair_body_via_pair_syntax() {
    // m2(x, y) = <x, y>; call m2(a, b) → Pair([a, b]).
    let src = "theory T begin\n\
            macros: m2(x, y) = <x, y>\n\
            rule R: [ In(m2(a, b)) ] --> [ ]\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let rule = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .unwrap();
    let arg = &rule.premises[0].args[0];
    if let p::Term::Pair(items) = arg {
        assert_eq!(items.len(), 2);
    } else {
        panic!("expected Pair, got {:?}", arg);
    }
}

#[test]
fn macro_inside_ifdef_is_expanded() {
    // A rule under a live `#ifdef FLAG` branch is spliced to the top
    // level by the parser, so its macro call-sites are expanded like any
    // other rule's.
    let src = "theory T begin\n\
            macros: id(x) = x\n\
            #ifdef FLAG\n\
            rule R: [ In(id(a)) ] --> [ ]\n\
            #endif\n\
            end\n";
    let mut thy = parse_theory(src, &["FLAG"]).expect("parse");
    expand_theory_macros(&mut thy);
    let rule = thy
        .items
        .iter()
        .find_map(|it| match it {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
        .expect("rule from live ifdef branch at top level");
    let arg = &rule.premises[0].args[0];
    assert!(
        matches!(arg, p::Term::Var(v) if v.name == "a"),
        "got {:?}",
        arg
    );
}

#[test]
fn case_test_formula_is_not_macro_expanded() {
    // HS keeps CaseTest as a `TranslationItem` and applies NO macros to
    // it (CloseRule.hs:82-90, see line 90; Theory/Text/Parser.hs:159-163, see line 163
    // `liftedAddCaseTest`). Probed
    // against the real HS prover (v1.13.0) on an equivalent theory: the
    // stored case-test formula prints `Blame( idm(a) )` UNEXPANDED, e.g.
    //   predicate: Blamed( a ) <=> ∃ #i. Blame( idm(a) ) @ #i
    // So after `expand_theory_macros` the case-test formula must still
    // contain the macro call `App("idm", ...)`.
    let src = "theory T begin\n\
            functions: id/1\n\
            macros: idm(x) = id(x)\n\
            rule R: [ In(x) ] --[ Blame(x) ]-> [ Out(x) ]\n\
            test blamed: \"Ex #i. Blame(idm(a)) @ #i\"\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let ct = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::CaseTest(c) => Some(c),
            _ => None,
        })
        .expect("case test");
    // The Action atom's fact arg must remain App("idm", [Var("a")]).
    fn check(f: &p::Formula) -> bool {
        match &f.kind {
            p::FormulaKind::Exists(_, body) | p::FormulaKind::Forall(_, body) => check(body),
            p::FormulaKind::And(a, b)
            | p::FormulaKind::Or(a, b)
            | p::FormulaKind::Implies(a, b)
            | p::FormulaKind::Iff(a, b) => check(a) || check(b),
            p::FormulaKind::Not(g) => check(g),
            p::FormulaKind::Atom(p::Atom::Action(fact, _)) => {
                matches!(fact.args.first(),
                        Some(p::Term::App(name, args)) if name == "idm" && args.len() == 1)
            }
            _ => false,
        }
    }
    assert!(
        check(&ct.formula),
        "case-test formula was macro-expanded (idm should survive): {:?}",
        ct.formula
    );
}

#[test]
fn acc_lemma_formula_is_not_macro_expanded() {
    // AccLemma is also a `TranslationItem` (CloseRule.hs:82-90, see line 90;
    // Theory/Text/Parser.hs:153-157, see line 157
    // `liftedAddAccLemma`) and is never macro-expanded. After
    // `expand_theory_macros` the acc-lemma formula must still contain the
    // macro call `App("idm", ...)`.
    let src = "theory T begin\n\
            functions: id/1\n\
            macros: idm(x) = id(x)\n\
            rule R: [ In(x) ] --[ Blame(x), Fin() ]-> [ Out(x) ]\n\
            test blamed: \"Ex #i. Blame(idm(a)) @ #i\"\n\
            lemma acc: blamed accounts for \"All #i. Fin() @ #i ==> Ex #j. Blame(idm(a)) @ #j\"\n\
            end\n";
    let mut thy = parse(src);
    expand_theory_macros(&mut thy);
    let acc = thy
        .items
        .iter()
        .find_map(|i| match i {
            p::TheoryItem::AccLemma(a) => Some(a),
            _ => None,
        })
        .expect("acc lemma");
    fn check(f: &p::Formula) -> bool {
        match &f.kind {
            p::FormulaKind::Exists(_, body) | p::FormulaKind::Forall(_, body) => check(body),
            p::FormulaKind::And(a, b)
            | p::FormulaKind::Or(a, b)
            | p::FormulaKind::Implies(a, b)
            | p::FormulaKind::Iff(a, b) => check(a) || check(b),
            p::FormulaKind::Not(g) => check(g),
            p::FormulaKind::Atom(p::Atom::Action(fact, _)) => {
                matches!(fact.args.first(),
                        Some(p::Term::App(name, args)) if name == "idm" && args.len() == 1)
            }
            _ => false,
        }
    }
    assert!(
        check(&acc.formula),
        "acc-lemma formula was macro-expanded (idm should survive): {:?}",
        acc.formula
    );
}

#[test]
fn no_macro_means_no_change() {
    let src = "theory T begin\n\
            rule R: [ In(a) ] --> [ ]\n\
            end\n";
    let mut thy = parse(src);
    let before = thy.clone();
    expand_theory_macros(&mut thy);
    assert_eq!(thy, before);
}
