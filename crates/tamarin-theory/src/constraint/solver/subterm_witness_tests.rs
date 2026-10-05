// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Regression coverage for `finishedSubterms` in
//! Theory/Constraint/Solver/ProofMethod.hs, including the patched oracle's
//! residual-subterm witness checks.

use super::*;
use crate::constraint::constraints::Goal;
use crate::fact::{Fact, Multiplicity};
use crate::formula::{lift_free, Quantifier};
use crate::guarded::{close_guarded, gfalse};
use tamarin_term::function_symbols::{fst_sym, pair_sym, AcSym, NoEqSym};
use tamarin_term::lterm::{fresh_term, pub_term};
use tamarin_term::term::{f_app_ac, f_app_no_eq};
use tamarin_term::vterm::var_term;

fn x() -> LVar {
    LVar::new("x", LSort::Msg, 0)
}
fn y() -> LVar {
    LVar::new("y", LSort::Msg, 1)
}
fn i() -> LVar {
    LVar::new("i", LSort::Node, 2)
}
fn pair(a: LNTerm, b: LNTerm) -> LNTerm {
    f_app_no_eq(pair_sym(), vec![a, b])
}

fn residual(small: LNTerm) -> System {
    let mut sys = System::empty();
    sys.subterm_store_mut().add(small, var_term(x()));
    sys
}

fn sig() -> MaudeSig {
    tamarin_term::maude_sig::pair_maude_sig()
}

fn action(t: LNTerm) -> crate::fact::LNFact {
    Fact::new(FactTag::Proto(Multiplicity::Linear, "A", 1), vec![t])
}

fn guard(pattern: LNTerm, with_equation: bool) -> Guarded {
    let mut atoms = vec![ProtoAtom::Action(var_term(i()), action(pattern))];
    if with_equation {
        atoms.push(ProtoAtom::EqE(var_term(y()), pub_term("c")));
    }
    close_guarded(Quantifier::All, vec![y(), i()], atoms, gfalse())
}

#[test]
fn subterm_witness_accepts_public_terms_and_unconstrained_variables() {
    for small in [
        pub_term("c"),
        var_term(LVar::new("p", LSort::Pub, 0)),
        var_term(y()),
        pair(pub_term("c"), var_term(y())),
    ] {
        assert!(
            finished_subterms(&sig(), &residual(small.clone())),
            "{small:?}"
        );
    }
}

#[test]
fn subterm_witness_rejects_secrets_private_symbols_destructors_and_naturals() {
    use tamarin_term::function_symbols::nat_one_sym;
    for small in [
        fresh_term("secret"),
        var_term(LVar::new("secret", LSort::Fresh, 0)),
        var_term(LVar::new("n", LSort::Nat, 0)),
        f_app_no_eq(nat_one_sym(), vec![]),
        f_app_no_eq(
            NoEqSym::new(
                "private",
                1,
                Privacy::Private,
                Constructability::Constructor,
            ),
            vec![pub_term("c")],
        ),
        // Even an irreducible public destructor has no construction rule.
        f_app_no_eq(
            NoEqSym::new("absent", 1, Privacy::Public, Constructability::Destructor),
            vec![pub_term("c")],
        ),
        f_app_no_eq(fst_sym(), vec![var_term(y())]),
        pair(pub_term("c"), fresh_term("secret")),
        f_app_ac(AcSym::Union, vec![pub_term("a"), pub_term("b")]),
        var_term(x()),
    ] {
        assert!(
            !finished_subterms(&sig(), &residual(small.clone())),
            "{small:?}"
        );
    }
}

#[test]
fn subterm_witness_groups_shared_containers_but_rejects_dependencies() {
    let mut sys = residual(pub_term("c"));
    sys.subterm_store_mut().add(pub_term("d"), var_term(x()));
    sys.subterm_store_mut().add(pub_term("e"), var_term(y()));
    assert!(finished_subterms(&sig(), &sys));
    sys.subterm_store_mut().add(var_term(x()), var_term(y()));
    assert!(!finished_subterms(&sig(), &sys));
}

#[test]
fn subterm_witness_rejects_other_constraints_on_the_container() {
    let base = residual(pub_term("c"));
    let mut negative = base.clone();
    negative
        .subterm_store_mut()
        .add_neg(pub_term("d"), var_term(x()));
    assert!(!finished_subterms(&sig(), &negative));
    let mut negative_small = base.clone();
    negative_small
        .subterm_store_mut()
        .add_neg(var_term(x()), var_term(y()));
    assert!(!finished_subterms(&sig(), &negative_small));
    let mut other_container = base.clone();
    other_container
        .subterm_store_mut()
        .add(pub_term("d"), pair(var_term(x()), var_term(y())));
    assert!(!finished_subterms(&sig(), &other_container));
    // All three formula stores constrain the witness, not just open formulas.
    let fm = std::sync::Arc::new(Guarded::Atom(ProtoAtom::EqE(
        lift_free(&var_term(x())),
        lift_free(&pub_term("c")),
    )));
    for store in 0..3 {
        let mut sys = base.clone();
        match store {
            0 => sys.formulas_mut().push(fm.clone()),
            1 => sys.solved_formulas_mut().push(fm.clone()),
            _ => sys.insert_lemma(fm.clone()),
        }
        assert!(!finished_subterms(&sig(), &sys));
    }
}

#[test]
fn subterm_witness_does_not_recheck_solved_or_negative_variable_subterms() {
    let mut sys = residual(fresh_term("secret"));
    let st = sys.subterm_store_mut().subterms.pop().unwrap();
    sys.subterm_store_mut().solved_subterms.push(st);
    sys.subterm_store_mut()
        .add_neg(fresh_term("other"), var_term(x()));
    assert!(finished_subterms(&sig(), &sys));
}

#[test]
fn subterm_witness_rejects_reducible_containers_in_every_store() {
    let reducible = f_app_no_eq(fst_sym(), vec![var_term(y())]);
    for store in 0..3 {
        let mut sys = System::empty();
        if store == 2 {
            sys.subterm_store_mut()
                .add_neg(pub_term("c"), reducible.clone());
        } else {
            sys.subterm_store_mut()
                .add(pub_term("c"), reducible.clone());
            if store == 1 {
                let st = sys.subterm_store_mut().subterms.pop().unwrap();
                sys.subterm_store_mut().solved_subterms.push(st);
            }
        }
        assert!(!finished_subterms(&sig(), &sys));
    }
}

#[test]
fn subterm_witness_checks_unsolved_actions_and_all_node_fact_positions() {
    use crate::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    for term in [
        pair(var_term(x()), pub_term("c")),
        f_app_no_eq(fst_sym(), vec![var_term(x())]),
        f_app_ac(AcSym::Union, vec![var_term(x()), pub_term("c")]),
    ] {
        let expected = matches!(&term, Term::App(FunSym::NoEq(f), _) if *f == pair_sym());
        for position in 0..4 {
            let mut sys = residual(pub_term("c"));
            if position == 3 {
                sys.add_goal(Goal::Action(i(), action(term.clone())));
            } else {
                let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
                    RuleInfo::Proto(ProtoRuleACInstInfo {
                        name: ProtoRuleName::Stand("Test"),
                        attributes: RuleAttributes::empty(),
                        loop_breakers: Vec::new(),
                    });
                let mut facts = [Vec::new(), Vec::new(), Vec::new()];
                facts[position].push(action(term.clone()));
                let [prems, concs, acts] = facts;
                sys.add_node(i(), Rule::new(info, prems, concs, acts));
            }
            assert_eq!(
                finished_subterms(&sig(), &sys),
                expected,
                "{term:?}, position {position}"
            );
        }
    }
}

#[test]
fn subterm_witness_checks_guard_shapes_and_equalities() {
    for (pattern, equation, expected) in [
        (var_term(y()), false, true),
        (var_term(y()), true, false),
        (pair(var_term(y()), pub_term("c")), false, false),
        (pub_term("other"), false, true),
    ] {
        let mut sys = residual(pub_term("c"));
        sys.add_goal(Goal::Action(i(), action(var_term(x()))));
        sys.insert_lemma(guard(pattern, equation));
        assert_eq!(finished_subterms(&sig(), &sys), expected);
    }
    // Inspect the occurrence inside an otherwise safe enclosing constructor.
    let mut sys = residual(pub_term("c"));
    sys.add_goal(Goal::Action(
        i(),
        action(pair(pub_term("tag"), var_term(x()))),
    ));
    sys.insert_lemma(guard(
        pair(pub_term("tag"), pair(var_term(y()), pub_term("c"))),
        false,
    ));
    assert!(!finished_subterms(&sig(), &sys));
    // A different constructor at that path cannot start matching.
    let mut other = residual(pub_term("c"));
    other.add_goal(Goal::Action(
        i(),
        action(pair(pub_term("tag"), var_term(x()))),
    ));
    other.insert_lemma(guard(f_app_no_eq(fst_sym(), vec![var_term(y())]), false));
    assert!(finished_subterms(&sig(), &other));
}

#[test]
fn subterm_witness_finds_nested_knowledge_guards() {
    let ku_guard = close_guarded(
        Quantifier::All,
        vec![i()],
        vec![ProtoAtom::Action(
            var_term(i()),
            Fact::new(FactTag::Ku, vec![pub_term("c")]),
        )],
        gfalse(),
    );
    for formula in [
        ku_guard.clone(),
        Guarded::Disj(vec![gfalse(), Guarded::Conj(vec![ku_guard.clone()].into())].into()),
        close_guarded(
            Quantifier::All,
            vec![i(), y()],
            vec![ProtoAtom::Action(var_term(i()), action(var_term(y())))],
            ku_guard,
        ),
    ] {
        let mut sys = residual(pub_term("c"));
        sys.formulas_mut().push(std::sync::Arc::new(formula));
        assert!(!finished_subterms(&sig(), &sys));
    }
}
