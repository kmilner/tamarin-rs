// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::System;
use tamarin_term::maude_sig::pair_maude_sig;

use tamarin_test_support::require_maude_path;

/// Returns a maude that speaks the pair signature.  Returns `None` when this
/// run accepts the no-maude skip.  [`maude_path`] panics when `MAUDE_PATH` is
/// set but points at nothing.  A maude that resolves but does not start is
/// the same misconfiguration.  That case panics.  It does not skip every test
/// in this file.
fn maude() -> Option<tamarin_term::maude_proc::MaudeHandle> {
    maude_with_sig(pair_maude_sig())
}

fn maude_with_sig(
    sig: tamarin_term::maude_sig::MaudeSig,
) -> Option<tamarin_term::maude_proc::MaudeHandle> {
    let path = require_maude_path()?;
    Some(
        tamarin_term::maude_proc::MaudeHandle::start(&path, sig).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 test here would otherwise skip silently"
            )
        }),
    )
}

fn ctx() -> Option<ProofContext> {
    Some(ProofContext::new(maude()?, Vec::new()))
}

/// Seeds a reduction for one fixed-point or fan-out row.
type Seed = fn(&mut Reduction);

/// Each CR-rule pass reaches a fixed point from its seed: some application
/// changes the system and a later one reports `Unchanged` (a pass that
/// re-derives a known fact loops the simplifier).  Where the pass keeps no
/// bookkeeping of its own, that application must also leave the system as
/// it was.  The check runs on the fixed point.
#[test]
fn passes_reach_a_fixed_point() {
    use crate::atom::ProtoAtom;
    use crate::guarded::{close_guarded, lift_free_atom, Guarded};
    use tamarin_term::lterm::{pub_term, LSort, LVar};
    use tamarin_term::vterm::var_term;

    fn fresh_eq(index: u64) -> Guarded {
        let term = var_term(LVar::new("x", LSort::Fresh, index));
        Guarded::Atom(lift_free_atom(&ProtoAtom::EqE(term.clone(), term)))
    }
    fn fresh_action(index: u64) -> crate::fact::LNFact {
        crate::fact::proto_fact(
            crate::fact::Multiplicity::Linear,
            "A",
            vec![var_term(LVar::new("x", LSort::Fresh, index))],
        )
    }
    let rows: &[(&str, Pass, Seed, bool, fn(&System))] = &[
        (
            // `All x #i. A(x) @ i ==> x = x` applied to a second, distinct x.
            "implied formulas over distinct x",
            insert_implied_formulas_pass,
            |red| {
                assert!(matches!(
                    red.insert_formula(fresh_eq(21)).unwrap(),
                    SystemOutcome::Linear
                ));
                let time = LVar::new("i", LSort::Node, 0);
                red.sys.insert_lemmas([std::sync::Arc::new(close_guarded(
                    crate::formula::Quantifier::All,
                    vec![LVar::new("x", LSort::Fresh, 0), time],
                    vec![ProtoAtom::Action(var_term(time), fresh_action(0))],
                    fresh_eq(0),
                ))]);
                red.insert_goal(crate::constraint::constraints::Goal::Action(
                    LVar::new("trace", LSort::Node, 1),
                    fresh_action(31),
                ));
            },
            true,
            |sys| {
                assert!(crate::guarded::stores_contains(
                    &sys.solved_formulas,
                    &fresh_eq(31)
                ))
            },
        ),
        (
            // S_neg must not re-emit an already-known disequality.
            "residual positive and negative subterms",
            propagate_subterm_obvious,
            |red| {
                let x = tamarin_term::builtin::msg_var("x", 0);
                red.sys.subterm_store_mut().add(pub_term("d"), x.clone());
                red.sys.subterm_store_mut().add_neg(pub_term("c"), x);
            },
            // The last round still records its negations as processed.
            false,
            |sys| assert!(!sys.subterm_store.contradictory),
        ),
    ];
    let Some(ctx) = ctx() else { return };
    for (label, pass, seed, identical, check) in rows {
        let mut red = Reduction::new(&ctx, System::empty());
        seed(&mut red);
        let mut changed = false;
        let fixed = (0..4).any(|_| {
            let before = red.sys.clone();
            red.changed = ChangeIndicator::Unchanged;
            assert!(
                matches!(pass(&mut red).unwrap(), SystemOutcome::Linear),
                "{label}"
            );
            if red.changed == ChangeIndicator::Changed {
                changed = true;
                return false;
            }
            if *identical {
                assert_eq!(red.sys, before, "{label}: Unchanged but the system moved");
            }
            true
        });
        assert!(changed && fixed, "{label}: changed={changed} fixed={fixed}");
        check(&red.sys);
    }
}

/// What a fan-out row's pass returns on its seed.
enum FanOut {
    /// This many arms, each meeting the check.
    Arms(usize, fn(&System)),
    /// The pass closes the system.
    Contradictory,
}

/// A pass whose work list meets several multi-unifier AC equalities fans out,
/// and every arm finishes the rest of the work list; a later contradiction
/// discards every arm.  Each row's seed has two independent arity-one
/// `x ∪ y = a ∪ b` style equalities (2 × 2 unifiers) unless noted.
#[test]
fn passes_finish_their_work_in_every_arm() {
    use crate::atom::ProtoAtom;
    use crate::constraint::constraints::Goal;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::formula::{lift_free, Quantifier};
    use crate::guarded::Guarded;
    use crate::rule::{ProtoRuleEInfo, Rule};
    use crate::theory::OpenProtoRule;
    use tamarin_term::builtin::{hash_sym, msg_var, pair};
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{pub_term, LSort, LVar, Name, NameTag};
    use tamarin_term::term::{f_app_ac, f_app_no_eq};
    use tamarin_term::vterm::{const_term, var_term};

    fn union(terms: Vec<tamarin_term::lterm::LNTerm>) -> tamarin_term::lterm::LNTerm {
        f_app_ac(AcSym::Union, terms)
    }
    fn equalities() -> [(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm); 2] {
        [
            (
                union(vec![msg_var("x", 0), msg_var("y", 1)]),
                union(vec![pub_term("a"), pub_term("b")]),
            ),
            (
                union(vec![msg_var("u", 2), msg_var("v", 3)]),
                union(vec![pub_term("c"), pub_term("d")]),
            ),
        ]
    }
    fn last() -> LVar {
        LVar::new("last", LSort::Node, 4)
    }
    // Three formulas behind trivially true guards, in Ord order: the two
    // equalities and a trailing `Last` atom, all in one frozen pass.
    fn guarded_formulas() -> Vec<Guarded> {
        let [first, second] =
            equalities().map(|(l, r)| Guarded::Atom(ProtoAtom::EqE(lift_free(&l), lift_free(&r))));
        let bodies = [
            first,
            second,
            Guarded::Atom(ProtoAtom::Last(lift_free(&var_term(last())))),
        ];
        let formulas: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .zip(bodies)
            .map(|(name, body)| Guarded::GGuarded {
                qua: Quantifier::All,
                vars: Vec::new().into(),
                guards: vec![ProtoAtom::EqE(
                    lift_free(&pub_term(name)),
                    lift_free(&pub_term(name)),
                )]
                .into(),
                body: std::sync::Arc::new(body),
            })
            .collect();
        assert!(formulas.windows(2).all(|pair| pair[0] < pair[1]));
        formulas
    }
    fn action(tag: &'static str, term: tamarin_term::lterm::LNTerm) -> crate::fact::LNFact {
        proto_fact(Multiplicity::Linear, tag, vec![term])
    }
    fn pub_const(name: &str) -> tamarin_term::lterm::LNTerm {
        const_term(Name::new(NameTag::Pub, name))
    }
    // Rules `FirstProducer: --[ First(<'marker', x ∪ y>) ]->` and
    // `SecondProducer: --[ Second('expected') ]->`.
    fn unique_actions_ctx() -> Option<ProofContext> {
        let mut sig = tamarin_term::maude_sig::mset_maude_sig();
        sig.st_fun_syms
            .extend(tamarin_term::function_symbols::pair_fun_sig());
        let producer = |name, fact| {
            OpenProtoRule::new(Rule::new(
                ProtoRuleEInfo::standard(name),
                Vec::new(),
                Vec::new(),
                vec![fact],
            ))
        };
        let first = action(
            "First",
            pair(
                pub_const("marker"),
                union(vec![msg_var("x", 0), msg_var("y", 1)]),
            ),
        );
        let rules = vec![
            producer("FirstProducer", first),
            producer("SecondProducer", action("Second", pub_const("expected"))),
        ];
        Some(ProofContext::new(maude_with_sig(sig.refresh())?, rules))
    }
    fn first_goal() -> Goal {
        let term = pair(
            pub_const("marker"),
            union(vec![pub_const("a"), pub_const("b")]),
        );
        Goal::Action(LVar::new("first", LSort::Node, 0), action("First", term))
    }
    fn mset_ctx() -> Option<ProofContext> {
        let sig = tamarin_term::maude_sig::mset_maude_sig();
        Some(ProofContext::new(maude_with_sig(sig)?, Vec::new()))
    }

    type Setup = fn() -> Option<(ProofContext, System)>;
    let rows: &[(&str, Pass, Setup, FanOut)] = &[
        (
            // `l ⊏ h(r)` with `l ≠ r` deduces `l = r` (S_subterm).
            "subterm deductions",
            propagate_subterm_obvious,
            || {
                let sig = tamarin_term::maude_sig::hash_maude_sig()
                    .merge(tamarin_term::maude_sig::mset_maude_sig());
                let ctx = ProofContext::new(maude_with_sig(sig)?, Vec::new());
                let mut sys = System::empty();
                for (left, right) in equalities() {
                    sys.subterm_store_mut()
                        .add(left.clone(), f_app_no_eq(hash_sym(), vec![right.clone()]));
                    sys.subterm_store_mut().add_neg(left, right);
                }
                Some((ctx, sys))
            },
            FanOut::Arms(4, |sys| assert_eq!(sys.eq_store().subst.len(), 4)),
        ),
        (
            "formula atom evaluation",
            eval_formula_atoms_pass,
            || {
                let mut sys = System::empty();
                for formula in guarded_formulas() {
                    sys.insert_formula(formula);
                }
                Some((mset_ctx()?, sys))
            },
            FanOut::Arms(4, |sys| {
                assert_eq!(sys.last_atom, Some(last()));
                for formula in &guarded_formulas() {
                    assert!(!crate::guarded::stores_contains(&sys.formulas, formula));
                    assert!(crate::guarded::stores_contains(
                        &sys.solved_formulas,
                        formula
                    ));
                }
            }),
        ),
        (
            // One equality only: the unique `First` action's unifiers.
            "unique actions",
            solve_unique_actions_pass_fan_out,
            || {
                let mut sys = System::empty();
                sys.add_goal(first_goal());
                Some((unique_actions_ctx()?, sys))
            },
            FanOut::Arms(2, |_| {}),
        ),
        (
            // A later unique action with no producer closes every arm.
            "unique actions, then a contradiction",
            solve_unique_actions_pass_fan_out,
            || {
                let mut sys = System::empty();
                sys.add_goal(first_goal());
                sys.add_goal(Goal::Action(
                    LVar::new("second", LSort::Node, 1),
                    action("Second", pub_const("impossible")),
                ));
                Some((unique_actions_ctx()?, sys))
            },
            FanOut::Contradictory,
        ),
    ];
    for (label, pass, setup, expected) in rows {
        let Some((ctx, sys)) = setup() else { return };
        let mut red = Reduction::new(&ctx, sys);
        match (pass(&mut red).unwrap(), expected) {
            (SystemOutcome::Cases(arms), FanOut::Arms(count, check)) => {
                assert_eq!(arms.len(), *count, "{label}");
                for arm in arms {
                    check(&arm.sys);
                }
            }
            (SystemOutcome::Contradictory, FanOut::Contradictory) => {}
            (other, _) => panic!("{label}: {other:?}"),
        }
    }
}

#[test]
fn last_injective_nodes_merge_unless_strictly_ordered() {
    use crate::constraint::constraints::{Edge, LessAtom, Reason};
    use crate::constraint::solver::contradictions::{contradictions, Contradiction};
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{
        ConcIdx, PremIdx, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    let Some(mut ctx) = ctx() else { return };
    let tag = FactTag::Proto(Multiplicity::Linear, "S", 1);
    std::sync::Arc::get_mut(&mut ctx.shared)
        .unwrap()
        .injective_fact_insts
        .insert((tag, Vec::new()));
    let fact = Fact::new(tag, vec![tamarin_term::lterm::pub_term("id")]);
    let rule = |name, prems, concs| {
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(name),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            prems,
            concs,
            Vec::new(),
        )
    };
    let i = LVar::new("i", LSort::Node, 0);
    let j = LVar::new("j", LSort::Node, 1);
    let k = LVar::new("k", LSort::Node, 2);
    let mut sys = System::empty();
    sys.add_node(i, rule("Init", vec![], vec![fact.clone()]));
    sys.add_node(j, rule("Fin", vec![fact.clone()], vec![]));
    sys.add_node(k, rule("Fin", vec![fact], vec![]));
    sys.add_edge(Edge {
        src: (i, ConcIdx(0)),
        tgt: (k, PremIdx(0)),
    });
    sys.add_less(LessAtom::new(i, j, Reason::Adversary));
    sys.set_last_atom(Some(k));
    assert!(!contradictions(&ctx, &sys)
        .unwrap()
        .iter()
        .any(|c| matches!(c, Contradiction::NonInjectiveFactInstance(..))));
    let mut merged = Reduction::new(&ctx, sys.clone());
    assert!(matches!(
        merge_last_injective_fact_nodes(&mut merged).unwrap(),
        SystemOutcome::Linear
    ));
    let subst = &merged.sys.eq_store().subst;
    assert_eq!(
        tamarin_term::subst::apply_vterm(subst, var_term(j)),
        tamarin_term::subst::apply_vterm(subst, var_term(k))
    );
    for (a, b) in [(j, k), (k, j)] {
        let mut ordered = sys.clone();
        ordered.add_less(LessAtom::new(a, b, Reason::Adversary));
        let mut red = Reduction::new(&ctx, ordered);
        assert!(matches!(
            merge_last_injective_fact_nodes(&mut red).unwrap(),
            SystemOutcome::Contradictory
        ));
    }
    // Direct contradiction callers also reject non-unifiable final rules.
    sys.add_node(
        j,
        rule(
            "Different",
            sys.nodes
                .iter()
                .find(|(id, _)| *id == j)
                .unwrap()
                .1
                .premises
                .clone(),
            vec![],
        ),
    );
    assert!(contradictions(&ctx, &sys)
        .unwrap()
        .iter()
        .any(|c| matches!(c, Contradiction::NonInjectiveFactInstance(..))));
}

#[test]
fn implied_formulas_do_not_force_existential_reuse_lemmas() {
    use crate::formula::Quantifier;
    use crate::guarded::{gtrue, Guarded};
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    sys.insert_lemma(Guarded::GGuarded {
        qua: Quantifier::Ex,
        vars: Vec::new().into(),
        guards: Vec::new().into(),
        body: std::sync::Arc::new(gtrue()),
    });
    let mut red = Reduction::new(&ctx, sys);
    assert!(matches!(
        insert_implied_formulas_pass(&mut red).unwrap(),
        SystemOutcome::Linear
    ));
    assert!(red.sys.formulas.is_empty());
    assert!(red.sys.goals.is_empty());
}

/// Run the production simplifier in tests that intentionally construct a
/// linear case. A surprise split is itself a regression in these fixtures.
fn simplify_one(ctx: &ProofContext, sys: System) -> System {
    let mut systems = simplify_system_with_fanout(ctx, sys).expect("infallible test context");
    assert_eq!(systems.len(), 1, "expected one simplified system");
    systems.pop().unwrap()
}

fn continuation_marker_goal(name: &'static str, idx: u64) -> crate::constraint::constraints::Goal {
    use crate::constraint::constraints::Goal;
    use crate::fact::{FactTag, LNFact};
    use tamarin_term::lterm::{LSort, LVar};

    Goal::Action(
        LVar::new(name, LSort::Node, idx),
        LNFact::new(FactTag::Out, Vec::new()),
    )
}

fn insert_continuation_marker(red: &mut Reduction<'_>, name: &'static str, idx: u64) {
    let goal = continuation_marker_goal(name, idx);
    if !red.sys.goals.iter().any(|(existing, _)| existing == &goal) {
        red.insert_goal(goal);
    }
}

fn insert_pre_marker_after_split(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some() {
        insert_continuation_marker(red, "pre", 10);
    }
    Ok(SystemOutcome::Linear)
}

fn insert_post_marker(red: &mut Reduction<'_>) -> Result<SystemOutcome, crate::prove::ProveError> {
    insert_continuation_marker(red, "post", 20);
    Ok(SystemOutcome::Linear)
}

fn mark_split_arm(sys: System) -> System {
    mark_split_arm_at(sys, 30)
}

fn mark_split_arm_at(mut sys: System, idx: u64) -> System {
    use tamarin_term::lterm::{LSort, LVar};

    let marker = LVar::new("split", LSort::Node, idx);
    sys.bump_cache_lvar(&marker);
    sys.set_last_atom(Some(marker));
    sys
}

fn split_into_success_then_failure(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some() {
        return Ok(SystemOutcome::Linear);
    }
    red.changed = ChangeIndicator::Changed;
    let counter = red.fresh.next_index();
    Ok(SystemOutcome::Cases(vec![
        SystemBranch {
            sys: mark_split_arm_at(red.sys.clone(), 30),
            counter,
        },
        SystemBranch {
            sys: mark_split_arm_at(red.sys.clone(), 31),
            counter,
        },
    ]))
}

fn fail_sources_in_second_arm(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some_and(|marker| marker.idx == 31) {
        red.ctx.ensure_saturated()?;
    }
    Ok(SystemOutcome::Linear)
}

fn split_once(red: &mut Reduction<'_>) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some() {
        return Ok(SystemOutcome::Linear);
    }
    red.changed = ChangeIndicator::Changed;
    let counter = red.fresh.next_index();
    Ok(SystemOutcome::Cases(vec![
        SystemBranch {
            sys: mark_split_arm(red.sys.clone()),
            counter,
        },
        SystemBranch {
            sys: mark_split_arm(red.sys.clone()),
            counter,
        },
    ]))
}

fn split_with_distinct_counters(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some() {
        return Ok(SystemOutcome::Linear);
    }
    red.changed = ChangeIndicator::Changed;
    Ok(SystemOutcome::Cases(vec![
        SystemBranch {
            sys: mark_split_arm_at(red.sys.clone(), 30),
            counter: 100,
        },
        SystemBranch {
            sys: mark_split_arm_at(red.sys.clone(), 31),
            counter: 200,
        },
    ]))
}

fn allocate_counter_marker_once(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    let already_allocated = red.sys.goals.iter().any(|(goal, _)| {
        matches!(goal, crate::constraint::constraints::Goal::Action(node, _) if node.name == "fresh")
    });
    if !already_allocated {
        let idx = red.fresh.fresh_idents(1);
        insert_continuation_marker(red, "fresh", idx);
    }
    Ok(SystemOutcome::Linear)
}

fn adopt_singleton_once(
    red: &mut Reduction<'_>,
) -> Result<SystemOutcome, crate::prove::ProveError> {
    if red.sys.last_atom.is_some() {
        return Ok(SystemOutcome::Linear);
    }
    let outcome = red.finish_system_cases(vec![SystemBranch {
        sys: mark_split_arm(red.sys.clone()),
        counter: 41,
    }]);
    assert!(matches!(outcome, SystemOutcome::Linear));
    assert_eq!(red.changed, ChangeIndicator::Changed);
    Ok(outcome)
}

fn assert_continuation_order(systems: Vec<SystemBranch>) {
    assert_eq!(systems.len(), 2);
    for SystemBranch { sys, .. } in systems {
        let nr = |name, idx| {
            let goal = continuation_marker_goal(name, idx);
            sys.goals
                .iter()
                .find_map(|(existing, status)| (existing == &goal).then_some(status.nr))
                .expect("continuation marker goal")
        };
        assert!(
            nr("post", 20) < nr("pre", 10),
            "the lexical post-split continuation must run before the next fixpoint iteration"
        );
    }
}

#[test]
fn branching_pass_resumes_at_its_lexical_continuation() {
    let Some(ctx) = ctx() else { return };
    let mut red = Reduction::new(&ctx, System::empty());
    let passes: [Pass; _] = [
        insert_pre_marker_after_split,
        split_once,
        insert_post_marker,
    ];
    assert_continuation_order(
        simplify_system_fan_out_inner_with_passes(&mut red, &passes)
            .expect("infallible test passes"),
    );
}

#[test]
fn split_arms_resume_with_their_own_fresh_counters() {
    let Some(ctx) = ctx() else { return };
    let mut red = Reduction::new(&ctx, System::empty());
    let passes: [Pass; _] = [split_with_distinct_counters, allocate_counter_marker_once];

    let systems = simplify_system_fan_out_inner_with_passes(&mut red, &passes)
        .expect("infallible test passes");
    assert_eq!(systems.len(), 2);
    for SystemBranch { sys, counter } in systems {
        let arm = sys.last_atom.expect("split arm").idx;
        let expected = match arm {
            30 => 100,
            31 => 200,
            other => panic!("unexpected split arm {other}"),
        };
        let allocated = sys
            .goals
            .iter()
            .find_map(|(goal, _)| match goal {
                crate::constraint::constraints::Goal::Action(node, _) if node.name == "fresh" => {
                    Some(node.idx)
                }
                _ => None,
            })
            .expect("fresh-counter marker");
        assert_eq!(allocated, expected);
        assert_eq!(counter, expected + 1);
    }
}

#[test]
fn contradictory_unique_action_discards_the_continuation() {
    use crate::constraint::constraints::Goal;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use crate::theory::OpenProtoRule;
    use tamarin_term::lterm::{LSort, LVar, Name, NameTag};
    use tamarin_term::vterm::const_term;

    let Some(base) = ctx() else { return };
    let action = |name| {
        proto_fact(
            Multiplicity::Linear,
            "Unique",
            vec![const_term(Name::new(NameTag::Pub, name))],
        )
    };
    let rule = Rule::new(
        ProtoRuleEInfo::standard("OnlyProducer"),
        Vec::new(),
        Vec::new(),
        vec![action("expected")],
    );
    let ctx = ProofContext::new(base.maude.clone(), vec![OpenProtoRule::new(rule)]);
    let node = LVar::new("i", LSort::Node, 0);
    let mut sys = System::empty();
    sys.add_goal(Goal::Action(node, action("impossible")));
    let mut red = Reduction::new(&ctx, sys);

    let passes: [Pass; _] = [solve_unique_actions_pass_fan_out, insert_post_marker];
    assert!(
        simplify_system_fan_out_inner_with_passes(&mut red, &passes)
            .expect("infallible test passes")
            .is_empty(),
        "a contradictory mapM element must discard its later continuation"
    );
}

#[test]
fn singleton_system_case_is_adopted_as_a_linear_continuation() {
    let Some(ctx) = ctx() else { return };
    let mut red = Reduction::new(&ctx, System::empty());
    let passes: [Pass; _] = [
        insert_pre_marker_after_split,
        adopt_singleton_once,
        insert_post_marker,
    ];
    let mut systems = simplify_system_fan_out_inner_with_passes(&mut red, &passes)
        .expect("infallible test passes");

    assert_eq!(systems.len(), 1);
    let SystemBranch { sys, counter } = systems.pop().unwrap();
    assert_eq!(sys.last_atom.expect("adopted branch marker").idx, 30);
    assert_eq!(counter, 41);
    let nr = |name, idx| {
        let marker = continuation_marker_goal(name, idx);
        sys.goals
            .iter()
            .find_map(|(goal, status)| (goal == &marker).then_some(status.nr))
            .expect("continuation marker")
    };
    assert!(nr("post", 20) < nr("pre", 10));
}

#[test]
fn fatal_source_error_discards_completed_sibling_arms() {
    use crate::constraint::solver::context::FailingSourceProvider;

    let Some(mut ctx) = ctx() else { return };
    ctx.set_source_provider(std::sync::Arc::new(FailingSourceProvider));
    let mut red = Reduction::new(&ctx, System::empty());
    let passes: [Pass; _] = [split_into_success_then_failure, fail_sources_in_second_arm];

    assert!(matches!(
        simplify_system_fan_out_inner_with_passes(&mut red, &passes),
        Err(crate::prove::ProveError::Guarded(message)) if message == "bad source"
    ));
}

#[test]
fn merge_candidates_finishes_each_group_before_starting_the_next() {
    use crate::constraint::solver::reduction::SystemBranch;
    use std::cell::Cell;
    use tamarin_term::lterm::{LSort, LVar};

    let Some(ctx) = ctx() else { return };
    let node = |idx| LVar::new("i", LSort::Node, idx);
    let mut red = Reduction::new(&ctx, System::empty());
    let calls = Cell::new(0);
    let outcome = merge_candidates(
        &mut red,
        vec![
            (0, 10, node(0)),
            (0, 11, node(1)),
            (1, 20, node(2)),
            (1, 21, node(3)),
        ],
        |red, eqs| {
            let call = calls.get();
            calls.set(call + 1);
            if call == 0 {
                assert_eq!((eqs[0].lhs, eqs[0].rhs), (10, 11));
                let counter = red.fresh.next_index();
                Ok::<_, crate::prove::ProveError>(SystemOutcome::Cases(vec![
                    SystemBranch {
                        sys: red.sys.clone(),
                        counter,
                    },
                    SystemBranch {
                        sys: red.sys.clone(),
                        counter,
                    },
                ]))
            } else {
                assert_eq!((eqs[0].lhs, eqs[0].rhs), (20, 21));
                assert!(
                    !red.sys.eq_store().subst.is_empty(),
                    "the first group's node equality must precede the second payload solve"
                );
                Ok(SystemOutcome::Linear)
            }
        },
    )
    .expect("solver operation");
    let SystemOutcome::Cases(arms) = outcome else {
        panic!("first-group fanout must remain a two-arm outcome");
    };
    assert_eq!(calls.get(), 3, "second group must run once in each arm");
    assert_eq!(arms.len(), 2);
    for arm in arms {
        assert_eq!(arm.sys.eq_store().subst.dom().count(), 2);
    }
}

#[test]
fn simplify_empty_is_no_op() {
    let Some(ctx) = ctx() else { return };
    let before = System::empty();
    let sys = simplify_one(&ctx, before.clone());
    // Every CR-rule pass runs over an empty system.  No pass may make a
    // constraint out of nothing.  `assert!(goals.is_empty())` alone does not
    // catch a pass that adds a node, an edge or a formula.
    assert!(
        sys == before,
        "simplify on an empty system must invent nothing, got {:?}",
        sys
    );
}

#[test]
fn plain_route_does_not_truncate_long_linear_chains() {
    use crate::constraint::constraints::NodeId;
    use crate::rule::ConcIdx;
    use std::collections::{BTreeMap, BTreeSet};
    use tamarin_term::lterm::{LSort, LVar};

    let node = |idx| LVar::new("i", LSort::Node, idx);
    let linear: BTreeSet<NodeId> = (0..40).map(node).collect();
    let edges: BTreeMap<_, _> = (0..40)
        .map(|idx| ((node(idx), ConcIdx(0)), node(idx + 1)))
        .collect();

    let route = plain_route(node(0), &linear, &edges);
    assert_eq!(route.len(), 41);
    assert_eq!(route.last(), Some(&node(40)));

    // A malformed cycle terminates at the first repeated node.
    let cyclic = BTreeMap::from([
        ((node(0), ConcIdx(0)), node(1)),
        ((node(1), ConcIdx(0)), node(0)),
    ]);
    assert_eq!(
        plain_route(node(0), &linear, &cyclic),
        vec![node(0), node(1)]
    );
}

/// CR-rule *N6* `exploitUniqueMsgOrder` (Simplify.hs) inserts
/// `i_kd < i_ku` for every message that is both a KD conclusion and a KU
/// action.  HS's `F.mapM_ insertLess … M.intersectionWith` has no condition.
/// A single node can both conclude `KD(m)` and carry a `KU(m)` action.  Such
/// a node gets the reflexive order `i < i`.  That self-edge makes the order
/// relation cyclic.  The contradiction check then discards the case.  An
/// `i_kd != i_ku` guard here looks like a harmless cleanup of a redundant
/// self-ordering.  In fact such a guard keeps a spurious source case for
/// every wf-invalid rule that uses the reserved KU/KD facts
/// (regression/trace/issue515.spthy).
#[test]
fn exploit_unique_msg_order_inserts_the_reflexive_self_edge() {
    let Some(ctx) = ctx() else { return };
    use tamarin_term::builtin::msg_var;
    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    let m = msg_var("m", 0);
    let node = |id: u64| tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, id);
    let pairs = |r: &Reduction<'_>| -> Vec<(u64, u64)> {
        r.sys
            .less_atoms
            .iter()
            .map(|la| (la.smaller.idx, la.larger.idx))
            .collect()
    };

    // One node in both roles.  HS orders that node before itself.
    let mut sys = System::empty();
    sys.add_node(
        node(1),
        crate::rule::Rule::new(
            info(),
            vec![],
            vec![crate::fact::kd_fact(m.clone())],
            vec![crate::fact::ku_fact(m.clone())],
        ),
    );
    let mut r = Reduction::new(&ctx, sys);
    exploit_unique_msg_order(&mut r);
    assert_eq!(pairs(&r), vec![(1, 1)], "the self-edge must be inserted");
    assert!(
        tamarin_utils::dag::cyclic(
            &r.sys
                .less_atoms
                .iter()
                .map(|atom| (atom.smaller, atom.larger))
                .collect()
        ),
        "the self-edge is only useful because it makes rawLessRel cyclic"
    );
    assert_eq!(
        r.sys.less_atoms[0].reason,
        crate::constraint::constraints::Reason::NormalForm
    );

    // Two nodes.  The pass adds the ordinary KD-before-KU edge.  The edge
    // goes from the KD node to the KU node.
    let mut sys = System::empty();
    sys.add_node(
        node(1),
        crate::rule::Rule::new(
            info(),
            vec![],
            vec![crate::fact::kd_fact(m.clone())],
            vec![],
        ),
    );
    sys.add_node(
        node(2),
        crate::rule::Rule::new(
            info(),
            vec![],
            vec![],
            vec![crate::fact::ku_fact(m.clone())],
        ),
    );
    let mut r = Reduction::new(&ctx, sys);
    exploit_unique_msg_order(&mut r);
    assert_eq!(pairs(&r), vec![(1, 2)], "KD node orders before KU node");

    // A KD conclusion with no matching KU action gives no order at all.  The
    // pass intersects the two term maps.  It does not order every pair of
    // nodes.
    let mut sys = System::empty();
    sys.add_node(
        node(1),
        crate::rule::Rule::new(info(), vec![], vec![crate::fact::kd_fact(m)], vec![]),
    );
    sys.add_node(
        node(2),
        crate::rule::Rule::new(
            info(),
            vec![],
            vec![],
            vec![crate::fact::ku_fact(msg_var("other", 0))],
        ),
    );
    let mut r = Reduction::new(&ctx, sys);
    exploit_unique_msg_order(&mut r);
    assert!(
        pairs(&r).is_empty(),
        "different messages must not be ordered"
    );
}

#[test]
fn simplify_decomposes_top_level_conj() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    // Conj([Atom1, Atom2]) — Atom1/Atom2 are reducible-formula leaves
    // when wrapped in Conj of size 2 since the Conj itself is
    // reducible (matches the `Conj _` arm of `reducible_formula`).
    use crate::atom::ProtoAtom;
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::formula::BLNTerm;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    // Use two distinct Last atoms with the same name but DIFFERENT
    // idx values so the test exercises Conj decomposition without
    // tripping Haskell's `insertLast` unification (which collapses
    // two distinct Last atoms with different node-ids into a single
    // node-id-equation, dropping one of the original atoms).
    let mkvar_idx =
        |n: &str, idx: u64| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, idx))) };
    let action = |name: &'static str, t: BLNTerm| {
        crate::guarded::Guarded::Atom(ProtoAtom::Action(
            t,
            Fact::fresh(FactTag::Proto(Multiplicity::Linear, name, 0), Vec::new()),
        ))
    };
    let a1 = action("P", mkvar_idx("i", 0));
    let a2 = action("Q", mkvar_idx("j", 0));
    sys.invalidate_max_var_idx_cache();
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::Guarded::Conj(
            vec![a1.clone(), a2.clone()].into(),
        )));
    let sys = simplify_one(&ctx, sys);
    // The Conj should have been removed from the open formula set.
    assert!(!sys
        .formulas
        .iter()
        .any(|f| matches!(f.as_ref(), crate::guarded::Guarded::Conj(items) if items.len() == 2)));
    // Haskell-faithful: GConj decomposition recurses on its
    // members with mark=False, so GAto-Action members are
    // inserted as `Goal::Action` (via `insertAtom -> insertAction`)
    // rather than being tracked as formulas/solved_formulas.
    // Mirrors HS `insert' mark fm = ... GConj fms -> mapM_ (insert
    // False) (getConj fms)` (Reduction.hs) where the inner
    // GAto path's `markAsSolved` is gated on `when mark`.
    let has_action_goal = |name: &str| {
        sys.goals.iter().any(|(g, _)| match g {
            crate::constraint::constraints::Goal::Action(_, fa) => matches!(&fa.tag,
                        crate::fact::FactTag::Proto(_, n, _) if &**n == name),
            _ => false,
        })
    };
    assert!(has_action_goal("P"));
    assert!(has_action_goal("Q"));
}

#[test]
fn simplify_disj_decomposes_into_goal() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    use crate::atom::ProtoAtom;
    use crate::formula::BLNTerm;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    let mkvar = |n: &str| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, 0))) };
    let a1 = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("i")));
    let a2 = crate::guarded::Guarded::Atom(ProtoAtom::Last(mkvar("j")));
    // Wrap a Disj inside a Conj so the outer formula is reducible
    // (Conj is) — reduce_formulas will trip on it and decompose
    // the Disj inside.
    let disj = crate::guarded::Guarded::Disj(vec![a1, a2].into());
    sys.invalidate_max_var_idx_cache();
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::Guarded::Conj(
            vec![disj].into(),
        )));
    let sys = simplify_one(&ctx, sys);
    // After decomposition, a Goal::Disj should exist.
    assert!(sys
        .goals
        .iter()
        .any(|(g, _)| matches!(g, crate::constraint::constraints::Goal::Disj(_))));
}

/// HS `partialAtomValuation` for `Last i` returns Just False ONLY
/// when `any (isInTrace sys) (nodesAfter i)` — the existence of a
/// less-relation edge `n < m` is NOT itself sufficient; `m` must
/// satisfy `isInTrace` (in sNodes / isLast / unsolved Action atom).
/// Direct port of HS Simplify.hs `partialAtomValuation`.
///
/// This test pins that behaviour: a less-atom with `smaller == n`
/// alone must NOT collapse `Last(n)` to `Some(false)`.
#[test]
fn partial_atom_valuation_last_returns_none_when_successor_not_in_trace() {
    let Some(h) = maude() else { return };
    use crate::atom::ProtoAtom;
    let mkvar_l = |n: &str, idx: u64| {
        tamarin_term::lterm::LVar::new(n, tamarin_term::lterm::LSort::Node, idx)
    };
    // Build a System with:
    //   - NO nodes (so neither n nor m is in sNodes)
    //   - NO last_atom (so the isLast check fails for n)
    //   - NO unsolved Action goals for n or m (so the
    //     unsolvedActionAtoms clause of isInTrace also fails)
    //   - ONE less_atom `n < m` (the only edge into / out of n).
    //
    // Under these conditions HS returns Nothing for `Last n`:
    //   isLast sys n             = False (no last_atom)
    //   any isInTrace (nodesAfter n) = isInTrace m = False
    //   case sLastAtom of Nothing -> Nothing
    let mut sys = System::empty();
    let n = mkvar_l("n", 0);
    let m = mkvar_l("m", 0);
    sys.invalidate_max_var_idx_cache();
    sys.content_mut()
        .less_atoms
        .push(crate::constraint::constraints::LessAtom::new(
            n,
            m,
            crate::constraint::constraints::Reason::Formula,
        ));
    let last_n = |sys: &crate::constraint::system::System| {
        let ab_adj = sys.build_always_before_adj();
        let node_rule_map = sys.node_rule_map();
        let reducible = h.maude_sig().reducible_fun_syms_fast.clone();
        let subterms =
            crate::tools::subterm_store::StoreValuation::new(&reducible, &sys.subterm_store);
        partial_atom_valuation_with(
            sys,
            &h,
            &ab_adj,
            &node_rule_map,
            &subterms,
            &ProtoAtom::Last(tamarin_term::vterm::var_term(mkvar_l("n", 0))),
        )
        .unwrap()
    };
    assert_eq!(
        last_n(&sys),
        None,
        "HS-faithful: `Last n` with `n < m` but m not in trace must \
             yield None (not Some(false)).  Mirrors HS Simplify.hs's \
             `any (isInTrace sys) (nodesAfter i)` guard."
    );

    // The next two steps are positive controls.  A `partialAtomValuation`
    // that answers `None` for every `Last` atom also passes the assertion
    // above.  These controls exclude that case.
    //
    // (1) Put `m` in the trace with an unsolved Action goal.  This is the
    //     `unsolvedActionAtoms` clause of `isInTrace`.  Now `n` has a
    //     successor in the trace.  So `Last n` is false in every model.
    sys.add_goal(crate::constraint::constraints::Goal::Action(
        m,
        crate::fact::LNFact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "P", 0),
            vec![],
        ),
    ));
    assert_eq!(
        last_n(&sys),
        Some(false),
        "an in-trace successor of `n` refutes `Last n`"
    );

    // (2) The code checks `isLast sys n` first.  That check decides the
    //     result on its own.
    sys.set_last_atom(Some(n));
    assert_eq!(
        last_n(&sys),
        Some(true),
        "`isLast` is the first guard and outranks the successor check"
    );
}

/// HS `nodesAfter` walks `rawLessRel`, which includes unsolved chains: a
/// chain from `n` to an in-trace node refutes `Last n`.
#[test]
fn partial_atom_valuation_last_follows_unsolved_chains() {
    let Some(h) = maude() else { return };
    use crate::constraint::constraints::Goal;
    use crate::rule::{ConcIdx, PremIdx};
    let node = |n: &str| tamarin_term::lterm::LVar::new(n, tamarin_term::lterm::LSort::Node, 0);
    let (n, m) = (node("n"), node("m"));
    let mut sys = System::empty();
    sys.add_goal(Goal::Chain((n, ConcIdx(0)), (m, PremIdx(0))));
    sys.add_goal(Goal::Action(
        m,
        crate::fact::LNFact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "P", 0),
            vec![],
        ),
    ));
    let ab_adj = sys.build_always_before_adj();
    let node_rule_map = sys.node_rule_map();
    let reducible = h.maude_sig().reducible_fun_syms_fast.clone();
    let subterms = crate::tools::subterm_store::StoreValuation::new(&reducible, &sys.subterm_store);
    let last_n = partial_atom_valuation_with(
        &sys,
        &h,
        &ab_adj,
        &node_rule_map,
        &subterms,
        &crate::atom::ProtoAtom::Last(tamarin_term::vterm::var_term(n)),
    )
    .unwrap();
    assert_eq!(last_n, Some(false));
}

/// HS `partialAtomValuation` asks `unifiableLNTerms` before reading node ids:
/// variables of incompatible sorts are unequal in every model.
#[test]
fn partial_atom_valuation_eq_unifies_before_reading_node_ids() {
    let Some(h) = maude() else { return };
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    let (i, j) = (
        LVar::new("i", LSort::Node, 0),
        LVar::new("j", LSort::Node, 0),
    );
    let mut sys = System::empty();
    let eval = |sys: &System, x: LVar, y: LVar| {
        let ab_adj = sys.build_always_before_adj();
        let node_rule_map = sys.node_rule_map();
        let reducible = h.maude_sig().reducible_fun_syms_fast.clone();
        let subterms =
            crate::tools::subterm_store::StoreValuation::new(&reducible, &sys.subterm_store);
        partial_atom_valuation_with(
            sys,
            &h,
            &ab_adj,
            &node_rule_map,
            &subterms,
            &crate::atom::ProtoAtom::EqE(var_term(x), var_term(y)),
        )
        .unwrap()
    };
    let a = LVar::new("A", LSort::Pub, 0);
    let b = LVar::new("b", LSort::Fresh, 0);
    assert_eq!(eval(&sys, a, b), Some(false));
    assert_eq!(eval(&sys, i, j), None);
    sys.add_less(crate::constraint::constraints::LessAtom::new(
        i,
        j,
        crate::constraint::constraints::Reason::Formula,
    ));
    assert_eq!(eval(&sys, i, j), Some(false));
}

#[test]
fn simplify_marks_subterm_self_contradiction() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    // Add `x ⊏ x` — contradiction.
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let t: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
    sys.invalidate_max_var_idx_cache();
    sys.subterm_store_mut().add(t.clone(), t);
    let sys = simplify_one(&ctx, sys);
    assert!(sys.subterm_store.contradictory);
}

// =========================================================================
// match_atom_via_maude correctness
// =========================================================================

/// The `(name, idx)` projection `try_match_all_guards` hoists and passes
/// to `match_atom_via_maude` in production.
fn mk_pattern_vars(
    vars: &[tamarin_term::lterm::LVar],
) -> std::collections::BTreeSet<(&'static str, u64)> {
    vars.iter().map(|v| (v.name, v.idx)).collect()
}
fn mk_var_l(name: &str, idx: u64, sort: tamarin_term::lterm::LSort) -> tamarin_term::lterm::LNTerm {
    tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
        tamarin_term::lterm::LVar::new(name, sort, idx),
    ))
}

/// Returns the `variable → subject term` bindings that the caller reads
/// back from a match.  The result is sorted, so an assertion on the complete
/// substitution is stable.
fn subst_pairs(s: &crate::tools::equation_store::LNSubst) -> Vec<(String, u64, String)> {
    let mut out: Vec<(String, u64, String)> = s
        .iter()
        .map(|(k, v)| match v {
            tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v)) => {
                (k.name.to_string(), k.idx, format!("{}.{}", v.name, v.idx))
            }
            other => (k.name.to_string(), k.idx, format!("{other:?}")),
        })
        .collect();
    out.sort();
    out
}

#[test]
fn match_atom_via_maude_simple_var_to_var() {
    let Some(h) = maude() else { return };
    // Pattern: All k #i. Setup(k)@i — guard: Action(Setup(k), #i).
    let vars = vec![
        tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0),
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
    ];
    let g_fact = crate::fact::proto_fact(
        crate::fact::Multiplicity::Linear,
        "Setup",
        vec![mk_var_l("k", 0, tamarin_term::lterm::LSort::Msg)],
    );
    let g_time = mk_var_l("i", 0, tamarin_term::lterm::LSort::Node);
    let i_node = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 7);
    let sys_arg = mk_var_l("alpha", 3, tamarin_term::lterm::LSort::Msg);
    let substs = match_atom_via_maude(
        &h,
        &vars,
        &mk_pattern_vars(&vars),
        &g_fact,
        &g_time,
        &i_node,
        &[sys_arg],
    )
    .expect("solver operation");
    // There is one matcher, and it binds both pattern vars.  It binds the
    // time directly, because the matcher sets the time before it calls
    // Maude.  It binds the fact argument structurally, in the pure phase of
    // `solveMatchLTerm`, before it consults Maude at all.  A check for only
    // "a match exists" also accepts a matcher that drops `k`.  The caller
    // substitutes the guarded body with exactly these bindings.
    assert_eq!(substs.len(), 1);
    assert_eq!(
        subst_pairs(&substs[0]),
        vec![
            ("i".to_string(), 0, "n.7".to_string()),
            ("k".to_string(), 0, "alpha.3".to_string()),
        ]
    );
}

#[test]
fn match_atom_via_maude_pattern_with_pair_against_pair() {
    let Some(h) = maude() else { return };
    // Pattern: All a b #i. Action(<a, b>) @ i.
    let vars = vec![
        tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Msg, 0),
        tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Msg, 0),
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
    ];
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::term::f_app_no_eq;
    let pair_sym = NoEqSym::new(
        b"pair".to_vec(),
        2,
        Privacy::Public,
        Constructability::Constructor,
    );
    let g_fact = crate::fact::proto_fact(
        crate::fact::Multiplicity::Linear,
        "Action",
        vec![f_app_no_eq(
            pair_sym,
            vec![
                mk_var_l("a", 0, tamarin_term::lterm::LSort::Msg),
                mk_var_l("b", 0, tamarin_term::lterm::LSort::Msg),
            ],
        )],
    );
    let g_time = mk_var_l("i", 0, tamarin_term::lterm::LSort::Node);
    let i_node = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 1);
    // System has Action(<x, y>) where x, y are concrete LNTerm vars.
    let sys_pair = f_app_no_eq(
        pair_sym,
        vec![
            mk_var_l("x", 5, tamarin_term::lterm::LSort::Msg),
            mk_var_l("y", 6, tamarin_term::lterm::LSort::Msg),
        ],
    );
    let substs = match_atom_via_maude(
        &h,
        &vars,
        &mk_pattern_vars(&vars),
        &g_fact,
        &g_time,
        &i_node,
        &[sys_pair],
    )
    .expect("solver operation");
    // The matcher goes into the pair.  It binds each component var to the
    // subject component at the same position.  `a` and `b` must get distinct
    // subject terms, in position order.  A matcher that binds the complete
    // pair to `a` also reports a match.  So does a matcher that binds the two
    // components the wrong way round.
    assert_eq!(substs.len(), 1);
    assert_eq!(
        subst_pairs(&substs[0]),
        vec![
            ("a".to_string(), 0, "x.5".to_string()),
            ("b".to_string(), 0, "y.6".to_string()),
            ("i".to_string(), 0, "n.1".to_string()),
        ]
    );
}

/// `match_atom_via_maude` does NOT itself filter on arity — its caller
/// does (`simplify.rs`'s `g_fact_subst.args.len() != fa_sys.arity()`
/// guard just above the call).  With no subject args the pairwise
/// equation list is empty, so the function short-circuits to the single
/// time-only substitution and never reaches Maude.  Pinned so that a
/// future rewrite cannot start silently binding unmatched pattern vars.
#[test]
fn match_atom_via_maude_zero_subject_args_binds_only_the_time() {
    let Some(h) = maude() else { return };
    // Pattern wants 1 arg; system has 0.
    let vars = vec![
        tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0),
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
    ];
    let g_fact = crate::fact::proto_fact(
        crate::fact::Multiplicity::Linear,
        "F",
        vec![mk_var_l("k", 0, tamarin_term::lterm::LSort::Msg)],
    );
    let g_time = mk_var_l("i", 0, tamarin_term::lterm::LSort::Node);
    let i_node = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 0);
    let substs = match_atom_via_maude(
        &h,
        &vars,
        &mk_pattern_vars(&vars),
        &g_fact,
        &g_time,
        &i_node,
        &[],
    )
    .expect("solver operation");
    assert_eq!(substs.len(), 1, "empty equation list ⇒ one trivial matcher");
    let subst = &substs[0];
    match subst.image_of(&tamarin_term::lterm::LVar::new(
        "i",
        tamarin_term::lterm::LSort::Node,
        0,
    )) {
        Some(tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v))) => {
            assert_eq!((v.name, v.idx), ("n", 0));
        }
        other => panic!("expected i → Var(n, 0), got {other:?}"),
    }
    assert!(
        subst
            .image_of(&tamarin_term::lterm::LVar::new(
                "k",
                tamarin_term::lterm::LSort::Msg,
                0
            ))
            .is_none(),
        "the unmatched pattern arg must stay unbound"
    );
}

#[test]
fn match_atom_via_maude_rejects_non_var_time() {
    let Some(h) = maude() else { return };
    // Time is a literal — pattern matcher should reject.
    let vars: Vec<tamarin_term::lterm::LVar> = Vec::new();
    let g_fact = crate::fact::proto_fact(crate::fact::Multiplicity::Linear, "F", vec![]);
    let g_time = tamarin_term::vterm::const_term(tamarin_term::lterm::Name::new(
        tamarin_term::lterm::NameTag::Pub,
        "notavar",
    ));
    let i_node = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 0);
    let substs = match_atom_via_maude(
        &h,
        &vars,
        &mk_pattern_vars(&vars),
        &g_fact,
        &g_time,
        &i_node,
        &[],
    )
    .expect("solver operation");
    assert!(substs.is_empty());
}

// =========================================================================
// enforce_ku_action_uniqueness — Haskell N5_u semantics
//
// Two KU(m) actions on different node ids must collapse to the same
// node. We exercise that with a hand-built System that has two
// rule instances each carrying a `KU(~k)` action.
// =========================================================================
#[test]
fn ku_action_uniqueness_merges_two_nodes_with_same_term() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    // Two protocol-rule instances at distinct node ids, both
    // emitting `KU(~k)` as an action.
    let k = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Fresh, 0);
    let k_term: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(k));
    let ku_fact = crate::fact::Fact::new(crate::fact::FactTag::Ku, vec![k_term.clone()]);
    let mk_rule = || {
        let info = crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
        crate::rule::Rule::new(info, vec![], vec![], vec![ku_fact.clone()])
    };
    let id_a = tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 1);
    let id_b = tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 2);
    sys.add_node(id_a, mk_rule());
    sys.add_node(id_b, mk_rule());
    let mut r = Reduction::new(&ctx, sys);
    let res = enforce_ku_action_uniqueness_pass(&mut r).expect("solver operation");
    assert!(matches!(res, SystemOutcome::Linear));
    assert_eq!(r.changed, ChangeIndicator::Changed);
    // The eq-store should now equate `a` and `b`.
    let id_term_a = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(id_a));
    let id_term_b = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(id_b));
    let mapped_a = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, id_term_a);
    let mapped_b = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, id_term_b);
    assert_eq!(
        mapped_a, mapped_b,
        "a and b should map to the same canonical id"
    );
}

/// `simpSplitNegSt` S_subterm-neg-ac-recurse: a negative multiset
/// subterm `¬(a++a ⊏ b++c)` whose AC sides do NOT cancel under
/// `processACSubterm` (so it returns `Left (nSmall, nBig)`) must
/// produce the `ACNewVarD` existential leaf, which `simpSplitNegSt`
/// turns into the `acFormula`:
///   ∀ newVar. (a++a) ++ newVar = (b++c) ⇒ ⊥
/// (HS SubtermStore.hs; the `ACNewVarD` leaf is
/// built by `splitSubterm`'s `step` at SubtermStore.hs).
///
/// Authenticity: HS's `tamarin-prover --prove` verifies the
/// corresponding lemma `not(a++a ⊏ b++c)` (4 steps) — the proof
/// closes precisely via this universally-quantified contradiction.
#[test]
fn simp_split_neg_ac_recurse_emits_ac_formula() {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_ac, Term};
    use tamarin_term::vterm::Lit;
    // The multiset signature makes `++` (AC Union) a non-reducible AC head.
    let Some(h) = maude_with_sig(tamarin_term::maude_sig::mset_maude_sig()) else {
        return;
    };
    let ctx = ProofContext::new(h, Vec::new());

    let mk_var = |name: &str| -> tamarin_term::lterm::LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    };
    let a = mk_var("a");
    let b = mk_var("b");
    let c = mk_var("c");
    // small = a ++ a, big = b ++ c — neither side cancels.
    let small = f_app_ac(AcSym::Union, vec![a.clone(), a.clone()]);
    let big = f_app_ac(AcSym::Union, vec![b.clone(), c.clone()]);

    let mut sys = System::empty();
    // Seed `¬(a++a ⊏ b++c)`.  `old_neg_subterms` is empty, so this
    // pair is in the "changed" set `negSubterms \ oldNegSubterms`.
    assert!(sys.subterm_store_mut().add_neg(small.clone(), big.clone()));
    let mut r = Reduction::new(&ctx, sys);

    assert!(matches!(
        propagate_subterm_obvious(&mut r).unwrap(),
        SystemOutcome::Linear
    ));
    assert_eq!(
        r.changed,
        ChangeIndicator::Changed,
        "negative AC subterm should drive a change (acFormula emission)"
    );
    // A universally-quantified formula `∀ newVar. _ = _ ⇒ ⊥` must
    // have been emitted (the ACNewVarD acFormula).
    let has_ac_formula = r.sys.formulas.iter().any(|f| {
        matches!(f.as_ref(),
            crate::guarded::Guarded::GGuarded {
                qua: crate::formula::Quantifier::All, vars, body, .. }
            if vars.len() == 1 && **body == crate::guarded::gfalse())
    });
    assert!(
        has_ac_formula,
        "expected an `∀ newVar. … ⇒ ⊥` acFormula from the \
             S_subterm-neg-ac-recurse ACNewVarD arm; got {:?}",
        r.sys.formulas
    );
}

/// `simpInjectiveFactEqMon` Constant-position case: two distinct
/// nodes both have premise `S(~id, k)` (same first term `~id`,
/// distinct second term `k_1` vs. `k_2`), and `S` is registered
/// as injective with position-1 = Constant.  The pass should
/// emit a term equation merging `k_1 = k_2`.
#[test]
fn simp_injective_eq_mon_emits_constant_eq() {
    let Some(mut ctx) = ctx() else { return };
    // Wire S as injective with one Constant behaviour position.
    let s_tag = crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "S", 2);
    std::sync::Arc::get_mut(&mut ctx.shared)
        .expect("a fresh context uniquely owns its shared data")
        .injective_fact_insts = [(
        s_tag,
        vec![vec![
            crate::tools::injective_fact_instances::MonotonicBehaviour::Constant,
        ]],
    )]
    .into_iter()
    .collect();

    let id = tamarin_term::lterm::LVar::new("id", tamarin_term::lterm::LSort::Fresh, 0);
    let id_t: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(id));
    let k1 = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 1);
    let k1_t: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(k1));
    let k2 = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 2);
    let k2_t: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(k2));

    let s_fact_a = crate::fact::Fact::new(s_tag, vec![id_t.clone(), k1_t.clone()]);
    let s_fact_b = crate::fact::Fact::new(s_tag, vec![id_t.clone(), k2_t.clone()]);

    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };

    let id_a = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 1);
    let id_b = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 2);
    let mut sys = System::empty();
    sys.add_node(
        id_a,
        crate::rule::Rule::new(info(), vec![s_fact_a], vec![], vec![]),
    );
    sys.add_node(
        id_b,
        crate::rule::Rule::new(info(), vec![s_fact_b], vec![], vec![]),
    );

    let mut r = Reduction::new(&ctx, sys);
    let res = simp_injective_fact_eq_mon_pass(&mut r).expect("solver operation");
    assert!(matches!(res, SystemOutcome::Linear));
    assert_eq!(r.changed, ChangeIndicator::Changed);
    // After the pass, k1 and k2 should be equated in the eq-store.
    let m1 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, k1_t);
    let m2 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, k2_t);
    assert_eq!(
        m1, m2,
        "k_1 and k_2 should have the same canonical image after merge"
    );
}

/// `simpInjectiveFactEqMon` with a TUPLE injective position: `S` is
/// injective with behaviour `[[Unstable, Constant]]`, i.e. the
/// second argument is a top-level tuple flattened to two pair-leaves
/// (2.1 Unstable, 2.2 Constant).  Two nodes carry `S(~id, <a1, k1>)`
/// and `S(~id, <a2, k2>)`.  The pass must equate ONLY the Constant
/// pair-leaf (`k1 = k2`), leaving the Unstable leaf (`a1`/`a2`)
/// untouched — pinning that the consumer pairs by pair-leaf (HS
/// `trimmedPairTerms`/`shapeTerm`, Simplify.hs), not by whole
/// argument position.
#[test]
fn simp_injective_eq_mon_pairs_tuple_leaves() {
    let Some(mut ctx) = ctx() else { return };
    use crate::tools::injective_fact_instances::MonotonicBehaviour::{Constant, Unstable};
    let s_tag = crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "S", 2);
    std::sync::Arc::get_mut(&mut ctx.shared)
        .expect("a fresh context uniquely owns its shared data")
        .injective_fact_insts = [(s_tag, vec![vec![Unstable, Constant]])]
        .into_iter()
        .collect();

    let mk_var = |n: &str, sort, idx| -> tamarin_term::lterm::LNTerm {
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
            tamarin_term::lterm::LVar::new(n, sort, idx),
        ))
    };
    let pair = |a: tamarin_term::lterm::LNTerm,
                b: tamarin_term::lterm::LNTerm|
     -> tamarin_term::lterm::LNTerm {
        tamarin_term::term::f_app_no_eq(tamarin_term::function_symbols::pair_sym(), vec![a, b])
    };
    let id_t = mk_var("id", tamarin_term::lterm::LSort::Fresh, 0);
    let a1 = mk_var("a", tamarin_term::lterm::LSort::Msg, 1);
    let a2 = mk_var("a", tamarin_term::lterm::LSort::Msg, 2);
    let k1 = mk_var("k", tamarin_term::lterm::LSort::Msg, 1);
    let k2 = mk_var("k", tamarin_term::lterm::LSort::Msg, 2);

    let s_fact_a = crate::fact::Fact::new(s_tag, vec![id_t.clone(), pair(a1.clone(), k1.clone())]);
    let s_fact_b = crate::fact::Fact::new(s_tag, vec![id_t.clone(), pair(a2.clone(), k2.clone())]);

    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    let node_a = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 1);
    let node_b = tamarin_term::lterm::LVar::new("n", tamarin_term::lterm::LSort::Node, 2);
    let mut sys = System::empty();
    sys.add_node(
        node_a,
        crate::rule::Rule::new(info(), vec![s_fact_a], vec![], vec![]),
    );
    sys.add_node(
        node_b,
        crate::rule::Rule::new(info(), vec![s_fact_b], vec![], vec![]),
    );

    let mut r = Reduction::new(&ctx, sys);
    let res = simp_injective_fact_eq_mon_pass(&mut r).expect("solver operation");
    assert!(matches!(res, SystemOutcome::Linear));
    assert_eq!(r.changed, ChangeIndicator::Changed);
    // The Constant leaf (k1, k2) is equated...
    let m_k1 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, k1);
    let m_k2 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, k2);
    assert_eq!(
        m_k1, m_k2,
        "k_1 and k_2 (Constant leaf 2.2) should be merged"
    );
    // ...but the Unstable leaf (a1, a2) is NOT.
    let m_a1 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, a1);
    let m_a2 = tamarin_term::subst::apply_vterm(&r.sys.eq_store().subst, a2);
    assert_ne!(
        m_a1, m_a2,
        "a_1 and a_2 (Unstable leaf 2.1) must NOT be merged — the consumer \
             pairs by pair-leaf, not by whole tuple argument"
    );
}

#[test]
fn ku_action_uniqueness_unchanged_when_terms_differ() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    let mk_ku = |name: &str, idx: u64| {
        let v = tamarin_term::lterm::LVar::new(name, tamarin_term::lterm::LSort::Fresh, idx);
        crate::fact::Fact::new(
            crate::fact::FactTag::Ku,
            vec![tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(v),
            )],
        )
    };
    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    let id_a = tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 1);
    let id_b = tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 2);
    sys.add_node(
        id_a,
        crate::rule::Rule::new(info(), vec![], vec![], vec![mk_ku("k1", 0)]),
    );
    sys.add_node(
        id_b,
        crate::rule::Rule::new(info(), vec![], vec![], vec![mk_ku("k2", 0)]),
    );
    let mut r = Reduction::new(&ctx, sys);
    let res = enforce_ku_action_uniqueness_pass(&mut r).expect("solver operation");
    assert!(matches!(res, SystemOutcome::Linear));
    assert_eq!(r.changed, ChangeIndicator::Unchanged);
}

/// HS `solveRuleConstraints (Just (Disj []))`: an empty variant disjunction
/// makes the equation store contradictory.
#[test]
fn empty_rule_variant_disjunction_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut red = Reduction::new(&ctx, System::empty());
    assert!(red.solve_rule_constraints(Some(Vec::new())).unwrap());
    let mut red = Reduction::new(&ctx, System::empty());
    assert!(!red
        .solve_rule_constraints(Some(vec![
            tamarin_term::subst_vfresh::LNSubstVFresh::empty()
        ]))
        .unwrap());
}
