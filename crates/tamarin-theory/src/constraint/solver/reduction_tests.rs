// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_term::maude_sig::pair_maude_sig;

use tamarin_test_support::require_maude_path;

fn ctx() -> Option<ProofContext> {
    let path = require_maude_path()?;
    // A maude that resolved but will not start is the same misconfiguration
    // as a dangling MAUDE_PATH: swallowing it with `.ok()?` would silently
    // skip every maude-backed test in this file, so fail loudly instead.
    let h =
        tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 test here would otherwise skip silently"
            )
        });
    Some(ProofContext::new(h, Vec::new()))
}

#[test]
fn maude_failure_is_not_a_closed_action_or_formula_branch() {
    use crate::atom::ProtoAtom;
    use crate::constraint::solver::proof_method::{exec_proof_method, ProofMethod};
    use crate::fact::{proto_fact, Multiplicity};
    use crate::prove::ProveError;
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::var_term;

    let Some(path) = require_maude_path() else {
        return;
    };
    let maude = tamarin_term::maude_proc::MaudeHandle::start(
        &path,
        tamarin_term::maude_sig::mset_maude_sig(),
    )
    .unwrap();
    let ctx = ProofContext::new(maude.clone(), Vec::new());
    let union = |a, b| {
        Term::App(
            FunSym::Ac(AcSym::Union),
            vec![
                var_term(LVar::new(a, LSort::Msg, 0)),
                var_term(LVar::new(b, LSort::Msg, 0)),
            ]
            .into(),
        )
    };
    let left = union("a", "b");
    let right = union("x", "y");
    let fact = |term| proto_fact(Multiplicity::Linear, "A", vec![term]);
    let node = LVar::new("i", LSort::Node, 0);
    let mut action_system = System::empty();
    action_system.add_node(
        node,
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("R"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            Vec::new(),
            vec![fact(left.clone())],
        ),
    );
    let goal = Goal::Action(node, fact(right.clone()));
    action_system.add_goal(goal.clone());
    let mut formula_system = System::empty();
    formula_system.insert_formula(Guarded::Atom(crate::guarded::lift_free_atom(
        &ProtoAtom::EqE(left, right),
    )));

    let operations = [
        (ProofMethod::SolveGoal(goal), action_system),
        (ProofMethod::Simplify, formula_system),
    ];
    for (method, system) in &operations {
        let cases = exec_proof_method(&ctx, method, system).unwrap().unwrap();
        assert!(
            !cases.is_empty(),
            "the healthy operation has valid branches"
        );
    }
    // Use a separate handle so the healthy control cannot warm its caches.
    let maude = tamarin_term::maude_proc::MaudeHandle::start(
        &path,
        tamarin_term::maude_sig::mset_maude_sig(),
    )
    .unwrap();
    let ctx = ProofContext::new(maude.clone(), Vec::new());
    maude.kill_subprocess();
    for (method, system) in &operations {
        assert!(
            matches!(
                exec_proof_method(&ctx, method, system),
                Err(ProveError::Maude(_))
            ),
            "transport failure must not close {method:?}"
        );
    }
}

/// The index-0 variable leaf of the given name and sort.
fn mkvar_ln(name: &str, sort: tamarin_term::lterm::LSort) -> tamarin_term::lterm::LNTerm {
    tamarin_term::vterm::var_term(tamarin_term::lterm::LVar::new(name, sort, 0))
}

/// `ku_vars` must read the two variables `removePermutations` permutes
/// off the AC constructor rules' own `KU(x)`, `KU(y)` premises — and
/// answer `OtherRule` for every other premise shape, including the
/// `KD`-headed destruction rules generated alongside them.
#[test]
fn ku_vars_reads_the_ac_constructor_premise_variables() {
    use crate::rule::{IntrRuleAC, ProtoRuleACInstInfo, Rule, RuleACInst, RuleInfo};
    use tamarin_term::function_symbols::{AcSym, FunSym};

    let inst = |r: &IntrRuleAC| -> RuleACInst {
        Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, _>::Intr(r.info.clone()),
            r.premises.clone(),
            r.conclusions.clone(),
            r.actions.clone(),
        )
    };
    // c_xor / c_mult (`multisetIntruderRules`' union constructor) are
    // the two builtin AC construction rules solveAction can label an
    // AC-headed `KU` goal with.
    for (rules, sym) in [
        (crate::intruder_rules::xor_intruder_rules(), AcSym::Xor),
        (
            crate::intruder_rules::multiset_intruder_rules(),
            AcSym::Union,
        ),
    ] {
        let constr = rules
            .iter()
            .find(|r| crate::rule::is_ac_constr_rule(&inst(r)) == Some(FunSym::Ac(sym)))
            .expect("generator emits one AC construction rule");
        let ru = inst(constr);
        let IsAcConstructor::AcConstructor(v1, v2) = ku_vars(&ru) else {
            panic!("{sym:?} construction rule must yield two KU premise vars");
        };
        // Exactly the rule's own premise variables, in premise order.
        let prem_var = |i: usize| match &*ru.premises[i].terms {
            [tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v))] => *v,
            other => panic!("premise {i} is not a single-variable fact: {other:?}"),
        };
        assert_eq!(ru.premises[0].tag, crate::fact::FactTag::Ku);
        assert_eq!(ru.premises[1].tag, crate::fact::FactTag::Ku);
        assert_eq!((v1, v2), (prem_var(0), prem_var(1)));
        assert_ne!(v1, v2);

        // The destruction rules from the same generator lead with a
        // `KD` premise, so they carry no permutable variable pair.
        for d in rules
            .iter()
            .filter(|r| matches!(r.info, crate::rule::IntrRuleACInfo::DestrRule { .. }))
        {
            assert_eq!(
                ku_vars(&inst(d)),
                IsAcConstructor::OtherRule,
                "destruction rule must not claim an AC-constructor var pair"
            );
        }
    }
}

#[test]
fn insert_goal_marks_changed() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    // A fresh `Reduction` starts `Unchanged`.  Without that precondition the
    // assertion after the insert below would hold whatever `insert_goal`
    // does. The simplifier fixpoint resets and re-reads this flag on every
    // iteration; without the precondition, it would also run forever on its
    // first step.
    assert_eq!(r.changed, ChangeIndicator::Unchanged);
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
    let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    let g = Goal::Action(v, f);
    r.insert_goal(g.clone());
    assert_eq!(r.changed, ChangeIndicator::Changed);
    assert_eq!(r.sys.goals.len(), 1);
    assert_eq!(r.sys.goals[0].0, g, "the goal is stored verbatim");
    assert!(!r.sys.goals[0].1.solved, "a fresh goal is open");
    // A second insert of the same goal does nothing.  HS `insertGoal` is
    // `M.insertWith combineGoalStatus` keyed by the goal.  The second
    // insert therefore merges into the first slot and raises no change
    // signal.  If the deduplication failed, the insert would append a
    // second copy with `solved=false`. The enclosing fixpoints would then
    // never converge.
    r.changed = ChangeIndicator::Unchanged;
    r.insert_goal(g);
    assert_eq!(r.sys.goals.len(), 1, "duplicate goal must not be re-added");
    assert_eq!(r.changed, ChangeIndicator::Unchanged);
}

#[test]
fn solve_split_prunes_non_normal_arms_before_returning_cases() {
    use crate::constraint::constraints::Goal;
    use crate::fact::{Fact, FactTag};
    use crate::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst, RuleAttributes,
        RuleInfo,
    };
    use tamarin_term::builtin::{fst, msg_var, pair};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::subst_vfresh::SubstVFresh;
    use tamarin_term::vterm::var_term;

    let Some(ctx) = ctx() else { return };
    let x = LVar::new("x", LSort::Msg, 0);
    let rule: RuleACInst = Rule::new(
        RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("R"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        Vec::new(),
        vec![Fact::new(FactTag::Out, vec![fst(var_term(x))])],
        Vec::new(),
    );
    let mut sys = System::empty();
    sys.add_node(LVar::new("i", LSort::Node, 0), rule);
    let split = sys.eq_store_mut().add_disj(vec![
        // This makes the live `fst(x)` reducible and must therefore die.
        SubstVFresh::from_list(vec![(x, pair(msg_var("a", 1), msg_var("b", 2)))]),
        // This leaves `fst(x)` in normal form and is the sole survivor.
        SubstVFresh::from_list(vec![(x, msg_var("y", 3))]),
    ]);
    let mut red = Reduction::new(&ctx, sys);
    red.insert_goal(Goal::Split(split));

    assert!(matches!(
        red.solve_split_goal(split).expect("split solve"),
        GoalCases::LinearNamed(ref name) if name == "split"
    ));
    assert!(!red.sys.eq_store().is_false());
}

#[test]
fn solve_term_eqs_trivial_equation_no_change() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    // x =? x is trivially true.
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let t: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let r_out = r
        .solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: t.clone(),
                rhs: t,
            }],
        )
        .expect("solve");
    assert!(matches!(r_out, SolveOutcome::Linear));
}

#[test]
fn solve_term_eqs_unifies_two_vars() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    // x =? y produces a single mgu.
    use tamarin_term::vterm::Lit;
    let x = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let y = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(x));
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(y));
    let r_out = r
        .solve_term_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }],
        )
        .expect("solve");
    assert!(matches!(r_out, SolveOutcome::Linear));
    assert_eq!(r.changed, ChangeIndicator::Changed);
}

// =====================================================================
// subst_system — Haskell-equivalent invariants
// =====================================================================
//
// Haskell's `Theory.Constraint.Solver.Reduction.substSystem`:
//   substSystem = do
//     c1 <- substNodes
//     substEdges
//     substLastAtom
//     substLessAtoms
//     ...
//     c2 <- substGoals
//     return (c1 <> c2)
// pulls the eq-store substitution through every node id, edge,
// less atom, last atom, and goal. The Rust port should preserve
// these invariants on completion.

/// `i_2 =? j_3` binds the variable with the higher index.  The eq-store
/// maps `j ↦ i`.  Every `subst_system` test below must therefore put the
/// node id that it wants rewritten on the `j` side.  A constraint that
/// mentions only `i` sits on the representative.  The pass does nothing to
/// such a constraint, so the pass cannot fail that test.
fn eqstore_binds_j_to_i(
    r: &mut Reduction<'_>,
    i: tamarin_term::lterm::LVar,
    j: tamarin_term::lterm::LVar,
) {
    use tamarin_term::vterm::Lit;
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal {
            lhs: tamarin_term::term::Term::Lit(Lit::Var(i)),
            rhs: tamarin_term::term::Term::Lit(Lit::Var(j)),
        }],
    )
    .expect("solve");
    assert_eq!(
        tamarin_term::subst::apply_vterm(
            &r.sys.eq_store().subst,
            tamarin_term::term::Term::Lit(Lit::Var(j)),
        ),
        tamarin_term::term::Term::Lit(Lit::Var(i)),
        "precondition: the unifier keeps the lower-idx id, so j ↦ i"
    );
}

#[test]
fn subst_system_rewrites_edge_node_ids_through_eqstore() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let t = LVar::new("t", LSort::Node, 99);
    // One edge has `j` as its source and one has `j` as its target.  The
    // test therefore observes both endpoint rewrites.  `t` is outside the
    // domain of the eq-store and must stay unchanged.
    r.sys.invalidate_max_var_idx_cache();
    r.sys
        .content_mut()
        .edges
        .push(crate::constraint::constraints::Edge {
            src: (j, crate::rule::ConcIdx(0)),
            tgt: (t, crate::rule::PremIdx(0)),
        });
    r.sys
        .content_mut()
        .edges
        .push(crate::constraint::constraints::Edge {
            src: (t, crate::rule::ConcIdx(0)),
            tgt: (j, crate::rule::PremIdx(0)),
        });
    eqstore_binds_j_to_i(&mut r, i, j);
    r.subst_system().expect("solver operation");
    // `substEdges` rewrites both endpoints.  The sort after the pass
    // compares the source first, and `Ord LVar` compares the index first.
    // `i.2` therefore comes before `t.99`.
    assert_eq!(
        r.sys.edges,
        vec![
            crate::constraint::constraints::Edge {
                src: (i, crate::rule::ConcIdx(0)),
                tgt: (t, crate::rule::PremIdx(0)),
            },
            crate::constraint::constraints::Edge {
                src: (t, crate::rule::ConcIdx(0)),
                tgt: (i, crate::rule::PremIdx(0)),
            },
        ],
        "substEdges must map both endpoints through the eq-store"
    );
}

#[test]
fn subst_system_rewrites_less_atom_node_ids() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let t = LVar::new("t", LSort::Node, 9);
    // `j` appears once as the smaller endpoint and once as the larger one.
    // The test therefore observes both `substLessAtoms` rewrites.
    r.sys.invalidate_max_var_idx_cache();
    for la in [
        crate::constraint::constraints::LessAtom::new(
            j,
            t,
            crate::constraint::constraints::Reason::Formula,
        ),
        crate::constraint::constraints::LessAtom::new(
            t,
            j,
            crate::constraint::constraints::Reason::Formula,
        ),
    ] {
        r.sys.content_mut().less_atoms.push(la);
    }
    eqstore_binds_j_to_i(&mut r, i, j);
    r.subst_system().expect("solver operation");
    assert_eq!(
        r.sys
            .less_atoms
            .iter()
            .map(|la| (la.smaller, la.larger))
            .collect::<Vec<_>>(),
        vec![(i, t), (t, i)],
        "substLessAtoms must map both endpoints, keeping insertion order"
    );
    // `LessAtom`'s `Eq` ignores the reason.  The pretty-printer uses the
    // reason to tell the user where the ordering comes from.  The rewrite
    // must therefore keep the reason instead of resetting it.
    assert!(r
        .sys
        .less_atoms
        .iter()
        .all(|la| la.reason == crate::constraint::constraints::Reason::Formula));
}

#[test]
fn subst_system_idempotent_on_empty_substitution() {
    let Some(ctx) = ctx() else { return };
    // This system has content, but its eq-store is empty.  The early return
    // in `subst_system_once` must leave every component byte-for-byte
    // identical.  The pass reorders the nodes (it mirrors `M.toList`), it
    // sorts and deduplicates the edges, and it deduplicates the less-atoms.
    // An early return with the wrong condition therefore shows up here as a
    // reorder, even though no id changes.
    use tamarin_term::lterm::{LSort, LVar};
    let mut sys = System::empty();
    let hi = LVar::new("i", LSort::Node, 7);
    let lo = LVar::new("i", LSort::Node, 1);
    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    // The insertion order is descending by id.  Only a pass that really
    // runs sorts these nodes.
    sys.add_node(hi, crate::rule::Rule::new(info(), vec![], vec![], vec![]));
    sys.add_node(lo, crate::rule::Rule::new(info(), vec![], vec![], vec![]));
    sys.add_edge(crate::constraint::constraints::Edge {
        src: (hi, crate::rule::ConcIdx(0)),
        tgt: (lo, crate::rule::PremIdx(0)),
    });
    sys.add_less(crate::constraint::constraints::LessAtom::new(
        lo,
        hi,
        crate::constraint::constraints::Reason::Formula,
    ));
    let mut r = Reduction::new(&ctx, sys);
    let before = r.sys.clone();
    let before_changed = r.changed;
    assert!(
        r.sys.eq_store().subst.is_empty(),
        "precondition: nothing to substitute"
    );
    r.subst_system().expect("solver operation");
    assert_eq!(r.changed, before_changed, "a no-op pass raises no signal");
    assert_eq!(
        r.sys.nodes.iter().map(|(n, _)| *n).collect::<Vec<_>>(),
        vec![hi, lo],
        "node order must survive an empty-substitution pass"
    );
    assert!(r.sys == before, "an empty substitution rewrites nothing");
}

#[test]
fn subst_system_marks_contradiction_on_shape_mismatch() {
    // Two nodes with the same canonical id but DIFFERENT rule
    // shapes (e.g. one with 0 conclusions, one with 1) cannot be
    // merged consistently — Haskell's `setNodes` reaches the same
    // conclusion via `solveRuleEqs` failing. Our port pushes
    // `gfalse` so the next contradictions check trips.
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    let info = || {
        crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        })
    };
    // First node has 0 conclusions; second has 1 — incompatible.
    r.sys
        .add_node(i, crate::rule::Rule::new(info(), vec![], vec![], vec![]));
    let dummy_fact = crate::fact::Fact::new(crate::fact::FactTag::Out, vec![]);
    r.sys.add_node(
        j,
        crate::rule::Rule::new(info(), vec![], vec![dummy_fact], vec![]),
    );
    // Force i = j into the eq-store.
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system().expect("solver operation");
    let bot = crate::guarded::gfalse();
    assert!(
        crate::guarded::stores_contains(&r.sys.formulas, &bot),
        "shape mismatch must push gfalse onto the formula list"
    );
}

#[test]
fn subst_system_merges_collided_nodes_and_equates_their_rules() {
    // When two nodes collapse to the same canonical id, Haskell's
    // `setNodes` runs `solveRuleEqs` on their facts. Our port queues
    // those into solve_fact_eqs at the tail of subst_system. Verify
    // that the merge happens and only one node remains under the
    // canonical id.
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    let i = LVar::new("i", LSort::Node, 2);
    let j = LVar::new("j", LSort::Node, 3);
    // Two empty rule instances, one keyed by i and one by j.
    let ru = || crate::rule::Rule {
        info: crate::rule::RuleInfo::Proto(crate::rule::ProtoRuleACInstInfo {
            name: crate::rule::ProtoRuleName::Stand("R"),
            attributes: crate::rule::RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        premises: vec![],
        conclusions: vec![],
        actions: vec![],
        new_vars: vec![],
    };
    r.sys.add_node(i, ru());
    r.sys.add_node(j, ru());
    let ti = tamarin_term::term::Term::Lit(Lit::Var(i));
    let tj = tamarin_term::term::Term::Lit(Lit::Var(j));
    r.solve_term_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal { lhs: ti, rhs: tj }],
    )
    .expect("solve");
    r.subst_system().expect("solver operation");
    assert_eq!(
        r.sys.nodes.len(),
        1,
        "two nodes with the same canonical id should merge"
    );
}

#[test]
fn solve_fact_eqs_tag_mismatch_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let f1 = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    let f2 = crate::fact::LNFact::new(crate::fact::FactTag::In, vec![]);
    let r_out = r
        .solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: f1, rhs: f2 }],
        )
        .expect("solve");
    assert!(matches!(r_out, SolveOutcome::Contradictory));
}

#[test]
fn solve_disj_goal_empty_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let d = Disj(Vec::<Guarded>::new());
    let out = r.solve_disj_goal(&d).expect("solver operation");
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn speculative_branch_isolates_reduction_state() {
    let Some(ctx) = ctx() else { return };
    let r = Reduction::new(&ctx, System::empty());
    let counter = r.maude.fresh_counter_peek();

    let mut trial = r.speculative_branch();
    trial.maude.fresh_idx();
    trial.sys.add_goal(Goal::Action(
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
        crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]),
    ));

    assert_eq!(r.maude.fresh_counter_peek(), counter);
    assert!(r.sys.goals.is_empty());
}

#[test]
fn goal_cases_preserve_each_branch_counter_and_adopt_the_singleton() {
    let Some(ctx) = ctx() else { return };
    let mut red = Reduction::new(&ctx, System::empty());
    let start = red.maude.fresh_counter_peek();
    let branches = vec![
        GoalBranch {
            name: "left".into(),
            sys: System::empty(),
            counter: start + 10,
        },
        GoalBranch {
            name: "right".into(),
            sys: System::empty(),
            counter: start + 20,
        },
    ];
    let GoalCases::Cases(branches) = red.finish_goal_cases(branches, "unused".into()) else {
        panic!("multiple goal arms must remain separate cases");
    };
    assert_eq!(
        branches
            .iter()
            .map(|branch| branch.counter)
            .collect::<Vec<_>>(),
        [start + 10, start + 20]
    );

    let marker = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 99);
    let mut singleton = System::empty();
    singleton.content_mut().last_atom = Some(marker);
    assert!(matches!(
        red.finish_goal_cases(
            vec![GoalBranch {
                name: "only".into(),
                sys: singleton,
                counter: start + 30,
            }],
            "only".into(),
        ),
        GoalCases::LinearNamed(name) if name == "only"
    ));
    assert_eq!(red.sys.last_atom, Some(marker));
    assert_eq!(red.maude.fresh_counter_peek(), start + 30);
}

#[test]
fn equality_formula_split_inherits_solved_bookkeeping() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let handle = tamarin_term::maude_proc::MaudeHandle::start(
        &path,
        tamarin_term::maude_sig::xor_maude_sig(),
    )
    .expect("start xor maude");
    let ctx = ProofContext::new(handle, Vec::new());
    use crate::atom::ProtoAtom;
    use crate::guarded::Guarded;
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::term::f_app_ac;
    use tamarin_term::vterm::var_term;
    let var = |name| var_term(BVar::Free(LVar::new(name, LSort::Msg, 0)));
    let formula = Guarded::Atom(ProtoAtom::EqE(
        f_app_ac(AcSym::Xor, vec![var("x"), var("a")]),
        f_app_ac(AcSym::Xor, vec![var("b"), var("y")]),
    ));
    let mut red = Reduction::new(&ctx, System::empty());

    let SystemOutcome::Cases(arms) = red
        .insert_formula(formula.clone())
        .expect("solver operation")
    else {
        panic!("precondition: XOR equality must split");
    };
    assert!(arms
        .iter()
        .all(|arm| crate::guarded::stores_contains(&arm.sys.solved_formulas, &formula)));

    let false_formula = crate::guarded::gfalse();
    let mut red = Reduction::new(&ctx, System::empty());
    let SystemOutcome::Cases(arms) = red
        .insert_formulas(&[formula, false_formula.clone()])
        .expect("solver operation")
    else {
        panic!("formula sequence must preserve the XOR split");
    };
    assert!(arms
        .iter()
        .all(|arm| crate::guarded::stores_contains(&arm.sys.formulas, &false_formula)));
}

#[test]
fn solve_disj_goal_singleton_is_linear() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    // Use gtrue() = Conj([]): it gets decomposed into solved_formulas
    // by insert_formula (not raw-pushed to formulas).
    let f = crate::guarded::gtrue();
    let d = Disj(vec![f.clone()]);
    r.insert_goal(Goal::Disj(d.clone()));
    let out = r.solve_disj_goal(&d).expect("solver operation");
    // Haskell `solveDisjunction` has no singleton special-case: a lone
    // alternative is named `case_1` (and `ppCases` only elides the
    // heading for the empty name), so the Rust continuation is a
    // single named linear case `case_1`, not an unnamed `Linear`.
    assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "case_1"));
    // gtrue (Conj []) decomposes to solved_formulas — see
    // insert_formula_inner for the Conj arm.
    assert!(crate::guarded::stores_contains(&r.sys.solved_formulas, &f));
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Disj(_)) && s.solved));
}

#[test]
fn solve_disj_goal_two_branches_forks() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let f1 = crate::guarded::gtrue(); // Conj([]) → solved_formulas
    let f2 = crate::guarded::gfalse(); // Disj([]) → formulas (gfalse sentinel)
    let d = Disj(vec![f1.clone(), f2.clone()]);
    r.insert_goal(Goal::Disj(d.clone()));
    let out = r.solve_disj_goal(&d).expect("solver operation");
    match out {
        GoalCases::Cases(systems) => {
            assert_eq!(systems.len(), 2);
            assert!(crate::guarded::stores_contains(
                &systems[0].sys.solved_formulas,
                &f1
            ));
            assert!(crate::guarded::stores_contains(
                &systems[1].sys.formulas,
                &f2
            ));
            for branch in &systems {
                let s = &branch.sys;
                assert!(s
                    .goals
                    .iter()
                    .any(|(g, st)| matches!(g, Goal::Disj(_)) && st.solved));
            }
        }
        other => panic!("expected Cases, got {:?}", other),
    }
}

#[test]
fn solve_subterm_goal_marks_solved_and_moves() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let w = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
    let ty: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(w));
    sys.invalidate_max_var_idx_cache();
    sys.subterm_store_mut().add(tx.clone(), ty.clone());
    sys.add_goal(Goal::Subterm((tx.clone(), ty.clone())));
    let mut r = Reduction::new(&ctx, sys);
    let out = r
        .solve_subterm_goal(&(tx.clone(), ty.clone()))
        .expect("solver operation");
    // `x:msg ⊏ y:msg`: big is a bare variable, so `splitSubterm`
    // (singleStep) cannot decompose ⇒ a single `SubtermD (x,y)` leaf.
    // HS `solveSubterm` therefore emits ONE case `SubtermSplit1`,
    // moves (x,y) into solvedSubterms, and re-adds (x,y) into
    // posSubterms via the SubtermD arm's `addSubterm` (the next
    // simplify drops it again via `posSubterms \ solvedSubterms`).
    assert!(matches!(&out, GoalCases::LinearNamed(n) if n == "SubtermSplit1"));
    assert_eq!(r.sys.subterm_store.subterms.len(), 1);
    assert_eq!(r.sys.subterm_store.solved_subterms.len(), 1);
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Subterm(_)) && s.solved));
}

#[test]
fn solve_subterm_self_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(v));
    sys.invalidate_max_var_idx_cache();
    sys.subterm_store_mut().add(tx.clone(), tx.clone());
    let mut r = Reduction::new(&ctx, sys);
    let out = r
        .solve_subterm_goal(&(tx.clone(), tx))
        .expect("solver operation");
    assert!(matches!(out, GoalCases::Contradictory));
    assert!(r.sys.subterm_store.contradictory);
}

/// When the goal's existing node already has the matching action,
/// `solve_action_goal` emits `GoalCases::LinearNamed(rule_case_name)`
/// rather than bare `Linear` — mirrors HS `solveAction`'s `Just ru ->
/// ... return ru` arm (Goals.hs) whose surrounding `showRuleCaseName
/// <$>` (Goals.hs:217-252, see line 223) unconditionally emits the rule's case name.
#[test]
fn solve_action_goal_existing_node_with_action_is_linear_named() {
    let Some(ctx) = ctx() else { return };
    // Build a system with a node already labelled by a rule that
    // produces the action `Out(x)`.
    let mut sys = System::empty();
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::out_fact(tx);
    let ru: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
        vec![],
        vec![],
        vec![fa.clone()],
    );
    sys.add_node(i, ru);
    sys.add_goal(Goal::Action(i, fa.clone()));
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_action_goal(&i, &fa).expect("solver operation");
    // The case name is `showRuleCaseName ru`.  For the `ISend` intruder
    // rule that is the rule name in lower case, `isend`.  The proof tree
    // renders this name after `case `.  The test compares the complete
    // string.  A check that the name is not empty would accept any
    // renaming.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "isend"),
        "expected LinearNamed(\"isend\"), got {:?}",
        out
    );
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Action(_, _)) && s.solved));
}

#[test]
fn solve_action_goal_no_node_no_rules_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::out_fact(tx);
    let out = r.solve_action_goal(&i, &fa).expect("solver operation");
    // No rules in the context → no candidates.
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_action_goal_no_node_with_matching_rule_unifies() {
    let Some(ctx_no) = ctx() else { return };
    // Build a context with one rule that has an Out(y) action.
    let v = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fact_y = crate::fact::out_fact(ty);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Send"),
        vec![],
        vec![],
        vec![fact_y],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let ctx2 = ProofContext::new(ctx_no.maude.clone(), vec![open]);
    let mut r = Reduction::new(&ctx2, System::empty());
    // Goal: Out(x) at fresh node i.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::out_fact(tx);
    let out = r.solve_action_goal(&i, &fa).expect("solver operation");
    // One matching rule with one matching action ⇒ LinearNamed
    // (the rule name); node added in-place to r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Send"),
        "expected LinearNamed(\"Send\"), got {:?}",
        out
    );
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.nodes[0].0, i);
}

#[test]
fn solve_premise_goal_no_user_rules_uses_intruder() {
    // With the intruder rules wired into ProofContext, an `In(x)`
    // premise can be discharged via `ISend` even when no user
    // rules exist. Tests that the intruder-rule fallback works.
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::in_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa).expect("solver operation");
    // In an empty context only the `ISend` intruder rule supplies `In(x)`.
    // Its `showRuleCaseName` is `isend`.  The solver applies the node and
    // the edge into the premise in place.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "isend"),
        "expected LinearNamed(\"isend\"), got {:?}",
        out
    );
    assert!(r.sys.nodes.iter().any(|(_, ru)| matches!(
        ru.info,
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend)
    )));
    assert_eq!(r.sys.edges.len(), 1);
    assert_eq!(r.sys.edges[0].tgt, p);
}

#[test]
fn solve_premise_goal_no_user_rules_unmatchable_fact_is_contradictory() {
    // Use a fact tag that no intruder rule produces (e.g. a
    // user-defined linear `Foo(x)` fact in an empty context).
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Foo", 1),
        vec![tx],
    );
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa).expect("solver operation");
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_premise_goal_with_matching_rule_inserts_edge() {
    let Some(base) = ctx() else { return };
    // Rule that produces an Out(y) conclusion.
    let v = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let conc_y = crate::fact::out_fact(ty);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Producer"),
        vec![],
        vec![conc_y],
        vec![],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let ctx2 = ProofContext::new(base.maude.clone(), vec![open]);
    let mut r = Reduction::new(&ctx2, System::empty());
    // Premise: Out(x) at node i, premise idx 0.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 5);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::out_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa).expect("solver operation");
    // Single matching rule → LinearNamed("Producer"); node + edge
    // applied in-place to r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Producer"),
        "expected LinearNamed(\"Producer\"), got {:?}",
        out
    );
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.edges.len(), 1);
    assert_eq!(r.sys.edges[0].tgt, p);
}

#[test]
fn solve_premise_goal_kd_fact_inserts_irecv_chain() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = crate::fact::kd_fact(tx);
    let p = (i, crate::rule::PremIdx(0));
    let _out = r.solve_premise_goal(&p, &fa).expect("solver operation");
    // KD branch inserts IRecv + Chain goal; the Out(mLearn) premise
    // is recursively solved inline (Haskell's solvePremise behaviour)
    // so it does NOT remain as a queued Premise goal.  The recursive
    // solve picks some producer (or Contradictory if there's none in
    // an empty test ctx); the structural invariants we check here are
    // just the IRecv node and chain goal.
    assert!(r.sys.nodes.iter().any(|(_, ru)| matches!(
        ru.info,
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv)
    )));
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, _)| matches!(g, Goal::Chain(_, _))));
}

#[test]
fn solve_chain_goal_missing_node_is_contradictory() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let j = tamarin_term::lterm::LVar::new("j", tamarin_term::lterm::LSort::Node, 0);
    let c = (i, crate::rule::ConcIdx(0));
    let p = (j, crate::rule::PremIdx(0));
    let out = r.solve_chain_goal(&c, &p).expect("solver operation");
    assert!(matches!(out, GoalCases::Contradictory));
}

#[test]
fn solve_chain_goal_compatible_facts_inserts_edge() {
    let Some(ctx) = ctx() else { return };
    // Build two nodes whose conc/prem facts are compatible.
    let mut sys = System::empty();
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let j = tamarin_term::lterm::LVar::new("j", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    // Node i conclusion: KD(x).
    let conc_kd = crate::fact::kd_fact(tx.clone());
    let ru_i: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IRecv),
        vec![],
        vec![conc_kd],
        vec![],
    );
    sys.add_node(i, ru_i);
    // Node j premise: KD(x).
    let prem_kd = crate::fact::kd_fact(tx);
    let ru_j: crate::rule::RuleACInst = crate::rule::Rule::new(
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::ISend),
        vec![prem_kd],
        vec![],
        vec![],
    );
    sys.add_node(j, ru_j);
    let c = (i, crate::rule::ConcIdx(0));
    let p = (j, crate::rule::PremIdx(0));
    sys.add_goal(Goal::Chain(c, p));
    let mut r = Reduction::new(&ctx, sys);
    let out = r.solve_chain_goal(&c, &p).expect("solver operation");
    // The facts are compatible, so there is one case.
    // `chain_direct_case_name` names that case from the message of the KD
    // conclusion.  HS `showLitName` spells the name `Var_<sort>_<name>` for
    // a variable with index 0.  The solver adds the edge and marks the goal
    // solved in place.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Var_msg_x"),
        "expected LinearNamed(\"Var_msg_x\"), got {:?}",
        out
    );
    assert_eq!(r.sys.edges.len(), 1);
    assert_eq!(r.sys.edges[0].src, c);
    assert_eq!(r.sys.edges[0].tgt, p);
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, s)| matches!(g, Goal::Chain(_, _)) && s.solved));
}

#[test]
fn insert_atom_action_creates_action_goal() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::LSort;
    let action = ProtoAtom::Action(
        mkvar_ln("i", LSort::Node),
        crate::fact::proto_fact(
            crate::fact::Multiplicity::Linear,
            "Setup",
            vec![mkvar_ln("k", LSort::Msg)],
        ),
    );
    assert!(matches!(
        r.insert_atom(&action).expect("atom insertion"),
        SystemOutcome::Linear
    ));
    assert_eq!(r.sys.goals.len(), 1);
    assert!(matches!(&r.sys.goals[0].0, Goal::Action(_, fact)
            if fact.tag == crate::fact::FactTag::Proto(
                crate::fact::Multiplicity::Linear, "Setup", 1)));
}

/// HS `insertAtom` answers `Syntactic _ -> return ()` (Reduction.hs:421):
/// the sugar carries no constraint, so nothing about the system moves.
#[test]
fn insert_atom_ignores_a_syntactic_atom() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let a = crate::atom::ProtoAtom::Syntactic(crate::atom::Unit2);
    assert!(matches!(
        r.insert_atom(&a).expect("atom insertion"),
        SystemOutcome::Linear
    ));
    assert!(r.sys.goals.is_empty());
    assert!(r.sys.less_atoms.is_empty());
    assert_eq!(r.sys.last_atom, None);
    assert!(r.sys.eq_store().subst.is_empty());
}

/// A `NameTag::Node` constant reaches the eq-store as itself.  It is the tag
/// Maude mints for a skolemised timepoint (maude_proc.rs).
#[test]
fn insert_atom_eq_keeps_the_node_name_tag() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use tamarin_term::lterm::{LSort, Name, NameTag};
    let node_name: tamarin_term::lterm::LNTerm =
        tamarin_term::vterm::const_term(Name::new(NameTag::Node, "n1"));
    let a = crate::atom::ProtoAtom::EqE(mkvar_ln("i", LSort::Node), node_name.clone());
    assert!(matches!(
        r.insert_atom(&a).expect("atom insertion"),
        SystemOutcome::Linear
    ));
    let i = tamarin_term::lterm::LVar::new("i", LSort::Node, 0);
    assert_eq!(
        r.sys.eq_store().subst.image_of(&i),
        Some(&node_name),
        "the eq-store binds the timepoint to the Node-tagged name itself"
    );
}

#[test]
fn insert_atom_less_creates_less_atom() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::LSort;
    let less = ProtoAtom::Less(mkvar_ln("i", LSort::Node), mkvar_ln("j", LSort::Node));
    assert!(matches!(
        r.insert_atom(&less).expect("atom insertion"),
        SystemOutcome::Linear
    ));
    assert_eq!(r.sys.less_atoms.len(), 1);
    // The order of the endpoints is the complete content of a `Less` atom.
    // The pretty-printer uses the reason tag to tell the user where the
    // ordering comes from.  Without these two assertions, a swapped pair or
    // a default reason also passes.
    let la = &r.sys.less_atoms[0];
    let node = |n: &str| tamarin_term::lterm::LVar::new(n, tamarin_term::lterm::LSort::Node, 0);
    assert_eq!((la.smaller, la.larger), (node("i"), node("j")));
    assert_eq!(la.reason, crate::constraint::constraints::Reason::Formula);
}

#[test]
fn insert_atom_last_sets_last_atom() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::LSort;
    let last = ProtoAtom::Last(mkvar_ln("i", LSort::Node));
    assert!(matches!(
        r.insert_atom(&last).expect("atom insertion"),
        SystemOutcome::Linear
    ));
    assert_eq!(
        r.sys.last_atom,
        Some(tamarin_term::lterm::LVar::new(
            "i",
            tamarin_term::lterm::LSort::Node,
            0
        )),
        "`insertLast` stores the atom's own node id, not just some id"
    );
}

#[test]
fn solve_action_with_fresh_premise_adds_fresh_supplier() {
    let Some(base) = ctx() else { return };
    // Setup-like rule: [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Fresh, 0);
    use tamarin_term::vterm::Lit;
    let tk: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let prem = crate::fact::fresh_fact(tk.clone());
    let act = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Setup", 1),
        vec![tk.clone()],
    );
    let conc = crate::fact::out_fact(tk);
    let rule: crate::rule::ProtoRuleE = crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Setup"),
        vec![prem],
        vec![conc],
        vec![act],
    );
    let open = crate::theory::OpenProtoRule::new(rule);
    let ctx2 = ProofContext::new(base.maude.clone(), vec![open]);
    let mut r = Reduction::new(&ctx2, System::empty());

    // Goal: Setup(x) at fresh node i.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v2 = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 1);
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    let fa = crate::fact::Fact::new(
        crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Setup", 1),
        vec![tx],
    );
    let out = r.solve_action_goal(&i, &fa).expect("solver operation");
    // LinearNamed("Setup") with in-place mutation: 2 nodes (Setup
    // instance + Fresh supplier) and 1 edge in r.sys.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Setup"),
        "expected LinearNamed(\"Setup\"), got {:?}",
        out
    );
    assert_eq!(
        r.sys.nodes.len(),
        2,
        "expected 2 nodes (Setup + Fresh supplier), got {}",
        r.sys.nodes.len()
    );
    assert_eq!(r.sys.edges.len(), 1, "expected 1 edge");
}

// =========================================================================
// Haskell-faithfulness invariants for case-naming.
//
// Mirrors Haskell's `casName` (Reduction.hs) which uses 1-INDEXED
// `case_<n>` for generic case labels.  Off-by-one here makes
// `distinguish` (ProofMethod.hs:282-339, see line 334) disambiguate against the
// wrong sibling suffix and the proof skeleton drifts.
// =========================================================================

/// `default_case_name(i)` produces `case_<i+1>` — 1-INDEXED.
///
/// Mirrors Haskell's `casName` convention; an off-by-one here regresses
/// the `case split` cluster.  Disjunction-driven case
/// labels (`case_1`, `case_2`, ...) must match the Haskell printer
/// exactly or proof-skeleton diffs report spurious mismatches.
#[test]
fn default_case_name_is_one_indexed() {
    assert_eq!(default_case_name(0), "case_1");
    assert_eq!(default_case_name(1), "case_2");
    assert_eq!(default_case_name(9), "case_10");
    assert_eq!(
        default_case_name(99),
        "case_100",
        "three-digit suffix renders without padding"
    );
}

/// Build a `∀[].[Less #i #j].⊥` GGuarded value — the negated-
/// `Less`-of-node-ids idiom HS calls `markAsSolved`+decompose on
/// (Reduction.hs:461-486).
fn neg_less_node_universal(i_name: &str, j_name: &str) -> Guarded {
    use crate::atom::ProtoAtom;
    use crate::formula::{BLNTerm, Quantifier};
    use tamarin_term::lterm::{BVar, LSort, LVar};
    use tamarin_term::vterm::var_term;
    let mkvar = |n: &str| -> BLNTerm { var_term(BVar::Free(LVar::new(n, LSort::Node, 0))) };
    let guard = ProtoAtom::Less(mkvar(i_name), mkvar(j_name));
    Guarded::GGuarded {
        qua: Quantifier::All,
        vars: Vec::new().into(),
        guards: vec![guard].into(),
        body: std::sync::Arc::new(crate::guarded::gfalse()),
    }
}

/// HS-faithful `markAsSolved = when mark $ modM sSolvedFormulas
/// $ S.insert fm` (Reduction.hs:427-494, see line 494).  Children of a Conj/Ex body
/// recurse via `insert' False`, so a negated-atom universal that
/// arrives transitively MUST NOT push into `solved_formulas`.
///
/// The four `solved_formulas.push` sites (Less-node-id, Eq-node-id,
/// Last, Subterm CR-rules) are gated on `mark`.
/// This test exercises the Less-node-id arm:
///   - `insert_formula_inner(_, mark=false)` must leave
///     `solved_formulas` untouched.
///   - `insert_formula_inner(_, mark=true)` (the top-level
///     `insert_formula` entrypoint) must push the formula.
///     Both calls produce the same decomposition (`#i = #j ∨ #j < #i`).
#[test]
fn insert_formula_negated_less_mark_false_does_not_push_solved() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let g = neg_less_node_universal("i", "j");
    assert!(
        r.sys.solved_formulas.is_empty(),
        "precondition: solved_formulas starts empty"
    );
    // mark=false (the Conj/Ex-body-recursion case).
    assert!(matches!(
        r.insert_formula_inner(g.clone(), false)
            .expect("formula insertion"),
        SystemOutcome::Linear
    ));
    assert!(
        !crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
        "mark=false MUST NOT push the negated-Less universal into \
             solved_formulas — HS `markAsSolved` is `when mark $ ...` \
             (Reduction.hs:491).  Pushing unconditionally inflates \
             sSolvedFormulas (Yubikey slightly_weaker_invariant: 3 vs 4)."
    );
    // The arm also really runs.  It decomposes the formula into
    // `#i = #j ∨ #j < #i`, which becomes a `Goal::Disj` with two
    // alternatives.  Without this check the negative assertion above also
    // passes when the CR-rule never runs.
    assert_disj_decomposition(&r);
}

/// The shared post-condition of the `∀[].[Less #i #j].⊥` CR-rule.  The rule
/// produces a `Goal::Disj` with two alternatives (`#i = #j ∨ #j < #i`).  It
/// also raises the change signal.  Neither result depends on the `mark`
/// flag.
fn assert_disj_decomposition(r: &Reduction<'_>) {
    assert_eq!(r.changed, ChangeIndicator::Changed);
    let disjs: Vec<usize> = r
        .sys
        .goals
        .iter()
        .filter_map(|(g, _)| match g {
            Goal::Disj(d) => Some(d.0.len()),
            _ => None,
        })
        .collect();
    assert_eq!(
        disjs,
        vec![2],
        "the negated-Less universal decomposes into exactly one \
         two-alternative disjunction goal (`#i = #j ∨ #j < #i`)"
    );
}

#[test]
fn insert_formula_negated_less_mark_true_pushes_solved() {
    let Some(ctx) = ctx() else { return };
    let mut r = Reduction::new(&ctx, System::empty());
    let g = neg_less_node_universal("i", "j");
    // mark=true (the top-level entrypoint).
    assert!(matches!(
        r.insert_formula_inner(g.clone(), true)
            .expect("formula insertion"),
        SystemOutcome::Linear
    ));
    assert!(
        crate::guarded::stores_contains(&r.sys.solved_formulas, &g),
        "mark=true (top-level `insert_formula`) MUST push the \
             negated-Less universal into solved_formulas — \
             HS `markAsSolved` fires (Reduction.hs:491)."
    );
    // `mark` controls only the push into solved_formulas.  The
    // decomposition is the same on both paths.
    assert_disj_decomposition(&r);
}
