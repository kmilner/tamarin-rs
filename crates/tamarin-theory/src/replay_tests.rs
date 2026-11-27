// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::constraint::solver::proof_method::Result as MethodResult;
use crate::constraint::solver::search::run_proof_search;
use crate::constraint::system::System;
use crate::theory::ProofTree;
use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::pair_maude_sig;

/// A maude handle for the pins below, or `None` only when the run has
/// explicitly opted out via `TAM_ALLOW_NO_MAUDE=1` — resolution and the
/// loud-failure policy live in [`tamarin_test_support::require_maude_path`].
fn maude() -> Option<MaudeHandle> {
    let path = tamarin_test_support::require_maude_path()?;
    // A maude that resolved but will not start is the same misconfiguration
    // as a dangling MAUDE_PATH: swallowing it with `.ok()` would silently
    // skip every pin in this file, so fail loudly instead.
    Some(MaudeHandle::start(&path, pair_maude_sig()).unwrap_or_else(|e| {
        panic!("maude at {path} failed to start: {e:?} — every maude-backed pin here would otherwise skip silently")
    }))
}

/// An otherwise-empty system that carries one solved formula.  The system
/// has no goals and no contradictions.  It is also past the initial state,
/// so `is_finished` runs and the auto-prover closes the system as Solved.
/// `System::empty()` on its own is still in the initial state.  It only ever
/// yields `Sorry`.  With that system, every assertion below that the
/// auto-prover ran would hold vacuously.
fn past_initial_system() -> System {
    let mut sys = System::empty();
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    sys
}

/// The `by sorry` leaf is where the two replay entry points differ.  That
/// difference is the reason both entry points exist.
///
/// `replace_sorry_prove` (HS `replaceSorryProver $ runAutoProver`, the
/// `--prove`-target path) must hand the leaf's system to the auto-prover.
/// Its result is then exactly the result of `run_proof_search`.
///
/// `check_and_extend` (HS `checkAndExtendProver (sorryProver Nothing)`, the
/// non-target path) must not prove.  It must leave an annotated `Sorry`
/// behind.  The `Sorry` must be annotated, so the lemma reprints as plain
/// `by sorry` with no `/* unannotated */`.
///
/// [`past_initial_system`] is the degenerate case that the auto-prover
/// closes as Solved.  That is what keeps the equality below from holding
/// vacuously between two `Sorry`s.
#[test]
fn sorry_leaf_runs_auto_prover_only_for_prove_targets() {
    let Some(h) = maude() else { return };
    let ctx = ProofContext::new(h, Vec::new());
    // Skeleton = `by sorry`.
    let skel = ProofTree {
        method: ProofMethod::Sorry(None),
        cases: BTreeMap::new(),
    };
    let replayed =
        replace_sorry_prove(&ctx, past_initial_system(), &skel, 50).expect("proof search");
    let direct = run_proof_search(&ctx, past_initial_system(), 50).expect("default ranking");
    assert_eq!(replayed.status, direct.status);
    assert_eq!(replayed.method, direct.method);
    assert_eq!(
        replayed.status,
        NodeStatus::Solved,
        "the auto-prover closes this system, so the equality above is not a \
         Sorry-equals-Sorry tautology"
    );

    let kept = check_and_extend(&ctx, past_initial_system(), &skel, 50).expect("proof replay");
    assert_eq!(
        kept.status,
        NodeStatus::Sorry,
        "a non-target lemma's stored sorry must survive unproved"
    );
    assert!(matches!(kept.method, ProofMethod::Sorry(None)));
    assert!(
        kept.annotation.is_checked(),
        "a stored sorry leaf stays annotated"
    );

    let reason = "kept reason".to_string();
    let explained = check_and_extend(
        &ctx,
        past_initial_system(),
        &ProofTree {
            method: ProofMethod::Sorry(Some(reason.clone())),
            cases: BTreeMap::new(),
        },
        50,
    )
    .expect("proof replay");
    assert_eq!(explained.method, ProofMethod::Sorry(Some(reason)));
}

#[test]
fn sorry_with_children_is_replaced_as_one_node() {
    let Some(h) = maude() else { return };
    let ctx = ProofContext::new(h, Vec::new());
    let child = ProofTree {
        method: ProofMethod::Finished(MethodResult::Contradictory(None)),
        cases: BTreeMap::new(),
    };
    let skel = ProofTree {
        method: ProofMethod::Sorry(Some("stale".into())),
        cases: BTreeMap::from([("kept".into(), child)]),
    };

    let replayed =
        replace_sorry_prove(&ctx, past_initial_system(), &skel, 50).expect("proof search");
    assert_eq!(replayed.status, NodeStatus::Solved);
    assert!(replayed.children.is_empty(), "the old subtree is replaced");

    let checked = check_and_extend(&ctx, past_initial_system(), &skel, 50).expect("proof replay");
    assert_eq!(checked.method, ProofMethod::Sorry(Some("stale".into())));
    assert!(checked.annotation.is_checked());
    let kept = &checked.children["kept"];
    assert!(
        !kept.annotation.is_checked(),
        "stored children have no checked system"
    );
    assert_eq!(
        kept.method,
        ProofMethod::Finished(MethodResult::Contradictory(None))
    );
}

/// A stale contradiction must be re-proved against the current system.
#[test]
fn contradiction_leaf_without_contradiction_falls_back_to_auto() {
    let Some(h) = maude() else { return };
    let ctx = ProofContext::new(h, Vec::new());
    let sys = past_initial_system();
    let skel = ProofTree {
        method: ProofMethod::Finished(MethodResult::Contradictory(None)),
        cases: BTreeMap::new(),
    };
    let result = replace_sorry_prove(&ctx, sys, &skel, 50).expect("proof search");
    // No goals, no contradictions → auto-prover recognises Solved. The
    // contract is "fall back to auto-prover, never fabricate
    // Contradictory".
    assert_ne!(
        result.status,
        NodeStatus::Contradictory,
        "walker must NOT fabricate Contradictory when runtime disagrees"
    );
    assert_eq!(result.status, NodeStatus::Solved);
}

/// `match_goal` binds a stored proof step's goal to a live goal by
/// structural equality over all of the system's goals, solved or not: HS's
/// `M.member` (ProofMethod.hs).  There is no fallback to a unique goal of
/// the same kind, so any drift in a name, index, sort, argument or
/// alternative misses.  Rows: `(label, live goals, stored goal, hit?)`;
/// a hit returns the stored goal itself.
#[test]
fn match_goal_is_structural_membership() {
    use crate::atom::ProtoAtom;
    use crate::constraint::constraints::{Disj, SplitId};
    use crate::constraint::system::GoalStatus;
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::formula::BLNTerm;
    use crate::guarded::Guarded;
    use crate::rule::{ConcIdx, PremIdx};
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::BVar;
    use tamarin_term::term::{f_app_ac, Term};
    use tamarin_term::vterm::{var_term, Lit};

    let msg = |n: &str, idx| Term::Lit(Lit::Var(LVar::new(n, LSort::Msg, idx)));
    let node = |n: &str, idx| LVar::new(n, LSort::Node, idx);
    let action = |name: &'static str, tp: &str, idx, args: Vec<_>| {
        let tag = FactTag::Proto(Multiplicity::Linear, name, args.len());
        Goal::Action(node(tp, idx), Fact::new(tag, args))
    };
    // HS shows a timepoint as `#t2` at index 0 and `#t2.7` at index 7
    // (`Show LVar`, LTerm.hs), so a stored goal names the index too.
    let step = |tp: &str, idx, arg: &str| action("Step", tp, idx, vec![msg(arg, 0)]);
    let premise = |n: &str| {
        let tag = FactTag::Proto(Multiplicity::Linear, "Inp", 0);
        Goal::Premise((node(n, 0), PremIdx(0)), Fact::new(tag, Vec::new()))
    };
    // `ChainG NodeConc NodePrem` carries a full node variable at each end.
    let chain = |i, j| Goal::Chain((node("i", i), ConcIdx(0)), (node("j", j), PremIdx(2)));
    let subterm = |small: &str, big: &str, idx| Goal::Subterm((msg(small, idx), msg(big, idx)));
    let free = |n: &str, sort| -> BLNTerm { var_term(BVar::Free(LVar::new(n, sort, 0))) };
    let last = |n: &str| Guarded::Atom(ProtoAtom::Last(free(n, LSort::Node)));
    let disj = |alts: Vec<Guarded>| Goal::Disj(Disj::new(alts));
    let sorted_eq = |sort| Guarded::Atom(ProtoAtom::EqE(free("x", sort), free("x", sort)));
    // `fAppAC` flattens and sorts (Term/Raw.hs), so both foldings are one value.
    let union_eq = |left_nested: bool| {
        let leaf = |n| free(n, LSort::Msg);
        let un = |l, r| f_app_ac(AcSym::Union, vec![l, r]);
        let chain = if left_nested {
            un(un(leaf("a"), leaf("b")), leaf("c"))
        } else {
            un(leaf("a"), un(leaf("b"), leaf("c")))
        };
        Guarded::Atom(ProtoAtom::EqE(chain, leaf("z")))
    };
    let solved = GoalStatus {
        solved: true,
        ..Default::default()
    };
    let open = GoalStatus::default;

    let steps = vec![(step("t1", 5, "x"), open()), (step("t2", 7, "y"), open())];
    // Yubikey `slightly_weaker_invariant` at `/non_empty_trace/case_1`: two
    // IH-body disjunctions that differ only in `last(#t1)` vs `last(#t2)`.
    let ih = vec![
        (disj(vec![last("t1"), last("a")]), open()),
        (disj(vec![last("t2"), last("a")]), open()),
    ];
    let pair = vec![(disj(vec![last("a"), last("b")]), open())];
    let rows: Vec<(&str, Vec<(Goal, GoalStatus)>, Goal, bool)> = vec![
        (
            "nullary action",
            vec![(action("Setup", "t", 0, vec![]), open())],
            action("Setup", "t", 0, vec![]),
            true,
        ),
        (
            "other fact name",
            vec![(action("Setup", "t", 0, vec![]), open())],
            action("WrongName", "t", 0, vec![]),
            false,
        ),
        (
            "solved goal",
            vec![(action("Setup", "t", 0, vec![]), solved)],
            action("Setup", "t", 0, vec![]),
            true,
        ),
        (
            "first of two actions",
            steps.clone(),
            step("t1", 5, "x"),
            true,
        ),
        (
            "second of two actions",
            steps.clone(),
            step("t2", 7, "y"),
            true,
        ),
        (
            "drifted timepoint index",
            steps.clone(),
            step("t2", 9, "y"),
            false,
        ),
        ("drifted argument", steps, step("t2", 7, "x"), false),
        (
            "premise by node",
            vec![(premise("u"), open()), (premise("v"), open())],
            premise("v"),
            true,
        ),
        ("chain", vec![(chain(3, 5), open())], chain(3, 5), true),
        (
            "chain without node indices",
            vec![(chain(3, 5), open())],
            chain(0, 0),
            false,
        ),
        (
            "split 3",
            vec![
                (Goal::Split(SplitId(7)), open()),
                (Goal::Split(SplitId(3)), open()),
            ],
            Goal::Split(SplitId(3)),
            true,
        ),
        (
            "split 7",
            vec![
                (Goal::Split(SplitId(7)), open()),
                (Goal::Split(SplitId(3)), open()),
            ],
            Goal::Split(SplitId(7)),
            true,
        ),
        (
            "unknown split",
            vec![(Goal::Split(SplitId(7)), open())],
            Goal::Split(SplitId(99)),
            false,
        ),
        (
            "subterm",
            vec![(subterm("x", "y", 99), open())],
            subterm("x", "y", 99),
            true,
        ),
        (
            "sole subterm, other terms",
            vec![(subterm("x", "y", 99), open())],
            subterm("p", "q", 99),
            false,
        ),
        (
            "sole subterm, other index",
            vec![(subterm("x", "y", 99), open())],
            subterm("x", "y", 0),
            false,
        ),
        (
            "disjunction t2",
            ih.clone(),
            disj(vec![last("t2"), last("a")]),
            true,
        ),
        (
            "disjunction t1",
            ih.clone(),
            disj(vec![last("t1"), last("a")]),
            true,
        ),
        (
            "disjunction t3",
            ih,
            disj(vec![last("t3"), last("a")]),
            false,
        ),
        (
            "fewer alternatives",
            pair.clone(),
            disj(vec![last("a")]),
            false,
        ),
        (
            "more alternatives",
            pair,
            disj(vec![last("a"), last("b"), last("c")]),
            false,
        ),
        (
            "disjunct of the same sort",
            vec![(disj(vec![sorted_eq(LSort::Msg)]), open())],
            disj(vec![sorted_eq(LSort::Msg)]),
            true,
        ),
        (
            "disjunct of another sort",
            vec![(disj(vec![sorted_eq(LSort::Msg)]), open())],
            disj(vec![sorted_eq(LSort::Fresh)]),
            false,
        ),
        (
            "AC chain folded the other way",
            vec![(disj(vec![union_eq(false)]), open())],
            disj(vec![union_eq(true)]),
            true,
        ),
    ];
    for (label, live, stored, hit) in rows {
        let mut sys = System::empty();
        sys.goals_mut().extend(live);
        let expected = hit.then(|| stored.clone());
        assert_eq!(match_goal(&stored, &sys), expected, "{label}");
    }
}

/// Stored induction is valid only at HS's initial-system shape. In
/// particular, a solved formula means replay must reject the step before
/// `exec_proof_method` can apply `ginduct` to a remaining formula.
#[test]
fn replay_checks_induction_applicability() {
    let Some(h) = maude() else { return };
    let ctx = ProofContext::new(h, Vec::new());
    let mut sys = System::empty();
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));

    assert!(exec_method_for(&ProofMethod::Induction, &sys, &ctx)
        .expect("method check")
        .is_none());
}

/// A stored-only case and all its descendants are unchecked.
#[test]
fn parsed_to_unannotated_marks_whole_subtree() {
    // Skeleton:  simplify → case "a" (by sorry), case "b" (by sorry)
    let leaf = |m| ProofTree {
        method: m,
        cases: BTreeMap::new(),
    };
    let skel = ProofTree {
        method: ProofMethod::Simplify,
        cases: BTreeMap::from([
            ("a".to_string(), leaf(ProofMethod::Sorry(None))),
            ("b".to_string(), leaf(ProofMethod::Sorry(None))),
        ]),
    };
    let node = parsed_to_unannotated(&skel);
    assert!(!node.annotation.is_checked(), "root must be unannotated");
    assert_eq!(node.children.len(), 2);
    for (name, child) in &node.children {
        assert!(
            !child.annotation.is_checked(),
            "child `{name}` must be unannotated"
        );
        assert!(matches!(child.method, ProofMethod::Sorry(None)));
    }
}
