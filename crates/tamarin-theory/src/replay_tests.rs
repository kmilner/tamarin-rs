// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::constraint::system::System;
use crate::theory::ProofTree;
use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::pair_maude_sig;

/// A maude handle for the pins below, or `None` only when the run has
/// explicitly opted out via `TAM_ALLOW_NO_MAUDE=1` — resolution and the
/// loud-failure policy live in [`crate::test_maude::maude_path`].
fn maude() -> Option<MaudeHandle> {
    let path = crate::test_maude::maude_path()?;
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
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let ctx = ProofContext::new(h, Vec::new());
    // Skeleton = `by sorry`.
    let skel = ProofTree {
        method: ProofMethod::Sorry(None),
        cases: Vec::new(),
    };
    let replayed = replace_sorry_prove(&ctx, past_initial_system(), &skel, 50);
    let direct = run_proof_search(&ctx, past_initial_system(), 50);
    assert_eq!(replayed.status, direct.status);
    assert_eq!(replayed.method, direct.method);
    assert_eq!(
        replayed.status,
        NodeStatus::Solved,
        "the auto-prover closes this system, so the equality above is not a \
         Sorry-equals-Sorry tautology"
    );

    let kept = check_and_extend(&ctx, past_initial_system(), &skel, 50);
    assert_eq!(
        kept.status,
        NodeStatus::Sorry,
        "a non-target lemma's stored sorry must survive unproved"
    );
    assert!(matches!(kept.method, ProofMethod::Sorry(None)));
    assert!(kept.annotated, "a stored sorry leaf stays annotated");
}

/// A `by contradiction` leaf on a system with no contradictions
/// must NOT silently emit Finished(Contradictory).  Per the
/// walker contract (the contradiction-leaf branch, `finished_leaf`),
/// when the runtime doesn't agree with the skeleton's `by contradiction`
/// claim, the walker falls back to `run_proof_search` — the
/// auto-prover then finds whatever the system actually proves
/// (or emits Sorry honestly).  Crucially, the walker must NOT
/// fabricate a Contradictory status.
///
/// On a system with no goals and no contradictions, the auto-prover
/// recognises the system as trivially Solved.  The assertion that matters
/// here is `status != Contradictory`.
#[test]
fn contradiction_leaf_without_contradiction_falls_back_to_auto() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let ctx = ProofContext::new(h, Vec::new());
    let sys = past_initial_system();
    let skel = ProofTree {
        method: ProofMethod::Finished(MethodResult::Contradictory(None)),
        cases: Vec::new(),
    };
    let result = replace_sorry_prove(&ctx, sys, &skel, 50);
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

// Every stored goal below is a `Goal` value, the shape
// `elaborate::goal_from_parsed` builds, and `match_goal` looks it up among
// the system's open goals by structural equality — HS's `M.member`
// (ProofMethod.hs:253-258).

/// Match an Action goal whose fact takes no arguments.
#[test]
fn match_action_goal_by_name_arity() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let goal = Goal::Action(i, Fact::new(tag, Vec::new()));
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    assert_eq!(match_goal(&goal, &sys).expect("should match"), goal);
}

/// match_goal returns None when no goal matches the fact name.
#[test]
fn no_match_returns_none() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let goal = |name: &'static str| {
        Goal::Action(
            i,
            Fact::new(FactTag::Proto(Multiplicity::Linear, name, 0), Vec::new()),
        )
    };
    let mut sys = System::empty();
    sys.goals_mut().push((goal("Setup"), Default::default()));
    assert!(match_goal(&goal("WrongName"), &sys).is_none());
}

/// A goal already marked solved is out of the lookup's reach, which is the
/// one place it ranges over less than HS's `sGoals`.
#[test]
fn match_goal_skips_a_solved_goal() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let goal = Goal::Action(LVar::new("t", LSort::Node, 0), Fact::new(tag, Vec::new()));
    let mut sys = System::empty();
    let status = crate::constraint::system::GoalStatus {
        solved: true,
        ..Default::default()
    };
    sys.goals_mut().push((goal.clone(), status));
    assert!(match_goal(&goal, &sys).is_none());
}

/// Two same-fact-name Action goals at different timepoints: the stored goal
/// carries the FULL timepoint LVar, name and index, so it binds exactly one
/// of them and a drifted index binds neither.
///
/// HS pretty-prints a timepoint as `#t2` when its index is 0 and `#t2.7`
/// when it is 7 (`Show LVar`, LTerm.hs:550-557), so the index in a stored
/// goal is the index of the goal it names.
#[test]
fn match_action_disambiguates_by_time_var_root() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let tag = FactTag::Proto(Multiplicity::Linear, "Step", 1);
    let arg = |n: &str| {
        vec![tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(LVar::new(n, LSort::Msg, 0)),
        )]
    };
    let goal = |tp: &str, idx: u64, a: &str| {
        Goal::Action(LVar::new(tp, LSort::Node, idx), Fact::new(tag, arg(a)))
    };
    let g1 = goal("t1", 5, "x");
    let g2 = goal("t2", 7, "y");
    let mut sys = System::empty();
    sys.goals_mut().push((g1.clone(), Default::default()));
    sys.goals_mut().push((g2.clone(), Default::default()));
    assert_eq!(match_goal(&g2, &sys).expect("should match"), g2);
    assert_eq!(match_goal(&g1, &sys).expect("should match"), g1);
    // A drifted index (stored `#t2.9`, runtime `#t2.7`) is an `M.member`
    // miss in HS.
    assert!(
        match_goal(&goal("t2", 9, "y"), &sys).is_none(),
        "drifted timepoint idx must miss like HS `M.member`"
    );
    // So is a drifted argument.
    assert!(match_goal(&goal("t2", 7, "x"), &sys).is_none());
}

/// Two same-(name, arity, prem idx) Premise goals at different node
/// timepoints.
#[test]
fn match_premise_disambiguates_by_time_var_root() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::PremIdx;
    let tag = FactTag::Proto(Multiplicity::Linear, "Inp", 0);
    let goal = |n: &str| {
        Goal::Premise(
            (LVar::new(n, LSort::Node, 0), PremIdx(0)),
            Fact::new(tag, Vec::new()),
        )
    };
    let mut sys = System::empty();
    sys.goals_mut().push((goal("u"), Default::default()));
    sys.goals_mut().push((goal("v"), Default::default()));
    assert_eq!(
        match_goal(&goal("v"), &sys).expect("should match"),
        goal("v")
    );
}

/// HS's `ChainG NodeConc NodePrem` carries a full `nodevar` at each
/// endpoint (Theory/Text/Parser/Proof.hs:28-36), so a stored chain goal
/// whose endpoint index differs from the runtime one is an `M.member` miss.
#[test]
fn chain_goal_requires_the_node_index() {
    use crate::rule::{ConcIdx, PremIdx};
    let chain = |i: u64, j: u64| {
        Goal::Chain(
            (LVar::new("i", LSort::Node, i), ConcIdx(0)),
            (LVar::new("j", LSort::Node, j), PremIdx(2)),
        )
    };
    let goal = chain(3, 5);
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    assert_eq!(match_goal(&goal, &sys).expect("should match"), goal);
    // The same root names with the indices dropped name a different goal.
    assert!(match_goal(&chain(0, 0), &sys).is_none());
}

/// Split matcher — exact id match on `Goal::Split(SplitId(n))`.
#[test]
fn match_split_goal_by_id() {
    use crate::constraint::constraints::SplitId;
    let goal_a = Goal::Split(SplitId(7));
    let goal_b = Goal::Split(SplitId(3));
    let mut sys = System::empty();
    sys.goals_mut().push((goal_a.clone(), Default::default()));
    sys.goals_mut().push((goal_b.clone(), Default::default()));
    assert_eq!(
        match_goal(&Goal::Split(SplitId(3)), &sys).expect("should match"),
        goal_b
    );
    assert_eq!(
        match_goal(&Goal::Split(SplitId(7)), &sys).expect("should match"),
        goal_a
    );
    assert!(match_goal(&Goal::Split(SplitId(99)), &sys).is_none());
}

/// Subterm matcher — the two terms are compared as `LNTerm`s, and a stored
/// goal that names neither open goal misses even when only one is open.
#[test]
fn subterm_goal_has_no_unique_fallback() {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let v = |n: &str, idx: u64| -> tamarin_term::lterm::LNTerm {
        Term::Lit(Lit::Var(LVar::new(n, LSort::Msg, idx)))
    };
    let goal = |small: &str, big: &str, idx: u64| Goal::Subterm((v(small, idx), v(big, idx)));
    let mut sys = System::empty();
    sys.goals_mut()
        .push((goal("x", "y", 99), Default::default()));
    assert_eq!(
        match_goal(&goal("x", "y", 99), &sys).expect("should match"),
        goal("x", "y", 99)
    );
    // The sole open Subterm goal is not a fallback: a stored goal naming
    // other terms, or the same names at another index, misses.
    assert!(match_goal(&goal("p", "q", 99), &sys).is_none());
    assert!(match_goal(&goal("x", "y", 0), &sys).is_none());
}

/// A node-sorted `VarSpec`, as `Parser::nodevar` builds it.
fn node_vs(name: &str) -> tamarin_parser::ast::VarSpec {
    tamarin_parser::ast::VarSpec {
        name: name.into(),
        idx: 0,
        sort: tamarin_term::lterm::LSort::Node,
        typ: None,
    }
}

/// `last(#<name>)` as one alternative of a disjunction goal.
fn last_alt(name: &str) -> crate::guarded::Guarded {
    use crate::guarded::{BVar, GAtom, GTerm, Guarded};
    Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Free(node_vs(name)))))
}

fn disj(alts: Vec<crate::guarded::Guarded>) -> Goal {
    Goal::Disj(crate::constraint::constraints::Disj::new(alts))
}

/// A disjunction goal binds the alternative list it names, not one of the
/// same length: HS compares the parsed `Disj [LNGuarded]` with `M.member`
/// (ProofMethod.hs:253-258).
#[test]
fn disj_goal_is_structural() {
    // The two open goals share their alternative count and every
    // alternative's shape; only one atom differs.  This is Yubikey
    // `slightly_weaker_invariant` at `/non_empty_trace/case_1`, where the
    // two IH-body disjunctions differ in `last(#t1)` vs `last(#t2)`.
    let first = disj(vec![last_alt("t1"), last_alt("a")]);
    let second = disj(vec![last_alt("t2"), last_alt("a")]);
    let mut sys = System::empty();
    sys.goals_mut().push((first.clone(), Default::default()));
    sys.goals_mut().push((second.clone(), Default::default()));
    assert_eq!(match_goal(&second, &sys).expect("should match"), second);
    assert_eq!(match_goal(&first, &sys).expect("should match"), first);
    assert!(match_goal(&disj(vec![last_alt("t3"), last_alt("a")]), &sys).is_none());
}

#[test]
fn disj_goal_rejects_a_different_alt_count() {
    let two = disj(vec![last_alt("a"), last_alt("b")]);
    let mut sys = System::empty();
    sys.goals_mut().push((two, Default::default()));
    assert!(match_goal(&disj(vec![last_alt("a")]), &sys).is_none());
    assert!(match_goal(
        &disj(vec![last_alt("a"), last_alt("b"), last_alt("c")]),
        &sys
    )
    .is_none());
}

/// The alternatives of a stored disjunction carry the sort of every free
/// leaf, so a disjunct that names the leaf at another sort is an `M.member`
/// miss.
#[test]
fn disj_goal_of_another_sort_misses() {
    use crate::guarded::{BVar, GAtom, GTerm, Guarded};
    use tamarin_parser::ast::VarSpec;
    let leaf = |sort: LSort| {
        GTerm::Var(BVar::Free(VarSpec {
            name: "x".into(),
            idx: 0,
            sort,
            typ: None,
        }))
    };
    let alt = |sort: LSort| Guarded::Atom(GAtom::Eq(leaf(sort), leaf(sort)));
    let live = disj(vec![alt(LSort::Msg)]);
    let mut sys = System::empty();
    sys.goals_mut().push((live.clone(), Default::default()));
    assert_eq!(
        match_goal(&disj(vec![alt(LSort::Msg)]), &sys).expect("should match"),
        live
    );
    assert!(match_goal(&disj(vec![alt(LSort::Fresh)]), &sys).is_none());
}

/// An AC chain of a runtime disjunct can be folded either way round
/// (guarded.rs `canonicalize_ac_in_guarded`), so `goal_matches` re-folds
/// both sides before comparing.
#[test]
fn disj_goal_matches_modulo_ac_fold() {
    use crate::guarded::{BVar, GAtom, GTerm, Guarded};
    use crate::guarded_types::ga;
    use tamarin_parser::ast::{BinOp, VarSpec};
    let leaf = |n: &str| {
        GTerm::Var(BVar::Free(VarSpec {
            name: n.into(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        }))
    };
    let un = |l: GTerm, r: GTerm| GTerm::BinOp(BinOp::Union, ga(l), ga(r));
    // `(a ++ b) ++ c` and `a ++ (b ++ c)` are the same HS `fAppAC` term.
    let left = un(un(leaf("a"), leaf("b")), leaf("c"));
    let right = un(leaf("a"), un(leaf("b"), leaf("c")));
    let alt = |t: GTerm| Guarded::Atom(GAtom::Eq(t, leaf("z")));
    let live = disj(vec![alt(right)]);
    let mut sys = System::empty();
    sys.goals_mut().push((live.clone(), Default::default()));
    let stored = disj(vec![alt(left)]);
    assert_ne!(stored, live, "the two foldings differ structurally");
    assert_eq!(match_goal(&stored, &sys).expect("should match"), live);
}

/// HS check-and-extend, `mergeMapsWith` rightOnly branch
/// (Theory/Proof.hs:463): a stored-skeleton case that the
/// re-executed method does NOT produce is mapped through
/// `noSystemPrf` over the WHOLE subtree → every node `Nothing` →
/// `/* unannotated */`.  `parsed_to_unannotated` must therefore set
/// `annotated == false` on EVERY node of the converted subtree, not
/// just the root.
#[test]
fn parsed_to_unannotated_marks_whole_subtree() {
    // Skeleton:  simplify → case "a" (by sorry), case "b" (by sorry)
    let leaf = |m| ProofTree {
        method: m,
        cases: Vec::new(),
    };
    let skel = ProofTree {
        method: ProofMethod::Simplify,
        cases: vec![
            ("a".to_string(), leaf(ProofMethod::Sorry(None))),
            ("b".to_string(), leaf(ProofMethod::Sorry(None))),
        ],
    };
    let node = parsed_to_unannotated(&skel, System::empty());
    assert!(!node.annotated, "root must be unannotated");
    assert_eq!(node.children.len(), 2);
    for (name, child) in &node.children {
        assert!(!child.annotated, "child `{name}` must be unannotated");
        assert!(matches!(child.method, ProofMethod::Sorry(None)));
    }
}
