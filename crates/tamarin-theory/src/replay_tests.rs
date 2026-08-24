// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::constraint::system::System;
use tamarin_parser::ast::{Fact as PFact, ParsedMethod, ParsedProofTree};
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
    let skel = ParsedProofTree {
        method: ParsedMethod::Sorry,
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
    let skel = ParsedProofTree {
        method: ParsedMethod::Contradiction,
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

// Every stored goal below is a `GoalSpec` the goal grammar would produce, so
// `match_goal` converts it through `elaborate::goal_from_parsed` and looks
// the result up by structural equality — HS's `M.member`
// (ProofMethod.hs:253-258).

/// A timepoint variable of a stored goal, as [`Parser::nodevar`] builds it.
fn node(name: &str, idx: u64) -> tamarin_parser::ast::VarSpec {
    tamarin_parser::ast::VarSpec {
        name: name.into(),
        idx,
        sort: LSort::Node,
        typ: None,
    }
}

/// A stored goal's fact, as `Parser::fact` builds it.
fn pfact(persistent: bool, name: &str, args: Vec<tamarin_parser::ast::Term>) -> PFact {
    PFact {
        persistent,
        name: name.into(),
        args,
        annotations: Vec::new(),
    }
}

/// Match an Action goal whose fact takes no arguments.
#[test]
fn match_action_goal_by_name_arity() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let goal = Goal::Action(i, Fact::new(tag, Vec::new()));
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    let spec = GoalSpec::Action(node("t", 0), pfact(false, "Setup", Vec::new()));
    assert_eq!(
        match_goal(&spec, &sys, &pair_maude_sig()).expect("should match"),
        goal
    );
}

/// match_goal returns None when no goal matches the fact name.
#[test]
fn no_match_returns_none() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let goal = Goal::Action(i, Fact::new(tag, Vec::new()));
    let mut sys = System::empty();
    sys.goals_mut().push((goal, Default::default()));
    let spec = GoalSpec::Action(node("t", 0), pfact(false, "WrongName", Vec::new()));
    assert!(match_goal(&spec, &sys, &pair_maude_sig()).is_none());
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
    use tamarin_parser::ast::Term as PTerm;
    let tag = FactTag::Proto(Multiplicity::Linear, "Step", 1);
    let arg = |n: &str| {
        vec![tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(LVar::new(n, LSort::Msg, 0)),
        )]
    };
    let g1 = Goal::Action(LVar::new("t1", LSort::Node, 5), Fact::new(tag, arg("x")));
    let g2 = Goal::Action(LVar::new("t2", LSort::Node, 7), Fact::new(tag, arg("y")));
    let mut sys = System::empty();
    sys.goals_mut().push((g1.clone(), Default::default()));
    sys.goals_mut().push((g2.clone(), Default::default()));
    let spec = |tp: &str, idx: u64, arg: &str| {
        GoalSpec::Action(
            node(tp, idx),
            pfact(
                false,
                "Step",
                vec![PTerm::Var(tamarin_parser::ast::VarSpec {
                    name: arg.into(),
                    idx: 0,
                    sort: LSort::Msg,
                    typ: None,
                })],
            ),
        )
    };
    assert_eq!(
        match_goal(&spec("t2", 7, "y"), &sys, &pair_maude_sig()).expect("should match"),
        g2
    );
    assert_eq!(
        match_goal(&spec("t1", 5, "x"), &sys, &pair_maude_sig()).expect("should match"),
        g1
    );
    // A drifted index (stored `#t2.9`, runtime `#t2.7`) is an `M.member`
    // miss in HS.
    assert!(
        match_goal(&spec("t2", 9, "y"), &sys, &pair_maude_sig()).is_none(),
        "drifted timepoint idx must miss like HS `M.member`"
    );
    // So is a drifted argument.
    assert!(match_goal(&spec("t2", 7, "x"), &sys, &pair_maude_sig()).is_none());
}

/// Two same-(name, arity, prem idx) Premise goals at different node
/// timepoints.
#[test]
fn match_premise_disambiguates_by_time_var_root() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::PremIdx;
    let tag = FactTag::Proto(Multiplicity::Linear, "Inp", 0);
    let g1 = Goal::Premise(
        (LVar::new("u", LSort::Node, 0), PremIdx(0)),
        Fact::new(tag, Vec::new()),
    );
    let g2 = Goal::Premise(
        (LVar::new("v", LSort::Node, 0), PremIdx(0)),
        Fact::new(tag, Vec::new()),
    );
    let mut sys = System::empty();
    sys.goals_mut().push((g1, Default::default()));
    sys.goals_mut().push((g2.clone(), Default::default()));
    let spec = GoalSpec::Premise((node("v", 0), 0), pfact(false, "Inp", Vec::new()));
    assert_eq!(
        match_goal(&spec, &sys, &pair_maude_sig()).expect("should match"),
        g2
    );
}

/// Chain matcher — two Chain goals at different (src, tgt) pairs.
#[test]
fn match_chain_goal_by_var_and_idx() {
    use crate::rule::{ConcIdx, PremIdx};
    let i = LVar::new("i", LSort::Node, 0);
    let j = LVar::new("j", LSort::Node, 0);
    let k = LVar::new("k", LSort::Node, 0);
    let g_ij = Goal::Chain((i, ConcIdx(0)), (j, PremIdx(2)));
    let g_jk = Goal::Chain((j, ConcIdx(1)), (k, PremIdx(0)));
    let mut sys = System::empty();
    sys.goals_mut().push((g_ij.clone(), Default::default()));
    sys.goals_mut().push((g_jk.clone(), Default::default()));
    let spec = |a: &str, c: u64, b: &str, p: u64| GoalSpec::Chain((node(a, 0), c), (node(b, 0), p));
    assert_eq!(
        match_goal(&spec("j", 1, "k", 0), &sys, &pair_maude_sig()).expect("should match"),
        g_jk
    );
    assert_eq!(
        match_goal(&spec("i", 0, "j", 2), &sys, &pair_maude_sig()).expect("should match"),
        g_ij
    );
    // Wrong conclusion index — no match.
    assert!(match_goal(&spec("i", 9, "j", 2), &sys, &pair_maude_sig()).is_none());
}

/// HS's `ChainG NodeConc NodePrem` carries a full `nodevar` at each
/// endpoint (Theory/Text/Parser/Proof.hs:28-36), so a stored chain goal
/// whose endpoint index differs from the runtime one is an `M.member` miss.
#[test]
fn chain_goal_requires_the_node_index() {
    use crate::rule::{ConcIdx, PremIdx};
    let goal = Goal::Chain(
        (LVar::new("i", LSort::Node, 3), ConcIdx(0)),
        (LVar::new("j", LSort::Node, 5), PremIdx(2)),
    );
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    let exact = GoalSpec::Chain((node("i", 3), 0), (node("j", 5), 2));
    assert_eq!(
        match_goal(&exact, &sys, &pair_maude_sig()).expect("should match"),
        goal
    );
    // The same root names with the indices dropped name a different goal.
    let root_only = GoalSpec::Chain((node("i", 0), 0), (node("j", 0), 2));
    assert!(match_goal(&root_only, &sys, &pair_maude_sig()).is_none());
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
        match_goal(&GoalSpec::Split(3), &sys, &pair_maude_sig()).expect("should match"),
        goal_b
    );
    assert_eq!(
        match_goal(&GoalSpec::Split(7), &sys, &pair_maude_sig()).expect("should match"),
        goal_a
    );
    assert!(match_goal(&GoalSpec::Split(99), &sys, &pair_maude_sig()).is_none());
}

/// Subterm matcher — the two terms are compared as `LNTerm`s, and a stored
/// goal that names neither open goal misses even when only one is open.
#[test]
fn subterm_goal_has_no_unique_fallback() {
    use tamarin_parser::ast::Term as PTerm;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let v = |n: &str, idx: u64| -> tamarin_term::lterm::LNTerm {
        Term::Lit(Lit::Var(LVar::new(n, LSort::Msg, idx)))
    };
    let goal = Goal::Subterm((v("x", 99), v("y", 99)));
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    let spec = |small: &str, big: &str, idx: u64| {
        let mk = |n: &str| {
            PTerm::Var(tamarin_parser::ast::VarSpec {
                name: n.into(),
                idx,
                sort: LSort::Msg,
                typ: None,
            })
        };
        GoalSpec::Subterm(mk(small), mk(big))
    };
    assert_eq!(
        match_goal(&spec("x", "y", 99), &sys, &pair_maude_sig()).expect("should match"),
        goal
    );
    // The sole open Subterm goal is not a fallback: a stored goal naming
    // other terms, or the same names at another index, misses.
    assert!(match_goal(&spec("p", "q", 99), &sys, &pair_maude_sig()).is_none());
    assert!(match_goal(&spec("x", "y", 0), &sys, &pair_maude_sig()).is_none());
}

/// Disj matcher — two open Disj goals of different alt counts; the
/// matcher picks by alt-count + per-alt shape signature.
///
/// HS reference: HS `disjSplitGoal` (Theory/Text/Parser/Proof.hs:61) parses to
/// `DisjG (Disj [Guarded])` and matches the runtime Goal::Disj by
/// structural equality (ProofMethod.hs:252-273, see line 258).  The RS shape
/// signature must uniquely pick the disjunction whose alt-count
/// matches the skeleton.
#[test]
fn match_disj_goal_by_alt_count() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{BVar, GAtom, Guarded};
    let mk_vs = |n: &str| tamarin_parser::ast::VarSpec {
        name: n.into(),
        idx: 0,
        sort: tamarin_term::lterm::LSort::Node,
        typ: None,
    };
    // Two non-quant alts.
    let two = Goal::Disj(Disj::new(vec![
        Guarded::Atom(GAtom::Last(crate::guarded::GTerm::Var(BVar::Free(mk_vs(
            "a",
        ))))),
        Guarded::Atom(GAtom::Last(crate::guarded::GTerm::Var(BVar::Free(mk_vs(
            "b",
        ))))),
    ]));
    // Three non-quant alts.
    let three = Goal::Disj(Disj::new(vec![
        Guarded::Atom(GAtom::Last(crate::guarded::GTerm::Var(BVar::Free(mk_vs(
            "c",
        ))))),
        Guarded::Atom(GAtom::Last(crate::guarded::GTerm::Var(BVar::Free(mk_vs(
            "d",
        ))))),
        Guarded::Atom(GAtom::Last(crate::guarded::GTerm::Var(BVar::Free(mk_vs(
            "e",
        ))))),
    ]));
    let mut sys = System::empty();
    sys.goals_mut().push((two.clone(), Default::default()));
    sys.goals_mut().push((three.clone(), Default::default()));
    // Spec with 3 NonQuant alts must pick the 3-alt goal.
    let spec3 = GoalSpec::Disj {
        alts: vec![DisjAlt::NonQuant, DisjAlt::NonQuant, DisjAlt::NonQuant],
        alt_texts: vec![String::new(), String::new(), String::new()],
    };
    assert_eq!(
        match_goal(&spec3, &sys, &pair_maude_sig()).expect("should match"),
        three
    );
    // Spec with 2 NonQuant alts must pick the 2-alt goal.
    let spec2 = GoalSpec::Disj {
        alts: vec![DisjAlt::NonQuant, DisjAlt::NonQuant],
        alt_texts: vec![String::new(), String::new()],
    };
    assert_eq!(
        match_goal(&spec2, &sys, &pair_maude_sig()).expect("should match"),
        two
    );
}

/// `normalize_disj_alt_text_for_match` is a hand-written mirror of the
/// skeleton parser's `normalize_disj_alt_text` (tamarin-parser
/// proof_tree.rs).  Both functions strip every whitespace character and
/// every `#`.
///
/// The two copies are private to their own crates, and the dependency runs
/// from parser to theory only.  A test cannot compare them directly.  This
/// test and tamarin-parser's `proof_tree_tests::solve_disj_two_alts` /
/// `solve_disj_five_alts` together guard against drift on the Yubikey
/// `slightly_weaker_invariant` replay path.  Those two parser tests check
/// the `alt_texts` that the parser emits and stores.  The inputs below are
/// the alt texts of those two tests, with the outer parens that the parser
/// drops already removed.  The expected outputs below are exactly the
/// strings that those two tests assert the parser stores.
#[test]
fn normalize_disj_alt_text_for_match_strips_whitespace_and_hash() {
    assert_eq!(normalize_disj_alt_text_for_match(" last(#t1) "), "last(t1)");
    assert_eq!(normalize_disj_alt_text_for_match("#t1 < #t2"), "t1<t2");
    // A nested alt keeps its inner parens.  The newlines and the indent that
    // come from line wrapping strip like any other whitespace.
    assert_eq!(
        normalize_disj_alt_text_for_match("(#t1 < #t2)\n   \u{2227} (last(#t3))"),
        "(t1<t2)\u{2227}(last(t3))"
    );
}

/// Disj matcher.  The system holds two open Disj goals.  They share an alt
/// count and a per-alt shape signature.  The shape filter therefore keeps
/// both of them, and source order alone would bind the first.  `match_goal`
/// renders each candidate's alts with `pretty_disj_alt` under
/// `normalize_disj_alt_text_for_match`.  It scores them against the
/// skeleton's stored `alt_texts`.  The best score wins over source order.
///
/// HS reference: HS keeps the parsed `Guarded`'s concrete LVar identities and
/// matches structurally (ProofMethod.hs:252-273, see line 258).  HS therefore
/// never needs the tie-break.  RS's shape signature is coarser, and it
/// recovers the distinction from the stored text.  This is the Yubikey
/// `slightly_weaker_invariant` situation.  There, two IH-body disjs share the
/// NonQuant×5 shape and differ only in their alt texts.
#[test]
fn match_disj_goal_prefers_alt_text_score_over_source_order() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{BVar, GAtom, GTerm, Guarded};
    let mk_vs = |n: &str| tamarin_parser::ast::VarSpec {
        name: n.into(),
        idx: 0,
        sort: tamarin_term::lterm::LSort::Node,
        typ: None,
    };
    let last = |n: &str| Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Free(mk_vs(n)))));
    // The two goals have the same alt count and the same NonQuant×2
    // signature.  Only the variable names differ.
    let first = Goal::Disj(Disj::new(vec![last("a"), last("b")]));
    let second = Goal::Disj(Disj::new(vec![last("c"), last("d")]));
    let mut sys = System::empty();
    sys.goals_mut().push((first.clone(), Default::default()));
    sys.goals_mut().push((second.clone(), Default::default()));

    // The texts that a skeleton stores for a given candidate.
    let stored_texts = |g: &Goal| -> Vec<String> {
        let Goal::Disj(d) = g else {
            panic!("expected a Disj goal");
        };
        d.0.iter()
            .map(|a| normalize_disj_alt_text_for_match(&pretty_disj_alt(a)))
            .collect()
    };
    let want = stored_texts(&second);
    // Preconditions for this test.  The texts must not be empty.  An
    // `alt_texts` that is empty everywhere skips the scoring branch
    // completely.  The texts must also tell the two candidates apart.  If
    // they do not, both candidates score alike and source order decides.
    assert!(
        want.iter().all(|s| !s.is_empty()),
        "rendered alt texts must be non-empty, got {want:?}"
    );
    assert_ne!(
        want,
        stored_texts(&first),
        "the two candidates must render differently"
    );

    let spec = GoalSpec::Disj {
        alts: vec![DisjAlt::NonQuant, DisjAlt::NonQuant],
        alt_texts: want,
    };
    assert_eq!(
        match_goal(&spec, &sys, &pair_maude_sig()).expect("should match"),
        second,
        "alt-text score must beat source order"
    );
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
    let leaf = |m| ParsedProofTree {
        method: m,
        cases: Vec::new(),
    };
    let skel = ParsedProofTree {
        method: ParsedMethod::Simplify,
        cases: vec![
            ("a".to_string(), leaf(ParsedMethod::Sorry)),
            ("b".to_string(), leaf(ParsedMethod::Sorry)),
        ],
    };
    let node = parsed_to_unannotated(&skel, System::empty(), &pair_maude_sig());
    assert!(!node.annotated, "root must be unannotated");
    assert_eq!(node.children.len(), 2);
    for (name, child) in &node.children {
        assert!(!child.annotated, "child `{name}` must be unannotated");
        assert!(matches!(child.method, ProofMethod::Sorry(None)));
    }
}
