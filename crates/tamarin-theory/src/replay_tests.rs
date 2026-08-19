use super::*;
use crate::constraint::system::System;
use tamarin_parser::ast::{Fact as PFact, ParsedMethod, ParsedProofTree};
use tamarin_parser::DUMMY_LOCATION;
use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::pair_maude_sig;

fn maude() -> Option<MaudeHandle> {
    let path = std::env::var("MAUDE_PATH").ok().or_else(|| {
        for c in ["/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() {
                return Some(c.to_string());
            }
        }
        None
    })?;
    MaudeHandle::start(&path, pair_maude_sig()).ok()
}

/// `canonicalise_term_text` must normalise away the wrap-induced
/// whitespace that a STORED proof's pretty-printer inserts directly
/// inside `<…>` / `(…)` delimiters when a term overflows the ribbon.
/// Regression for the trace-existence `exists_trace` replay bug: the
/// skeleton `solve( !KU(hmac(<KSQ, $USR, senc(<…>, …)>, …)) )` term
/// wraps as `senc(< … CD_j.1 >, …)` (note `< `/` >`), while the
/// runtime renders `senc(<…CD_j.1>, …)` (no inner space).  If these
/// don't canonicalise equal, term-disambiguation in `match_goal`
/// fails and the time-var fallback mis-picks the smallest-idx `#vk`
/// knowledge goal (`!KU($USR)`) instead of the intended hmac goal.
#[test]
fn canonicalise_strips_wrap_spaces_inside_brackets() {
    // Wrapped (skeleton) form after the whitespace-collapse pass:
    let skel = "hmac(<KSQ, $USR, senc(< ~CDSK_j_USR_O, ~MDSK_j_USR_O, KSQ, $USR, keystatus, CD_j.1 >, ~UK_i_USR_O) >, ~MDSK_j_USR_O)";
    // Runtime (un-wrapped) form:
    let rt = "hmac(<KSQ, $USR, senc(<~CDSK_j_USR_O, ~MDSK_j_USR_O, KSQ, $USR, keystatus, CD_j.1>, ~UK_i_USR_O)>, ~MDSK_j_USR_O)";
    assert_eq!(canonicalise_term_text(skel), canonicalise_term_text(rt));
    // The canonical form must carry NO space adjacent to the inside
    // of a bracket/paren.
    let c = canonicalise_term_text(skel);
    assert!(!c.contains("< "), "no `< ` in {c}");
    assert!(!c.contains(" >"), "no ` >` in {c}");
    assert!(!c.contains("( "), "no `( ` in {c}");
    assert!(!c.contains(" )"), "no ` )` in {c}");
    // Multi-line input (raw skeleton text with newlines + indent)
    // canonicalises identically to the runtime form.
    let multiline = "hmac(<KSQ, \n   $USR, \n   senc(<\n     ~CDSK_j_USR_O, KSQ, $USR, keystatus, CD_j.1\n    >,\n    ~UK_i_USR_O)\n   >,\n   ~MDSK_j_USR_O)";
    let rt2 = "hmac(<KSQ, $USR, senc(<~CDSK_j_USR_O, KSQ, $USR, keystatus, CD_j.1>, ~UK_i_USR_O)>, ~MDSK_j_USR_O)";
    assert_eq!(
        canonicalise_term_text(multiline),
        canonicalise_term_text(rt2)
    );
    // Inter-token spaces (e.g. after commas) are PRESERVED so distinct
    // terms never collapse together.
    assert_eq!(canonicalise_term_text("<a, b>"), "<a, b>");
    assert_ne!(
        canonicalise_term_text("<a, b>"),
        canonicalise_term_text("<a, c>")
    );
}

/// A Sorry-only skeleton on an empty system should be a degenerate
/// replay → equivalent to running the auto-prover directly.
#[test]
fn sorry_leaf_runs_auto_prover() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let ctx = ProofContext::new(h, Vec::new());
    let sys = System::empty();
    // Skeleton = `by sorry`.
    let skel = ParsedProofTree {
        method: ParsedMethod::Sorry,
        cases: Vec::new(),
    };
    let _ = replace_sorry_prove(&ctx, sys, &skel, 50);
    // Just must terminate; status indeterminate on empty system.
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
/// On an empty system (no goals, no contradictions) the auto-prover
/// recognises the system as trivially Solved.  The key assertion
/// is `status != Contradictory` — the original Sorry-emit was
/// later replaced by the auto-prove fallback.
#[test]
fn contradiction_leaf_without_contradiction_falls_back_to_auto() {
    let h = match maude() {
        Some(m) => m,
        None => return,
    };
    let ctx = ProofContext::new(h, Vec::new());
    let mut sys = System::empty();
    // Force out of initial state so is_finished can run.
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
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

/// Match an Action goal by fact name + arity.  Uses an empty-args
/// fact for simplicity (matches by tag name + arity 0).
#[test]
fn match_action_goal_by_name_arity() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let fact = Fact::new(tag, Vec::new());
    let goal = Goal::Action(i, fact);
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    let spec = GoalSpec::Action {
        fact: PFact {
            persistent: false,
            name: "Setup".into(),
            args: Vec::new(),
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        time_var: "t".into(),
        time_idx: 0,
    };
    let matched = match_goal(&spec, &sys).expect("should match");
    assert!(matches!(matched, Goal::Action(_, _)));
}

/// match_goal returns None when no goal matches the fact name.
#[test]
fn no_match_returns_none() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i = LVar::new("t", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Setup", 0);
    let fact = Fact::new(tag, Vec::new());
    let goal = Goal::Action(i, fact);
    let mut sys = System::empty();
    sys.goals_mut().push((goal, Default::default()));
    let spec = GoalSpec::Action {
        fact: PFact {
            persistent: false,
            name: "WrongName".into(),
            args: Vec::new(),
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        time_var: "t".into(),
        time_idx: 0,
    };
    assert!(match_goal(&spec, &sys).is_none());
}

/// Variable-renaming-aware Action match: two same-fact-name Action
/// goals at different timepoints — the matcher must disambiguate by
/// the skeleton's FULL timepoint LVar (root name AND idx), mirroring
/// HS `M.member`.
///
/// HS reference: `ActionG i fa` carries the exact timepoint LVar `i`;
/// HS dispatches `SolveGoal goal -> guard (goal `M.member` sGoals)`
/// (ProofMethod.hs:348-459, see line 374) — the goal key is the full LVar, so the idx is
/// part of the match.  HS pretty-prints a timepoint as `#t2` when its
/// idx is 0 and `#t2.7` when its idx is 7 (`Show LVar`, LTerm.hs:526-533),
/// so a stored skeleton's `time_idx` always equals the LVar idx of the
/// goal it was generated from — the matcher requires that exact idx.
#[test]
fn match_action_disambiguates_by_time_var_root() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    let i1 = LVar::new("t1", LSort::Node, 5);
    let i2 = LVar::new("t2", LSort::Node, 7);
    let tag = FactTag::Proto(Multiplicity::Linear, "Step", 1);
    // Two goals with the same fact tag/arity but different
    // timepoints.
    let g1 = Goal::Action(
        i1,
        Fact::new(
            tag,
            vec![tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(LVar::new("x", LSort::Msg, 0)),
            )],
        ),
    );
    let g2 = Goal::Action(
        i2,
        Fact::new(
            tag,
            vec![tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(LVar::new("y", LSort::Msg, 0)),
            )],
        ),
    );
    let mut sys = System::empty();
    sys.goals_mut().push((g1.clone(), Default::default()));
    sys.goals_mut().push((g2.clone(), Default::default()));
    // Skeleton spec asking for the t2 goal: full LVar `#t2.7`.
    let spec = GoalSpec::Action {
        fact: PFact {
            persistent: false,
            name: "Step".into(),
            args: vec![tamarin_parser::ast::Term::Var(
                tamarin_parser::ast::VarSpec {
                    name: "y".into(),
                    idx: 0,
                    sort: tamarin_parser::ast::SortHint::Untagged,
                    typ: None,
                    location: DUMMY_LOCATION,
                },
            )],
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        time_var: "t2".into(),
        time_idx: 7,
    };
    let matched = match_goal(&spec, &sys).expect("should match");
    match matched {
        Goal::Action(i, _) => assert_eq!(
            i.name, "t2",
            "matcher must pick the goal whose timepoint LVar.name == time_var"
        ),
        other => panic!("expected Action, got {:?}", other),
    }
    // And with the t1 goal's full LVar `#t1.5` we get the other goal.
    let spec2 = GoalSpec::Action {
        fact: PFact {
            persistent: false,
            name: "Step".into(),
            args: vec![tamarin_parser::ast::Term::Var(
                tamarin_parser::ast::VarSpec {
                    name: "x".into(),
                    idx: 0,
                    sort: tamarin_parser::ast::SortHint::Untagged,
                    typ: None,
                    location: DUMMY_LOCATION,
                },
            )],
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        time_var: "t1".into(),
        time_idx: 5,
    };
    let matched2 = match_goal(&spec2, &sys).expect("should match");
    match matched2 {
        Goal::Action(i, _) => assert_eq!(i.name, "t1"),
        other => panic!("expected Action, got {:?}", other),
    }
    // A drifted idx (stored `#t2.9`, runtime `#t2.7`) is an `M.member`
    // miss in HS — the matcher must reject it (→ invalid step).
    let spec_drift = GoalSpec::Action {
        fact: PFact {
            persistent: false,
            name: "Step".into(),
            args: vec![tamarin_parser::ast::Term::Var(
                tamarin_parser::ast::VarSpec {
                    name: "y".into(),
                    idx: 0,
                    sort: tamarin_parser::ast::SortHint::Untagged,
                    typ: None,
                    location: DUMMY_LOCATION,
                },
            )],
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        time_var: "t2".into(),
        time_idx: 9,
    };
    assert!(
        match_goal(&spec_drift, &sys).is_none(),
        "drifted timepoint idx must miss like HS `M.member`"
    );
}

/// Variable-renaming-aware Premise match: two same-(name, arity,
/// prem_idx) Premise goals at different node timepoints.
#[test]
fn match_premise_disambiguates_by_time_var_root() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::PremIdx;
    let n1 = LVar::new("u", LSort::Node, 0);
    let n2 = LVar::new("v", LSort::Node, 0);
    let tag = FactTag::Proto(Multiplicity::Linear, "Inp", 0);
    let g1 = Goal::Premise((n1, PremIdx(0)), Fact::new(tag, Vec::new()));
    let g2 = Goal::Premise((n2, PremIdx(0)), Fact::new(tag, Vec::new()));
    let mut sys = System::empty();
    sys.goals_mut().push((g1, Default::default()));
    sys.goals_mut().push((g2, Default::default()));
    let spec = GoalSpec::Premise {
        fact: PFact {
            persistent: false,
            name: "Inp".into(),
            args: Vec::new(),
            annotations: Vec::new(),
            location: DUMMY_LOCATION,
        },
        prem_idx: 0,
        time_var: "v".into(),
        time_idx: 0,
    };
    let matched = match_goal(&spec, &sys).expect("should match");
    match matched {
        Goal::Premise((node, _), _) => assert_eq!(node.name, "v"),
        other => panic!("expected Premise, got {:?}", other),
    }
}

/// Chain matcher — synthetic system with two Chain goals at
/// different (src,tgt) pairs; the matcher picks by var+idx.
#[test]
fn match_chain_goal_by_var_and_idx() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{ConcIdx, PremIdx};
    let _ = (Fact::<u32>::new, FactTag::Ku, Multiplicity::Linear); // keep imports alive
    let i = LVar::new("i", LSort::Node, 3);
    let j = LVar::new("j", LSort::Node, 5);
    let k = LVar::new("k", LSort::Node, 7);
    let g_ij = Goal::Chain((i, ConcIdx(0)), (j, PremIdx(2)));
    let g_jk = Goal::Chain((j, ConcIdx(1)), (k, PremIdx(0)));
    let mut sys = System::empty();
    sys.goals_mut().push((g_ij.clone(), Default::default()));
    sys.goals_mut().push((g_jk.clone(), Default::default()));
    // Ask for (#j, 1) ~~> (#k, 0).
    let spec = GoalSpec::Chain {
        src_var: "j".into(),
        conc_idx: 1,
        tgt_var: "k".into(),
        prem_idx: 0,
    };
    let matched = match_goal(&spec, &sys).expect("should match");
    assert_eq!(matched, g_jk);
    // And the other side.
    let spec2 = GoalSpec::Chain {
        src_var: "i".into(),
        conc_idx: 0,
        tgt_var: "j".into(),
        prem_idx: 2,
    };
    assert_eq!(match_goal(&spec2, &sys).expect("should match"), g_ij);
    // Wrong idx — no match.
    let bad = GoalSpec::Chain {
        src_var: "i".into(),
        conc_idx: 9,
        tgt_var: "j".into(),
        prem_idx: 2,
    };
    assert!(match_goal(&bad, &sys).is_none());
}

/// Subterm matcher — open Subterm goals are matched by canonical
/// pretty-printed-text equality on both sides.
#[test]
fn match_subterm_goal_by_pretty_text() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    // small = x:msg, big = y:msg (two distinct vars).
    let small = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
    let big = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 0)));
    let goal = Goal::Subterm((small.clone(), big.clone()));
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    // Skeleton-parsed small_raw / big_raw must canonicalise to the
    // same text as `pretty_lnterm(small)` / `pretty_lnterm(big)`.
    use tamarin_term::pretty::pretty_lnterm;
    let small_s = pretty_lnterm(&small);
    let big_s = pretty_lnterm(&big);
    let spec = GoalSpec::Subterm {
        small_raw: small_s,
        big_raw: big_s,
    };
    let matched = match_goal(&spec, &sys).expect("should match");
    assert_eq!(matched, goal);
}

/// Subterm matcher fallback — when skeleton text differs from
/// runtime pretty (e.g. LVar idx renumbering) but only ONE open
/// Subterm goal exists, the unique-match fallback picks it.
#[test]
fn match_subterm_unique_fallback() {
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let small = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 99)));
    let big = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 99)));
    let goal = Goal::Subterm((small, big));
    let mut sys = System::empty();
    sys.goals_mut().push((goal.clone(), Default::default()));
    // Skeleton small/big text deliberately uses a name the runtime
    // doesn't have — text mismatch but unique-Subterm fallback
    // still picks the goal.
    let spec = GoalSpec::Subterm {
        small_raw: "skel_small".into(),
        big_raw: "skel_big".into(),
    };
    let matched = match_goal(&spec, &sys).expect("unique-fallback should match");
    assert_eq!(matched, goal);
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
    let spec = GoalSpec::Split { split_id: 3 };
    let matched = match_goal(&spec, &sys).expect("should match");
    assert_eq!(matched, goal_b);
    let spec2 = GoalSpec::Split { split_id: 7 };
    assert_eq!(match_goal(&spec2, &sys).expect("should match"), goal_a);
    // No id 99 in the system → None.
    let none = GoalSpec::Split { split_id: 99 };
    assert!(match_goal(&none, &sys).is_none());
}

/// Disj matcher — two open Disj goals of different alt counts; the
/// matcher picks by alt-count + per-alt shape signature.
///
/// HS reference: HS `disjSplitGoal` (Proof.hs:61) parses to
/// `DisjG (Disj [Guarded])` and matches the runtime Goal::Disj by
/// structural equality (ProofMethod.hs:348-459, see line 374).  The RS shape
/// signature must uniquely pick the disjunction whose alt-count
/// matches the skeleton.
#[test]
fn match_disj_goal_by_alt_count() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{BVar, GAtom, Guarded};
    let mk_vs = |n: &str| tamarin_parser::ast::VarSpec {
        name: n.into(),
        idx: 0,
        sort: tamarin_parser::ast::SortHint::Node,
        typ: None,
        location: DUMMY_LOCATION,
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
    assert_eq!(match_goal(&spec3, &sys).expect("should match"), three);
    // Spec with 2 NonQuant alts must pick the 2-alt goal.
    let spec2 = GoalSpec::Disj {
        alts: vec![DisjAlt::NonQuant, DisjAlt::NonQuant],
        alt_texts: vec![String::new(), String::new()],
    };
    assert_eq!(match_goal(&spec2, &sys).expect("should match"), two);
}

/// HS check-and-extend, `mergeMapsWith` rightOnly branch
/// (Proof.hs): a stored-skeleton case that the
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
    let node = parsed_to_unannotated(&skel, System::empty());
    assert!(!node.annotated, "root must be unannotated");
    assert_eq!(node.children.len(), 2);
    for (name, child) in &node.children {
        assert!(!child.annotated, "child `{name}` must be unannotated");
        assert!(matches!(child.method, ProofMethod::Sorry(None)));
    }
}
