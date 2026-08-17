// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::constraint::system::System;
use crate::test_maude::maude_path;

#[test]
fn single_goal_returned() {
    let mut sys = System::empty();
    assert!(
        open_goals(&sys).is_empty(),
        "precondition: nothing is open before a goal is added"
    );
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
    let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    let g = Goal::Action(v, f);
    sys.add_goal(g.clone());
    let goals = open_goals(&sys);
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].goal, g, "the goal is carried through verbatim");
    assert_eq!(goals[0].usefulness, Usefulness::Useful);
}

#[test]
fn solved_goal_filtered() {
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
    let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
    sys.add_goal(Goal::Action(v, f));
    assert_eq!(
        open_goals(&sys).len(),
        1,
        "precondition: open before solving"
    );
    sys.goals_mut()[0].1.solved = true;
    assert!(open_goals(&sys).is_empty());
}

/// `is_open_in_sys` treats the empty disjunction as closed while it is still
/// unsolved.  This mirrors HS `DisjG (Disj []) -> False` (Goals.hs:89).  The
/// contradictions pass disposes of the empty disjunction, not goal solving.
/// The `solved` flag stays false here, so the default arm `_ -> not solved`
/// would report this goal open.  Only the empty-Disj arm keeps it out of
/// `open_goals`.  The control case with a one-item Disj shows that the arm
/// is specific to the empty disjunction.  The arm is not a filter for every
/// Disj.
#[test]
fn empty_disj_goal_is_never_open() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{gtrue, Guarded};

    let mut sys = System::empty();
    sys.add_goal(Goal::Disj(Disj::<Guarded>::new(Vec::new())));
    assert!(!sys.goals[0].1.solved);
    assert!(open_goals(&sys).is_empty());

    let mut sys = System::empty();
    sys.add_goal(Goal::Disj(Disj::new(vec![gtrue()])));
    assert!(!sys.goals[0].1.solved);
    assert_eq!(open_goals(&sys).len(), 1);
}

/// `dispatch_solve_goal` marks the goal solved before it delegates.  This
/// mirrors HS `solveGoal` (Goals.hs:201-213).  The solver that it delegates
/// to can rewrite the terms of the goal through `solveFactEqs` or
/// `substSystem`.  A mark after the solve would then miss the substituted
/// key and leave the goal open.
#[test]
fn dispatch_solve_goal_marks_solved_then_routes() {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::reduction::{GoalCases, Reduction};
    use tamarin_term::maude_sig::pair_maude_sig;

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());
    let mut sys = System::empty();
    // Nothing can satisfy an empty disjunction.  The Disj solver that this
    // call must route to therefore answers `Contradictory`.
    let d = crate::constraint::constraints::Disj::<crate::guarded::Guarded>::new(Vec::new());
    let g = Goal::Disj(d);
    sys.add_goal(g.clone());
    let mut r = Reduction::new(&ctx, sys);
    let out = dispatch_solve_goal(&mut r, &g);
    assert!(matches!(out, GoalCases::Contradictory));
    assert!(
        r.sys.goals.iter().any(|(gg, st)| gg == &g && st.solved),
        "the goal must be marked solved even on the contradictory route"
    );
}

// =========================================================================
// Haskell-faithfulness invariants for Goal-Ord.
//
// Haskell `data Goal` (Constraints.hs:159-172) declares variants in
// this exact order, and derives `Ord`:
//
//     data Goal = ActionG _ _
//               | ChainG _ _
//               | PremiseG _ _
//               | SplitG _
//               | DisjG _
//               | SubtermG _
//               deriving( ..., Ord, ... )
//
// So the constructor tag order is:
//     Action < Chain < Premise < Split < Disj < Subterm
//
// Rust's `Goal` (constraints.rs) derives no `Ord`; `goal_cmp`
// (goals.rs) hand-codes the tag function, and it is the comparator
// every goal sort in the solver goes through (pretty_system,
// rename_precise, sources, reduction).  Any divergence between it and
// the HS declaration order silently sorts goals differently than
// Haskell.
// =========================================================================

/// Pin Haskell's Goal-Ord tag order: Action < Chain < Premise < Split
/// < Disj < Subterm.
///
/// This is the exact order from Constraints.hs:159-172.  `goal_cmp`
/// orders every goal list the solver sorts, so this tag ranking decides
/// which goal each step picks — and hence the proof shape.
#[test]
fn goal_cmp_tag_order_matches_haskell_declaration() {
    use crate::constraint::constraints::{Disj, NodeId, SplitId};
    use crate::fact::{FactTag, LNFact, Multiplicity};
    use crate::rule::{ConcIdx, PremIdx};
    use std::cmp::Ordering;
    use tamarin_term::lterm::{LSort, LVar};

    // Build one minimal instance of each Goal variant.
    let v: LVar = LVar::new("k", LSort::Msg, 0);
    let n: NodeId = LVar::new("i", LSort::Node, 0);
    let f: LNFact = LNFact::new(FactTag::Proto(Multiplicity::Linear, "F", 0), vec![]);

    let action: Goal = Goal::Action(v, f.clone());
    let chain: Goal = Goal::Chain((n, ConcIdx(0)), (n, PremIdx(0)));
    let premise: Goal = Goal::Premise((n, PremIdx(0)), f.clone());
    let split: Goal = Goal::Split(SplitId(0));
    let disj: Goal = Goal::Disj(Disj::<crate::guarded::Guarded>::new(vec![]));
    // Use plain msg vars for the Subterm pair.
    let sub: Goal = Goal::Subterm((
        tamarin_term::builtin::msg_var("a", 0),
        tamarin_term::builtin::msg_var("b", 0),
    ));

    // The order from Constraints.hs:159-172 (deriving Ord):
    //   ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG
    //
    // **THIS IS THE CONTRACT.**  If Rust's `goal_cmp` differs, every
    // goal sort that routes through it orders differently from
    // Haskell, causing proof-step divergences silently.
    let order = [&action, &chain, &premise, &split, &disj, &sub];
    let names = ["Action", "Chain", "Premise", "Split", "Disj", "Subterm"];
    for i in 0..order.len() {
        // Every variant compares Equal with itself.  The short-circuit on
        // the tag must fall through to a payload comparison that agrees.
        assert_eq!(
            goal_cmp(order[i], order[i]),
            Ordering::Equal,
            "{} must compare Equal with itself",
            names[i]
        );
        for j in (i + 1)..order.len() {
            assert_eq!(
                goal_cmp(order[i], order[j]),
                Ordering::Less,
                "Haskell Goal-Ord requires {} < {} \
                     (Constraints.hs:159-172 declaration order).  \
                     goal_cmp put them in the wrong order — this WILL \
                     cause silent proof divergence.",
                names[i],
                names[j]
            );
            assert_eq!(
                goal_cmp(order[j], order[i]),
                Ordering::Greater,
                "Haskell Goal-Ord requires {} > {}",
                names[j],
                names[i]
            );
        }
    }
}

/// Pin that `Goal`'s variant declaration order in Rust matches Haskell's
/// data-decl order.  The test above pins `goal_cmp`'s hand-written tag
/// function; this pins the enum that function shadows, so reordering one
/// without the other fails here.  `Goal` derives no `Ord` and stable Rust
/// cannot reflect over variants, so read the declaration out of the
/// source — `discriminant` values are opaque and stay pairwise distinct
/// under ANY reordering, which is why they cannot pin an order.
#[test]
fn rust_goal_enum_variant_order_matches_haskell() {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/constraint/constraints.rs"
    ))
    .expect("constraints.rs is readable");
    let body = src
        .split_once("pub enum Goal {")
        .expect("Goal enum declaration present")
        .1
        .split_once("\n}")
        .expect("Goal enum declaration closes")
        .0;
    let variants: Vec<&str> = body
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with("//") && !l.starts_with('#'))
        .map(|l| l.split(['(', '{', ',', ' ']).next().unwrap_or(l))
        .collect();
    assert_eq!(
        variants,
        ["Action", "Chain", "Premise", "Split", "Disj", "Subterm"],
        "Goal's variants must be declared in HS's `data Goal` order \
         (Constraints.hs:159-172); `goal_cmp` ranks tags by that order"
    );
}

// -- Tactic ranking tests -------------------------------------------------

/// HS `pg =~ regex` is an UNANCHORED PCRE search (matches anywhere).
#[test]
fn regex_unanchored_and_pcre_features() {
    // Unanchored substring search.
    assert!(regex_is_match("In_S", "solve( In_S( 'H1' ) )"));
    assert!(!regex_is_match("In_S", "solve( In_A( 'H1' ) )"));
    // Literal escaped paren `\(` (PCRE).
    assert!(regex_is_match(r"In_A\( 'S'", "In_A( 'S', <'codes'>)"));
    assert!(!regex_is_match(r"In_A\( 'S'", "In_A( 'BB', x)"));
    // Quoted-literal pattern from the corpus tactics.
    assert!(regex_is_match("'proofV'", "BB_C( <'proofV', x> )"));
    // PCRE negative lookahead — fancy-regex feature the `regex` crate
    // can't compile.  `!KU( <not one|true> )`.
    let pat = r"!KU\( (?!(one|true))[a-zA-Z0-9.]+ \)";
    assert!(regex_is_match(pat, "!KU( foo )"));
    assert!(!regex_is_match(pat, "!KU( one )"));
    // PCRE lookbehind.
    let lb = r"(?<!'g'\^)~[a-zA-Z.0-9]*";
    assert!(regex_is_match(lb, "x ~n1"));
    assert!(!regex_is_match(lb, "'g'^~n1"));
    // A regex that fails to compile yields `false`, never panics.
    assert!(!regex_is_match("(", "anything"));
}

/// PCRE (`regex-pcre-builtin`, the HS engine) has NO `\<` / `\>`
/// word-boundary assertions — they are the escaped LITERAL chars `<`/`>`.
/// `fancy-regex` would otherwise treat them as word boundaries, which
/// diverges from HS (wisec21 5G_handover `secret_k_asme` tactic prio
/// `.*RcvS.*~K_ASME\>.*`).  Behaviour pinned against the real HS library:
///   `"a\\>" =~ "a>"  == True`,  `"a\\>" =~ "a b"/"ab" == False`.
#[test]
fn regex_backslash_lt_gt_are_pcre_literals() {
    // `\>` == literal '>'.
    assert!(regex_is_match(r"a\>", "a>"));
    assert!(!regex_is_match(r"a\>", "a b")); // NOT a word boundary
    assert!(!regex_is_match(r"a\>", "ab"));
    // `\<` == literal '<'.
    assert!(regex_is_match(r"\<a", "<a"));
    assert!(!regex_is_match(r"\<a", " a"));
    // The exact corpus prio: must NOT match a `~K_ASME,` (comma) goal.
    let prio = r".*RcvS.*~K_ASME\>.*";
    assert!(!regex_is_match(
        prio,
        "RcvS( ~cid_N26.1, <'fr_req', ~K_ASME, ~eNB_UE_S1AP_ID.1>)"
    ));
    // …but DOES match a goal where '>' literally follows ~K_ASME.
    assert!(regex_is_match(prio, "RcvS( <'ho_required', x, ~K_ASME>)"));
    // `\b` is still the standard word boundary (unchanged).
    assert!(regex_is_match(r"a\b", "a b"));
    assert!(!regex_is_match(r"a\b", "ab"));
    // An escaped backslash before '>' is left intact: `\\>` = '\' then '>'.
    assert!(regex_is_match(r"a\\>", "a\\>"));
    assert!(!regex_is_match(r"a\\>", "a>"));
}

/// `apply_ranking_fn "smallest"` sorts by rendered length, stably;
/// "id"/unknown is identity.
#[test]
fn ranking_fn_smallest_and_id() {
    use crate::fact::ku_fact;
    use tamarin_term::lterm::fresh_term;
    let mk = |s: &str, seq: u64| {
        let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
        AnnotatedGoal::new(
            Goal::Action(v, ku_fact(fresh_term(s))),
            seq,
            Usefulness::Useful,
        )
    };
    // `~aaaa` renders longer than `~a`.
    let g_long = mk("aaaa", 0);
    let g_short = mk("a", 1);
    let out = apply_ranking_fn("smallest", vec![g_long.clone(), g_short.clone()]);
    assert_eq!(out[0].seq, 1, "shortest rendered goal first");
    assert_eq!(out[1].seq, 0);
    // id keeps input order.
    let out2 = apply_ranking_fn("id", vec![g_long.clone(), g_short.clone()]);
    assert_eq!(out2[0].seq, 0);
    assert_eq!(out2[1].seq, 1);
}

/// `it_ranking` result = rankedPrioGoals ++ nonRanked ++ rankedDeprioGoals,
/// with prio groups in ascending-block order and unmatched goals
/// preserved in presort order.
#[test]
fn it_ranking_prio_nonranked_deprio_order() {
    use crate::fact::ku_fact;
    use crate::tactic::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};
    use tamarin_term::lterm::fresh_term;

    let mk = |s: &str, seq: u64| {
        let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
        AnnotatedGoal::new(
            Goal::Action(v, ku_fact(fresh_term(s))),
            seq,
            Usefulness::Useful,
        )
    };
    // Goals render as `!KU( ~skS )`, `!KU( ~r )`, `!KU( ~x )`.
    let g_sks = mk("skS", 0);
    let g_r = mk("r", 1);
    let g_x = mk("x", 2);
    let ags = vec![g_sks.clone(), g_r.clone(), g_x.clone()];

    let prio = |pat: &str| PrioBlock {
        ranking: "id".to_string(),
        disjuncts: vec![format!("regex \"{}\"", pat)],
        selectors: vec![SelectorExpr::Leaf(SelectorLeaf {
            name: "regex".to_string(),
            params: vec![pat.to_string()],
        })],
    };
    // Fresh names render as `~'skS'` etc.  prio 0 matches ~'r',
    // prio 1 matches ~'skS'; ~'x' matches no prio. deprio matches ~'x'.
    let tactic = Tactic {
        name: "t".to_string(),
        presort: 'C',
        prios: vec![prio("~'r'"), prio("~'skS'")],
        deprios: vec![prio("~'x'")],
    };

    let sys = System::empty();
    let out = it_ranking(&tactic, ags, false, None, &sys).unwrap();
    let seqs: Vec<u64> = out.iter().map(|a| a.seq).collect();
    // rankedPrio = [~r (block0), ~skS (block1)]; nonRanked = []
    // (every goal matched a prio or deprio); rankedDeprio = [~x].
    assert_eq!(
        seqs,
        vec![1, 0, 2],
        "prio(~r) then prio(~skS) then deprio(~x); got {:?}",
        seqs
    );
}

/// A goal matching NO prio/deprio lands in `nonRanked`, between the
/// prio'd and deprio'd goals, in presort order.
#[test]
fn it_ranking_nonranked_preserved() {
    use crate::fact::ku_fact;
    use crate::tactic::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};
    use tamarin_term::lterm::fresh_term;
    let mk = |s: &str, seq: u64| {
        let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
        AnnotatedGoal::new(
            Goal::Action(v, ku_fact(fresh_term(s))),
            seq,
            Usefulness::Useful,
        )
    };
    // Put the prio-matching goal LAST in presort order so a passing
    // result genuinely proves reordering (not a no-op).
    let g_b = mk("b", 0); // no match → nonRanked
    let g_c = mk("c", 1); // no match → nonRanked
    let g_a = mk("a", 2); // matches prio → moves to front
    let prio = PrioBlock {
        ranking: "id".to_string(),
        disjuncts: vec!["regex \"~'a'\"".to_string()],
        selectors: vec![SelectorExpr::Leaf(SelectorLeaf {
            name: "regex".to_string(),
            params: vec!["~'a'".to_string()],
        })],
    };
    let tactic = Tactic {
        name: "t".to_string(),
        presort: 'C',
        prios: vec![prio],
        deprios: vec![],
    };
    let sys = System::empty();
    let out = it_ranking(&tactic, vec![g_b, g_c, g_a], false, None, &sys).unwrap();
    let seqs: Vec<u64> = out.iter().map(|a| a.seq).collect();
    // ~'a' (prio, seq 2) first, then nonRanked [~'b'=0, ~'c'=1] in
    // presort order.
    assert_eq!(seqs, vec![2, 0, 1]);
}

// -- moveNatToEnd / isNatSubtermSplit (ProofMethod.hs:1064-1066) ----------

/// `isNatSubtermSplit` (ProofMethod.hs:1048-1129, see line 1065) = `isNatSubterm st`
/// (SubtermStore.hs:112-113, see line 113): `(sort small == Nat || isMsgVar small) &&
/// sort big == Nat`.  Non-SubtermG goals are False.
#[test]
fn is_nat_subterm_split_matches_haskell() {
    use crate::constraint::constraints::SplitId;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;

    let nat = |n: &str| var_term(LVar::new(n, LSort::Nat, 0));
    let msg = |n: &str| tamarin_term::builtin::msg_var(n, 0);
    let fresh = |n: &str| tamarin_term::builtin::fresh_var(n, 0);

    // small Nat, big Nat -> true.
    assert!(is_nat_subterm_split(&Goal::Subterm((nat("a"), nat("b")))));
    // small MsgVar, big Nat -> true (isMsgVar small branch).
    assert!(is_nat_subterm_split(&Goal::Subterm((msg("a"), nat("b")))));
    // small Nat, big NOT Nat -> false (big must be Nat).
    assert!(!is_nat_subterm_split(&Goal::Subterm((
        nat("a"),
        fresh("b")
    ))));
    // small Fresh (not Nat, not MsgVar), big Nat -> false.
    assert!(!is_nat_subterm_split(&Goal::Subterm((
        fresh("a"),
        nat("b")
    ))));
    // Non-Subterm goal -> false.
    assert!(!is_nat_subterm_split(&Goal::Split(SplitId(0))));
}

// -- UsefulGoalNr ('c') derived Usefulness Ord (ProofMethod.hs:479-502, see line 484) ------

/// HS `UsefulGoalNrRanking -> sortOn (\(_, (nr, useless)) -> (useless,
/// nr))` sorts on the DERIVED `Ord Usefulness` (declaration order
/// Useful<LoopBreaker<ProbablyConstructible<CurrentlyDeducible,
/// AnnotatedGoals.hs:18-27), NOT `tagUsefulness` (which would collapse
/// LoopBreaker and ProbablyConstructible to the same key).  So a
/// LoopBreaker goal must rank BEFORE a ProbablyConstructible goal even
/// when its creation-nr is larger.
#[test]
fn useful_goal_nr_uses_derived_usefulness_ord() {
    use tamarin_term::lterm::{LSort, LVar};
    let mk = |seq: u64, u: Usefulness| {
        let v = LVar::new("k", LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        AnnotatedGoal::new(Goal::Action(v, f), seq, u)
    };
    // LoopBreaker with the LARGER nr, ProbablyConstructible with the
    // smaller nr.  HS Usefulness Ord (LoopBreaker < ProbablyConstructible)
    // must dominate the nr tiebreak.  The test drives the shared production
    // sorter `sort_useful_goal_nr`.  The `UsefulGoalNr` ranking arm and the
    // tactic presort use that same sorter.  The test does not repeat the
    // sort logic here.
    let lb = mk(5, Usefulness::LoopBreaker);
    let pc = mk(1, Usefulness::ProbablyConstructible);
    let mut ags = [pc.clone(), lb.clone()];
    sort_useful_goal_nr(&mut ags);
    // LoopBreaker (seq 5) ranks first despite the larger nr: HS
    // `Usefulness` Ord (LoopBreaker < ProbablyConstructible) dominates the
    // nr tiebreak, even though `tag_usefulness` collapses the two (below).
    assert_eq!(
        ags[0].seq, 5,
        "LoopBreaker must rank before ProbablyConstructible"
    );
    assert_eq!(ags[1].seq, 1);
    // With equal usefulness, the sorter still breaks ties by creation nr, in
    // ascending order.
    let mut same = [mk(9, Usefulness::Useful), mk(2, Usefulness::Useful)];
    sort_useful_goal_nr(&mut same);
    assert_eq!([same[0].seq, same[1].seq], [2, 9]);
    // And tag_usefulness genuinely WOULD collapse these two — proving the
    // distinction matters.
    assert_eq!(
        tag_usefulness(Usefulness::LoopBreaker),
        tag_usefulness(Usefulness::ProbablyConstructible)
    );
    // The derived Ord does NOT collapse them.
    assert!(Usefulness::LoopBreaker < Usefulness::ProbablyConstructible);
}

// -- goal_cmp Disj structural Ord (Constraints.hs derived Ord) -----------

/// HS `Disj a = Disj [a]` derives Ord = list Ord bottoming out at the
/// structural `Ord LNGuarded`, whose var leaves use `Ord LVar = (idx,
/// sort, name)`.  When two Disj goals differ at a leaf var of different
/// SORT (idx and name equal), HS LSort Ord (Pub<Fresh<Msg<Node<Nat)
/// decides.  This pins that the comparator orders by that structural HS
/// `Ord LSort` (Pub<Fresh), not by the `{:?}` sort-name string
/// (Fresh<Msg<Nat<Node<Pub).
#[test]
fn goal_cmp_disj_var_sort_uses_lsort_ord() {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{BVar, GAtom, GTerm, Guarded};
    use std::cmp::Ordering;
    use tamarin_parser::ast::{SortHint, VarSpec};

    // A single-atom Disj over `Last(v)` where v differs only by sort.
    let mk_disj = |sort: SortHint| -> Goal {
        let v = VarSpec {
            name: "x".to_string(),
            idx: 0,
            sort,
            typ: None,
        };
        let atom = GAtom::Last(GTerm::Var(BVar::Free(v)));
        Goal::Disj(Disj::new(vec![Guarded::Atom(atom)]))
    };
    let pub_disj = mk_disj(SortHint::Pub);
    let fresh_disj = mk_disj(SortHint::Fresh);
    // HS LSort Ord: Pub < Fresh.  The structural comparator must put the
    // Pub-var Disj first (by sort, not by Debug-string name order).
    assert_eq!(
        goal_cmp(&pub_disj, &fresh_disj),
        Ordering::Less,
        "HS LSort Ord requires Pub < Fresh in Disj structural compare"
    );
    assert_eq!(goal_cmp(&fresh_disj, &pub_disj), Ordering::Greater);
}
