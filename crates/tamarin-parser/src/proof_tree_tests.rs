// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;

/// The three childless leaf forms a printed proof can end in, each mapping
/// to its own [`ParsedMethod`] and carrying no case block.
#[test]
fn leaf_forms() {
    for (src, method) in [
        ("by sorry", ParsedMethod::Sorry),
        ("by contradiction", ParsedMethod::Contradiction),
        ("SOLVED", ParsedMethod::SolvedLeaf),
    ] {
        let t = parse_proof_tree(src).unwrap_or_else(|e| panic!("{src}: {e}"));
        assert_eq!(t.method, method, "{src}");
        assert!(t.cases.is_empty(), "{src} must be childless: {:?}", t.cases);
    }
}

#[test]
fn count_quant_vars_with_dotted_idx() {
    // Bound vars with idx>0 render as `name.idx` (HS LVar Show).
    // The `.idx` suffix must NOT terminate the count; only the
    // body-terminator `.` (followed by ws/EOF) ends the var list.
    assert_eq!(count_quant_vars("x y #i.1 #j."), 4);
    assert_eq!(count_quant_vars("t.5 x."), 2);
    // Trailing dotted var before the body terminator.
    assert_eq!(count_quant_vars("#t #t.1."), 2);
    // No dotted suffixes.
    assert_eq!(count_quant_vars("a b c."), 3);
}

#[test]
fn induction_with_case_block() {
    let src = "
            induction
            case empty_trace
            by contradiction
            next
            case non_empty_trace
            by sorry
            qed
        ";
    let t = parse_proof_tree(src).expect("parse");
    assert_eq!(t.method, ParsedMethod::Induction);
    assert_eq!(t.cases.len(), 2);
    assert_eq!(t.cases[0].0, "empty_trace");
    assert_eq!(t.cases[0].1.method, ParsedMethod::Contradiction);
    assert_eq!(t.cases[1].0, "non_empty_trace");
    assert_eq!(t.cases[1].1.method, ParsedMethod::Sorry);
}

#[test]
fn identifier_stops_at_hyphen() {
    // HS `identifier` (Token.hs:214-230, see line 224 `identLetter = alphaNum <|> oneOf
    // "_"`) does NOT accept `-`, so a case name like `foo-bar` is
    // tokenised as the identifier `foo`; the `-bar` is not part of the
    // case name.  This locks in HS-faithful identifier termination.
    let t = parse_proof_tree("induction case foo-bar by sorry qed").expect("parse");
    assert_eq!(t.method, ParsedMethod::Induction);
    assert_eq!(t.cases.len(), 1);
    assert_eq!(t.cases[0].0, "foo");
}

#[test]
fn bare_inter_method_without_child_is_err() {
    // HS `interProof` (Theory/Text/Parser/Proof.hs:109-113) has no
    // childless-leaf branch:
    // a method must be followed by either a `case`-block (`next`/`qed`)
    // or a recursive `proofSkeleton`.  A bare `simplify` with nothing
    // after it is a parse error in the v1.13.0 prover ("unexpected ...,
    // expecting case/qed/SOLVED/by/sorry/simplify/solve/...").  We must
    // mirror that failure (the caller downgrades `Err` to `tree: None`
    // and replays via the auto-prover), so it must NOT parse to a leaf.
    assert!(parse_proof_tree("simplify").is_err());
    assert!(parse_proof_tree("induction").is_err());
    // A method followed by an inline sub-proof DOES parse (the inline
    // single-child `""` subproof branch), and the leaf form is `by`.
    assert!(parse_proof_tree("simplify by sorry").is_ok());
    assert!(parse_proof_tree("by simplify").is_ok());
}

#[test]
fn solve_action_goal() {
    let src = "solve( Foo( x ) @ #i )";
    let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(
            GoalSpec::Action {
                fact,
                time_var,
                time_idx,
            },
            _,
        ) => {
            assert_eq!(fact.name, "Foo");
            assert_eq!(fact.args.len(), 1);
            assert_eq!(time_var, "i");
            assert_eq!(*time_idx, 0);
        }
        other => panic!("expected Action solve goal, got {:?}", other),
    }
    assert_eq!(t.cases.len(), 1);
    assert_eq!(t.cases[0].0, "");
    assert_eq!(t.cases[0].1.method, ParsedMethod::Sorry);
}

#[test]
fn solve_action_goal_captures_timepoint_idx() {
    // HS's `ActionG i fa` carries the full timepoint LVar incl. idx;
    // dropping `.6` would re-render the head as `#vk` (regression) and
    // break exact goal matching.
    let src = "solve( !KU( ~AK ) @ #vk.6 )";
    let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(
            GoalSpec::Action {
                time_var, time_idx, ..
            },
            _,
        ) => {
            assert_eq!(time_var, "vk");
            assert_eq!(*time_idx, 6);
        }
        other => panic!("expected Action solve goal, got {:?}", other),
    }
}

#[test]
fn solve_premise_goal_subscript() {
    // ▶₀ (subscript 0)
    let src = "solve( Server( pid, sid, otc ) \u{25B6}\u{2080} #t1 )";
    let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(
            GoalSpec::Premise {
                fact,
                prem_idx,
                time_var,
                time_idx,
            },
            _,
        ) => {
            assert_eq!(fact.name, "Server");
            assert_eq!(*prem_idx, 0);
            assert_eq!(time_var, "t1");
            assert_eq!(*time_idx, 0);
        }
        other => panic!("expected Premise solve goal, got {:?}", other),
    }
}

#[test]
fn solve_persistent_premise() {
    // !F_Fact(...) ▶₂ #i
    let src = "solve( !F_OutSessKeys( a, b ) \u{25B6}\u{2082} #i )";
    let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Premise { fact, prem_idx, .. }, _) => {
            assert!(fact.persistent);
            assert_eq!(fact.name, "F_OutSessKeys");
            assert_eq!(*prem_idx, 2);
        }
        other => panic!("expected persistent premise, got {:?}", other),
    }
}

#[test]
fn nested_case_block() {
    let src = "
            solve( Foo( a ) @ #i )
              case case_1
              solve( Bar( b ) @ #j )
                case case_a
                by sorry
              next
                case case_b
                by contradiction
              qed
            next
              case case_2
              by sorry
            qed
        ";
    let t = parse_proof_tree(src).expect("parse");
    assert!(matches!(t.method, ParsedMethod::SolveGoal(_, _)));
    assert_eq!(t.cases.len(), 2);
    assert_eq!(t.cases[0].0, "case_1");
    assert_eq!(t.cases[0].1.cases.len(), 2);
    assert_eq!(t.cases[0].1.cases[0].0, "case_a");
    assert_eq!(t.cases[0].1.cases[1].0, "case_b");
    assert_eq!(t.cases[1].0, "case_2");
}

#[test]
fn raw_goalspec_fallback() {
    // Unknown gibberish goal-text — should fall back to
    // GoalSpec::Raw.  All recognised forms (Action, Premise, Disj,
    // Chain, Subterm, Split) need specific structural markers.
    let src = "solve( garbage_no_marker ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Raw(_), _) => {}
        other => panic!("expected Raw goal-spec, got {:?}", other),
    }
}

#[test]
fn solve_chain_goal() {
    // HS `chainGoal` (Theory/Text/Parser/Proof.hs:39-72, see line 59)
    // pretty-print:
    // `(#i, 0) ~~> (#j, 2)`  (NodeConc ~~> NodePrem).
    let src = "solve( (#i, 0) ~~> (#j, 2) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(
            GoalSpec::Chain {
                src_var,
                conc_idx,
                tgt_var,
                prem_idx,
            },
            _,
        ) => {
            assert_eq!(src_var, "i");
            assert_eq!(*conc_idx, 0);
            assert_eq!(tgt_var, "j");
            assert_eq!(*prem_idx, 2);
        }
        other => panic!("expected Chain goal-spec, got {:?}", other),
    }
}

#[test]
fn solve_chain_goal_with_freshen_suffix() {
    // HS sometimes emits a freshen suffix like `#i.2` on the
    // pretty-printed nodevar; the parser must strip it.
    let src = "solve( (#i.5, 1) ~~> (#j.7, 0) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(
            GoalSpec::Chain {
                src_var,
                conc_idx,
                tgt_var,
                prem_idx,
            },
            _,
        ) => {
            // Freshen suffix stripped from the var ROOT.
            assert_eq!(src_var, "i");
            assert_eq!(*conc_idx, 1);
            assert_eq!(tgt_var, "j");
            assert_eq!(*prem_idx, 0);
        }
        other => panic!("expected Chain goal-spec, got {:?}", other),
    }
}

#[test]
fn solve_subterm_goal() {
    // HS `stSplitGoal` (Theory/Text/Parser/Proof.hs:63-66) pretty-print:
    // `<term> ⊏ <term>` (U+228F).
    let src = "solve( foo(a, b) \u{228F} bar(c) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Subterm { small_raw, big_raw }, _) => {
            assert_eq!(small_raw, "foo(a, b)");
            assert_eq!(big_raw, "bar(c)");
        }
        other => panic!("expected Subterm goal-spec, got {:?}", other),
    }
}

#[test]
fn solve_split_goal() {
    // HS `eqSplitGoal` (Theory/Text/Parser/Proof.hs:70-72) pretty-print:
    // `splitEqs(N)`, including the boundary id 0 (the first one minted by
    // EquationStore).
    for id in [42i64, 0] {
        let src = format!("solve( splitEqs({id}) ) by sorry");
        let t = parse_proof_tree(&src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Split { split_id }, _) => {
                assert_eq!(*split_id, id, "{src}");
            }
            other => panic!("expected Split goal-spec for {src}, got {:?}", other),
        }
    }
}

/// `solve( (last(#t1)) ∥ (#t1 < #t2) )` — two non-quant alts.  The captured
/// `alt_texts` are the tie-breaker `tamarin_theory::replay::match_goal` uses
/// when several `sys.goals` disjs share an alt SHAPE, so they must come out
/// under the normalisation the runtime side re-applies in
/// `normalize_disj_alt_text_for_match`: outer parens dropped, then every
/// whitespace and `#` character stripped.
#[test]
fn solve_disj_two_alts() {
    let src = "solve( (last(#t1)) \u{2225} (#t1 < #t2) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts }, _) => {
            assert_eq!(alts.len(), 2);
            assert!(matches!(alts[0], DisjAlt::NonQuant));
            assert!(matches!(alts[1], DisjAlt::NonQuant));
            assert_eq!(*alt_texts, vec!["last(t1)", "t1<t2"]);
        }
        other => panic!("expected Disj goal-spec, got {:?}", other),
    }
}

#[test]
fn solve_disj_quantified_alts() {
    // Yubikey slightly_weaker_invariant first solve(...) — 2 alts:
    // ∀-quantified with 7 vars, ∃-quantified with 5 vars.
    let src = "solve( (\u{2200} pid otc1 tc1 otc2 tc2 #t1 #t2. \
                          (last(#t1)) \u{2228} (last(#t2))) \u{2225} \
                          (\u{2203} #t1 #t2 a b c. (last(#t1))) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts: _ }, _) => {
            assert_eq!(alts.len(), 2);
            assert_eq!(alts[0], DisjAlt::All { n_vars: 7 });
            assert_eq!(alts[1], DisjAlt::Ex { n_vars: 5 });
        }
        other => panic!("expected Disj goal-spec, got {:?}", other),
    }
}

/// Yubikey `slightly_weaker_invariant` inner solve — 5 non-quant alts.  This
/// is the goal whose binding-A and binding-B instantiations share the 5-alt
/// NonQuant shape, so only `alt_texts` (here: alt[0] `last(t2)` vs the other
/// disj's `last(t1)`) tells them apart; a nested alt keeps its INNER parens.
#[test]
fn solve_disj_five_alts() {
    let src = "solve( (last(#t2)) \u{2225} (last(#t1)) \u{2225} \
                          ((#t1 < #t2) \u{2227} (last(#t3))) \u{2225} \
                          (#t2 < #t1) \u{2225} (#t1 = #t2) ) by sorry";
    let t = parse_proof_tree(src).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj { alts, alt_texts }, _) => {
            assert_eq!(alts.len(), 5);
            for a in alts.iter() {
                assert!(matches!(a, DisjAlt::NonQuant));
            }
            assert_eq!(
                *alt_texts,
                vec![
                    "last(t2)",
                    "last(t1)",
                    "(t1<t2)\u{2227}(last(t3))",
                    "t2<t1",
                    "t1=t2",
                ]
            );
        }
        other => panic!("expected Disj goal-spec, got {:?}", other),
    }
}
