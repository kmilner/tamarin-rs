// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::ast::{Atom, BinOp, FactAnnotation, Formula, GoalSpec, Term};
use crate::parser::{parse_goal_str, Parser};
use tamarin_term::lterm::LSort;

/// The three childless leaf forms that a printed proof can end in.  Each form
/// maps to its own [`ParsedMethod`].  No form carries a case block.
#[test]
fn leaf_forms() {
    for (src, method) in [
        ("by sorry", ParsedMethod::Sorry),
        ("by contradiction", ParsedMethod::Contradiction),
        ("SOLVED", ParsedMethod::SolvedLeaf),
    ] {
        let t = parse_proof_tree(src, &bare_parser()).unwrap_or_else(|e| panic!("{src}: {e}"));
        assert_eq!(t.method, method, "{src}");
        assert!(t.cases.is_empty(), "{src} must be childless: {:?}", t.cases);
    }
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
    let t = parse_proof_tree(src, &bare_parser()).expect("parse");
    assert_eq!(t.method, ParsedMethod::Induction);
    assert_eq!(t.cases.len(), 2);
    assert_eq!(t.cases[0].0, "empty_trace");
    assert_eq!(t.cases[0].1.method, ParsedMethod::Contradiction);
    assert_eq!(t.cases[1].0, "non_empty_trace");
    assert_eq!(t.cases[1].1.method, ParsedMethod::Sorry);
}

#[test]
fn identifier_stops_at_hyphen() {
    // HS `identifier` (Token.hs:214-230, see line 224 `identLetter = alphaNum
    // <|> oneOf "_"`) does NOT accept `-`, so `case foo-bar` names the case
    // `foo` and leaves `-bar` where `proofSkeleton` expects a proof method,
    // which no `proofMethod` alternative reads.  An underscore IS an
    // `identLetter`, so the same shape with `_` parses and names one case.
    assert!(parse_proof_tree("induction case foo-bar by sorry qed", &bare_parser()).is_err());
    let t = parse_proof_tree("induction case foo_bar by sorry qed", &bare_parser()).expect("parse");
    assert_eq!(t.method, ParsedMethod::Induction);
    assert_eq!(t.cases.len(), 1);
    assert_eq!(t.cases[0].0, "foo_bar");
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
    assert!(parse_proof_tree("simplify", &bare_parser()).is_err());
    assert!(parse_proof_tree("induction", &bare_parser()).is_err());
    // A method followed by an inline sub-proof DOES parse (the inline
    // single-child `""` subproof branch), and the leaf form is `by`.
    assert!(parse_proof_tree("simplify by sorry", &bare_parser()).is_ok());
    assert!(parse_proof_tree("by simplify", &bare_parser()).is_ok());
}

/// A parser with no theory symbols declared, standing in for the theory
/// parser a stored proof's goals are read inside.
fn bare_parser() -> Parser<'static> {
    Parser::new("", &[], false)
}

/// The same with `msig`'s symbols installed, as the theory parser holds the
/// theory's.
fn sig_parser(msig: &tamarin_term::maude_sig::MaudeSig) -> Parser<'static> {
    let mut p = Parser::new("", &[], false);
    p.seed_signature(msig);
    p
}

/// Every goal shape below goes through the sub-parser entry point the
/// `solve( ... )` arm uses, so the assertions pin the grammar itself rather
/// than the framing around it.
fn goal(src: &str) -> GoalSpec {
    parse_goal_str(src, &bare_parser()).unwrap_or_else(|e| panic!("{src}: {e}"))
}

/// HS `actionGoal` (Theory/Text/Parser/Proof.hs:49-52) keeps the whole
/// timepoint `LVar` in `ActionG i fa`, index included, so `#vk.6` must not
/// collapse to `#vk`.
#[test]
fn action_goal_keeps_the_timepoint_index() {
    match goal("!KU( ~AK ) @ #vk.6") {
        GoalSpec::Action(i, fact) => {
            assert_eq!(i.name, "vk");
            assert_eq!(i.idx, 6);
            assert_eq!(i.sort, LSort::Node);
            assert!(fact.persistent);
            assert_eq!(fact.name, "KU");
            assert_eq!(fact.args.len(), 1);
        }
        other => panic!("expected an action goal, got {other:?}"),
    }
    match goal("Foo( x ) @ #i") {
        GoalSpec::Action(i, fact) => {
            assert_eq!(i.name, "i");
            assert_eq!(i.idx, 0);
            assert_eq!(fact.name, "Foo");
        }
        other => panic!("expected an action goal, got {other:?}"),
    }
}

/// HS `premiseGoal` (Theory/Text/Parser/Proof.hs:54-57) reads `opRequires`
/// (`▶` plus a SUBSCRIPT natural, Token.hs:617-619) between the fact and the
/// node variable.
#[test]
fn premise_goal_reads_the_subscript_index() {
    match goal("Server( pid, sid, otc ) \u{25B6}\u{2080} #t1") {
        GoalSpec::Premise((i, v), fact) => {
            assert_eq!(i.name, "t1");
            assert_eq!(v, 0);
            assert_eq!(fact.name, "Server");
            assert_eq!(fact.args.len(), 3);
        }
        other => panic!("expected a premise goal, got {other:?}"),
    }
    match goal("!F_OutSessKeys( a, b ) \u{25B6}\u{2082} #i") {
        GoalSpec::Premise((_, v), fact) => {
            assert!(fact.persistent);
            assert_eq!(fact.name, "F_OutSessKeys");
            assert_eq!(v, 2);
        }
        other => panic!("expected a premise goal, got {other:?}"),
    }
}

/// `fact llit` is `fact'` (Theory/Text/Parser/Fact.hs:39-63), which reads the
/// `option [] $ list factAnnotation` suffix, so an annotated fact is a goal
/// like any other.
#[test]
fn premise_goal_accepts_an_annotated_fact() {
    match goal("!Pk( x )[no_precomp] \u{25B6}\u{2080} #vr.2") {
        GoalSpec::Premise((i, v), fact) => {
            assert_eq!(i.name, "vr");
            assert_eq!(i.idx, 2);
            assert_eq!(v, 0);
            assert_eq!(fact.name, "Pk");
            assert_eq!(fact.annotations, vec![FactAnnotation::NoSources]);
        }
        other => panic!("expected a premise goal, got {other:?}"),
    }
}

/// HS `chainGoal` (Theory/Text/Parser/Proof.hs:59) is `nodeConc <* opChain`
/// then `nodePrem`, and both endpoints are a full `nodevar` plus a natural
/// (Theory/Text/Parser/Proof.hs:28-36) — the node index is part of the goal.
#[test]
fn chain_goal_keeps_both_node_indices() {
    match goal("(#i.2, 0) ~~> (#j, 1)") {
        GoalSpec::Chain((src, conc), (tgt, prem)) => {
            assert_eq!(src.name, "i");
            assert_eq!(src.idx, 2);
            assert_eq!(conc, 0);
            assert_eq!(tgt.name, "j");
            assert_eq!(tgt.idx, 0);
            assert_eq!(prem, 1);
        }
        other => panic!("expected a chain goal, got {other:?}"),
    }
}

/// HS `eqSplitGoal` (Theory/Text/Parser/Proof.hs:70-72).  Id 0 is the first
/// id the equation store mints.
#[test]
fn split_goal_reads_the_split_id() {
    for id in [3i64, 0, 42] {
        match goal(&format!("splitEqs({id})")) {
            GoalSpec::Split(n) => assert_eq!(n, id),
            other => panic!("expected a split goal for {id}, got {other:?}"),
        }
    }
}

/// HS `stSplitGoal` (Theory/Text/Parser/Proof.hs:63-68) accepts both
/// spellings of `opSubterm` (Token.hs:574-576).
#[test]
fn subterm_goal_accepts_both_spellings() {
    for src in ["x \u{228F} h(x)", "x << h(x)"] {
        match goal(src) {
            GoalSpec::Subterm(small, big) => {
                assert!(matches!(&small, Term::Var(v) if v.name == "x"), "{src}");
                assert!(
                    matches!(&big, Term::App(n, a) if n == "h" && a.len() == 1),
                    "{src}"
                );
            }
            other => panic!("expected a subterm goal for {src}, got {other:?}"),
        }
    }
}

/// A user-declared `[AC]` symbol is written INFIX, and `acterm`
/// (Theory/Text/Parser/Term.hs:165-174) reads it only when the symbol is in
/// the signature the sub-parser inherits.
#[test]
fn goal_reads_a_user_ac_argument_infix() {
    let mut msig = tamarin_term::maude_sig::pair_maude_sig();
    msig.st_ac_fun_syms
        .insert(tamarin_term::function_symbols::AcFctSym::new(
            b"add".to_vec(),
            tamarin_term::function_symbols::Privacy::Public,
            tamarin_term::function_symbols::Constructability::Constructor,
            tamarin_term::function_symbols::NdcState::NotNdc,
        ));
    let g = parse_goal_str("F( (z add h(y)) ) @ #i", &sig_parser(&msig)).expect("parse");
    match g {
        GoalSpec::Action(_, fact) => match &fact.args[..] {
            [Term::BinOp(BinOp::AcFct(op), l, r)] => {
                assert_eq!(*op, "add");
                assert!(matches!(&**l, Term::Var(v) if v.name == "z"));
                assert!(matches!(&**r, Term::App(n, _) if n == "h"));
            }
            other => panic!("expected one infix AC argument, got {other:?}"),
        },
        other => panic!("expected an action goal, got {other:?}"),
    }
    // Without the symbol in the signature the infix spelling is not a term.
    assert!(parse_goal_str("F( (z add h(y)) ) @ #i", &bare_parser()).is_err());
}

/// `diff(a, b)` is a term only when the theory enables it, so the goal
/// sub-parser carries the parent's `diff` bit.
#[test]
fn goal_diff_argument_follows_the_diff_bit() {
    let g = parse_goal_str("F( diff(a, b) ) @ #i", &Parser::new("", &[], true)).expect("parse");
    match g {
        GoalSpec::Action(_, fact) => {
            assert!(matches!(&fact.args[..], [Term::Diff(_, _)]));
        }
        other => panic!("expected an action goal, got {other:?}"),
    }
    assert!(parse_goal_str("F( diff(a, b) ) @ #i", &bare_parser()).is_err());
}

/// HS reads the goal as `parens goal` (Theory/Text/Parser/Proof.hs:80), so
/// the whole text between the parentheses is the goal.
#[test]
fn goal_rejects_trailing_text() {
    assert!(parse_goal_str("Foo( x ) @ #i and then some", &bare_parser()).is_err());
    assert!(parse_goal_str("splitEqs(3) splitEqs(4)", &bare_parser()).is_err());
}

/// HS `nodevar` (Token.hs:443-448) is `sortedLVar [LSortNode]` or a bare
/// `indexedIdentifier`; a `$`/`~`/`%` sigil names a different sort.
#[test]
fn nodevar_rejects_a_non_node_sigil() {
    assert!(parse_goal_str("Foo( x ) @ $i", &bare_parser()).is_err());
    assert!(parse_goal_str("Foo( x ) @ ~i", &bare_parser()).is_err());
    // The two spellings HS does accept.
    for src in ["Foo( x ) @ #i", "Foo( x ) @ i", "Foo( x ) @ i:node"] {
        match goal(src) {
            GoalSpec::Action(i, _) => {
                assert_eq!(i.name, "i", "{src}");
                assert_eq!(i.sort, LSort::Node, "{src}");
            }
            other => panic!("expected an action goal for {src}, got {other:?}"),
        }
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
    let t = parse_proof_tree(src, &bare_parser()).expect("parse");
    assert!(matches!(t.method, ParsedMethod::SolveGoal(_)));
    assert_eq!(t.cases.len(), 2);
    assert_eq!(t.cases[0].0, "case_1");
    assert_eq!(t.cases[0].1.cases.len(), 2);
    assert_eq!(t.cases[0].1.cases[0].0, "case_a");
    assert_eq!(t.cases[0].1.cases[1].0, "case_b");
    assert_eq!(t.cases[1].0, "case_2");
}

/// HS reads the goal of a `solve( ... )` step with `parens goal`
/// (Theory/Text/Parser/Proof.hs:80), so text no alternative of `goal`
/// accepts fails the whole skeleton parse.
#[test]
fn unparseable_goal_fails_the_tree_parse() {
    assert!(parse_proof_tree("solve( garbage_no_marker ) by sorry", &bare_parser()).is_err());
}

/// HS `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) is an `asum` of seven
/// keyword alternatives with no catch-all, so an unknown token fails.
#[test]
fn unknown_method_token_fails_the_tree_parse() {
    assert!(parse_proof_tree("rule-equivalence by sorry", &bare_parser()).is_err());
    assert!(parse_proof_tree("by ATTACK", &bare_parser()).is_err());
}

/// HS `disjSplitGoal` (Theory/Text/Parser/Proof.hs:61) is
/// `sepBy1 guardedFormula (symbol "∥")`, so each alternative is a whole
/// formula and the goal keeps them all.
#[test]
fn solve_disj_two_alts() {
    let src = "solve( (last(#t1)) \u{2225} (#t1 < #t2) ) by sorry";
    let t = parse_proof_tree(src, &bare_parser()).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj(alts)) => {
            assert_eq!(alts.len(), 2);
            assert!(matches!(alts[0], Formula::Atom(Atom::Last(_))));
            assert!(matches!(alts[1], Formula::Atom(Atom::Less(_, _))));
        }
        other => panic!("expected a disjunction goal, got {:?}", other),
    }
}

/// `sepBy1` accepts a single alternative.  The solver mints a `DisjG` goal
/// only from a case split with two or more disjuncts, so no example file
/// stores one; this is the only coverage of that language.
#[test]
fn solve_disj_one_alt() {
    let t = parse_proof_tree("solve( (last(#t1)) ) by sorry", &bare_parser()).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj(alts)) => {
            assert_eq!(alts.len(), 1);
            assert!(matches!(alts[0], Formula::Atom(Atom::Last(_))));
        }
        other => panic!("expected a disjunction goal, got {:?}", other),
    }
}

/// Yubikey `slightly_weaker_invariant`'s first `solve(...)`: a `∀` alt with
/// seven binders and an `∃` alt with five.
#[test]
fn solve_disj_quantified_alts() {
    let src = "solve( (\u{2200} pid otc1 tc1 otc2 tc2 #t1 #t2. \
                          (last(#t1)) \u{2228} (last(#t2))) \u{2225} \
                          (\u{2203} #t1 #t2 a b c. (last(#t1))) ) by sorry";
    let t = parse_proof_tree(src, &bare_parser()).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj(alts)) => {
            assert_eq!(alts.len(), 2);
            match (&alts[0], &alts[1]) {
                (Formula::Forall(vs, _), Formula::Exists(ws, _)) => {
                    assert_eq!(vs.len(), 7);
                    assert_eq!(ws.len(), 5);
                }
                other => panic!("expected a ∀ alt then an ∃ alt, got {other:?}"),
            }
        }
        other => panic!("expected a disjunction goal, got {:?}", other),
    }
}

/// The inner `solve(...)` of Yubikey `slightly_weaker_invariant` has five
/// alternatives, one of them a conjunction.
#[test]
fn solve_disj_five_alts() {
    let src = "solve( (last(#t2)) \u{2225} (last(#t1)) \u{2225} \
                          ((#t1 < #t2) \u{2227} (last(#t3))) \u{2225} \
                          (#t2 < #t1) \u{2225} (#t1 = #t2) ) by sorry";
    let t = parse_proof_tree(src, &bare_parser()).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Disj(alts)) => {
            assert_eq!(alts.len(), 5);
            assert!(matches!(alts[0], Formula::Atom(Atom::Last(_))));
            assert!(matches!(alts[1], Formula::Atom(Atom::Last(_))));
            assert!(matches!(alts[2], Formula::And(_, _)));
            assert!(matches!(alts[3], Formula::Atom(Atom::Less(_, _))));
            assert!(matches!(alts[4], Formula::Atom(Atom::Eq(_, _))));
        }
        other => panic!("expected a disjunction goal, got {:?}", other),
    }
}

/// A public name may hold a bracket: HS `singleQuotedString`
/// (Token.hs:452-453) reads `many1 (noneOf "'\n")`, and `prettyGoal` prints
/// the name back with the bracket inside the quotes.  Framing the text of a
/// `solve( ... )` step therefore has to step over a quoted name instead of
/// counting its brackets, or the goal is cut short and the whole skeleton
/// fails to parse.
#[test]
fn solve_goal_with_bracket_in_pub_name() {
    let t = parse_proof_tree("solve( A( 'a)b' ) @ #i ) by sorry", &bare_parser()).expect("parse");
    match &t.method {
        ParsedMethod::SolveGoal(GoalSpec::Action(v, fact)) => {
            assert_eq!(v.name, "i");
            assert_eq!(fact.name, "A");
            assert_eq!(fact.args, vec![Term::PubLit("a)b".to_string())]);
        }
        other => panic!("expected an action goal, got {other:?}"),
    }
    assert_eq!(t.cases[0].1.method, ParsedMethod::Sorry);
}
