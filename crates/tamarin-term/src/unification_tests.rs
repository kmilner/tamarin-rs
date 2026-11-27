// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::builtin::{fresh_var, msg_var, mult, pair, pk, pub_var, union};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::vterm::Lit;

fn lvar(t: &LNTerm) -> LVar {
    match t {
        Term::Lit(Lit::Var(v)) => *v,
        _ => panic!("expected a variable, got {t:?}"),
    }
}

/// `Ord LVar` is idx-first, then sort, then name (LTerm.hs: "An ord instance
/// that prefers the 'lvarIdx' over the 'lvarName'"), the opposite of a
/// derived name-first order.  `restrict`, `BTreeMap<LVar, _>` iteration and
/// the var-var orientation of the unify table below all ride on it.
#[test]
fn lvar_ord_is_idx_first_then_sort_then_name() {
    let v = |name, sort, idx| LVar::new(name, sort, idx);
    assert!(v("x", LSort::Msg, 1) < v("x", LSort::Msg, 5));
    assert!(v("z", LSort::Msg, 1) < v("a", LSort::Msg, 5));
    assert!(v("a", LSort::Msg, 3) < v("b", LSort::Msg, 3));
    assert!(v("a", LSort::Pub, 3) < v("a", LSort::Fresh, 3));
}

#[test]
fn lvar_ord_btreemap_iteration_is_idx_first() {
    let mut m = std::collections::BTreeMap::new();
    m.insert(LVar::new("z", LSort::Msg, 1), 'a');
    m.insert(LVar::new("a", LSort::Msg, 10), 'b');
    m.insert(LVar::new("m", LSort::Msg, 5), 'c');
    let keys_in_order: Vec<u64> = m.keys().map(|k| k.idx).collect();
    assert_eq!(keys_in_order, vec![1, 5, 10]);
}

/// The unify-factored table: HS `unifyLTermFactored` (Unification.hs) over
/// `unifyRaw`.  `None` is no unifier; `Some((subst, residuals))` is the
/// local non-AC substitution and the number of AC equations delayed for
/// Maude.
///
/// - var-var, same sort: `if vl < vr then elim vr l else elim vl r`, so the
///   larger var under idx-first `Ord LVar` is the key.
/// - var-var, cross sort: `sortGeqLTerm sortOf vl r -> elim vl r`, so the
///   broader var is the key; incomparable sorts (Pub, Fresh) fail.
/// - var-term: the var is the key; the occurs check fails.
/// - AC: only same-symbol AC on both sides is delayed (`tell`); any other AC
///   pairing falls through to `mzero`.
/// - chained: `elim` substitutes through the accumulator, so both vars of a
///   var-var link end bound to the later term.
///
/// The runner checks each row as given and again with the two sides of
/// every equation swapped: orientation comes from `Ord LVar` and sorts, never
/// from input order.
#[test]
fn every_unify_factored_row_holds_whichever_side_each_term_is_on() {
    type Expect = Option<(Vec<(LNTerm, LNTerm)>, usize)>;
    let (x, y) = (msg_var("x", 0), msg_var("y", 0));
    let blind = pair(msg_var("m", 28), msg_var("r", 28));
    let pair_ab = pair(msg_var("a", 10), msg_var("b", 20));
    let rows: Vec<(&str, Vec<(LNTerm, LNTerm)>, Expect)> = vec![
        (
            "same idx: name breaks the tie",
            vec![(x.clone(), y.clone())],
            Some((vec![(y.clone(), x.clone())], 0)),
        ),
        (
            "same sort: larger idx is the key",
            vec![(msg_var("t", 1), msg_var("e", 10))],
            Some((vec![(msg_var("e", 10), msg_var("t", 1))], 0)),
        ),
        (
            "Msg is broader than Fresh",
            vec![(msg_var("m", 5), fresh_var("k", 100))],
            Some((vec![(msg_var("m", 5), fresh_var("k", 100))], 0)),
        ),
        (
            "Msg is broader than Pub",
            vec![(msg_var("m", 5), pub_var("A", 100))],
            Some((vec![(msg_var("m", 5), pub_var("A", 100))], 0)),
        ),
        (
            "Pub and Fresh are incomparable",
            vec![(pub_var("A", 1), fresh_var("k", 2))],
            None,
        ),
        (
            "var against an application",
            vec![(msg_var("x", 5), pair_ab.clone())],
            Some((vec![(msg_var("x", 5), pair_ab)], 0)),
        ),
        (
            "constructor clash",
            vec![(pair(x.clone(), y.clone()), pk(msg_var("z", 0)))],
            None,
        ),
        (
            "occurs check",
            vec![(x.clone(), pair(x.clone(), y.clone()))],
            None,
        ),
        (
            "x = x binds nothing",
            vec![(x.clone(), x.clone())],
            Some((vec![], 0)),
        ),
        (
            "AC-free pair-pair",
            vec![(
                pair(msg_var("a", 1), msg_var("b", 2)),
                pair(msg_var("x", 10), msg_var("y", 20)),
            )],
            Some((
                vec![
                    (msg_var("x", 10), msg_var("a", 1)),
                    (msg_var("y", 20), msg_var("b", 2)),
                ],
                0,
            )),
        ),
        (
            "chained var-var then var-term",
            vec![
                (msg_var("t", 1), msg_var("m", 19)),
                (msg_var("m", 19), blind.clone()),
            ],
            Some((
                vec![(msg_var("t", 1), blind.clone()), (msg_var("m", 19), blind)],
                0,
            )),
        ),
        (
            "distinct AC symbols",
            vec![(
                mult(msg_var("a", 0), msg_var("b", 0)),
                union(msg_var("c", 0), msg_var("d", 0)),
            )],
            None,
        ),
        (
            "AC against NoEq",
            vec![(mult(msg_var("a", 0), msg_var("b", 0)), pk(x.clone()))],
            None,
        ),
        (
            "same AC symbol is delayed",
            vec![(
                mult(msg_var("a", 0), msg_var("b", 0)),
                mult(msg_var("c", 0), msg_var("d", 0)),
            )],
            Some((vec![], 1)),
        ),
    ];
    for (label, eqs, expect) in rows {
        let expect = expect.map(|(s, n)| {
            let s: Vec<(LVar, LNTerm)> = s.into_iter().map(|(k, v)| (lvar(&k), v)).collect();
            (s, n)
        });
        for swapped in [false, true] {
            let eqs = eqs
                .iter()
                .map(|(l, r)| match swapped {
                    false => Equal::new(l.clone(), r.clone()),
                    true => Equal::new(r.clone(), l.clone()),
                })
                .collect();
            let got = unify_lnterm_factored(eqs).map(|(s, res)| (s.to_list(), res.len()));
            assert_eq!(got, expect, "{label} (swapped: {swapped})");
        }
    }
}

/// The match-lterm table: HS `solveMatchLTerm` (Unification.hs) without the
/// Maude fallback.  `matchRaw` checks a variable pattern first, so an
/// AC-headed subject under a variable pattern binds natively; an AC pattern
/// facing a variable subject is `NoMatcher`; only same-symbol AC on both
/// sides needs Maude.  A pattern variable outside the bindable set is a
/// skolem constant (HS `skolemizeTerm`) that matches only itself.
#[test]
fn every_match_lterm_row_has_its_outcome() {
    enum Expect {
        Matched(Vec<(LNTerm, LNTerm)>),
        NoMatcher,
        NeedsAc,
    }
    fn any(_: &LVar) -> bool {
        true
    }
    fn only_y(v: &LVar) -> bool {
        v.name == "y"
    }
    let v = |n: &str| msg_var(n, 0);
    let ab = || mult(v("a"), v("b"));
    let rows: Vec<(&str, LNTerm, LNTerm, fn(&LVar) -> bool, Expect)> = vec![
        (
            "pattern vars bind positionally",
            pair(v("a"), v("b")),
            pair(v("x"), v("y")),
            any,
            Expect::Matched(vec![(v("x"), v("a")), (v("y"), v("b"))]),
        ),
        (
            "arity clash",
            pk(v("a")),
            pair(v("x"), v("y")),
            any,
            Expect::NoMatcher,
        ),
        (
            "AC subject under a var pattern",
            ab(),
            v("x"),
            any,
            Expect::Matched(vec![(v("x"), ab())]),
        ),
        (
            "AC pattern against a var subject",
            v("x"),
            ab(),
            any,
            Expect::NoMatcher,
        ),
        (
            "same AC symbol on both sides",
            ab(),
            mult(v("c"), v("d")),
            any,
            Expect::NeedsAc,
        ),
        (
            "AC subterm under NoEq, var pattern",
            pk(ab()),
            pk(v("x")),
            any,
            Expect::Matched(vec![(v("x"), ab())]),
        ),
        (
            "head clash",
            pk(v("x")),
            pair(v("a"), v("b")),
            any,
            Expect::NoMatcher,
        ),
        (
            "non-bindable var matches itself",
            pair(v("x"), v("a")),
            pair(v("x"), v("y")),
            only_y,
            Expect::Matched(vec![(v("y"), v("a"))]),
        ),
        (
            "non-bindable var is a constant",
            pair(v("a"), v("x")),
            pair(v("x"), v("y")),
            only_y,
            Expect::NoMatcher,
        ),
    ];
    for (label, subject, pattern, bindable, expect) in rows {
        let got = solve_match_lterm(
            &crate::lterm::sort_of_name,
            &bindable,
            Match::match_with(subject, pattern),
        );
        match (got, expect) {
            (MatchOutcome::Matched(s), Expect::Matched(want)) => {
                let want: Vec<(LVar, LNTerm)> =
                    want.into_iter().map(|(k, t)| (lvar(&k), t)).collect();
                assert_eq!(s.to_list(), want, "{label}");
            }
            (MatchOutcome::NoMatcher, Expect::NoMatcher)
            | (MatchOutcome::NeedsAc, Expect::NeedsAc) => {}
            (got, _) => panic!(
                "{label}: got {}",
                match got {
                    MatchOutcome::Matched(_) => "Matched",
                    MatchOutcome::NoMatcher => "NoMatcher",
                    MatchOutcome::NeedsAc => "NeedsAc",
                }
            ),
        }
    }
}
