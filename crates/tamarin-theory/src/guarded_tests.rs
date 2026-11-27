// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::elaborate::formula_to_guarded_parsed;
use tamarin_parser::ast as p;
use tamarin_parser::parser::parse_formula_str;
use tamarin_term::function_symbols::AcSym;
use tamarin_term::lterm::pub_term;
use tamarin_term::maude_sig::pair_maude_sig;
use tamarin_term::term::f_app_ac;

fn g(s: &str) -> Result<Guarded, GuardError> {
    let sig = pair_maude_sig();
    let f = parse_formula_str(s, &sig).map_err(|e| err(format!("parse: {}", e)))?;
    formula_to_guarded_parsed(&f, &sig)
}

/// A free variable leaf of a guarded formula's term.
fn bfree(name: &str, idx: u64, sort: LSort) -> BLNTerm {
    var_term(BVar::Free(LVar::new(name, sort, idx)))
}

/// A public-name leaf of a guarded formula's term.
fn bpub(name: &str) -> BLNTerm {
    pub_term(name)
}

/// An opened atom carries its free variables straight across.
#[test]
fn bvar_to_lvar_frees_an_opened_atom() {
    use crate::atom::ProtoAtom;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    let i = LVar::new("i", LSort::Node, 0);
    let a: Atom<BLNTerm> = ProtoAtom::Last(var_term(tamarin_term::lterm::BVar::Free(i)));
    assert_eq!(bvar_to_lvar(&a), ProtoAtom::Last(var_term(i)));
}

/// HS `bvarToLVar`'s `boundError` (Guarded.hs): the atom must have
/// every enclosing binder opened before it is read over plain `LVar`s.
#[test]
#[should_panic(expected = "bvarToLVar: left-over bound variable '2'")]
fn bvar_to_lvar_rejects_a_left_over_bound_variable() {
    use crate::atom::ProtoAtom;
    use tamarin_term::vterm::var_term;
    let a: Atom<BLNTerm> = ProtoAtom::Last(var_term(tamarin_term::lterm::BVar::Bound(2)));
    bvar_to_lvar(&a);
}

/// A guarded fact over the given argument terms, tagged as `fact_tag_of`
/// tags the parser fact of the same name and arity.
fn bfact(persistent: bool, name: &str, args: Vec<BLNTerm>) -> Fact<BLNTerm> {
    let tag = crate::elaborate::fact_tag_of(&p::Fact {
        persistent,
        name: name.into(),
        args: vec![p::Term::PubLit("_".into()); args.len()],
        annotations: vec![],
    });
    Fact::new(tag, args)
}

/// Both variable orderings compare the sort with `LSort`'s derived `Ord`,
/// which ranks the five sorts in their declaration order
/// (Term/LTerm.hs): `Pub`, `Fresh`, `Msg`, `Node`, `Nat`.  The printed
/// operand order of an AC application rides on this through `Ord LVar`, so a
/// reordering of the `LSort` variants moves printed output.
#[test]
fn variable_ordering_ranks_sorts_in_lsort_declaration_order() {
    let declared = [
        LSort::Pub,
        LSort::Fresh,
        LSort::Msg,
        LSort::Node,
        LSort::Nat,
    ];

    let v = |sort| LVar::new("x", sort, 0);
    let b = |sort| ("x".to_string(), sort);
    for (i, &s) in declared.iter().enumerate() {
        for (j, &t) in declared.iter().enumerate() {
            let want = i.cmp(&j);
            assert_eq!(v(s).cmp(&v(t)), want, "{s:?} vs {t:?}");
            assert_eq!(b(s).cmp(&b(t)), want, "{s:?} vs {t:?}");
        }
    }
}

// =========================================================================
// Conversion and printing: `formula_to_guarded_parsed` (HS `formulaToGuarded`,
// Guarded.hs) read through `prettyGuarded`
// =========================================================================

/// The signature of a theory that declares only `decls`; an empty `decls`
/// is the pair signature every theory carries.
fn sig_of(decls: &str) -> tamarin_term::maude_sig::MaudeSig {
    if decls.is_empty() {
        return pair_maude_sig();
    }
    let thy = tamarin_parser::parse_theory(&format!("theory T begin\n{decls}\nend"), &[])
        .expect("declarations parse");
    crate::elaborate::elaborate(&thy)
        .expect("declarations elaborate")
        .signature
}

/// What one conversion row expects.
enum Conv {
    /// Converts and prints as these bytes, laid out flat (`None`) or by the
    /// HughesPJ engine at the given start column.
    Prints(Option<usize>, &'static str),
    /// Converts to exactly what the other source converts to.
    Same(&'static str),
    /// Fails with this message.
    Fails(&'static str),
}

struct ConvRow {
    decls: &'static str,
    src: String,
    want: Conv,
    /// `isSafetyFormula` and `isClosed` (Guarded.hs), when the row pins them.
    safety: Option<bool>,
    closed: Option<bool>,
}

fn prints(src: &str, out: &'static str) -> ConvRow {
    ConvRow {
        decls: "",
        src: src.to_string(),
        want: Conv::Prints(None, out),
        safety: None,
        closed: None,
    }
}

#[test]
fn guarded_conversion_table() {
    use Conv::*;
    let mut rows = vec![
        prints("T", "⊤"),
        prints("F", "⊥"),
        // The antecedent's action atom guards the universal's binders, and
        // the consequent becomes its body.
        ConvRow {
            safety: Some(true),
            ..prints("All k #i. Setup(k) @ #i ==> F", "∀ k #i. (Setup( k ) @ #i) ⇒ ⊥")
        },
        prints("Ex k #i. Setup(k) @ #i", "∃ k #i. (Setup( k ) @ #i)"),
        // A top-level implication nests the consequent's quantifier; it is
        // not turned into a disjunction.
        prints(
            "All k #i. Setup(k) @ #i ==> (Ex j #t. Setup(j) @ #t)",
            "∀ k #i. (Setup( k ) @ #i) ⇒ ∃ j #t. (Setup( j ) @ #t)",
        ),
        // A guarded `∀` with no binders over `⊥` prints as the negated guard.
        prints("not(#i < #j)", "¬(#i < #j)"),
        ConvRow {
            decls: "functions: sdec/2",
            ..prints("sdec{body}key = 'z'", "sdec(body, key) = 'z'")
        },
        ConvRow {
            decls: "functions: senc/2",
            want: Prints(Some(0), "senc(<a, b>, k) = 'z'"),
            ..prints("senc{<a, b>}k = 'z'", "")
        },
        // HS `prettyTerm` breaks an over-wide AC chain after each operator,
        // the same way inside a formula as inside a rule.
        ConvRow {
            decls: "builtins: multiset",
            want: Prints(
                Some(12),
                concat!(
                    "z =\n",
                    "            (<'1', ~longPayloadNameNumberOne>++<'2', ~longPayloadNameNumberTwo>++\n",
                    "             <'3', ~longPayloadNameNumberThree>)",
                ),
            ),
            ..prints(
                "z = <'1', ~longPayloadNameNumberOne> ++ <'2', ~longPayloadNameNumberTwo> \
                 ++ <'3', ~longPayloadNameNumberThree>",
                "",
            )
        },
        ConvRow {
            safety: Some(false),
            ..prints(
                "All k #i. Setup(k) @ #i ==> Ex j #t. Foo(j) @ #t",
                "∀ k #i. (Setup( k ) @ #i) ⇒ ∃ j #t. (Foo( j ) @ #t)",
            )
        },
        // `last` atoms are never safety, even in a closed formula.
        ConvRow {
            safety: Some(false),
            closed: Some(true),
            ..prints("All #i. K('a') @ i ==> last(i)", "∀ #i. (K( 'a' ) @ #i) ⇒ last(#i)")
        },
        ConvRow {
            safety: Some(false),
            closed: Some(true),
            ..prints(
                "All #i. K('a') @ i & last(i) ==> F",
                "∀ #i. (K( 'a' ) @ #i) ⇒ ¬(last(#i))",
            )
        },
        ConvRow {
            safety: Some(false),
            closed: Some(true),
            ..prints(
                "All #i. K('a') @ i ==> not last(i)",
                "∀ #i. (K( 'a' ) @ #i) ⇒ ¬(last(#i))",
            )
        },
        ConvRow {
            want: Fails("unguarded variable(s) 'k' in the subformula"),
            ..prints("Ex k. F", "")
        },
        // HS `convAll` accepts only an implication beneath the prefix.
        ConvRow {
            want: Fails("universal quantifier without toplevel implication"),
            ..prints("All k #i. Setup(k) @ #i", "")
        },
        // A bare fact is predicate sugar, which the conversion cannot strip.
        ConvRow {
            want: Fails("Syntactic sugar is not allowed, guarded formula expected."),
            ..prints("Ex x #i. A(x) @ #i & P(x)", "")
        },
        // Equivalence is the conjunction of its two implications at positive
        // polarity and the disjunction of their negations at negative.
        ConvRow {
            want: Same(
                "((Ex x #i. A(x) @ #i) ==> (Ex y #j. B(y) @ #j)) & \
                 ((Ex y #j. B(y) @ #j) ==> (Ex x #i. A(x) @ #i))",
            ),
            ..prints("(Ex x #i. A(x) @ #i) <=> (Ex y #j. B(y) @ #j)", "")
        },
        ConvRow {
            want: Same(
                "not (((Ex x #i. A(x) @ #i) ==> (Ex y #j. B(y) @ #j)) & \
                 ((Ex y #j. B(y) @ #j) ==> (Ex x #i. A(x) @ #i)))",
            ),
            ..prints("not ((Ex x #i. A(x) @ #i) <=> (Ex y #j. B(y) @ #j))", "")
        },
    ];
    // The equivalence truth table, under zero, one and two negations.
    let tf = |b: bool| if b { "T" } else { "F" };
    let truth: Vec<(String, bool)> = [(false, false), (false, true), (true, false), (true, true)]
        .into_iter()
        .flat_map(|(l, r)| {
            let iff = format!("({} <=> {})", tf(l), tf(r));
            [
                (iff.clone(), l == r),
                (format!("not {iff}"), l != r),
                (format!("not (not {iff})"), l == r),
            ]
        })
        .collect();
    for (src, value) in &truth {
        rows.push(prints(src, if *value { "⊤" } else { "⊥" }));
    }

    for row in &rows {
        let sig = sig_of(row.decls);
        let convert = |src: &str| {
            let f = parse_formula_str(src, &sig).unwrap_or_else(|e| panic!("{src}: parse: {e}"));
            formula_to_guarded_parsed(&f, &sig)
        };
        let got = convert(&row.src);
        match (&row.want, &got) {
            (Prints(None, out), Ok(gf)) => {
                assert_eq!(
                    &crate::pretty_formula::pretty_guarded(gf),
                    out,
                    "{}",
                    row.src
                )
            }
            (Prints(Some(col), out), Ok(gf)) => assert_eq!(
                &crate::pretty_formula::guarded_doc(gf).render_at(
                    crate::pretty_hpj::LINE_LENGTH,
                    crate::pretty_hpj::RIBBON,
                    *col
                ),
                out,
                "{}",
                row.src
            ),
            (Same(other), Ok(gf)) => {
                assert_eq!(gf, &convert(other).expect("converts"), "{}", row.src)
            }
            (Fails(msg), Err(e)) => assert_eq!(&e.message, msg, "{}", row.src),
            (_, got) => panic!("{}: unexpected {got:?}", row.src),
        }
        if let Some(safety) = row.safety {
            assert_eq!(
                is_safety_formula(got.as_ref().unwrap()),
                safety,
                "{}",
                row.src
            );
        }
        if let Some(closed) = row.closed {
            assert_eq!(is_closed(got.as_ref().unwrap()), closed, "{}", row.src);
        }
    }
}

// =========================================================================
// Smart constructors and negation: `gconj`, `gdisj`, `gnot` (Guarded.hs)
// =========================================================================

/// `last(#<name>)`, a guarded atom that only the given name distinguishes.
fn last_atom(name: &str) -> Guarded {
    g(&format!("last(#{name})")).unwrap()
}

/// `gtrue` is `GConj []` and `gfalse` is `GDisj []`; `gconj`/`gdisj`
/// flatten nested conjunctions/disjunctions at every depth, drop the
/// neutral element, short-circuit on the absorbing one, `nub` duplicates
/// (first occurrence wins) and unwrap a singleton; `gnot` pushes negation
/// through with De Morgan and swaps `∀`/`∃`.  Each row is `(case, got,
/// want)`, and `gnot` is an involution on every `want`.
#[test]
fn guarded_algebra_table() {
    let [a, b, c, d, e] = ["a", "b", "c", "d", "e"].map(last_atom);
    let conj = |xs: &[&Guarded]| Guarded::Conj(xs.iter().map(|x| (*x).clone()).collect());
    let disj = |xs: &[&Guarded]| Guarded::Disj(xs.iter().map(|x| (*x).clone()).collect());
    let all = g("All x #i. P(x)@#i ==> Q(x)@#i").unwrap();
    let ex = g("Ex x #i. P(x)@#i").unwrap();
    let quantifier = |f: &Guarded| match f {
        Guarded::GGuarded { qua, .. } => Some(*qua),
        _ => None,
    };

    let rows: Vec<(&str, Guarded, Guarded)> = vec![
        ("gtrue", gtrue(), conj(&[])),
        ("gfalse", gfalse(), disj(&[])),
        ("¬⊤", gnot(&gtrue()), gfalse()),
        ("¬⊥", gnot(&gfalse()), gtrue()),
        ("⊤ ∧ ⊤ ∧ ⊤", gconj(vec![gtrue(), gtrue(), gtrue()]), gtrue()),
        (
            "⊤ ∧ ⊥ ∧ a",
            gconj(vec![gtrue(), gfalse(), a.clone()]),
            gfalse(),
        ),
        ("a ∧ ⊥", gconj(vec![a.clone(), gfalse()]), gfalse()),
        ("⊥ ∨ ⊥", gdisj(vec![gfalse(), gfalse()]), gfalse()),
        (
            "⊥ ∨ ⊤ ∨ ⊥",
            gdisj(vec![gfalse(), gtrue(), gfalse()]),
            gtrue(),
        ),
        (
            "a ∧ b ∧ a",
            gconj(vec![a.clone(), b.clone(), a.clone()]),
            conj(&[&a, &b]),
        ),
        (
            "a ∨ b ∨ a ∨ b",
            gdisj(vec![a.clone(), b.clone(), a.clone(), b.clone()]),
            disj(&[&a, &b]),
        ),
        // `nub` runs before the singleton unwrap.
        ("a ∧ a", gconj(vec![a.clone(), a.clone()]), a.clone()),
        ("a ∨ a", gdisj(vec![a.clone(), a.clone()]), a.clone()),
        ("∧ [a]", gconj(vec![a.clone()]), a.clone()),
        (
            "(a ∧ b) ∧ c",
            gconj(vec![conj(&[&a, &b]), c.clone()]),
            conj(&[&a, &b, &c]),
        ),
        (
            "(((a ∧ b) ∧ c) ∧ d) ∧ e",
            gconj(vec![conj(&[
                &conj(&[&conj(&[&conj(&[&a, &b]), &c]), &d]),
                &e,
            ])]),
            conj(&[&a, &b, &c, &d, &e]),
        ),
        (
            "(((a ∨ b) ∨ c) ∨ d) ∨ e",
            gdisj(vec![disj(&[
                &disj(&[&disj(&[&disj(&[&a, &b]), &c]), &d]),
                &e,
            ])]),
            disj(&[&a, &b, &c, &d, &e]),
        ),
        (
            "¬(a ∧ b)",
            gnot(&conj(&[&a, &b])),
            disj(&[&gnot(&a), &gnot(&b)]),
        ),
        (
            "¬(a ∨ b)",
            gnot(&disj(&[&a, &b])),
            gconj(vec![gnot(&a), gnot(&b)]),
        ),
        (
            "¬∀",
            gnot(&all),
            g("Ex x #i. P(x)@#i & not(Q(x)@#i)").unwrap(),
        ),
        ("¬∃", gnot(&ex), g("All x #i. P(x)@#i ==> F").unwrap()),
    ];
    for (case, got, want) in &rows {
        assert_eq!(got, want, "{case}");
        assert_eq!(&gnot(&gnot(want)), want, "¬¬({case})");
    }
    assert_eq!(quantifier(&gnot(&all)), Some(Quantifier::Ex));
    assert_eq!(quantifier(&gnot(&ex)), Some(Quantifier::All));
}

// =========================================================================
// `simplify_guarded_with` (HS `simplifyGuardedOrReturn`, Guarded.hs):
//   simp (GAto a)       = maybe fm gtf (valuation a)
//   simp (GDisj fms)    = gdisj (map simp fms)
//   simp (GConj fms)    = gconj (map simp fms)
//   simp (GGuarded All [] atos gf)
//     | any (Just False ==) (map valuation atos) = gtrue
//     | otherwise = gall [] (filter unknown atos) (simp gf)
//   simp (GGuarded ...) = fm  -- delay past binders
// =========================================================================

/// The `a = b` equality over two free `Msg` leaves.
fn eq_atom(a: &str, b: &str) -> Atom<BLNTerm> {
    ProtoAtom::EqE(bfree(a, 0, LSort::Msg), bfree(b, 0, LSort::Msg))
}

/// A universal over `vars` with the given equality guards and the body
/// `p = q`.
fn universal(vars: &[&str], guards: &[(&str, &str)]) -> Guarded {
    Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vars.iter().map(|v| (v.to_string(), LSort::Msg)).collect(),
        guards: guards.iter().map(|(a, b)| eq_atom(a, b)).collect(),
        body: std::sync::Arc::new(Guarded::Atom(eq_atom("p", "q"))),
    }
}

/// Each row is `(formula, the valuation's decided equalities, its answer
/// for every other atom, want)`.  The valuation sees each atom over plain
/// `LVar`s (HS `unbindAtom`).
#[test]
fn guarded_simplify_table() {
    let atom = |a: &str, b: &str| Guarded::Atom(eq_atom(a, b));
    type Row<'a> = (
        Guarded,
        &'a [(&'a str, &'a str, bool)],
        Option<bool>,
        Guarded,
    );
    let rows: Vec<Row> = vec![
        (atom("x", "y"), &[], Some(true), gtrue()),
        (atom("x", "y"), &[], Some(false), gfalse()),
        (atom("x", "y"), &[], None, atom("x", "y")),
        (
            Guarded::Disj(vec![atom("p", "q"), atom("r", "s")].into()),
            &[("r", "s", false)],
            None,
            atom("p", "q"),
        ),
        (
            Guarded::Conj(vec![atom("p", "q"), atom("r", "s")].into()),
            &[("r", "s", false)],
            None,
            gfalse(),
        ),
        // One false guard makes a binder-free universal vacuous.
        (
            universal(&[], &[("a", "b"), ("c", "d")]),
            &[("a", "b", false)],
            None,
            gtrue(),
        ),
        // True guards drop; unknown ones and the body stay.
        (
            universal(&[], &[("a", "b"), ("c", "d")]),
            &[("a", "b", true)],
            None,
            universal(&[], &[("c", "d")]),
        ),
        // With every guard true only the body is left (`gall _ [] gf = gf`);
        // the body stays unknown so that `gf == gtrue` cannot decide it.
        (
            universal(&[], &[("a", "b")]),
            &[("a", "b", true)],
            None,
            atom("p", "q"),
        ),
        // A universal with binders is left alone.
        (
            universal(&["x"], &[("a", "b")]),
            &[],
            Some(true),
            universal(&["x"], &[("a", "b")]),
        ),
    ];
    for (formula, known, otherwise, want) in rows {
        let val = |at: &Atom<LNTerm>| {
            Ok::<_, ()>(
                known
                    .iter()
                    .find(|(a, b, _)| *at == bvar_to_lvar(&eq_atom(a, b)))
                    .map(|(_, _, v)| *v)
                    .or(otherwise),
            )
        };
        assert_eq!(
            simplify_guarded_with(&formula, &val),
            Ok(want),
            "{formula:?}"
        );
    }
}

// =========================================================================
// Induction: `satisfiedByEmptyTrace`, `ginduct`, `toInductionHypothesis`
// (Guarded.hs)
// =========================================================================

/// Every `Last(Bound n)` index the formula reaches, guards before body: the
/// order `to_induction_hypothesis` emits its `lastAtos` in.
fn last_bound_indices(g: &Guarded) -> Vec<u64> {
    fn atom(a: &Atom<BLNTerm>, out: &mut Vec<u64>) {
        if let ProtoAtom::Last(Term::Lit(Lit::Var(BVar::Bound(n)))) = a {
            out.push(*n);
        }
    }
    fn go(g: &Guarded, out: &mut Vec<u64>) {
        match g {
            Guarded::Atom(a) => atom(a, out),
            Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().for_each(|x| go(x, out)),
            Guarded::GGuarded { guards, body, .. } => {
                guards.iter().for_each(|a| atom(a, out));
                go(body, out);
            }
        }
    }
    let mut out = Vec::new();
    go(g, &mut out);
    out
}

struct InductRow {
    case: &'static str,
    formula: Guarded,
    /// `satisfiedByEmptyTrace`; `None` when it errors.
    empty_trace: Option<bool>,
    /// `ginduct`'s base case, and the induction hypothesis's outer
    /// quantifier; `None` when `ginduct` errors.  The step case is always
    /// `gconj [gf, toInductionHypothesis gf]`.
    induct: Option<(Guarded, Quantifier)>,
    /// The hypothesis's `Last (Bound j)` indices, one per node-sorted
    /// binder counted from the innermost outwards.
    ih_last: &'static [u64],
}

#[test]
fn ginduct_table() {
    use Quantifier::{All, Ex};
    let row = |case: &'static str,
               empty_trace: Option<bool>,
               induct: Option<(Guarded, Quantifier)>,
               ih_last: &'static [u64]| InductRow {
        case,
        formula: g(case).unwrap(),
        empty_trace,
        induct,
        ih_last,
    };
    let mut rows = vec![
        InductRow {
            case: "⊤",
            formula: gtrue(),
            empty_trace: Some(true),
            induct: None,
            ih_last: &[],
        },
        InductRow {
            case: "⊥",
            formula: gfalse(),
            empty_trace: Some(false),
            induct: None,
            ih_last: &[],
        },
        // A quantifier-free atom is not doubly guarded.
        row("last(#i)", None, None, &[]),
        row(
            "All x #i. P(x)@#i ==> Q(x)@#i",
            Some(true),
            Some((gtrue(), Ex)),
            &[0],
        ),
        row("Ex k #i. P(k)@#i", Some(false), Some((gfalse(), All)), &[0]),
        row(
            "All k #i. Setup(k) @ #i ==> Ex #j. Setup(k) @ #j & #j < #i",
            Some(true),
            Some((gtrue(), Ex)),
            &[0, 0],
        ),
        row(
            "All #i. Setup('k') @ #i ==> G('x') @ #i",
            Some(true),
            Some((gtrue(), Ex)),
            &[0],
        ),
        // `lastAtos` skips the message binder and reverses the binder list.
        row(
            "All k #i #j. (Setup(k) @ #i & Setup(k) @ #j) ==> F",
            Some(true),
            Some((gtrue(), Ex)),
            &[0, 1],
        ),
    ];
    // Equality-only guards can have witnesses without any trace action, so
    // neither quantifier is decided by vacuity (#958), and neither Boolean
    // fold short-circuits before it reaches such a child.  The parser never
    // builds these, so the rows are built directly.
    let x = crate::formula::lift_free(&tamarin_term::builtin::msg_var("x", 0));
    for qua in [All, Ex] {
        let eq_only = Guarded::GGuarded {
            qua,
            vars: Vec::new().into(),
            guards: vec![Atom::EqE(x.clone(), x.clone())].into(),
            body: std::sync::Arc::new(gtrue()),
        };
        for formula in [
            eq_only.clone(),
            Guarded::Disj(vec![gtrue(), eq_only.clone()].into()),
            Guarded::Conj(vec![gfalse(), eq_only].into()),
        ] {
            rows.push(InductRow {
                case: "equality-only guard",
                formula,
                empty_trace: None,
                induct: None,
                ih_last: &[],
            });
        }
    }

    for r in &rows {
        assert_eq!(
            satisfied_by_empty_trace(&r.formula).ok(),
            r.empty_trace,
            "{}",
            r.case
        );
        let Some((base, ih_qua)) = &r.induct else {
            assert!(ginduct(&r.formula).is_err(), "{}", r.case);
            continue;
        };
        let (got_base, step) = ginduct(&r.formula).expect(r.case);
        let ih = to_induction_hypothesis(&r.formula).expect(r.case);
        assert_eq!(&got_base, base, "{}", r.case);
        assert_eq!(
            step,
            Guarded::Conj(vec![r.formula.clone(), ih.clone()].into()),
            "{}",
            r.case
        );
        let (Guarded::GGuarded { qua, vars, .. }, Guarded::GGuarded { vars: gf_vars, .. }) =
            (&ih, &r.formula)
        else {
            panic!("{}: a guarded hypothesis of a guarded formula", r.case)
        };
        assert_eq!(qua, ih_qua, "{}", r.case);
        assert_eq!(
            vars, gf_vars,
            "{}: the hypothesis keeps the binders",
            r.case
        );
        assert_eq!(last_bound_indices(&ih), r.ih_last, "{}", r.case);
    }
}

// =========================================================================
// Substitution
// =========================================================================

fn pubconst(s: &str) -> LNTerm {
    pub_term(s)
}

/// The `LVar` key of a message-sorted substitution entry.
fn key(name: &str, idx: u64) -> LVar {
    LVar::new(name, LSort::Msg, idx)
}

#[test]
fn applying_a_substitution_to_a_guarded_formula_leaves_bound_leaves_alone() {
    // `Ex k. Action(k) @ i` — substituting `k` from outside should
    // NOT rewrite the inner `k` because it's positionally bound
    // (DeBruijn `Bound(0)` in the body, not Free LVar `k:0`).
    let s = LNSubst::from_list(vec![(key("k", 0), pubconst("OUTER"))]);
    let inner_k = LVar::new("k", LSort::Msg, 0);
    // Build via close_guarded so that `k` becomes Bound(0) in the body.
    let g = close_guarded(
        Quantifier::Ex,
        vec![inner_k],
        Vec::new(),
        Guarded::Atom(ProtoAtom::Action(
            var_term(BVar::Free(LVar::new("i", LSort::Node, 0))),
            bfact(false, "Action", vec![bfree("k", 0, LSort::Msg)]),
        )),
    );
    let result = subst_guarded(&g, &s);
    // Body should be unchanged: subst on Free `(k, 0)` doesn't
    // touch the Bound `k` reference.
    match result {
        Guarded::GGuarded { body, .. } => match &*body {
            Guarded::Atom(ProtoAtom::Action(_, fa)) => {
                // Walk the body atom and verify the `k` slot is still Bound(0).
                match &fa.terms()[0] {
                    Term::Lit(Lit::Var(BVar::Bound(0))) => {}
                    other => panic!("expected Bound(0), got {:?}", other),
                }
            }
            other => panic!("expected Atom(Action), got {:?}", other),
        },
        other => panic!("expected GGuarded, got {:?}", other),
    }
}

/// `closeGuarded` substitutes each abstracted variable for its De Bruijn
/// index through `substFreeAtom`, whose `fmapTerm` rebuilds every
/// application with `fApp` (Guarded.hs).  The derived `Ord BVar`
/// puts `Bound i` before `Free x` (LTerm.hs), so an AC argument
/// list whose second operand is the one being bound comes back re-sorted
/// under the index.
#[test]
fn close_guarded_resorts_ac_arguments_under_the_bound_indices() {
    // `a * x` with `a` and `x` both free sorts to [a, x] (Ord LVar is
    // (idx, sort, name), LTerm.hs).
    let a = LVar::new("a", LSort::Msg, 0);
    let x = LVar::new("x", LSort::Msg, 0);
    let open: BLNTerm = f_app_ac(
        AcSym::Mult,
        vec![var_term(BVar::Free(a)), var_term(BVar::Free(x))],
    );
    let Term::App(_, open_args) = &open else {
        panic!("an application")
    };
    assert_eq!(
        open_args.as_ref(),
        &[var_term(BVar::Free(a)), var_term(BVar::Free(x))]
    );

    let closed = close_guarded(
        Quantifier::Ex,
        vec![x],
        vec![ProtoAtom::EqE(
            f_app_ac(AcSym::Mult, vec![var_term(a), var_term(x)]),
            pub_term("z"),
        )],
        gtrue(),
    );
    let Guarded::GGuarded { guards, .. } = &closed else {
        panic!("close_guarded builds a GGuarded")
    };
    let ProtoAtom::EqE(lhs, _) = &guards[0] else {
        panic!("the guard is the equality")
    };
    let Term::App(_, args) = lhs else {
        panic!("an application")
    };
    assert_eq!(
        args.as_ref(),
        &[var_term(BVar::Bound(0)), var_term(BVar::Free(a))],
        "binding `x` moves it ahead of the free `a`"
    );
}

/// `subst_blnterm_cow` reports `Some` exactly on a domain hit: the leaf's
/// whole `LVar` is the key, and a `Subst` holds no `x ~> x` mapping
/// (SubstVFree.hs), so a hit always changes the leaf.  The image is
/// lifted through `fmapTerm (fmap Free)` (SubstVFree.hs).
#[test]
fn subst_blnterm_cow_reports_a_domain_hit() {
    let s = LNSubst::from_list(vec![(
        LVar::new("x", LSort::Msg, 0),
        var_term(LVar::new("x", LSort::Msg, 7)),
    )]);

    let leaf = |sort: LSort| bfree("x", 0, sort);

    // A hit rebuilds to the lifted image.
    assert_eq!(
        subst_blnterm_cow(&leaf(LSort::Msg), &s),
        Some(bfree("x", 7, LSort::Msg)),
        "a domain hit must rebuild to the lifted image"
    );

    // A leaf that shares the name and the index but carries another sort is
    // another variable, so it is a miss.
    assert_eq!(
        subst_blnterm_cow(&leaf(LSort::Fresh), &s),
        None,
        "a leaf of another sort must report None"
    );

    // A leaf whose name is not in the domain returns None (miss).
    assert_eq!(
        subst_blnterm_cow(&bfree("y", 0, LSort::Msg), &s),
        None,
        "a domain miss must report None"
    );

    // A `Bound` leaf carries no variable identity, so it is never a hit.
    assert_eq!(subst_blnterm_cow(&var_term(BVar::Bound(0)), &s), None);
}

// =============================================================================
// Opened binders
// =============================================================================

// =============================================================================
// openGuarded (Guarded.hs)
// =============================================================================

/// Anything but a `GGuarded` opens to `None` (HS `openGuarded _ = return
/// Nothing`, Guarded.hs).
#[test]
fn open_guarded_declines_a_non_guarded_formula() {
    use tamarin_utils::fresh::PreciseFreshState;
    let mut fresh = PreciseFreshState::nothing_used();
    assert!(open_guarded(&gtrue(), &mut fresh).is_none());
    assert!(open_guarded(&gfalse(), &mut fresh).is_none());
}

// =============================================================================
// HasFrees for Guarded (Guarded.hs)
// =============================================================================

fn hf_leaf(name: &str, idx: u64, sort: LSort) -> BLNTerm {
    bfree(name, idx, sort)
}

fn hf_fact(name: &str, args: Vec<BLNTerm>) -> Fact<BLNTerm> {
    bfact(false, name, args)
}

fn hf_names(g: &Guarded) -> Vec<String> {
    let mut out = Vec::new();
    g.for_each_free(&mut |v| out.push(format!("{}.{}", v.name, v.idx)));
    out
}

/// HS `Foldable`/`Traversable ProtoAtom` fold the timepoint of an `Action`
/// before the fact (Atom.hs).  Both directions of the
/// `HasFrees` instance carry that order.
#[test]
fn action_atom_visits_timepoint_before_fact() {
    let atom = ProtoAtom::Action(
        hf_leaf("i", 2, LSort::Node),
        hf_fact("A", vec![hf_leaf("x", 1, LSort::Msg)]),
    );
    let g = Guarded::Atom(atom.clone());

    assert_eq!(hf_names(&g), vec!["i.2", "x.1"]);

    assert_eq!(
        tamarin_term::lterm::frees_list(&atom)
            .iter()
            .map(|v| v.name)
            .collect::<Vec<_>>(),
        vec!["i", "x"]
    );

    let mut mapped = Vec::new();
    let _ = atom.clone().map_free(&mut |v| {
        mapped.push(v.name.to_string());
        v
    });
    assert_eq!(mapped, vec!["i", "x"]);
}

/// `BVar::Bound` leaves are positional and carry no variable identity, so
/// neither direction of the instance touches them (Guarded.hs folds
/// through the atoms only).
#[test]
fn bound_leaves_are_skipped() {
    let g = Guarded::GGuarded {
        qua: Quantifier::Ex,
        vars: vec![("z".to_string(), LSort::Msg)].into(),
        guards: vec![ProtoAtom::EqE(
            var_term(BVar::Bound(0)),
            hf_leaf("y", 4, LSort::Msg),
        )]
        .into(),
        body: std::sync::Arc::new(gtrue()),
    };

    assert_eq!(hf_names(&g), vec!["y.4"]);

    let renamed = g
        .clone()
        .map_free(&mut |v| LVar::new("r", v.sort, v.idx + 10));
    let Guarded::GGuarded { guards, vars, .. } = &renamed else {
        panic!("map_free must keep the GGuarded shape")
    };
    assert_eq!(vars[0].0, "z", "the binder list stays verbatim");
    assert_eq!(
        guards[0],
        ProtoAtom::EqE(var_term(BVar::Bound(0)), hf_leaf("r", 14, LSort::Msg))
    );
}

/// HS folds a `GGuarded`'s guard atoms before its body
/// (`foldMap … as `mappend` b`, Guarded.hs).
#[test]
fn guards_visited_before_body() {
    let g = Guarded::GGuarded {
        qua: Quantifier::All,
        vars: vec![].into(),
        guards: vec![ProtoAtom::EqE(
            hf_leaf("g", 1, LSort::Msg),
            hf_leaf("h", 2, LSort::Msg),
        )]
        .into(),
        body: std::sync::Arc::new(Guarded::Conj(
            vec![Guarded::Atom(ProtoAtom::Last(hf_leaf("b", 3, LSort::Node)))].into(),
        )),
    };
    assert_eq!(hf_names(&g), vec!["g.1", "h.2", "b.3"]);
}

/// HS `mapFrees`/`foldFrees` on a guarded formula reach the `LVar` inside a
/// `Free` leaf and write the mapped variable back WHOLE (Guarded.hs
/// through `HasFrees LVar`, LTerm.hs), so the mapped sort is the one
/// the leaf carries afterwards.
#[test]
fn hasfrees_map_takes_the_mapped_sort() {
    let g = Guarded::Atom(ProtoAtom::Last(hf_leaf("x", 1, LSort::Fresh)));

    let renamed = g.map_free(&mut |v| {
        assert_eq!(v.sort, LSort::Fresh);
        LVar::new("w", LSort::Msg, 9)
    });
    assert_eq!(
        renamed,
        Guarded::Atom(ProtoAtom::Last(hf_leaf("w", 9, LSort::Msg)))
    );
}

/// `mapFrees` rebuilds each application through `fApp`
/// (`fmapTerm`, Term/Term/Raw.hs), so a rename that reorders an AC
/// argument list under `Ord LVar` comes back sorted.
#[test]
fn renaming_a_guarded_formula_resorts_its_ac_arguments() {
    // `a * b` sorts to [a, b]; renaming `a` to `z` must swap them.
    let a = LVar::new("a", LSort::Msg, 0);
    let b = LVar::new("b", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let g = Guarded::Atom(ProtoAtom::EqE(
        f_app_ac(
            AcSym::Mult,
            vec![var_term(BVar::Free(a)), var_term(BVar::Free(b))],
        ),
        bpub("t"),
    ));

    let renamed = g.map_free(&mut |v| if v == a { z } else { v });
    assert_eq!(
        renamed,
        Guarded::Atom(ProtoAtom::EqE(
            f_app_ac(
                AcSym::Mult,
                vec![var_term(BVar::Free(b)), var_term(BVar::Free(z))],
            ),
            bpub("t"),
        ))
    );
}
