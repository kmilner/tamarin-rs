// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Parity for formula atoms whose term relation starts with a parenthesised
//! term — `(x ++ z) = y`.
//!
//! HS `fatom` tries `blatom` BEFORE `parens (iff …)`
//! (Theory/Text/Parser/Formula.hs:63-70), and `blatom`'s term-relation arms
//! (Subterm/smallerp/EqE, Theory/Text/Parser/Formula.hs:48-51) are
//! `try`-guarded parses of `msetterm <* op` — and a term may itself be
//! parenthesised.  So a `(`-headed atom is a term relation whenever a term
//! parse reaches a relational operator, and a grouped formula otherwise.
//!
//! WHICH theories parse (and which fail) is pinned to the Haskell oracle
//! (Git revision ef3f0468): every accepted theory here loads with exit 0
//! there, the rejected one fails on both sides.  The rejection's position
//! and label set are the port's own.

use tamarin_parser::ast::{Atom, BinOp, Fact, Formula, FormulaKind, Term, TheoryItem};
use tamarin_parser::{parse_theory, ParseError};

/// The parsed formula of `src`'s single lemma.
fn lemma_formula(src: &str) -> Formula {
    let thy = parse_theory(src, &[]).expect("theory should parse");
    thy.items
        .iter()
        .find_map(|i| match i {
            TheoryItem::Lemma(l) => Some(l.formula.clone()),
            _ => None,
        })
        .expect("one lemma")
}

/// Every atom of `f`, in syntactic order.
fn atoms(f: &Formula) -> Vec<Atom> {
    match &f.kind {
        FormulaKind::False | FormulaKind::True => Vec::new(),
        FormulaKind::Atom(a) => vec![a.clone()],
        FormulaKind::Not(g) | FormulaKind::Forall(_, g) | FormulaKind::Exists(_, g) => atoms(g),
        FormulaKind::And(a, b)
        | FormulaKind::Or(a, b)
        | FormulaKind::Implies(a, b)
        | FormulaKind::Iff(a, b) => {
            let mut v = atoms(a);
            v.extend(atoms(b));
            v
        }
    }
}

fn multiset_lemma(consequent: &str) -> String {
    format!(
        "theory T begin\nbuiltins: multiset\n\
         rule R: [ In(x), In(y) ] --[ A(x), B(y) ]-> [ ]\n\
         lemma L: \"All x y #i #j. A(x) @ #i & B(y) @ #j ==> {consequent}\"\nend\n"
    )
}

/// A parenthesised `++` term before `=` is a term equality, not a grouped
/// formula.  The oracle loads the theory at exit 0.
#[test]
fn parenthesised_term_before_eq_is_a_term_equality() {
    let f = lemma_formula(&multiset_lemma("not(Ex z. (x ++ z) = y)"));
    let eqs: Vec<_> = atoms(&f)
        .into_iter()
        .filter(|a| matches!(a, Atom::Eq(..)))
        .collect();
    let [Atom::Eq(lhs, Term::Var(rhs))] = &eqs[..] else {
        panic!("expected one variable-RHS equality atom, got {eqs:?}");
    };
    assert!(
        matches!(lhs, Term::BinOp(BinOp::Union, _, _)),
        "the LHS keeps its `++` shape: {lhs:?}"
    );
    assert_eq!(rhs.name, "y");
}

/// The same before `<<` is a subterm atom.
#[test]
fn parenthesised_term_before_subterm_op_is_a_subterm_atom() {
    let f = lemma_formula(&multiset_lemma("not((x ++ y) << y)"));
    assert!(
        atoms(&f)
            .iter()
            .any(|a| matches!(a, Atom::Subterm(Term::BinOp(BinOp::Union, _, _), _))),
        "expected a subterm atom with a `++` LHS in {f:?}"
    );
}

/// The same before `(<)`, which desugars into the built-in `Smaller`
/// predicate fact (HS `smallerp`, Theory/Text/Parser/Formula.hs:29-37).
#[test]
fn parenthesised_term_before_smaller_op_is_a_smaller_predicate() {
    let f = lemma_formula(&multiset_lemma("not((x ++ x) (<) y)"));
    assert!(
        atoms(&f)
            .iter()
            .any(|a| matches!(a, Atom::Pred(Fact { name, args, .. })
                if name == "Smaller" && args.len() == 2)),
        "expected a Smaller predicate atom in {f:?}"
    );
}

/// Nesting does not change the reading: `((h(x)) = y)` is the equality of a
/// doubly-parenthesised application and a variable.
#[test]
fn nested_parentheses_still_read_as_a_term_relation() {
    let src = "theory T begin\nbuiltins: hashing\n\
               rule R: [ In(x), In(y) ] --[ A(x), B(y) ]-> [ ]\n\
               lemma L: \"All x y #i #j. A(x) @ #i & B(y) @ #j ==> ((h(x)) = y)\"\nend\n";
    let f = lemma_formula(src);
    assert!(
        atoms(&f)
            .iter()
            .any(|a| matches!(a, Atom::Eq(Term::App(n, _), _) if n == "h")),
        "expected an equality atom with an `h` application LHS in {f:?}"
    );
}

/// A `(`-headed GROUPED formula still parses as one: no relational operator
/// follows the probe, so the parenthesised-formula reading wins.
#[test]
fn grouped_formulas_still_group() {
    let src = "theory T begin\nrule R: [ In(x) ] --[ A(x) ]-> [ ]\n\
               lemma L: \"All x #i. (A(x) @ #i) ==> (Ex #j. A(x) @ #j)\"\nend\n";
    let f = lemma_formula(src);
    let FormulaKind::Forall(_, body) = &f.kind else {
        panic!("expected the quantifier, got {f:?}");
    };
    let FormulaKind::Implies(lhs, _) = &body.kind else {
        panic!("expected the implication, got {body:?}");
    };
    assert!(
        matches!(&lhs.kind, FormulaKind::Atom(Atom::Action(..))),
        "the grouped antecedent stays an action atom: {lhs:?}"
    );
}

/// A parenthesised term with NO relational operator after it is not a
/// formula on either side; the port reports the missing operator inside the
/// group.
#[test]
fn parenthesised_term_without_an_operator_still_fails() {
    let src = "theory T begin\nrule R: [ In(x) ] --[ A(x) ]-> [ ]\n\
               lemma L: \"All x #i. A(x) @ #i ==> ('a')\"\nend\n";
    let e = parse_theory(src, &[]).expect_err("a bare term is not a formula");
    assert!(
        matches!(&e, ParseError::Expected { .. }),
        "expected the `Expected` variant, got {e:?}"
    );
    let at = e.location();
    assert_eq!((at.line, at.col), (3, 39), "position of {e:?}");
    assert!(e.found().unwrap_or("").starts_with(')'));
    assert_eq!(
        e.expected().unwrap_or_default(),
        ["=", "<<", "<", "(<)"].map(String::from)
    );
}
