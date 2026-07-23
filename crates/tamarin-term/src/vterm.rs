// Currently GPL 3.0 until granted permission by the following authors:
//   beschmi, meiersi, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/VTerm.hs, lib/theory/src/Theory/Sapic/Term.hs

//! Port of `Term.VTerm` from `lib/term/src/Term/VTerm.hs`.
//!
//! `VTerm<C, V>` is a term whose literals are either *constants* (of type
//! `C`) or *variables* (of type `V`).

use crate::term::{lit, Term, TermView};

/// Literal: either a constant `Con(c)` or a variable `Var(v)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lit<C, V> {
    Con(C),
    Var(V),
}

/// `VTerm<C, V>` = `Term<Lit<C, V>>`. Type alias only — all term operations
/// from [`crate::term`] apply.
pub type VTerm<C, V> = Term<Lit<C, V>>;

/// `varTerm v`: lift a variable into a term.
pub fn var_term<C, V>(v: V) -> VTerm<C, V> {
    lit(Lit::Var(v))
}

/// `constTerm c`: lift a constant into a term.
pub fn const_term<C, V>(c: C) -> VTerm<C, V> {
    lit(Lit::Con(c))
}

/// `isVar t`: whether `t` is a single variable literal.
///
/// Mirrors the exported `VTerm.hs` `isVar`; retained for surface parity, no
/// caller yet.
pub fn is_var<C, V>(t: &VTerm<C, V>) -> bool {
    matches!(t, Term::Lit(Lit::Var(_)))
}

/// `termVar t`: the variable literal of `t`, if `t` is exactly a variable.
///
/// Mirrors the exported `VTerm.hs` `termVar`; retained for surface parity, no
/// caller yet.
pub fn term_var<C, V>(t: &VTerm<C, V>) -> Option<&V> {
    match t.view() {
        TermView::Lit(Lit::Var(v)) => Some(v),
        _ => None,
    }
}

/// `varsVTerm t`: deduplicated list of variables in `t`, in sorted order.
pub fn vars_vterm<C, V: Ord + Clone>(t: &VTerm<C, V>) -> Vec<V> {
    let mut out = Vec::new();
    collect_vars(t, &mut out);
    out.sort();
    out.dedup();
    out
}

/// In-order list of variables in `t`, with duplicates and in source order
/// (left-to-right, depth-first). Mirrors the HS `foldMap (foldMap (:[]))`
/// traversal used by `freesSapicTerm` (Theory/Sapic/Term.hs:131-132) — NOT sorted,
/// NOT deduplicated. Use [`vars_vterm`] when set semantics are wanted.
pub fn vars_vterm_in_order<C, V: Clone>(t: &VTerm<C, V>) -> Vec<V> {
    let mut out = Vec::new();
    collect_vars(t, &mut out);
    out
}

fn collect_vars<C, V: Clone>(t: &VTerm<C, V>, out: &mut Vec<V>) {
    match t {
        Term::Lit(Lit::Var(v)) => out.push(v.clone()),
        Term::Lit(Lit::Con(_)) => {}
        Term::App(_, ts) => {
            for t in ts.iter() {
                collect_vars(t, out);
            }
        }
    }
}

/// `True` iff `t` contains no variable literals (i.e. is ground).
/// Non-allocating, short-circuits on the first variable found — cheaper than
/// `vars_vterm(t).is_empty()` on the hot match path.
pub fn is_ground_vterm<C, V>(t: &VTerm<C, V>) -> bool {
    match t {
        Term::Lit(Lit::Var(_)) => false,
        Term::Lit(Lit::Con(_)) => true,
        Term::App(_, ts) => ts.iter().all(is_ground_vterm),
    }
}

/// `occursVTerm v t`: whether `v` appears anywhere in `t`.
pub fn occurs_vterm<C, V: PartialEq>(v: &V, t: &VTerm<C, V>) -> bool {
    match t {
        Term::Lit(Lit::Var(w)) => w == v,
        Term::Lit(Lit::Con(_)) => false,
        Term::App(_, ts) => ts.iter().any(|t| occurs_vterm(v, t)),
    }
}

/// `constsVTerm t`: sorted, deduplicated list of constants in `t`.
///
/// Mirrors the exported `VTerm.hs` `constsVTerm`; retained for surface parity,
/// no caller yet.
pub fn consts_vterm<C: Ord + Clone, V>(t: &VTerm<C, V>) -> Vec<C> {
    let mut out = Vec::new();
    collect_consts(t, &mut out);
    out.sort();
    out.dedup();
    out
}

fn collect_consts<C: Clone, V>(t: &VTerm<C, V>, out: &mut Vec<C>) {
    match t {
        Term::Lit(Lit::Con(c)) => out.push(c.clone()),
        Term::Lit(Lit::Var(_)) => {}
        Term::App(_, ts) => {
            for t in ts.iter() {
                collect_consts(t, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::pair_sym;
    use crate::term::f_app_no_eq;

    type V = &'static str;
    type C = u32;

    #[test]
    fn var_and_const_terms() {
        let v: VTerm<C, V> = var_term("x");
        let c: VTerm<C, V> = const_term(1);
        assert!(is_var(&v));
        assert!(!is_var(&c));
        assert_eq!(term_var(&v), Some(&"x"));
        assert_eq!(term_var(&c), None);
    }

    #[test]
    fn vars_collected_sorted_unique() {
        let t: VTerm<C, V> = f_app_no_eq(
            pair_sym(),
            vec![
                var_term("y"),
                f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("y")]),
            ],
        );
        assert_eq!(vars_vterm(&t), vec!["x", "y"]);
    }

    #[test]
    fn occurs_finds_variable() {
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), const_term(0)]);
        assert!(occurs_vterm(&"x", &t));
        assert!(!occurs_vterm(&"z", &t));
    }

    #[test]
    fn consts_collected() {
        let t: VTerm<C, V> = f_app_no_eq(
            pair_sym(),
            vec![
                const_term(2),
                f_app_no_eq(pair_sym(), vec![const_term(1), const_term(2)]),
            ],
        );
        assert_eq!(consts_vterm(&t), vec![1, 2]);
    }
}
