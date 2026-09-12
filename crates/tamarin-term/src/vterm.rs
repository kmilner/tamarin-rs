// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Term.VTerm` from `lib/term/src/Term/VTerm.hs`.
//!
//! `VTerm<C, V>` is a term whose literals are either *constants* (of type
//! `C`) or *variables* (of type `V`).

use std::{fmt, ops::ControlFlow};

use crate::term::{lit, walk_terms, Term};

/// Literal: either a constant `Con(c)` or a variable `Var(v)`.
///
/// HS `data Lit c v = Con c | Var v` derives `Eq`/`Ord` in that variant order
/// (VTerm.hs:56-57), and `Term`'s own `Ord` reads it, so `Con < Var` decides
/// the argument order of every printed AC term.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lit<C, V> {
    Con(C),
    Var(V),
}

/// HS `instance (Show v, Show c) => Show (Lit c v)` (VTerm.hs:98-100): a
/// literal writes its payload, with no constructor name around it.
impl<C: fmt::Display, V: fmt::Display> fmt::Display for Lit<C, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Con(c) => write!(f, "{c}"),
            Lit::Var(v) => write!(f, "{v}"),
        }
    }
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
    t.for_each_lit(|literal| {
        if let Lit::Var(v) = literal {
            out.push(v.clone());
        }
    });
}

/// `True` iff `t` contains no variable literals (i.e. is ground).
/// Short-circuits on the first variable without collecting a variable list.
/// Unary paths need no continuation allocation.
pub fn is_ground_vterm<C, V>(t: &VTerm<C, V>) -> bool {
    walk_terms(std::slice::from_ref(t), |node| match node {
        Term::Lit(Lit::Var(_)) => ControlFlow::Break(()),
        _ => ControlFlow::Continue(true),
    })
    .is_continue()
}

/// `occursVTerm v t`: whether `v` appears anywhere in `t`.
pub fn occurs_vterm<C, V: PartialEq>(v: &V, t: &VTerm<C, V>) -> bool {
    walk_terms(std::slice::from_ref(t), |node| match node {
        Term::Lit(Lit::Var(w)) if w == v => ControlFlow::Break(()),
        _ => ControlFlow::Continue(true),
    })
    .is_break()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::pair_sym;
    use crate::term::f_app_no_eq;

    type V = &'static str;
    type C = u32;

    /// `Con` before `Var`, the variant order of HS's `Lit c v`.  `Term`'s
    /// `Ord` reads this when it sorts the arguments of an AC term, so it
    /// decides printed argument order.
    #[test]
    fn lit_ord_puts_constants_before_variables() {
        let c: Lit<C, V> = Lit::Con(1);
        let v: Lit<C, V> = Lit::Var("x");
        assert!(c < v);
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
        // The in-order sibling keeps the traversal order, and it also keeps
        // the duplicates.  `freesSapicTerm` and the SAPIC binder walks depend
        // on first-appearance order.  The function must therefore not use
        // set semantics.
        assert_eq!(vars_vterm_in_order(&t), vec!["y", "x", "y"]);
    }

    #[test]
    fn occurs_finds_variable() {
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), const_term(0)]);
        assert!(occurs_vterm(&"x", &t));
        assert!(!occurs_vterm(&"z", &t));
        assert!(!is_ground_vterm(&t), "one variable anywhere ⇒ not ground");
    }

    #[test]
    fn ground_terms_contain_no_variables() {
        let t: VTerm<C, V> = f_app_no_eq(
            pair_sym(),
            vec![
                const_term(2),
                f_app_no_eq(pair_sym(), vec![const_term(1), const_term(2)]),
            ],
        );
        assert!(is_ground_vterm(&t), "constants only ⇒ ground");
    }

    #[test]
    fn deep_variable_scans_preserve_order_and_membership() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term: VTerm<u32, &str> = f_app_no_eq(
                    pair_sym(),
                    vec![
                        var_term("y"),
                        f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("y")]),
                    ],
                );
                let mut ground = const_term::<_, &str>(0u32);
                for _ in 0..8192 {
                    term = f_app_no_eq(crate::builtin::hash_sym(), vec![term]);
                    ground = f_app_no_eq(crate::builtin::hash_sym(), vec![ground]);
                }
                assert_eq!(vars_vterm_in_order(&term), vec!["y", "x", "y"]);
                assert_eq!(vars_vterm(&term), vec!["x", "y"]);
                assert!(occurs_vterm(&"x", &term));
                assert!(!occurs_vterm(&"z", &term));
                assert!(!is_ground_vterm(&term));
                assert!(is_ground_vterm(&ground));
                assert!(vars_vterm(&ground).is_empty());
                assert!(!occurs_vterm(&"x", &ground));
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
