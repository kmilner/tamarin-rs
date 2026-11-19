//! Finite term sizes are affine in the sizes of the variable images.
//! UnifierSize.refutes applies before abstracting compound AC operands.
use crate::function_symbols::FunSym;
use crate::lterm::{LNTerm, LVar};
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashMap;

pub(in crate::lean_unification) fn refutes(eq: &Equal<LNTerm>) -> bool {
    // Bound this optional refutation independently of the matrix solver.
    // A compact DAG can unfold to many occurrences of the same subtree.
    let mut remaining = 65_536;
    let mut counts = FxHashMap::default();
    let Some(left) = tally(&eq.lhs, -1, &mut counts, &mut remaining) else {
        return false;
    };
    let Some(right) = tally(&eq.rhs, 1, &mut counts, &mut remaining) else {
        return false;
    };
    match left.cmp(&right) {
        std::cmp::Ordering::Less => counts.values().all(|&delta| delta >= 0),
        std::cmp::Ordering::Greater => counts.values().all(|&delta| delta <= 0),
        std::cmp::Ordering::Equal => false,
    }
}

fn tally(
    term: &LNTerm,
    direction: i32,
    counts: &mut FxHashMap<LVar, i32>,
    remaining: &mut usize,
) -> Option<usize> {
    *remaining = remaining.checked_sub(1)?;
    match term {
        Term::Lit(Lit::Var(v)) => {
            *counts.entry(*v).or_default() += direction;
            Some(1)
        }
        Term::Lit(Lit::Con(_)) => Some(1),
        Term::App(f, args) => {
            // A flattened AC application represents n-1 binary nodes.
            let root = match f {
                FunSym::Ac(_) => args.len().checked_sub(1)?,
                FunSym::NoEq(_) | FunSym::C(_) => 1,
                FunSym::List => return None,
            };
            args.iter().try_fold(root, |size, child| {
                Some(size + tally(child, direction, counts, remaining)?)
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::function_symbols::{AcSym, FunSym};
    use crate::lterm::{pub_term, LSort};
    use crate::maude_proc::MaudeHandle;
    use crate::maude_sig::{hash_maude_sig, mset_maude_sig};
    use crate::term::f_app_ac;

    fn x(i: u64) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)))
    }
    fn sum(xs: Vec<LNTerm>) -> LNTerm {
        f_app_ac(AcSym::Union, xs)
    }

    #[test]
    fn size_clash_respects_shared_variables_and_flattened_ac() {
        let xs: Vec<_> = (0..8).map(x).collect();
        let eq = Equal {
            lhs: sum(xs.clone()),
            rhs: sum(xs.into_iter().map(hash).collect()),
        };
        assert!(refutes(&eq));
        assert!(refutes(&Equal {
            lhs: eq.rhs.clone(),
            rhs: eq.lhs.clone()
        }));
        let original = (0..8).collect();
        let mut budget = crate::lean_unification::residual::Budget::new();
        let solutions =
            crate::lean_unification::residual::solve(vec![eq.clone()], &original, &mut budget)
                .unwrap();
        assert!(solutions.unwrap().is_empty());
        // An additional independent variable can absorb the size difference.
        let flexible = Equal {
            lhs: sum(vec![x(0), x(1)]),
            rhs: sum(vec![hash(x(0)), pub_term("a")]),
        };
        assert!(!refutes(&flexible));
        if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_none() {
            let sig = mset_maude_sig().merge(hash_maude_sig());
            let native =
                MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::NativeOnly)
                    .unwrap();
            assert!(native.unify(std::slice::from_ref(&eq)).unwrap().is_empty());
            assert!(!native
                .unify(std::slice::from_ref(&flexible))
                .unwrap()
                .is_empty());
        }
        if let Some(path) = tamarin_test_support::require_maude_path() {
            let oracle = MaudeHandle::start_with_backend(
                &path,
                mset_maude_sig().merge(hash_maude_sig()),
                AlgebraBackend::Maude,
            )
            .unwrap();
            for width in 2..=4 {
                let vs: Vec<_> = (0..width).map(x).collect();
                let cyclic = Equal {
                    lhs: sum(vs.clone()),
                    rhs: sum(vs.into_iter().map(hash).collect()),
                };
                assert!(oracle.unify_via_maude(&[cyclic]).unwrap().is_empty());
            }
            assert!(!oracle.unify_via_maude(&[flexible]).unwrap().is_empty());
        }
        // Raw binary bracketing and a flattened ternary have equal model size.
        let three = [x(0), x(1), x(2)];
        let raw = Term::App(
            FunSym::Ac(AcSym::Union),
            vec![three[0].clone(), sum(three[1..].to_vec())].into(),
        );
        assert!(!refutes(&Equal {
            lhs: raw,
            rhs: sum(three.to_vec())
        }));
    }
}
