//! Reconcile homogeneous AC answers with the original operands. The Lean
//! contract ProjectedOperands.Correct connects interned occurrences to tagged residuals.
use super::homogeneous::{Allocation, MatrixCache};
use super::{ac_sort, initialize, subsort, Error};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, LNTerm};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::FxHashSet;

pub(super) fn indivisible(symbol: AcSym, t: &LNTerm) -> bool {
    match t {
        Term::Lit(Lit::Var(v)) => !subsort(ac_sort(symbol), v.sort),
        Term::Lit(Lit::Con(_)) => true,
        Term::App(f, _) => *f != FunSym::Ac(symbol),
    }
}

pub(super) fn flatten<'a>(symbol: AcSym, t: &'a LNTerm, factors: &mut Vec<&'a LNTerm>) {
    if let Term::App(FunSym::Ac(f), args) = t
        && *f == symbol
    {
        for arg in args.iter() {
            flatten(symbol, arg, factors);
        }
    } else {
        factors.push(t);
    }
}

pub(super) fn allocate<'a>(
    symbol: AcSym,
    eqs: &'a [Equal<LNTerm>],
    reserved: &FxHashSet<u64>,
    matrices: &mut MatrixCache,
    remaining_calls: &mut usize,
) -> Result<Allocation<impl DoubleEndedIterator<Item = Vec<Equal<LNTerm>>> + use<'a>>, Error> {
    let outer = FunSym::Ac(symbol);
    let (matrix, mut pending): (Vec<_>, Vec<_>) = eqs.iter().partition(|e| {
        [&e.lhs, &e.rhs]
            .iter()
            .any(|t| matches!(t, Term::App(f, _) if *f == outer))
    });
    if matrix.len() > 64 {
        return Ok(Allocation::Unsupported);
    }
    let sort = ac_sort(symbol);
    let mut columns = IdentityTable::default();
    let mut rows = Vec::with_capacity(2 * matrix.len());
    let mut factors = Vec::new();
    for t in matrix.iter().flat_map(|e| [&e.lhs, &e.rhs]) {
        if !subsort(sort_of_lterm(t, sort_of_name), sort) {
            return Ok(Allocation::Unsupported);
        }
        flatten(symbol, t, &mut factors);
        let mut row = Vec::with_capacity(factors.len());
        for factor in factors.drain(..) {
            let Some(index) = columns.intern(factor).filter(|&i| i < 32) else {
                return Ok(Allocation::Unsupported);
            };
            row.push(index);
        }
        rows.push(row);
    }
    // An equality between two existing columns can constrain the basis
    // directly, without adding dimensions or introducing an AC residual.
    pending.retain(|e| {
        if rows.len() < 128
            && let (Some(l), Some(r)) = (columns.id(&e.lhs), columns.id(&e.rhs))
        {
            for i in [l, r] {
                rows.push(vec![i]);
            }
            false
        } else {
            true
        }
    });
    let width = columns.len();
    let mut mask = 0u64;
    for (i, term) in columns.values().iter().enumerate() {
        if indivisible(symbol, term) {
            mask |= 1 << i;
        }
    }
    initialize()?;
    let result = matrices.images(remaining_calls, symbol, reserved, width, mask, rows)?;
    Ok(result.map(|branches| {
        branches.into_iter().map(move |branch| {
            columns
                .values()
                .iter()
                .zip(branch)
                .map(|(&t, image)| Equal {
                    lhs: image,
                    rhs: t.clone(),
                })
                .chain(pending.iter().map(|&eq| eq.clone()))
                .collect()
        })
    }))
}

mod ground_branches;
mod pivot;
mod size_clash;
pub(super) use ground_branches::split as split_ground;
pub(super) use pivot::{split as split_binary_pivot, split_indivisible, split_owner};
pub(super) use size_clash::refutes as refutes_size;
