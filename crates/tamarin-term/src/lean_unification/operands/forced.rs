//! Recover equations between original operands from simultaneous AC rows.
use super::super::{initialize, Error, WordSlice, LEAN_THREAD};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::LNTerm;
use crate::rewriting::Equal;
use crate::term::Term;
use std::collections::BTreeMap;

unsafe extern "C" {
    fn tamarin_lean_forced_operand_classes(
        width: u64,
        sides: *const WordSlice,
        count: usize,
        labels: *mut u64,
    ) -> u8;
}

fn head(term: &LNTerm) -> Option<AcSym> {
    match term {
        Term::App(FunSym::Ac(f), _) => Some(*f),
        _ => None,
    }
}

fn factors(symbol: AcSym, term: &LNTerm) -> &[LNTerm] {
    match term {
        Term::App(FunSym::Ac(f), xs) if *f == symbol => xs,
        _ => std::slice::from_ref(term),
    }
}

/// Every ID refers to one term across both sides of all rows in this group.
/// Class labels are opaque. Connect peers to their first member so any
/// permutation of the labels produces exactly the same equations.
fn collect(
    symbol: AcSym,
    equations: &[&Equal<LNTerm>],
    added: &mut Vec<Equal<LNTerm>>,
) -> Result<(), Error> {
    let mut columns = IdentityTable::default();
    let mut sides = Vec::with_capacity(2 * equations.len());
    for term in equations.iter().flat_map(|e| [&e.lhs, &e.rhs]) {
        let factors = factors(symbol, term);
        if factors.is_empty() || factors.len() > 4096 {
            return Ok(());
        }
        let mut row = Vec::with_capacity(factors.len());
        for factor in factors {
            let Some(id) = columns.intern(factor).filter(|&id| id < 4096) else {
                return Ok(());
            };
            row.push(id);
        }
        sides.push(row);
    }
    initialize()?;
    let slices: Vec<_> = sides.iter().map(|s| WordSlice::new(s)).collect();
    let mut labels = vec![0; columns.len()];
    // SAFETY: the shim copies all input slices and writes exactly width
    // labels on success. No references cross the call boundary.
    let status = LEAN_THREAD.with(|_| unsafe {
        tamarin_lean_forced_operand_classes(
            columns.len() as u64,
            slices.as_ptr(),
            slices.len(),
            labels.as_mut_ptr(),
        )
    });
    match status {
        0 => return Ok(()),
        1 => {}
        invalid => return Err(Error::InvalidStatus(invalid)),
    }
    let mut first: Vec<Option<&LNTerm>> = vec![None; columns.len()];
    for (label, &term) in labels.into_iter().zip(columns.values()) {
        let representative = first
            .get_mut(usize::try_from(label).map_err(|_| Error::InvalidAtom(label))?)
            .ok_or(Error::InvalidAtom(label))?;
        if let Some(peer) = *representative {
            added.push(Equal {
                lhs: peer.clone(),
                rhs: term.clone(),
            });
        } else {
            *representative = Some(term);
        }
    }
    Ok(())
}

pub(in crate::lean_unification) fn consequences(
    equations: &[Equal<LNTerm>],
) -> Result<Vec<Equal<LNTerm>>, Error> {
    let mut added = Vec::new();
    if !(1..=64).contains(&equations.len()) {
        return Ok(added);
    }
    let mut groups = BTreeMap::<_, Vec<_>>::new();
    for e in equations {
        let left = head(&e.lhs);
        let right = head(&e.rhs);
        if let Some(f) = left {
            groups.entry(f).or_default().push(e);
        }
        if let Some(f) = right.filter(|r| Some(*r) != left) {
            groups.entry(f).or_default().push(e);
        }
    }
    for (f, rows) in groups {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        collect(f, &rows, &mut added)?;
    }
    Ok(added)
}
