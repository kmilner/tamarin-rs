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

fn side<'a>(
    symbol: AcSym,
    term: &'a LNTerm,
    columns: &mut IdentityTable<&'a LNTerm>,
) -> Option<Vec<u64>> {
    let mut row = Vec::new();
    let mut pending = vec![term];
    while let Some(t) = pending.pop() {
        if let Term::App(FunSym::Ac(f), xs) = t
            && *f == symbol
        {
            // Each pending term contributes at least one factor. Check the
            // expanded size before following shared or nested applications.
            if xs.len() < 2 || xs.len() > 4096 - row.len() - pending.len() {
                return None;
            }
            pending.extend(xs.iter().rev());
        } else {
            row.push(columns.intern(t).filter(|&id| id < 4096)?);
        }
    }
    Some(row)
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
        let Some(row) = side(symbol, term, &mut columns) else {
            return Ok(());
        };
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::pub_term;

    #[test]
    fn counts_every_occurrence_under_shared_nested_ac_nodes() {
        let raw = |xs: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Union), xs.into());
        let pair = raw(vec![pub_term("a"), pub_term("b")]);
        let nested = raw(vec![pair.clone(), pair]);
        assert_eq!(
            side(AcSym::Union, &nested, &mut IdentityTable::default()),
            Some(vec![0, 1, 0, 1])
        );
        let wide = (0..11).fold(nested, |t, _| raw(vec![t.clone(), t]));
        assert!(side(AcSym::Union, &wide, &mut IdentityTable::default()).is_none());
    }
}
