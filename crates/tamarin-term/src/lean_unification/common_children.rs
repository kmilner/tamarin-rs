//! Cancel identical full children of an AC term before solving the residual system.
use super::{initialize, tamarin_lean_cancel_common, Error, LEAN_THREAD};
use crate::lean_identity::IdentityTable;
use crate::lterm::LNTerm;

pub(super) fn residuals(
    left: &[LNTerm],
    right: &[LNTerm],
) -> Result<(Vec<LNTerm>, Vec<LNTerm>), Error> {
    let (l, r) = residual_refs(left, right)?;
    Ok((
        l.into_iter().cloned().collect(),
        r.into_iter().cloned().collect(),
    ))
}

// The matching worklist retains references to original operands across
// nested AC nodes. Decode the same cancellation packet without cloning trees.
pub(super) fn residual_refs<'a>(
    left: impl IntoIterator<Item = &'a LNTerm>,
    right: impl IntoIterator<Item = &'a LNTerm>,
) -> Result<(Vec<&'a LNTerm>, Vec<&'a LNTerm>), Error> {
    let mut ids = IdentityTable::<&LNTerm>::default();
    let mut intern = |t| ids.intern(t).ok_or(Error::InvalidStatus(255));
    let left = left
        .into_iter()
        .map(&mut intern)
        .collect::<Result<Vec<_>, _>>()?;
    let right = right
        .into_iter()
        .map(intern)
        .collect::<Result<Vec<_>, _>>()?;
    let mut left_out = vec![0; left.len()];
    let mut right_out = vec![0; right.len()];
    let mut left_len = 0;
    let mut right_len = 0;
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim bounds each result row by its side's capacity;
        // both input slices and output buffers live through the call.
        let code = unsafe {
            tamarin_lean_cancel_common(
                left.as_ptr(),
                left.len(),
                right.as_ptr(),
                right.len(),
                left_out.as_mut_ptr(),
                &mut left_len,
                right_out.as_mut_ptr(),
                &mut right_len,
            )
        };
        if code != 0 || left_len > left_out.len() || right_len > right_out.len() {
            return Err(Error::InvalidStatus(255));
        }
        let decode = |row: &[u64]| {
            row.iter()
                .map(|id| ids.get(*id).ok_or(Error::InvalidSubject(*id)))
                .collect::<Result<Vec<_>, Error>>()
        };
        Ok((
            decode(&left_out[..left_len])?,
            decode(&right_out[..right_len])?,
        ))
    })
}
