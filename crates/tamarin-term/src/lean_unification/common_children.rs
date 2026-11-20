//! Cancel identical full children of an AC term before solving the residual system.
use super::{ac_children, initialize, tamarin_lean_cancel_common, Error, LEAN_THREAD};
use crate::lean_identity::IdentityTable;
use crate::lterm::{HasFrees, LNTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use std::collections::BTreeSet;

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

// A VFresh range has its own variable scope. If an ordinary unifier mentions
// an unbound input variable, export an explicit binding to the same witness
// for that input too, including when it appears in a factored alias.
pub(super) fn freshen(
    ordinary: &Subst<Name, LVar>,
    original: &[Equal<LNTerm>],
) -> Result<Vec<(LVar, LNTerm)>, Error> {
    let mut floor = 0;
    for eq in original {
        eq.lhs.for_each_free(&mut |v| floor = floor.max(v.idx));
        eq.rhs.for_each_free(&mut |v| floor = floor.max(v.idx));
    }
    let mut retained = BTreeSet::new();
    for t in ordinary.range() {
        t.for_each_free(&mut |v| {
            retained.insert(*v);
        });
    }
    let mut aliases = Vec::with_capacity(retained.len());
    for v in retained {
        floor = floor.checked_add(1).ok_or(Error::FreshVariableOverflow)?;
        aliases.push((v, Term::Lit(Lit::Var(LVar { idx: floor, ..v }))));
    }
    Ok(Subst::from_list(aliases).compose(ordinary).to_list())
}

/// Jointly factor every equation each cancellation exposes. The caller keeps
/// ownership of the residual system, including any newly visible C roots.
pub(super) enum Simplification {
    Unchanged,
    Reduced,
    Contradiction,
    Unconfirmed,
}

pub(super) fn simplify(
    table: &super::RuleTable,
    current: &mut Vec<Equal<LNTerm>>,
    bindings: &mut Subst<Name, LVar>,
) -> Result<Simplification, Error> {
    let mut status = Simplification::Unchanged;
    while current.iter().any(|eq| ac_children(eq).is_some()) {
        let mut reduced = Vec::with_capacity(current.len());
        let mut changed = false;
        for eq in current.drain(..) {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some((f, left, right)) = ac_children(&eq) else {
                reduced.push(eq);
                continue;
            };
            let (l, r) = residuals(left, right)?;
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            if l.len() == left.len() && r.len() == right.len() {
                reduced.push(eq);
                continue;
            }
            changed = true;
            match (l.is_empty(), r.is_empty()) {
                (true, true) => {}
                (true, false) | (false, true) => return Ok(Simplification::Contradiction),
                (false, false) => reduced.push(Equal {
                    lhs: f_app_ac(f, l),
                    rhs: f_app_ac(f, r),
                }),
            }
        }
        if !changed {
            *current = reduced;
            break;
        }
        // With a fixed variable inventory each cancellation strictly shortens
        // the system. If factoring expands a term, it also eliminates one or
        // more variables. No step introduces a new search variable.
        let Some((extra, pending)) = crate::unification::unify_lterm_factored(
            &crate::maude_types::sort_of_name,
            reduced.clone(),
        ) else {
            return Ok(if table.refutes_factor_clash(&reduced)? {
                Simplification::Contradiction
            } else {
                Simplification::Unconfirmed
            });
        };
        if !table.accepts_factor(&reduced, &extra, &pending)? {
            return Ok(Simplification::Unconfirmed);
        }
        *bindings = extra.compose(bindings);
        *current = pending;
        status = Simplification::Reduced;
    }
    Ok(status)
}
