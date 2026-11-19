//! Instantiate the two equations in each Lean AC pivot recipe. An operand
//! slot denotes a full term, so repeated variables across equations stay shared.
use super::super::{ac_children, ac_sort, initialize, Error, MatchRows, LEAN_THREAD};
use crate::function_symbols::AcSym;
use crate::lterm::{LNTerm, LVar};
use crate::rewriting::Equal;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::FxHashSet;

unsafe extern "C" {
    fn tamarin_lean_open_match_select(rigid: u64, subject: u64) -> *mut std::ffi::c_void;
    fn tamarin_lean_ac_pivot(size: u64) -> *mut std::ffi::c_void;
}

// Find the sole variable capable of absorbing several factors. All other
// occurrences must stay indivisible under every sorted substitution.
fn open_slot(symbol: AcSym, side: &[LNTerm]) -> Option<(usize, LVar)> {
    let mut open = None;
    for (i, t) in side.iter().enumerate() {
        if !super::indivisible(symbol, t) {
            let Term::Lit(Lit::Var(v)) = t else {
                return None;
            };
            if v.sort != ac_sort(symbol) || open.replace((i, *v)).is_some() {
                return None;
            }
        }
    }
    open
}

fn read_equation(
    symbol: AcSym,
    slots: &[LNTerm],
    key: u64,
    image: &[u64],
) -> Result<Equal<LNTerm>, Error> {
    let slot = |id: u64| {
        usize::try_from(id)
            .ok()
            .and_then(|i| slots.get(i))
            .cloned()
            .ok_or(Error::InvalidStatus(255))
    };
    if image.is_empty() {
        return Err(Error::InvalidStatus(255));
    }
    Ok(Equal {
        lhs: slot(key)?,
        rhs: f_app_ac(
            symbol,
            image.iter().copied().map(slot).collect::<Result<_, _>>()?,
        ),
    })
}

pub(in crate::lean_unification) fn split(
    eqs: &[Equal<LNTerm>],
    reserved: &FxHashSet<u64>,
) -> Result<Option<Vec<Vec<Equal<LNTerm>>>>, Error> {
    for (pos, eq) in eqs.iter().enumerate() {
        let Some((symbol, left, right)) = ac_children(eq) else {
            continue;
        };
        let (one, many) = if left.len() == 2 {
            (left, right)
        } else {
            (right, left)
        };
        if one.len() != 2 || !(2..=33).contains(&many.len()) {
            continue;
        }
        let (Some((xi, x)), Some((yi, y))) = (open_slot(symbol, one), open_slot(symbol, many))
        else {
            continue;
        };
        let a = &one[1 - xi];
        if x == y || many.contains(a) {
            continue;
        }
        let fresh = (0..=u64::MAX)
            .find(|i| !reserved.contains(i))
            .ok_or(Error::FreshVariableOverflow)?;
        let witness = Term::Lit(Lit::Var(LVar::new("x", ac_sort(symbol), fresh)));
        let mut slots = vec![one[xi].clone(), a.clone(), many[yi].clone(), witness];
        slots.extend(
            many.iter()
                .enumerate()
                .filter(|(i, _)| *i != yi)
                .map(|(_, t)| t.clone()),
        );
        initialize()?;
        return LEAN_THREAD.with(|_| {
            // SAFETY: MatchRows owns the returned array until it drops on this thread.
            let raw = unsafe { tamarin_lean_ac_pivot((many.len() - 1) as u64) };
            if raw.is_null() {
                return Ok(None);
            }
            let rows = MatchRows::new(raw)?;
            if rows.count() != 1 {
                return Err(Error::InvalidStatus(255));
            }
            let mut words = [0; 38];
            let mut branches = Vec::with_capacity(rows.rows(0));
            for i in 0..rows.rows(0) {
                let n = rows.copy_row(0, i, &mut words)?;
                let [key, count, rest @ ..] = &words[..n] else {
                    return Err(Error::InvalidStatus(255));
                };
                let Some((image, next)) = rest.split_at_checked(
                    usize::try_from(*count).map_err(|_| Error::InvalidStatus(255))?,
                ) else {
                    return Err(Error::InvalidStatus(255));
                };
                let Some((&other, tail)) = next.split_first() else {
                    return Err(Error::InvalidStatus(255));
                };
                let mut branch = vec![
                    read_equation(symbol, &slots, *key, image)?,
                    read_equation(symbol, &slots, other, tail)?,
                ];
                branch.extend(eqs[..pos].iter().chain(&eqs[pos + 1..]).cloned());
                if !branches.contains(&branch) {
                    branches.push(branch);
                }
            }
            Ok(Some(branches))
        });
    }
    Ok(None)
}

/// In X * A = B₁ * … * Bₙ, a sorted instance of A and each B is a
/// single factor. All unselected occurrences belong to X.
pub(in crate::lean_unification) fn split_indivisible(
    eqs: &[Equal<LNTerm>],
) -> Result<Option<Vec<Vec<Equal<LNTerm>>>>, Error> {
    select_owner(eqs, None)
}

/// In A * L = B₁ * … * Bₙ only A must remain indivisible. An owner B
/// can equal A or contain a nonempty surplus W. The latter branch uses
/// B = A * W and L = W * (the other occurrences).
pub(in crate::lean_unification) fn split_owner(
    eqs: &[Equal<LNTerm>],
    reserved: &FxHashSet<u64>,
) -> Result<Option<Vec<Vec<Equal<LNTerm>>>>, Error> {
    select_owner(eqs, Some(reserved))
}

fn select_owner(
    eqs: &[Equal<LNTerm>],
    reserved: Option<&FxHashSet<u64>>,
) -> Result<Option<Vec<Vec<Equal<LNTerm>>>>, Error> {
    for (pos, eq) in eqs.iter().enumerate() {
        let Some((symbol, lhs, rhs)) = ac_children(eq) else {
            continue;
        };
        for (side, opposite) in [(lhs, rhs), (rhs, lhs)] {
            if !(2..=64).contains(&opposite.len()) {
                continue;
            }
            let pivot = if reserved.is_some() {
                side.iter().position(|t| super::indivisible(symbol, t))
            } else if side.len() == 2 && opposite.iter().all(|t| super::indivisible(symbol, t)) {
                open_slot(symbol, side).map(|(i, _)| 1 - i)
            } else {
                None
            };
            let Some(i) = pivot else { continue };
            let atom = &side[i];
            let fringe = f_app_ac(
                symbol,
                side[..i].iter().chain(&side[i + 1..]).cloned().collect(),
            );
            let cancellable = opposite.contains(atom);
            let remainder = if let Some(used) = reserved
                && !cancellable
                && opposite.iter().any(|b| !super::indivisible(symbol, b))
            {
                let fresh = (0..=u64::MAX)
                    .find(|i| !used.contains(i))
                    .ok_or(Error::FreshVariableOverflow)?;
                Some(Term::Lit(Lit::Var(LVar::new("x", ac_sort(symbol), fresh))))
            } else {
                None
            };
            initialize()?;
            return LEAN_THREAD.with(|_| {
                // SAFETY: MatchRows owns the returned selection packet on this thread.
                let raw = unsafe { tamarin_lean_open_match_select(1, opposite.len() as u64) };
                if raw.is_null() {
                    return Ok(None);
                }
                let packet = MatchRows::new(raw)?;
                if packet.count() != 1 {
                    return Err(Error::InvalidStatus(255));
                }
                let mut indices = vec![0; opposite.len()];
                let mut selected = FxHashSet::default();
                let mut branches = Vec::new();
                let mut emit = |lhs, rhs, rest| {
                    let mut branch = vec![
                        Equal { lhs, rhs },
                        Equal {
                            lhs: fringe.clone(),
                            rhs: rest,
                        },
                    ];
                    branch.extend(eqs[..pos].iter().chain(&eqs[pos + 1..]).cloned());
                    branches.push(branch);
                };
                for k in 0..packet.rows(0) {
                    tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                    if packet.copy_row(0, k, &mut indices)? != opposite.len() {
                        return Err(Error::InvalidStatus(255));
                    }
                    let operand = |&j: &u64| {
                        usize::try_from(j)
                            .ok()
                            .and_then(|j| opposite.get(j))
                            .ok_or(Error::InvalidStatus(255))
                    };
                    let owner = operand(&indices[0])?;
                    // Equal choices have equal complementary multisets. A
                    // common occurrence can always be cancelled directly.
                    if (cancellable && atom != owner) || !selected.insert(owner) {
                        continue;
                    }
                    let rest = f_app_ac(
                        symbol,
                        indices[1..]
                            .iter()
                            .map(|j| operand(j).cloned())
                            .collect::<Result<_, _>>()?,
                    );
                    emit(atom.clone(), owner.clone(), rest.clone());
                    if let Some(w) = &remainder
                        && !super::indivisible(symbol, owner)
                    {
                        emit(
                            owner.clone(),
                            f_app_ac(symbol, vec![atom.clone(), w.clone()]),
                            f_app_ac(symbol, vec![w.clone(), rest]),
                        );
                    }
                }
                Ok(Some(branches))
            });
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{pub_term, LSort};

    #[test]
    fn indivisible_split_accepts_either_side_at_equal_width_and_defers_other_domains() {
        let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
        let x = var("x", LSort::Msg);
        let fresh = var("r", LSort::Fresh);
        let sum = |ts| f_app_ac(AcSym::Union, ts);
        let narrow = sum(vec![x.clone(), fresh.clone()]);
        let wide = sum(vec![pub_term("a"), pub_term("b")]);
        let eq = |lhs, rhs| Equal { lhs, rhs };
        for q in [
            eq(narrow.clone(), wide.clone()),
            eq(wide.clone(), narrow.clone()),
        ] {
            assert_eq!(split_indivisible(&[q]).unwrap().unwrap().len(), 2);
        }
        for other in [sum(vec![pub_term("a"); 65]), sum(vec![x, pub_term("a")])] {
            assert!(split_indivisible(&[eq(narrow.clone(), other)])
                .unwrap()
                .is_none());
        }
        let already_equal = sum(vec![pub_term("a"), fresh.clone(), fresh]);
        assert_eq!(
            split_indivisible(&[eq(narrow, already_equal)])
                .unwrap()
                .unwrap()
                .len(),
            1
        );
    }
}
