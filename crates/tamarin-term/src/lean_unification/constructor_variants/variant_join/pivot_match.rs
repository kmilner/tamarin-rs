//! Decide simultaneous flat AC matches from a coordinate which assigns each
//! rigid subject factor to exactly one pattern variable. Rows use canonical
//! flattened/sorted terms, so factor equality reflects structural B-equivalence.
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_unification::{ac_sort, residual, subsort, Error};
use crate::lterm::{LNTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::FxHashMap;

fn factors(t: &LNTerm, symbol: AcSym) -> Option<&[LNTerm]> {
    match t {
        Term::App(FunSym::Ac(f), args) if *f == symbol => Some(args),
        _ => None,
    }
}

fn bag(terms: &[LNTerm], width: usize) -> Option<FxHashMap<&LNTerm, Vec<usize>>> {
    let mut columns = FxHashMap::default();
    for term in terms {
        if columns.insert(term, vec![0; width]).is_some() {
            return None;
        }
    }
    Some(columns)
}

enum Decision {
    Clash,
    Witness(Subst<Name, LVar>),
}

pub(super) fn decide(
    equations: &[Equal<LNTerm>],
    seed: &FxHashMap<LVar, LNTerm>,
    budget: &mut usize,
) -> Result<Option<bool>, Error> {
    match classify(equations, seed, budget) {
        Some(Decision::Clash) => Ok(Some(false)),
        Some(Decision::Witness(subst)) => {
            if !residual::charge_expansion(budget, equations.iter().map(|e| &e.lhs), Some(&subst))?
            {
                return Ok(None);
            }
            // Subjects are rigid, including any variables shared with patterns.
            Ok(equations
                .iter()
                .all(|e| apply_vterm(&subst, e.lhs.clone()) == e.rhs)
                .then_some(true))
        }
        None => Ok(None),
    }
}

/// Each pivot factor occurs once. In every other row it occurs as often
/// as its owner. A group of owners with identical profiles needs at least
/// one distinct factor per owner. OpenMatch.Profiles.refutes_canonical
/// proves that a violation rules out all simultaneous matches.
fn classify(
    equations: &[Equal<LNTerm>],
    seed: &FxHashMap<LVar, LNTerm>,
    budget: &mut usize,
) -> Option<Decision> {
    let Term::App(FunSym::Ac(symbol), _) = &equations.first()?.lhs else {
        return None;
    };
    if equations.len() < 2 {
        return None;
    }
    let rows: Vec<_> = equations
        .iter()
        .map(|e| Some((factors(&e.lhs, *symbol)?, factors(&e.rhs, *symbol)?)))
        .collect::<Option<_>>()?;
    let visits = rows.iter().try_fold(0usize, |total, (p, s)| {
        total.checked_add(p.len())?.checked_add(s.len())
    })?;
    for (p, s) in &rows {
        let work = p
            .len()
            .checked_add(s.len())?
            .checked_mul(rows.len())?
            .checked_add(visits)?;
        *budget = budget.checked_sub(work)?;
        if !p.iter().all(|t| {
            matches!(t, Term::Lit(Lit::Var(v)) if
            !seed.contains_key(v) && subsort(ac_sort(*symbol), v.sort))
        }) {
            continue;
        }
        let Some(mut keys) = bag(p, rows.len()) else {
            continue;
        };
        let Some(mut subjects) = bag(s, rows.len()) else {
            continue;
        };
        if !rows
            .iter()
            .all(|(lhs, _)| lhs.iter().all(|x| keys.contains_key(x)))
        {
            continue;
        }
        for (i, (lhs, rhs)) in rows.iter().enumerate() {
            for x in lhs.iter() {
                keys.get_mut(x).expect("all pattern factors occur in pivot")[i] += 1;
            }
            for t in rhs.iter() {
                let Some(profile) = subjects.get_mut(t) else {
                    return Some(Decision::Clash);
                };
                profile[i] += 1;
            }
        }
        let mut groups = FxHashMap::<_, (Vec<LVar>, Vec<&LNTerm>)>::default();
        for (key, profile) in keys {
            let Term::Lit(Lit::Var(v)) = key else {
                return None;
            };
            groups.entry(profile).or_default().0.push(*v);
        }
        for (term, profile) in subjects {
            let Some((_, atoms)) = groups.get_mut(&profile) else {
                return Some(Decision::Clash);
            };
            atoms.push(term);
        }
        let mut bindings = Vec::new();
        for (owners, mut atoms) in groups.into_values() {
            if owners.len() > atoms.len() {
                return Some(Decision::Clash);
            }
            let (last, others) = owners.split_last()?;
            for owner in others {
                bindings.push((*owner, atoms.pop()?.clone()));
            }
            bindings.push((
                *last,
                f_app_ac(*symbol, atoms.into_iter().cloned().collect()),
            ));
        }
        return Some(Decision::Witness(Subst::from_list(bindings)));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::msg_var;
    use crate::lean_unification::{open_match, Outcome};
    use crate::lterm::pub_term;

    #[test]
    fn profile_decisions_agree_with_all_open_matches_on_small_bags() {
        let [a, b] = [msg_var("a", 0), msg_var("b", 0)];
        // a is also a subject atom and must stay rigid during substitution.
        let atoms = [a.clone(), pub_term("c"), pub_term("d")];
        let ac = |terms| f_app_ac(AcSym::Union, terms);
        let pivot = Equal::new(ac(vec![a.clone(), b.clone()]), ac(atoms.to_vec()));
        let mut outcomes = [0, 0];
        for (na, nb) in [(2, 0), (1, 1), (0, 2), (1, 2)] {
            let pattern = ac([vec![a.clone(); na], vec![b.clone(); nb]].concat());
            for multiplicities in 0..27 {
                let mut rhs = Vec::new();
                let mut digits = multiplicities;
                for atom in &atoms {
                    rhs.extend(std::iter::repeat_n(atom.clone(), digits % 3));
                    digits /= 3;
                }
                if rhs.len() < 2 {
                    continue;
                }
                let eqs = [pivot.clone(), Equal::new(pattern.clone(), ac(rhs))];
                let Outcome::Complete(matches) =
                    open_match::with_captures_budget(&eqs, vec![], &mut 100_000).unwrap()
                else {
                    panic!("small exhaustive reference exceeded its budget")
                };
                let result = decide(&eqs, &FxHashMap::default(), &mut 100_000)
                    .unwrap()
                    .unwrap();
                assert_eq!(result, !matches.is_empty(), "{eqs:?}");
                outcomes[usize::from(result)] += 1;
            }
        }
        assert!(outcomes.into_iter().all(|n| n > 0));
    }
}
