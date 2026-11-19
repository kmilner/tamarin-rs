//! Simplify a conjunction of rigid-subject matches under the same captures.
use crate::function_symbols::FunSym;
use crate::lean_unification::{residual, Error};
use crate::lterm::{sort_of_lterm, HasFrees, LNTerm, LVar};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) enum RowMatch {
    Clash,
    Deferred,
    Pending(Vec<Equal<LNTerm>>),
}

/// Cancel every fully determined factor under AC. A single unmatched
/// variable must take the entire nonempty remainder. Its capture can settle
/// other equations in the same row, including ones at different heads.
pub(super) fn residual_row_matches(
    mut pending: Vec<(&LNTerm, &LNTerm)>,
    captures: &mut FxHashMap<LVar, LNTerm>,
) -> Result<RowMatch, Error> {
    let mut nodes = residual::MAX_EXPANDED;
    // Repeated observations can give exactly the same ordered pair as a
    // caller image. Keep one obligation for this shared directional match.
    if pending.len() > 1 {
        let mut unique = FxHashSet::default();
        pending.retain(|pair| unique.insert(*pair));
    }
    let mut equations: Vec<_> = pending
        .into_iter()
        .map(|(p, s)| Equal {
            lhs: p.clone(),
            rhs: s.clone(),
        })
        .collect();
    loop {
        let before = captures.len();
        let subst = Subst::from_list(captures.iter().map(|(v, t)| (*v, t.clone())));
        let fixed = |p: &LNTerm| {
            let mut known = true;
            p.for_each_free(&mut |v| known &= captures.contains_key(v));
            known
        };
        let mut next = Vec::new();
        let mut forced = Vec::new();
        for mut eq in equations {
            if fixed(&eq.lhs) {
                if !residual::charge_expansion(&mut nodes, [&eq.lhs], Some(&subst))? {
                    return Ok(RowMatch::Deferred);
                }
                if apply_vterm(&subst, eq.lhs) != eq.rhs {
                    return Ok(RowMatch::Clash);
                }
                continue;
            }
            if let (Term::App(FunSym::Ac(f), ps), Term::App(FunSym::Ac(g), ss)) = (&eq.lhs, &eq.rhs)
                && f == g
                && ps.iter().any(&fixed)
            {
                let mut rigid = Vec::new();
                let mut open = Vec::new();
                for p in ps.iter() {
                    if fixed(p) {
                        if !residual::charge_expansion(&mut nodes, [p], Some(&subst))? {
                            return Ok(RowMatch::Deferred);
                        }
                        match apply_vterm(&subst, p.clone()) {
                            Term::App(FunSym::Ac(head), xs) if head == *f => {
                                rigid.extend(xs.iter().cloned())
                            }
                            atom => rigid.push(atom),
                        }
                    } else {
                        open.push(p.clone());
                    }
                }
                let (missing, rest) =
                    crate::lean_unification::common_children::residual_refs(&rigid, ss.iter())?;
                if !missing.is_empty() || rest.len() < open.len() {
                    return Ok(RowMatch::Clash);
                }
                eq = Equal {
                    lhs: f_app_ac(*f, open),
                    rhs: f_app_ac(*f, rest.into_iter().cloned().collect()),
                };
            }
            if let Term::Lit(Lit::Var(v)) = eq.lhs {
                if !crate::lean_unification::subsort(sort_of_lterm(&eq.rhs, sort_of_name), v.sort) {
                    return Ok(RowMatch::Clash);
                }
                forced.push((v, eq.rhs));
            } else {
                next.push(eq);
            }
        }
        for (v, value) in forced {
            if captures.get(&v).is_some_and(|old| old != &value) {
                return Ok(RowMatch::Clash);
            }
            captures.insert(v, value);
        }
        if before == captures.len() {
            // The same substitution must match every coordinate. Resolve a
            // short AC subject first so later partitions can reuse its captures.
            next.sort_by_key(|eq| match &eq.rhs {
                Term::App(FunSym::Ac(_), factors) => factors.len(),
                _ => 0,
            });
            return Ok(RowMatch::Pending(next));
        }
        equations = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::hash;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LSort};

    #[test]
    fn forced_captures_propagate_as_simultaneous_rigid_images() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 1);
        let z = LVar::new("z", LSort::Fresh, 2);
        let var = |v| Term::Lit(Lit::Var(v));
        let product = |args| f_app_ac(AcSym::Union, args);
        let a = pub_term("a");
        let original = product(vec![a.clone(), var(x)]);
        let first = product(vec![var(x), var(y)]);
        let subject = product(vec![original.clone(), var(z)]);
        let second = product(vec![hash(var(y)), var(z)]);
        let target = product(vec![hash(var(z)), var(z)]);
        let seed = FxHashMap::from_iter([(x, original)]);
        let mut captures = seed.clone();
        assert!(
            matches!(residual_row_matches(vec![(&second, &target), (&first, &subject)], &mut captures).unwrap(), RowMatch::Pending(ref eqs) if eqs.is_empty())
        );
        assert_eq!(captures[&y], var(z));
        assert_eq!(captures[&z], var(z));
        // A public constant cannot fill the fresh slot, even though it is a rigid leaf.
        let bad = product(vec![hash(var(z)), a]);
        assert!(matches!(
            residual_row_matches(vec![(&second, &bad), (&first, &subject)], &mut seed.clone())
                .unwrap(),
            RowMatch::Clash
        ));
    }

    #[test]
    fn repeated_large_capture_defers_before_expansion() {
        let key = LVar::new("k", LSort::Msg, 0);
        let key_term = Term::Lit(Lit::Var(key));
        let mut factors = vec![key_term; 256];
        factors.push(Term::Lit(Lit::Var(LVar::new("rest", LSort::Msg, 1))));
        let pattern = f_app_ac(AcSym::Union, factors);
        let subject = f_app_ac(AcSym::Union, vec![pub_term("a"); 257]);
        let image = f_app_ac(AcSym::Union, vec![pub_term("a"); 256]);
        assert!(matches!(
            residual_row_matches(
                vec![(&pattern, &subject)],
                &mut FxHashMap::from_iter([(key, image)])
            )
            .unwrap(),
            RowMatch::Deferred
        ));
    }
}
