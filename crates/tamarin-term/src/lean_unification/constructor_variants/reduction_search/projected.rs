//! Compute distinct rule outputs without allocating matches for independent
//! variables erased by the RHS. Subject occurrences always remain frozen.
use super::*;
use crate::lean_unification::components::pattern_components;
use crate::lterm::HasFrees;
use crate::rewriting::Equal;

fn free_leaves(pattern: &LNTerm, subject: &LNTerm, rows: &mut Vec<Equal<LNTerm>>) -> bool {
    if let (Term::App(FunSym::NoEq(f), ps), Term::App(FunSym::NoEq(g), ss)) = (pattern, subject)
        && f == g
        && ps.len() == ss.len()
    {
        return ps
            .iter()
            .zip(ss.iter())
            .all(|(p, s)| free_leaves(p, s, rows));
    }
    if rows.len() >= 64 {
        return false;
    }
    rows.push(Equal {
        lhs: pattern.clone(),
        rhs: subject.clone(),
    });
    true
}

impl RuleTable {
    pub(super) fn projected_rule_values(
        &self,
        pattern: &LNTerm,
        rhs: &LNTerm,
        subject: &LNTerm,
        budget: &mut usize,
    ) -> Result<Option<BTreeSet<LNTerm>>, Error> {
        // Check the small, fixed rule before traversing the query. Commit the
        // inspection cost to the graph once an erased branching group exists.
        let mut left = *budget;
        if !charge_expansion(&mut left, [pattern], None)? {
            return Ok(None);
        }
        // Free matching alone cannot branch. The existing direct matcher also
        // handles rules in which every nondeterministic component is observable.
        let deterministic =
            |p: &LNTerm| p.all_fun_syms(|f| !matches!(f, FunSym::Ac(_) | FunSym::C(_)));
        if deterministic(pattern) {
            return Ok(None);
        }
        if !charge_expansion(&mut left, [rhs, subject], None)? {
            return Ok(None);
        }
        let keys = frees(rhs);
        let mut rows = Vec::new();
        if !free_leaves(pattern, subject, &mut rows) || rows.is_empty() {
            return Ok(None);
        }
        let mut parts = pattern_components(&rows);
        if parts.is_empty() {
            parts.push(rows);
        }
        let (observed, hidden): (Vec<_>, Vec<_>) = parts.into_iter().partition(|part| {
            part.iter().any(|e| {
                let mut live = false;
                e.lhs.for_each_free(&mut |v| {
                    live |= keys.binary_search(v).is_ok();
                });
                live
            })
        });
        if !hidden.iter().flatten().any(|e| !deterministic(&e.lhs)) {
            return Ok(None);
        }
        *budget = left;

        for part in hidden {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let public_rows: Vec<_> = part
                .iter()
                .map(|e| Equal {
                    lhs: e.rhs.clone(),
                    rhs: e.lhs.clone(),
                })
                .collect();
            let mut decision = None;
            if Self::may_be_ac_bag_match(&public_rows) {
                decision = self.ac_bag_has_match(&public_rows)?;
            }
            if decision.is_none() {
                decision = open_match::has_match_budget(&part, budget)?;
            }
            match decision {
                Some(true) => {}
                Some(false) => return Ok(Some(BTreeSet::new())),
                None => return Ok(None),
            }
        }

        let kept: Vec<_> = observed.into_iter().flatten().collect();
        let arms = if kept.is_empty() {
            vec![Vec::new()]
        } else {
            let Outcome::Complete(arms) =
                open_match::with_captures_budget(&kept, Vec::new(), budget)?
            else {
                return Ok(None);
            };
            arms
        };
        let mut values = BTreeSet::new();
        for arm in arms {
            let subst = Subst::from_list(arm);
            // A hidden group has an existential witness, so replay only the
            // kept equations. All variables in the RHS occur in these groups.
            for eq in &kept {
                if !charge_expansion(budget, [&eq.lhs], Some(&subst))? {
                    return Ok(None);
                }
                if apply_vterm(&subst, eq.lhs.clone()) != eq.rhs {
                    return Err(Error::InvalidStatus(255));
                }
            }
            if !charge_expansion(budget, [rhs], Some(&subst))? {
                return Ok(None);
            }
            values.insert(apply_vterm(&subst, rhs.clone()));
        }
        Ok(Some(values))
    }
}
