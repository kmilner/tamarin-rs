//! Search every interleaving of AC rule occurrences and changes inside their
//! operands. A rule can consume any subbag of at least two occurrences.
use super::{subgroups::ProperSubgroups, InputDomain, RuleTable};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_unification::{
    canonical_capture, open_match, residual::charge_expansion, subsort, Error, Outcome,
};
use crate::lterm::{frees, LNTerm, LSort, LVar};
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app, f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeSet;

enum Visit {
    Enter(LNTerm),
    Leave(LNTerm),
}

impl RuleTable {
    pub(super) fn ac_root_reduce(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        self.ac_reduction_search(term, 100_000)
    }

    fn ac_reduction_search(
        &self,
        term: &LNTerm,
        mut budget: usize,
    ) -> Result<Option<LNTerm>, Error> {
        let Term::App(FunSym::Ac(ac), _) = term else {
            return Ok(None);
        };
        if !self.ac_rules.contains_key(ac) || !self.admits_sorted(std::iter::once(term)) {
            return Ok(None);
        }
        let mut visits = vec![Visit::Enter(canonical_capture(term))];
        // An unfinished node is on the active DFS path. Reaching a finished
        // node shares its completed search, while a back edge defers the query.
        let mut finished = FxHashMap::default();
        let mut normal = None;
        while let Some(visit) = visits.pop() {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let state = match visit {
                Visit::Enter(t) => t,
                Visit::Leave(t) => {
                    finished.insert(t, true);
                    continue;
                }
            };
            if let Some(done) = finished.get(&state) {
                if !done {
                    return Ok(None);
                }
                continue;
            }
            let Some(next) = self.successors(&state, &mut budget)? else {
                return Ok(None);
            };
            if next.is_empty() {
                if normal.as_ref().is_some_and(|prior| prior != &state) {
                    return Ok(None);
                }
                normal.get_or_insert_with(|| state.clone());
                finished.insert(state, true);
            } else {
                finished.insert(state.clone(), false);
                visits.push(Visit::Leave(state));
                visits.extend(next.into_iter().map(Visit::Enter));
            }
        }
        Ok(normal)
    }

    fn successors(
        &self,
        state: &LNTerm,
        budget: &mut usize,
    ) -> Result<Option<BTreeSet<LNTerm>>, Error> {
        if !charge_expansion(budget, [state], None)? {
            return Ok(None);
        }
        let mut next = BTreeSet::new();
        let Term::App(head, children) = state else {
            return Ok(Some(next));
        };
        let rules = match head {
            FunSym::Ac(f) if self.ac_rules.contains_key(f) => Some((*f, &self.ac_rules[f])),
            FunSym::Ac(f) if !self.ac_patterns.contains_key(f) => None,
            FunSym::NoEq(f) if !self.patterns.contains_key(f) => None,
            // Uncompiled active buckets (including equations with named
            // literals) can close here only when the whole term is normal.
            _ => return Ok(self.irreducible_native(state)?.then_some(next)),
        };
        for (i, child) in children.iter().enumerate() {
            // Equal factors have the same untouched multiset when replaced.
            if matches!(head, FunSym::Ac(_)) && i > 0 && children[i - 1] == *child {
                continue;
            }
            let Some(changes) = self.successors(child, budget)? else {
                return Ok(None);
            };
            for changed in changes {
                let mut args = children.to_vec();
                args[i] = changed;
                if !charge_expansion(budget, &args, None)? {
                    return Ok(None);
                }
                next.insert(f_app(*head, args));
            }
        }
        let Some((head, rules)) = rules else {
            return Ok(Some(next));
        };
        let factors = children;
        if self.excludes_ac_rules(head, factors, false)? {
            return Ok(Some(next));
        }
        let mut patterns = Vec::with_capacity(rules.len());
        for rule in rules {
            if !self.admits_sorted([&rule.lhs, &rule.rhs].into_iter()) {
                return Ok(None);
            }
            let inputs = frees(&rule.lhs);
            if frees(&rule.rhs).iter().any(|v| !inputs.contains(v)) {
                return Ok(None);
            }
            patterns.push((canonical_capture(&rule.lhs), canonical_capture(&rule.rhs)));
        }
        let mut search = SubbagMatches {
            table: self,
            head,
            sort: super::super::ac_sort(head),
            patterns: &patterns,
            next: &mut next,
            budget,
        };
        if !search.extend(state, &[])? {
            return Ok(None);
        }
        if factors.len() > 2 {
            let Some(mut groups) = ProperSubgroups::new(factors.len())? else {
                if !search.with_extension(state)? {
                    return Ok(None);
                }
                return Ok(Some(next));
            };
            let mut seen = FxHashSet::default();
            while let Some(selected) = groups.next()? {
                tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                if *search.budget < selected.len() {
                    return Ok(None);
                }
                *search.budget -= selected.len();
                let mut taken = Vec::new();
                let mut rest = Vec::new();
                for (factor, &use_it) in factors.iter().zip(selected) {
                    if use_it {
                        taken.push(factor.clone());
                    } else {
                        rest.push(factor.clone());
                    }
                }
                let piece = f_app_ac(head, taken);
                // The complement in one fixed bag is determined by the
                // selected multiplicities, including repeated equal factors.
                if seen.insert(piece.clone()) && !search.extend(&piece, &rest)? {
                    return Ok(None);
                }
            }
        }
        Ok(Some(next))
    }
}

struct SubbagMatches<'a> {
    table: &'a RuleTable,
    head: AcSym,
    sort: LSort,
    patterns: &'a [(LNTerm, LNTerm)],
    next: &'a mut BTreeSet<LNTerm>,
    budget: &'a mut usize,
}

impl SubbagMatches<'_> {
    fn with_extension(&mut self, state: &LNTerm) -> Result<bool, Error> {
        // Standardize the single remainder variable apart from all rule and
        // caller variables. It has the declared operand sort of this AC head.
        let mut reserved: FxHashSet<_> = frees(state).into_iter().map(|v| v.idx).collect();
        for (pattern, _) in self.patterns {
            reserved.extend(frees(pattern).into_iter().map(|v| v.idx));
        }
        let index = (0..=u64::MAX)
            .find(|idx| !reserved.contains(idx))
            .ok_or(Error::FreshVariableOverflow)?;
        let rest = Term::Lit(Lit::Var(LVar::new("rest", self.sort, index)));
        for (pattern, rhs) in self.patterns {
            // A variable in ordinary AC matching consumes at least one factor.
            // The very same simultaneous binding restores it on the RHS.
            let lhs = f_app_ac(self.head, vec![pattern.clone(), rest.clone()]);
            let rhs = f_app_ac(self.head, vec![rhs.clone(), rest.clone()]);
            if !self.rewrite(&lhs, &rhs, state, &[])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn extend(&mut self, piece: &LNTerm, rest: &[LNTerm]) -> Result<bool, Error> {
        for (pattern, rhs) in self.patterns {
            if !self.rewrite(pattern, rhs, piece, rest)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn rewrite(
        &mut self,
        pattern: &LNTerm,
        rhs: &LNTerm,
        piece: &LNTerm,
        rest: &[LNTerm],
    ) -> Result<bool, Error> {
        let Outcome::Complete(arms) = open_match::root(pattern, piece, self.budget)? else {
            return Ok(false);
        };
        for arm in arms {
            let subst = Subst::from_list(arm);
            // Charge every actual variable occurrence before expanding a
            // duplicating RHS. The same counter governs the whole graph.
            if !charge_expansion(self.budget, [rhs], Some(&subst))? {
                return Ok(false);
            }
            if apply_vterm(&subst, pattern.clone()) != *piece {
                return Err(Error::InvalidStatus(255));
            }
            let value = apply_vterm(&subst, rhs.clone());
            if !self
                .table
                .collect(&value, &mut Vec::new(), InputDomain::Sorted)
                .is_some_and(|s| subsort(s, self.sort))
            {
                return Ok(false);
            }
            let state = if rest.is_empty() {
                value
            } else {
                let mut whole = rest.to_vec();
                whole.push(value);
                f_app_ac(self.head, whole)
            };
            self.next.insert(state);
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
