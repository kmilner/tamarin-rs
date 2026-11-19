//! Check overlap agreement on live rule heads before comparing all terminal
//! rows. `GuardedRuleBuckets.Query.caller_unique` applies to every normalized
//! caller instance under the same rule table.
use super::{Frontier, Row};
use crate::function_symbols::FunSym;
use crate::lean_unification::{residual, Error};
use crate::lterm::{HasFrees, LNTerm};
use crate::term::{is_subterm, Term};
use crate::vterm::Lit;
use std::collections::BTreeSet;

enum Stage {
    Normal,
    Pending(FunSym),
}

impl Frontier<'_> {
    fn guarded_stage(
        &mut self,
        term: &LNTerm,
        heads: &mut BTreeSet<FunSym>,
    ) -> Result<Option<Stage>, Error> {
        if !residual::charge_expansion(&mut self.search.frontier_nodes, [term], None)? {
            return Ok(None);
        }
        if self.table.stably_normal_native(term)? {
            return Ok(Some(Stage::Normal));
        }
        let Term::App(head @ FunSym::NoEq(symbol), args) = term else {
            return Ok(None);
        };
        let mut children = Vec::with_capacity(args.len());
        for arg in args.iter() {
            let Some(child) = self.guarded_stage(arg, heads)? else {
                return Ok(None);
            };
            children.push(child);
        }
        if let Some(rules) = self.table.ordinary_rules.get(head) {
            for rule in rules {
                if !residual::charge_expansion(
                    &mut self.search.frontier_nodes,
                    [&rule.lhs, &rule.rhs],
                    None,
                )? {
                    return Ok(None);
                }
                let Term::App(_, pattern) = &rule.lhs else {
                    return Ok(None);
                };
                if pattern.len() != children.len() {
                    return Ok(None);
                }
                for (arg, child) in pattern.iter().zip(&children) {
                    if let Stage::Pending(pending) = child {
                        match arg {
                            Term::Lit(Lit::Var(_)) => return Ok(None),
                            Term::App(f, _) if f == pending => return Ok(None),
                            _ => {}
                        }
                    }
                }
                // A subterm of one normal argument remains normal. A ground
                // result may also be used if it is already irreducible.
                if !pattern.iter().any(|p| is_subterm(&rule.rhs, p)) {
                    let mut ground = true;
                    rule.rhs.for_each_free(&mut |_| ground = false);
                    if !ground || self.normal(&rule.rhs)? != Some(true) {
                        return Ok(None);
                    }
                }
            }
            heads.insert(*head);
        } else if self.table.patterns.contains_key(symbol) {
            // A live bucket discarded during validation is incomplete.
            return Ok(None);
        }
        Ok(Some(Stage::Pending(*head)))
    }

    pub(super) fn bucket_unique_instances(
        &mut self,
        term: &LNTerm,
        terminals: usize,
    ) -> Result<bool, Error> {
        if !matches!(term, Term::App(FunSym::NoEq(_), _)) {
            return Ok(false);
        }
        let mut heads = BTreeSet::new();
        if self.guarded_stage(term, &mut heads)?.is_none() {
            return Ok(false);
        }
        // Count the rule pairs and terminal pairs, including self-overlaps.
        // Try the rule check only when it needs fewer comparisons.
        let comparisons = |n: usize| (n as u128) * (n as u128 + 1) / 2;
        let rule_pairs: u128 = heads
            .iter()
            .map(|h| comparisons(self.table.ordinary_rules[h].len()))
            .sum();
        if rule_pairs >= comparisons(terminals) {
            return Ok(false);
        }
        for head in heads {
            let rules = &self.table.ordinary_rules[&head];
            let mut rows = Vec::with_capacity(rules.len());
            for rule in rules {
                let Term::App(_, args) = &rule.lhs else {
                    return Ok(false);
                };
                let row = Row {
                    images: args.to_vec(),
                    values: vec![rule.rhs.clone()],
                };
                for previous in rows.iter().chain(std::iter::once(&row)) {
                    if !self.functional(&row, previous)? {
                        return Ok(false);
                    }
                }
                rows.push(row);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::msg_var;
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::lean_unification::constructor_variants::RuleTable;
    use crate::maude_sig::hash_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_no_eq;

    #[test]
    fn compatible_overlaps_do_not_excuse_a_parent_rewriting_early() {
        let f = |name: &[u8], arity| {
            NoEqSym::new(name, arity, Privacy::Public, Constructability::Constructor)
        };
        let [outer, inner, wrap, a, b] = [
            f(b"select", 2),
            f(b"inner", 1),
            f(b"wrap", 1),
            f(b"a", 0),
            f(b"b", 0),
        ];
        let call = |head, t| f_app_no_eq(head, vec![t]);
        let select = |l, r| f_app_no_eq(outer, vec![l, r]);
        let (a0, b0) = (f_app_no_eq(a, vec![]), f_app_no_eq(b, vec![]));
        let x = msg_var("x", 0);
        let y = msg_var("y", 1);
        let rule = |l, r| rrule_to_ctxt_st_rule(&RRule::new(l, r)).unwrap();
        let mut sig = hash_maude_sig();
        sig.st_fun_syms.extend([outer, inner, wrap, a, b]);
        for declaration in [
            rule(call(inner, x.clone()), x.clone()),
            rule(select(call(wrap, x.clone()), y.clone()), x.clone()),
            rule(select(call(wrap, a0.clone()), y.clone()), a0.clone()),
        ] {
            sig.st_rules.insert(declaration);
        }
        let q = select(call(inner, x.clone()), y.clone());
        let agrees = |sig: crate::maude_sig::MaudeSig| {
            let table = RuleTable::new(&sig.refresh()).unwrap();
            let mut frontier = Frontier {
                table: &table,
                search: &mut super::super::JoinSearch::new(),
                original: &Default::default(),
                states: Vec::new(),
                seen_normal_inputs: BTreeSet::new(),
                terminals: BTreeSet::new(),
            };
            frontier.bucket_unique_instances(&q, 8).unwrap()
        };
        // On the common instance select(wrap(a), y), both rules give a.
        assert!(agrees(sig.clone()));
        // With x = wrap(a), the new rule gives b before inner reduces,
        // while reducing inner first still yields a.
        sig.st_rules.insert(rule(select(call(inner, x), y), b0));
        assert!(!agrees(sig));
    }
}
