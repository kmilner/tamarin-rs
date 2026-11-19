//! Finite ordinary narrowing with extension at AC heads. Every node carries
//! the original input images through each specialization and every fold.
use super::{fresh_renaming, IndexedRow, JoinSearch, Row};
use crate::function_symbols::FunSym;
use crate::lean_unification::constructor_variants::{InputDomain, RuleTable};
use crate::lean_unification::{canonical_capture, residual, subsort, Error};
use crate::lterm::{HasFrees, LNTerm, LSort, LVar};
use crate::rewriting::{Equal, RRule};
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app, f_app_ac, is_subterm, Term};
use crate::vterm::Lit;
use rustc_hash::FxHashSet;
use std::collections::BTreeSet;

struct Frontier<'a> {
    table: &'a RuleTable,
    search: &'a mut JoinSearch,
    original: &'a FxHashSet<u64>,
    states: Vec<IndexedRow>,
    seen_normal_inputs: BTreeSet<Row>,
    terminals: BTreeSet<Row>,
}

fn variable(v: LVar) -> LNTerm {
    Term::Lit(Lit::Var(v))
}

/// Replay an ordinary rule instance on the extended rule itself. Every
/// further instance then factors through that very same ordinary rule.
fn absorbs_extension(
    rule: &RRule<LNTerm>,
    extended: &RRule<LNTerm>,
    sort: LSort,
    rest: &LNTerm,
) -> bool {
    let Term::App(FunSym::Ac(ac), args) = &rule.lhs else {
        return false;
    };
    args.iter().any(|arg| {
        let Term::Lit(Lit::Var(v)) = arg else {
            return false;
        };
        if !subsort(sort, v.sort) {
            return false;
        }
        let subst = Subst::from_list([(*v, f_app_ac(*ac, vec![arg.clone(), rest.clone()]))]);
        apply_vterm(&subst, rule.lhs.clone()) == extended.lhs
            && apply_vterm(&subst, rule.rhs.clone()) == extended.rhs
    })
}

fn replace_at(t: &LNTerm, path: &[usize], rhs: &LNTerm) -> LNTerm {
    let Some((&i, tail)) = path.split_first() else {
        return rhs.clone();
    };
    let Term::App(f, args) = t else {
        unreachable!("path selected by structural descent")
    };
    let mut context = args.to_vec();
    context[i] = replace_at(&context[i], tail, rhs);
    f_app(*f, context)
}

impl RuleTable {
    // RepeatedACDecoder.caller_unique: every live root here projects the sole
    // capture from at least two identical AC factors. Different operations,
    // factors and multiplicities may be used at successive levels.
    fn decoder_unique_instances(&self, app: &LNTerm) -> Result<bool, Error> {
        let mut current = app;
        let mut recognized = false;
        while let Term::App(head @ FunSym::NoEq(symbol), args) = current {
            let Some([rule]) = self.ordinary_rules.get(head).map(Vec::as_slice) else {
                break;
            };
            let Term::App(_, pattern) = &rule.lhs else {
                break;
            };
            let [Term::App(FunSym::Ac(_), copies)] = pattern.as_ref() else {
                break;
            };
            if symbol.arity != 1
                || args.len() != 1
                || copies.len() < 2
                || !matches!(rule.rhs, Term::Lit(Lit::Var(_)))
                || !copies.iter().all(|t| t == &rule.rhs)
            {
                break;
            }
            recognized = true;
            current = &args[0];
        }
        Ok(recognized && self.stably_normal_native(current)?)
    }

    pub(super) fn finite_narrowing(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        let mut frontier = Frontier {
            table: self,
            search,
            original,
            states: Vec::new(),
            seen_normal_inputs: BTreeSet::new(),
            terminals: BTreeSet::new(),
        };
        let seed = Row {
            images: keys.iter().copied().map(variable).collect(),
            values: vec![canonical_capture(app)],
        };
        if !frontier.insert(seed)? {
            return Ok(None);
        }
        let mut i = 0;
        while i < frontier.states.len() {
            let row = frontier.states[i].row.clone();
            let value = &row.values[0];
            match frontier.normal(value)? {
                Some(true) => {
                    frontier.terminals.insert(row.clone());
                }
                Some(false) => {}
                None => return Ok(None),
            }
            let mut reserved = original.clone();
            for t in row.iter() {
                t.for_each_free(&mut |v| {
                    reserved.insert(v.idx);
                });
            }
            if !frontier.positions(&row, value, &mut Vec::new(), &reserved)? {
                return Ok(None);
            }
            i += 1;
        }
        let terminals = std::mem::take(&mut frontier.terminals);
        let Some(kept) =
            self.prune_specializations(terminals, &mut frontier.search.frontier_nodes)?
        else {
            return Ok(None);
        };
        let unique_instances =
            self.dh_unique_instances(app)? || self.decoder_unique_instances(app)?;
        for (i, r) in kept.iter().enumerate() {
            let subst = Subst::from_list(keys.iter().copied().zip(r.images.iter().cloned()));
            if !residual::charge_expansion(
                &mut frontier.search.frontier_nodes,
                [app],
                Some(&subst),
            )? {
                return Ok(None);
            }
            let instantiated = apply_vterm(&subst, app.clone());
            if !self
                .reduce_native(&instantiated)?
                .is_some_and(|n| canonical_capture(&n) == r.values[0])
            {
                return Ok(None);
            }
            // Packed observations may reuse this value for every appearance
            // of the input. Without a uniqueness theorem, check all overlaps,
            // including one with a fresh copy of this very row.
            if !unique_instances {
                for other in &kept[..=i] {
                    if !frontier.functional(r, other)? {
                        return Ok(None);
                    }
                }
            }
        }
        Ok(Some(kept))
    }
}

impl Frontier<'_> {
    fn charge(&mut self) -> bool {
        let Some(left) = self.search.pairs.checked_sub(1) else {
            return false;
        };
        self.search.pairs = left;
        true
    }

    fn normal(&mut self, t: &LNTerm) -> Result<Option<bool>, Error> {
        if let Some(&Some(known)) = self.search.normal.get(t) {
            return Ok(Some(known));
        }
        let status = if let Some(root) = self.table.dh_root_normal(t) {
            if !residual::charge_expansion(&mut self.search.frontier_nodes, [t], None)? {
                return Ok(None);
            }
            super::normal_with_root(t, root, |arg| self.normal(arg))?
        } else {
            self.table
                .successors(t, &mut self.search.frontier_nodes)?
                .map(|xs| xs.is_empty())
        };
        self.search.normal.insert(t.clone(), status);
        Ok(status)
    }

    fn insert(&mut self, r: Row) -> Result<bool, Error> {
        let Some(row) = self.table.index_row(r) else {
            return Ok(false);
        };
        let mut unknown = false;
        for image in &row.row.images {
            match self.normal(image)? {
                Some(false) => return Ok(true), // Every instance still has this step.
                Some(true) => {}
                None => unknown = true,
            }
        }
        if unknown {
            return Ok(false);
        }
        // The same fully renamed candidate can arise through several rules
        // or CSU arms. Its already-checked fold remains valid as states grow.
        if !self.seen_normal_inputs.insert(row.row.clone()) {
            return Ok(true);
        }
        for prior in &self.states {
            match prior.subsumes(&row, &mut self.search.frontier_nodes)? {
                Some(true) => return Ok(true),
                Some(false) => {}
                None => return Ok(false),
            }
        }
        // Each actual state, CSU and overlap counts once. Instantiated arms
        // (including discarded ones) were already charged by expanded size.
        if !self.charge() {
            return Ok(false);
        }
        self.states.push(row);
        Ok(true)
    }

    fn positions(
        &mut self,
        row: &Row,
        t: &LNTerm,
        path: &mut Vec<usize>,
        reserved: &FxHashSet<u64>,
    ) -> Result<bool, Error> {
        if row.images.iter().any(|image| is_subterm(t, image)) {
            // Every admissible caller image is normal, including all its
            // subterms after the same substitution. This covers variable slots.
            return Ok(true);
        }
        let Term::App(head, args) = t else {
            return Ok(matches!(t, Term::Lit(Lit::Con(_))));
        };
        let Some((id, _, sort)) = self.table.declaration(*head) else {
            return Ok(false);
        };
        if let Some(rules) = self.table.ordinary_rules.get(head) {
            for rule in rules {
                let mut used = reserved.clone();
                let index = (0..=u64::MAX)
                    .find(|i| !used.contains(i))
                    .ok_or(Error::FreshVariableOverflow)?;
                used.insert(index);
                let rule = {
                    let mut open = fresh_renaming(&used);
                    RRule::new(open(&rule.lhs), open(&rule.rhs))
                };
                rule.lhs.for_each_free(&mut |v| {
                    used.insert(v.idx);
                });
                if !self.narrow(row, path, t, &rule, sort, &used)? {
                    return Ok(false);
                }
                if let FunSym::Ac(ac) = head {
                    let rest = variable(LVar::new("rest", sort, index));
                    let extended = RRule::new(
                        f_app_ac(*ac, vec![rule.lhs.clone(), rest.clone()]),
                        f_app_ac(*ac, vec![rule.rhs.clone(), rest.clone()]),
                    );
                    if !absorbs_extension(&rule, &extended, sort, &rest)
                        && !self.narrow(row, path, t, &extended, sort, &used)?
                    {
                        return Ok(false);
                    }
                }
            }
        } else if self.table.roots.binary_search(&id).is_ok() {
            // The table lacks a complete, interpretable rule bucket here.
            return Ok(false);
        }
        for (i, child) in args.iter().enumerate() {
            // Symmetric, structurally equal occurrences have the same context.
            if matches!(head, FunSym::C(_) | FunSym::Ac(_)) && i > 0 && args[i - 1] == *child {
                continue;
            }
            path.push(i);
            if !self.positions(row, child, path, reserved)? {
                return Ok(false);
            }
            path.pop();
        }
        Ok(true)
    }

    fn narrow(
        &mut self,
        row: &Row,
        path: &[usize],
        source: &LNTerm,
        rule: &RRule<LNTerm>,
        sort: LSort,
        reserved: &FxHashSet<u64>,
    ) -> Result<bool, Error> {
        if !self.charge() {
            return Ok(false);
        }
        let eq = Equal {
            lhs: rule.lhs.clone(),
            rhs: source.clone(),
        };
        let Some(arms) = residual::solve(vec![eq], reserved, &mut self.search.budget)? else {
            return Ok(false);
        };
        if arms.is_empty() {
            return Ok(true);
        }
        let context = replace_at(&row.values[0], path, &rule.rhs);
        for subst in arms {
            if !residual::charge_expansion(
                &mut self.search.frontier_nodes,
                row.images
                    .iter()
                    .chain([&context, &rule.rhs, &rule.lhs, source]),
                Some(&subst),
            )? {
                return Ok(false);
            }
            if apply_vterm(&subst, rule.lhs.clone()) != apply_vterm(&subst, source.clone()) {
                return Err(Error::InvalidStatus(255));
            }
            let value = apply_vterm(&subst, rule.rhs.clone());
            if !self
                .table
                .collect(&value, &mut Vec::new(), InputDomain::Sorted)
                .is_some_and(|s| subsort(s, sort))
            {
                return Ok(false);
            }
            let next = Row {
                images: row
                    .images
                    .iter()
                    .map(|t| apply_vterm(&subst, t.clone()))
                    .collect(),
                values: vec![apply_vterm(&subst, context.clone())],
            }
            .rename(self.original);
            if !self.insert(next)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn functional(&mut self, left: &Row, right: &Row) -> Result<bool, Error> {
        if !self.charge() {
            return Ok(false);
        }
        let mut reserved = self.original.clone();
        for t in left.iter() {
            t.for_each_free(&mut |v| {
                reserved.insert(v.idx);
            });
        }
        let right = right.rename(&reserved);
        for t in right.iter() {
            t.for_each_free(&mut |v| {
                reserved.insert(v.idx);
            });
        }
        let equations = left
            .images
            .iter()
            .zip(&right.images)
            .map(|(l, r)| Equal {
                lhs: l.clone(),
                rhs: r.clone(),
            })
            .collect();
        let Some(arms) = residual::solve(equations, &reserved, &mut self.search.budget)? else {
            return Ok(false);
        };
        for subst in arms {
            if !residual::charge_expansion(
                &mut self.search.frontier_nodes,
                left.iter().chain(right.iter()),
                Some(&subst),
            )? {
                return Ok(false);
            }
            let apply = |t: &LNTerm| apply_vterm(&subst, t.clone());
            if !left
                .images
                .iter()
                .zip(&right.images)
                .all(|(l, r)| apply(l) == apply(r))
            {
                return Err(Error::InvalidStatus(255));
            }
            let l = apply(&left.values[0]);
            let r = apply(&right.values[0]);
            if l == r {
                continue;
            }
            let mut impossible = false;
            for t in [l, r].into_iter().chain(left.images.iter().map(apply)) {
                if self.normal(&t)? == Some(false) {
                    impossible = true;
                    break;
                }
            }
            if !impossible {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{hash, nat_plus};
    use crate::function_symbols::nat_one_sym;
    use crate::lean_unification::Outcome;
    use crate::maude_sig::{hash_maude_sig, nat_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::{f_app_list, f_app_no_eq};

    #[test]
    fn decoder_requires_a_complete_projecting_bucket_and_a_stable_leaf() {
        use crate::builtin::msg_var;
        use crate::function_symbols::{AcSym, Constructability, NoEqSym, Privacy};
        use crate::subterm_rule::rrule_to_ctxt_st_rule;
        let op =
            |name: &[u8]| NoEqSym::new(name, 1, Privacy::Public, Constructability::Constructor);
        let d = op(b"decode_two");
        let e = op(b"decode_three");
        let changed = op(b"changed");
        let call = |f, t| f_app_no_eq(f, vec![t]);
        let v = msg_var("v", 0);
        let marker = crate::lterm::pub_term("stop");
        let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
        let repeated = |n| f_app_ac(AcSym::Union, vec![v.clone(); n]);
        let mut sig = hash_maude_sig().merge(crate::maude_sig::mset_maude_sig());
        sig.st_fun_syms.extend([d, e, changed]);
        sig.st_rules.insert(rule(call(d, repeated(2)), v.clone()));
        sig.st_rules.insert(rule(call(e, repeated(3)), v.clone()));
        sig.st_rules
            .insert(rule(call(changed, marker.clone()), marker.clone()));
        let query = |t| call(d, call(e, t));
        let table = RuleTable::new(&sig.clone().refresh()).unwrap();
        assert!(table.decoder_unique_instances(&query(v.clone())).unwrap());
        assert!(!table
            .decoder_unique_instances(&query(call(changed, marker.clone())))
            .unwrap());
        sig.st_rules.insert(rule(call(e, repeated(3)), marker));
        let modified = RuleTable::new(&sig.refresh()).unwrap();
        assert!(!modified.decoder_unique_instances(&query(v)).unwrap());
    }

    #[test]
    fn omits_only_extensions_replayed_on_both_sides_with_one_sorted_substitution() {
        use crate::builtin::xor;
        let x = variable(LVar::new("x", LSort::Msg, 1));
        let fresh = variable(LVar::new("x", LSort::Fresh, 1));
        let r = variable(LVar::new("rest", LSort::Msg, 9));
        let a = crate::lterm::pub_term("a");
        let check = |lhs: LNTerm, rhs: LNTerm| {
            let extended = RRule::new(xor(lhs.clone(), r.clone()), xor(rhs.clone(), r.clone()));
            absorbs_extension(&RRule::new(lhs, rhs), &extended, LSort::Msg, &r)
        };
        assert!(check(xor(x.clone(), a.clone()), x.clone()));
        assert!(check(
            xor(x.clone(), a.clone()),
            xor(x.clone(), hash(a.clone()))
        ));
        assert!(!check(xor(x.clone(), a.clone()), a.clone()));
        assert!(!check(xor(x.clone(), x.clone()), x.clone()));
        assert!(!check(xor(x.clone(), a.clone()), hash(x)));
        assert!(!check(xor(fresh.clone(), a), fresh));
    }

    #[test]
    fn wider_constructor_slot_keeps_narrower_changing_child_intact() {
        let one = f_app_no_eq(nat_one_sym(), vec![]);
        let key = LVar::new("n", LSort::Nat, 0);
        let n = variable(key);
        let mut signature = nat_maude_sig().merge(hash_maude_sig());
        signature.st_rules.insert(CtxtStRule::new(
            nat_plus(one.clone(), one.clone()),
            StRhs {
                positions: vec![],
                term: one.clone(),
            },
        ));
        let table = RuleTable::new(&signature.refresh()).unwrap();
        let observed = hash(nat_plus(n.clone(), one.clone()));
        let query = f_app_list(vec![observed, n]);
        let Outcome::Complete(rows) = table.joined_variants(&query).unwrap() else {
            panic!("the original Msg observation retains the Nat constraint");
        };
        let mut cases = BTreeSet::new();
        for row in rows {
            let subst = Subst::from_list(row);
            let image = apply_vterm(&subst, variable(key));
            let source = hash(nat_plus(image.clone(), one.clone()));
            let (case, value) = match &image {
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Nat => (0, source.clone()),
                t if *t == one => (1, hash(image.clone())),
                Term::App(FunSym::Ac(_), args)
                    if args.len() == 2
                        && args.contains(&one)
                        && args.iter().any(
                            |t| matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Nat),
                        ) =>
                {
                    (2, hash(image.clone()))
                }
                other => panic!("unexpected Nat input image {other}"),
            };
            assert!(cases.insert(case));
            assert_eq!(table.reduce_native(&source).unwrap(), Some(value));
        }
        assert_eq!(cases, BTreeSet::from([0, 1, 2]));
    }
}
