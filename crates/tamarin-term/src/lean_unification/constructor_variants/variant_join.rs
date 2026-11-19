//! Join complete variant families on the images of all caller variables.
//! Each row also carries its predicted normal values so a specialization
//! that introduces a redex in an earlier observation can be discarded.
mod finite_narrowing;
mod residual_match;
mod scalar_action;
mod signed_graph;
use residual_match::{residual_row_matches, RowMatch};

use super::{InputDomain, RuleTable};
use crate::function_symbols::{exp_sym, inv_sym, AcSym, FunSym};
use crate::lean_unification::{initialize, residual, Error, Outcome, WordSlice, LEAN_THREAD};
use crate::lterm::{frees_list, sort_of_lterm, HasFrees, LNTerm, LSort, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeSet;

unsafe extern "C" {
    fn tamarin_lean_select_joined_variants(
        rows: *const WordSlice,
        count: usize,
        mask: *mut u8,
    ) -> u8;
}

fn select_normal_rows(checks: &[Vec<u64>]) -> Result<Option<Vec<u8>>, Error> {
    initialize()?;
    let words: Vec<_> = checks.iter().map(|r| WordSlice::new(r)).collect();
    let mut mask = vec![0; checks.len()];
    LEAN_THREAD.with(|_| {
        // SAFETY: the shim borrows each row and writes at most one byte per row.
        match unsafe {
            tamarin_lean_select_joined_variants(words.as_ptr(), words.len(), mask.as_mut_ptr())
        } {
            0 => Ok(None),
            1 => Ok(Some(mask)),
            status => Err(Error::InvalidStatus(status)),
        }
    })
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct Row {
    images: Vec<LNTerm>,
    values: Vec<LNTerm>,
}

fn fresh_renaming(reserved: &FxHashSet<u64>) -> impl FnMut(&LNTerm) -> LNTerm + '_ {
    let mut names = FxHashMap::default();
    let mut available = (0..=u64::MAX).filter(|i| !reserved.contains(i));
    move |t| {
        t.clone().map_free(&mut |v| {
            *names.entry(v).or_insert_with(|| {
                LVar::new(
                    "x",
                    v.sort,
                    available.next().expect("bounded variant variables"),
                )
            })
        })
    }
}

impl Row {
    fn iter(&self) -> impl Iterator<Item = &LNTerm> {
        self.images.iter().chain(&self.values)
    }
    fn rename(&self, reserved: &FxHashSet<u64>) -> Self {
        let mut rename = fresh_renaming(reserved);
        Self {
            images: self.images.iter().map(&mut rename).collect(),
            values: self.values.iter().map(rename).collect(),
        }
    }
}

/// Count rigid symbols in a B representative. A flattened AC application
/// represents arity - 1 binary symbols. Substitution can only add symbols.
fn rigid_size(t: &LNTerm) -> usize {
    match t {
        Term::Lit(Lit::Var(_)) => 0,
        Term::Lit(Lit::Con(_)) => 1,
        Term::App(head, args) => {
            let root = if matches!(head, FunSym::Ac(_)) {
                args.len() - 1
            } else {
                1
            };
            args.iter()
                .fold(root, |n, child| n.saturating_add(rigid_size(child)))
        }
    }
}

struct IndexedRow {
    row: Row,
    sizes: Vec<usize>,
}

/// Free argument positions and bare captures force the same bindings across
/// the complete row. C/AC equations wait until all those bindings are known.
fn compare_rigid<'a>(
    p: &'a LNTerm,
    s: &'a LNTerm,
    captures: &mut FxHashMap<LVar, &'a LNTerm>,
    pending: &mut Vec<(&'a LNTerm, &'a LNTerm)>,
) -> bool {
    match (p, s) {
        (Term::Lit(Lit::Var(v)), _) => {
            super::super::subsort(sort_of_lterm(s, sort_of_name), v.sort)
                && *captures.entry(*v).or_insert(s) == s
        }
        (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b))) => a == b,
        (Term::App(f, ps), Term::App(g, ss)) if f == g => {
            if matches!(f, FunSym::NoEq(_)) {
                return ps
                    .iter()
                    .zip(ss.iter())
                    .all(|(a, b)| compare_rigid(a, b, captures, pending));
            }
            if ps.len() > ss.len() {
                return false;
            }
            if matches!(f, FunSym::Ac(_)) {
                let before = pending.len();
                if !super::super::open_match::align_rigid_factors(ps, ss, |p, s| {
                    compare_rigid(p, s, captures, pending)
                }) {
                    return false;
                }
                // The parent match still covers these forced subequations.
                // Carry their bindings without queuing the same checks twice.
                pending.truncate(before);
            }
            pending.push((p, s));
            true
        }
        _ => false,
    }
}

impl IndexedRow {
    fn subsumes(&self, other: &Self, budget: &mut usize) -> Result<Option<bool>, Error> {
        if self.sizes.iter().zip(&other.sizes).any(|(p, s)| p > s) {
            return Ok(Some(false));
        }
        let mut captures = FxHashMap::default();
        let mut pending = Vec::new();
        if !self
            .row
            .iter()
            .zip(other.row.iter())
            .all(|(p, s)| compare_rigid(p, s, &mut captures, &mut pending))
        {
            return Ok(Some(false));
        }
        if pending.is_empty() {
            return Ok(Some(true));
        }
        let mut seed = captures.into_iter().map(|(v, t)| (v, t.clone())).collect();
        let equations = match residual_row_matches(pending, &mut seed)? {
            RowMatch::Clash => return Ok(Some(false)),
            RowMatch::Deferred => return Ok(None),
            RowMatch::Pending(eqs) => eqs,
        };
        if equations.is_empty() {
            return Ok(Some(true));
        }
        Ok(
            match super::super::open_match::with_captures_budget(
                &equations,
                seed.into_iter().collect(),
                budget,
            )? {
                Outcome::Complete(rows) => Some(!rows.is_empty()),
                Outcome::Unsupported => None,
            },
        )
    }
}

/// Rebuild a context from its already normalized child observations. Only
/// original nodes are replaced. Variables inside a captured image belong to
/// the row witnesses, so another caller binding must never be applied there.
fn operand_value(
    t: &LNTerm,
    subst: &Subst<Name, LVar>,
    values: &FxHashMap<&LNTerm, &LNTerm>,
) -> LNTerm {
    if let Some(value) = values.get(t) {
        return (*value).clone();
    }
    match t {
        Term::Lit(Lit::Var(v)) => subst.image_of(v).unwrap_or(t).clone(),
        Term::Lit(_) => t.clone(),
        Term::App(head, args) => crate::term::f_app(
            *head,
            args.iter()
                .map(|a| operand_value(a, subst, values))
                .collect(),
        ),
    }
}

struct JoinSearch {
    budget: residual::Budget,
    normal: FxHashMap<LNTerm, Option<bool>>,
    pairs: usize,
    matching: usize,
    // All ordinary narrowing frontiers in this query share this allowance
    // for expanded terms, concrete rewrites and state/terminal comparisons.
    frontier_nodes: usize,
    graph_work: usize,
}

/// A known root redex or child redex suffices regardless of any undecided
/// sibling. With a clear root, normality requires all children to be normal.
fn normal_with_root(
    term: &LNTerm,
    root_clear: bool,
    mut child_normal: impl FnMut(&LNTerm) -> Result<Option<bool>, Error>,
) -> Result<Option<bool>, Error> {
    if !root_clear {
        return Ok(Some(false));
    }
    let mut result = Some(true);
    if let Term::App(_, args) = term {
        for arg in args.iter() {
            match child_normal(arg)? {
                Some(false) => return Ok(Some(false)),
                Some(true) => {}
                None => result = None,
            }
        }
    }
    Ok(result)
}

impl JoinSearch {
    fn new() -> Self {
        Self {
            budget: residual::Budget::new(),
            normal: FxHashMap::default(),
            pairs: 4096,
            matching: 100_000,
            graph_work: residual::MAX_EXPANDED,
            frontier_nodes: 1 << 21,
        }
    }
}

impl RuleTable {
    /// Collect the narrowing problems for a sorted observation, borrowing the
    /// original nodes. Exact.wrapFree exposes every child of an inert free
    /// head. The tuple join supplies one shared substitution for all leaves.
    fn collect_variant_applications<'a>(
        &self,
        t: &'a LNTerm,
        slot: Option<LSort>,
        applications: &mut Vec<&'a LNTerm>,
    ) -> Result<bool, Error> {
        let Term::App(head, args) = t else {
            return Ok(true);
        };
        if let Some(required) = slot
            && self
                .declaration(*head)
                .is_none_or(|(_, _, sort)| sort != required)
        {
            // The parent slot cannot certify the narrower result sort of a
            // changing child. A stable child always retains its input sorts.
            return self.stably_normal_native(t);
        }
        if let FunSym::NoEq(f) = head
            && !self.patterns.contains_key(f)
        {
            for child in args.iter() {
                // Every non-nullary free declaration in the module takes Msg arguments.
                if !self.collect_variant_applications(child, Some(LSort::Msg), applications)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if applications.contains(&t)
            || self.stably_normal_native(t)?
            || self.uniform_reduct(t)?.is_some()
        {
            return Ok(true);
        }
        if let FunSym::Ac(f) = head
            && self.guarded_pair(*f, args)
        {
            for child in args.iter() {
                if !self.collect_variant_applications(
                    child,
                    Some(super::super::ac_sort(*f)),
                    applications,
                )? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if crate::vterm::is_ground_vterm(t) {
            // These reducers establish uniqueness as well as reachability.
            let value = match self.cancellation_normal(t)? {
                Some(n) => Some(n),
                None => self.search_reduction(t)?,
            };
            if value.as_ref().is_some_and(crate::vterm::is_ground_vterm) {
                return Ok(true);
            }
        }
        applications.push(t);
        Ok(true)
    }

    fn join_normal(&self, t: &LNTerm) -> Result<Option<bool>, Error> {
        self.canonical_join_normal(&super::super::canonical_capture(t))
    }

    fn canonical_join_normal(&self, t: &LNTerm) -> Result<Option<bool>, Error> {
        if let Some(root) = self.dh_root_normal(t) {
            return normal_with_root(t, root, |arg| self.canonical_join_normal(arg));
        }
        if self.irreducible_native(t)? {
            return Ok(Some(true));
        }
        if let Some(n) = self.reduce_native(t)? {
            // Normal forms compare modulo B. A component with a normal form
            // in its own B-class is normal (Select.normal_iff_same).
            return Ok(Some(super::super::canonical_capture(&n) == *t));
        }
        // A known step below the root refutes normality even if this head's
        // reduction is unsupported. No absence of steps follows from deferral.
        if let Term::App(_, xs) = t {
            for x in xs.iter() {
                if self.canonical_join_normal(x)? == Some(false) {
                    return Ok(Some(false));
                }
            }
        }
        Ok(None)
    }

    /// Validate hereditary convergence under this rule table all the way to
    /// stably normal leaves. Only the outermost active terms need independent
    /// variant families; their values rebuild every enclosing inert wrapper.
    fn staged_children<'a>(
        &self,
        t: &'a LNTerm,
        mut children: Option<&mut Vec<&'a LNTerm>>,
    ) -> Result<bool, Error> {
        if self.stably_normal_native(t)? {
            return Ok(true);
        }
        let Term::App(head, args) = t else {
            return Ok(false);
        };
        let active = match head {
            FunSym::Ac(f) if self.cancellation_units.contains_key(f) => true,
            FunSym::NoEq(f) if self.narrowing.get(f).is_some_and(|r| r.positional()) => true,
            FunSym::NoEq(f) if !self.patterns.contains_key(f) => false,
            _ => return Ok(false),
        };
        for arg in args.iter() {
            if !self.staged_children(
                arg,
                if active {
                    None
                } else {
                    children.as_deref_mut()
                },
            )? {
                return Ok(false);
            }
        }
        if active
            && let Some(children) = children
            && !children.contains(&t)
        {
            children.push(t);
        }
        Ok(true)
    }

    fn single_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        if let Some(rows) = self.direct_rows(keys, original, app)? {
            return Ok(Some(rows));
        }
        if let Some(rows) = self.scalar_action_rows(keys, original, app, search)? {
            return Ok(Some(rows));
        }
        // At most eight sign profiles. Larger matrices are attempted only
        // after the existing component solvers defer on the entire operation.
        if let Some(rows) = self.signed_graph_rows(
            keys,
            std::slice::from_ref(app),
            signed_graph::QUICK_COORDINATES,
            search,
        )? {
            return Ok(Some(rows));
        }
        if let Some(rows) = self.staged_rows(keys, original, app, search)? {
            return Ok(Some(rows));
        }
        self.finite_narrowing(keys, original, app, search)
    }

    fn staged_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        let Term::App(head, args) = app else {
            return Ok(None);
        };
        let dh = self.builtin_dh
            && match head {
                FunSym::Ac(AcSym::Mult) => true,
                FunSym::NoEq(f) => *f == exp_sym() || *f == inv_sym(),
                _ => false,
            };
        let arity = match head {
            _ if dh && self.dh_unique_instances(app)? => {
                let Some((_, arity, _)) = self.declaration(*head) else {
                    return Ok(None);
                };
                arity
            }
            FunSym::Ac(f) if self.cancellation_units.contains_key(f) => 2,
            FunSym::NoEq(f) if self.narrowing.get(f).is_some_and(|r| r.positional()) => args.len(),
            _ => return Ok(None),
        };
        let mut children = Vec::new();
        for arg in args.iter() {
            if dh {
                if !self.stably_normal_native(arg)? && !children.contains(&arg) {
                    children.push(arg);
                }
            } else if !self.staged_children(arg, Some(&mut children))? {
                return Ok(None);
            }
        }
        // A flat product wider than the binary schema still has intermediate
        // products to normalize, even when all original operands are stable.
        if dh && children.is_empty() && args.len() == arity {
            return Ok(None);
        }
        // Message arguments can be specialized to their original sorts. A
        // folded AC application reuses the same schema at each binary split.
        let mut formals = Vec::with_capacity(arity);
        for (i, arg) in args.iter().take(arity).enumerate() {
            let sort = if dh && arity == args.len() {
                let Some(sort) = self.collect(arg, &mut Vec::new(), InputDomain::Sorted) else {
                    return Ok(None);
                };
                sort
            } else {
                LSort::Msg
            };
            formals.push(LVar::new("x", sort, i as u64));
        }
        let variable = |v| Term::Lit(Lit::Var(v));
        let template = crate::term::f_app(*head, formals.iter().copied().map(variable).collect());
        let reserved = formals.iter().map(|v| v.idx).collect();
        let family = match self.direct_rows(&formals, &reserved, &template)? {
            Some(rows) => rows,
            None if dh => {
                let Some(rows) = self.finite_narrowing(&formals, &reserved, &template, search)?
                else {
                    return Ok(None);
                };
                rows
            }
            None => return Ok(None),
        };
        let mut operands = if let Some((first, others)) = children.split_first() {
            let Some(mut rows) = self.single_rows(keys, original, first, search)? else {
                return Ok(None);
            };
            for child in others {
                let Some(right) = self.single_rows(keys, original, child, search)? else {
                    return Ok(None);
                };
                let Some(joined) = self.join_families(&rows, &right, original, search)? else {
                    return Ok(None);
                };
                rows = joined.into_iter().collect();
            }
            // The joint witnesses determine all child values. Reconstruct the
            // operand vector including every free wrapper and repeated slot.
            for row in &mut rows {
                let subst = Subst::from_list(keys.iter().copied().zip(row.images.iter().cloned()));
                let values = children.iter().copied().zip(&row.values).collect();
                row.values = args
                    .iter()
                    .map(|arg| operand_value(arg, &subst, &values))
                    .collect();
            }
            rows
        } else {
            vec![Row {
                images: keys.iter().copied().map(variable).collect(),
                values: args.to_vec(),
            }]
        };

        // The operation family is reused at every split. Keep unconsumed
        // operands in the visible tuple while pruning, so later stages share
        // the same substitution even when their operands can themselves narrow.
        let mut width = args.len();
        loop {
            for row in &mut operands {
                // The operation sees the first operands as its input columns.
                // Its join retains the caller images, then the pending operands.
                let pending = row.values.split_off(arity);
                std::mem::swap(&mut row.images, &mut row.values);
                row.values.extend(pending);
            }
            let Some(joined) = self.join_families(&operands, &family, original, search)? else {
                return Ok(None);
            };
            let projected = joined
                .into_iter()
                .map(|row| {
                    let mut images = row.values;
                    let mut values = images.split_off(keys.len());
                    // Move the operation's last output before the pending operands.
                    values.rotate_right(1);
                    Row { images, values }.rename(original)
                })
                .collect();
            let Some(rows) = self.prune_specializations(projected, &mut search.matching)? else {
                return Ok(None);
            };
            if width == arity {
                return Ok(Some(rows));
            }
            width -= arity - 1;
            operands = rows;
        }
    }

    fn join_families(
        &self,
        left: &[Row],
        right: &[Row],
        original: &FxHashSet<u64>,
        search: &mut JoinSearch,
    ) -> Result<Option<BTreeSet<Row>>, Error> {
        let mut joined = BTreeSet::new();
        for l in left {
            for r in right {
                tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                if search.pairs == 0
                    || !self.join_rows(
                        l,
                        r,
                        original,
                        &mut search.budget,
                        &mut search.normal,
                        &mut joined,
                    )?
                {
                    return Ok(None);
                }
                search.pairs -= 1;
            }
        }
        Ok(Some(joined))
    }

    fn index_row(&self, mut row: Row) -> Option<IndexedRow> {
        // Validate each row once, then compare canonical subjects directly.
        if !self.admits_sorted(row.iter()) {
            return None;
        }
        for t in row.images.iter_mut().chain(&mut row.values) {
            *t = super::super::canonical_capture(t);
        }
        let sizes = row.iter().map(rigid_size).collect();
        Some(IndexedRow { row, sizes })
    }

    /// Specialization can turn distinct generic cases into instances of each
    /// other. Compare every input image and output under one rigid-subject
    /// match (Row.Subsumes). Transitivity covers earlier deletions if their
    /// representative is itself replaced.
    fn prune_specializations(
        &self,
        projected: BTreeSet<Row>,
        budget: &mut usize,
    ) -> Result<Option<Vec<Row>>, Error> {
        let mut kept: Vec<IndexedRow> = Vec::new();
        'candidate: for r in projected {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some(row) = self.index_row(r) else {
                return Ok(None);
            };
            let mut i = 0;
            while i < kept.len() {
                match kept[i].subsumes(&row, budget)? {
                    Some(true) => continue 'candidate,
                    Some(false) => {}
                    None => return Ok(None),
                }
                match row.subsumes(&kept[i], budget)? {
                    Some(true) => {
                        kept.swap_remove(i);
                    }
                    Some(false) => i += 1,
                    None => return Ok(None),
                }
            }
            kept.push(row);
        }
        Ok(Some(kept.into_iter().map(|r| r.row).collect()))
    }

    fn direct_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
    ) -> Result<Option<Vec<Row>>, Error> {
        let used: FxHashSet<_> = frees_list(app).into_iter().collect();
        let local_keys: Vec<_> = keys.iter().copied().filter(|v| used.contains(v)).collect();
        let open_row = |subst: &Subst<Name, LVar>, value| {
            let mut row = Row {
                images: local_keys
                    .iter()
                    .map(|&v| apply_vterm(subst, Term::Lit(Lit::Var(v))))
                    .collect(),
                values: vec![value],
            };
            if local_keys.len() != keys.len() {
                // A leaf may have chosen a witness with the same name as an
                // unrelated caller variable. Open its images AND value apart
                // before adding those variables' independent identity images.
                row = row.rename(original);
                let padded = Subst::from_list(local_keys.iter().copied().zip(row.images));
                row.images = keys
                    .iter()
                    .map(|&v| {
                        padded
                            .image_of(&v)
                            .cloned()
                            .unwrap_or(Term::Lit(Lit::Var(v)))
                    })
                    .collect();
            }
            row
        };
        if let Some(arms) = self.cancellation_rows(app)? {
            return Ok(Some(
                arms.into_iter().map(|(s, v)| open_row(&s, v)).collect(),
            ));
        }
        let family = if let Some((base, factors)) = self.dh_peer_factors(app)? {
            super::dh_peer::received_base_rows(app, base, &factors)?
        } else if self.builtin_dh
            && let family @ Outcome::Complete(_) = self.dh_exponent_variants(app, &[app])?
        {
            // A complete exponent family can be a component of any joint
            // observation. open_row keeps unrelated caller inputs independent.
            family
        } else if let family @ Outcome::Complete(_) = self.fresh_xor_variants(app)? {
            family
        } else {
            // Packing repeated observations requires a unique normal value
            // under specialization. Positional narrowing certifies this;
            // a family carrying several possible output values would not.
            let Term::App(FunSym::NoEq(head), args) = app else {
                return Ok(None);
            };
            let Some(rule) = self.narrowing.get(head) else {
                return Ok(None);
            };
            rule.variants(std::slice::from_ref(app), app, args, |t| {
                self.normal_message(t)
            })?
        };
        let Outcome::Complete(arms) = family else {
            return Ok(None);
        };
        let mut rows = Vec::with_capacity(arms.len());
        for arm in arms {
            let subst = Subst::from_list(arm);
            let Some(value) = self.reduce_native(&apply_vterm(&subst, app.clone()))? else {
                return Ok(None);
            };
            rows.push(open_row(&subst, value));
        }
        Ok(Some(rows))
    }

    fn join_rows(
        &self,
        left: &Row,
        right: &Row,
        original: &FxHashSet<u64>,
        budget: &mut residual::Budget,
        normal: &mut FxHashMap<LNTerm, Option<bool>>,
        answers: &mut BTreeSet<Row>,
    ) -> Result<bool, Error> {
        let mut used = original.clone();
        for t in left.iter() {
            t.for_each_free(&mut |v| {
                used.insert(v.idx);
            });
        }
        let right = right.rename(&used);
        for t in right.iter() {
            t.for_each_free(&mut |v| {
                used.insert(v.idx);
            });
        }
        let eqs: Vec<_> = left
            .images
            .iter()
            .zip(&right.images)
            .map(|(l, r)| Equal {
                lhs: l.clone(),
                rhs: r.clone(),
            })
            .collect();
        if !self.admits_terms(&eqs) {
            return Ok(false);
        }
        let Some((free, pending)) = crate::unification::unify_lterm_factored(&sort_of_name, eqs)
        else {
            return Ok(true);
        };
        // Reserving variables from output values protects them through factor
        // composition even when they do not occur in the input equations.
        // VariantJoin.join_csu proves this is equivalent to reflexive anchors.
        let Some(rest) = residual::solve(pending, &used, budget)? else {
            return Ok(false);
        };
        let mut candidates = Vec::with_capacity(rest.len());
        let mut checks = Vec::with_capacity(rest.len());
        for next in rest {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let subst = next.compose(&free);
            let apply = |t: &LNTerm| apply_vterm(&subst, t.clone());
            let row = Row {
                images: left.images.iter().map(apply).collect(),
                values: left.values.iter().chain(&right.values).map(apply).collect(),
            };
            let mut evidence = Vec::with_capacity(row.images.len() + row.values.len());
            for t in row.iter() {
                let status = if let Some(s) = normal.get(t) {
                    *s
                } else {
                    let s = self.join_normal(t)?;
                    normal.insert(t.clone(), s);
                    s
                };
                evidence.push(match status {
                    Some(false) => 0,
                    Some(true) => 1,
                    None => 2,
                });
            }
            candidates.push(row);
            checks.push(evidence);
        }
        let Some(mask) = select_normal_rows(&checks)? else {
            return Ok(false);
        };
        for (row, keep) in candidates.into_iter().zip(mask) {
            if keep == 1 {
                answers.insert(row.rename(original));
            }
        }
        Ok(true)
    }

    pub(crate) fn joined_variants(&self, query: &LNTerm) -> Result<Outcome, Error> {
        let terms = match query {
            Term::App(FunSym::List, xs) => xs.as_ref(),
            _ => std::slice::from_ref(query),
        };
        let mut applications = Vec::new();
        for t in terms {
            if self
                .collect(t, &mut Vec::new(), InputDomain::Sorted)
                .is_none()
            {
                return Ok(Outcome::Unsupported);
            }
            let before = applications.len();
            if !self.collect_variant_applications(t, None, &mut applications)? {
                // Projection through a wider parent sort can lose the child's
                // sort requirement. Narrowing the original observation keeps it.
                applications.truncate(before);
                if !applications.contains(&t) {
                    applications.push(t);
                }
            }
        }
        let Some((first, others)) = applications.split_first() else {
            return Ok(Outcome::Complete(vec![vec![]]));
        };
        if self.builtin_dh {
            if others.is_empty()
                && let Some((base, factors)) = self.dh_peer_factors(first)?
                && let done @ Outcome::Complete(_) =
                    super::dh_peer::received_base_rows(query, base, &factors)?
            {
                return Ok(done);
            }
            if let done @ Outcome::Complete(_) = self.dh_exponent_variants(query, &applications)? {
                return Ok(done);
            }
        }
        let mut keys = frees_list(query);
        let mut seen = BTreeSet::new();
        keys.retain(|v| seen.insert(*v));
        let original = keys.iter().map(|v| v.idx).collect();
        let mut search = JoinSearch::new();
        let mut result = None;
        if !others.is_empty() {
            result =
                self.signed_graph_rows(&keys, terms, signed_graph::QUICK_COORDINATES, &mut search)?;
        }
        if result.is_none() {
            result = self.join_applications(&keys, &original, first, others, &mut search)?;
        }
        if result.is_none() {
            result =
                self.signed_graph_rows(&keys, terms, signed_graph::MAX_COORDINATES, &mut search)?;
        }
        Ok(match result {
            Some(rows) => Outcome::Complete(
                rows.into_iter()
                    .map(|r| keys.iter().copied().zip(r.images).collect())
                    .collect(),
            ),
            None => Outcome::Unsupported,
        })
    }

    fn join_applications(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        first: &LNTerm,
        others: &[&LNTerm],
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        let Some(mut rows) = self.single_rows(keys, original, first, search)? else {
            return Ok(None);
        };
        if others.is_empty() {
            for row in &mut rows {
                *row = row.rename(original);
            }
        }
        for app in others {
            let Some(right) = self.single_rows(keys, original, app, search)? else {
                return Ok(None);
            };
            let Some(answers) = self.join_families(&rows, &right, original, search)? else {
                return Ok(None);
            };
            rows = answers.into_iter().collect();
        }
        if !others.is_empty() {
            let Some(kept) =
                self.prune_specializations(rows.into_iter().collect(), &mut search.matching)?
            else {
                return Ok(None);
            };
            rows = kept;
        }
        Ok(Some(rows))
    }
}
