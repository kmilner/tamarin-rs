//! Join complete variant families on the images of all caller variables.
//! Each row also carries its predicted normal values so a specialization
//! that introduces a redex in an earlier observation can be discarded.
use super::{InputDomain, RuleTable};
use crate::function_symbols::FunSym;
use crate::lean_unification::{initialize, residual, Error, Outcome, WordSlice, LEAN_THREAD};
use crate::lterm::{frees_list, HasFrees, LNTerm, LVar};
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

impl Row {
    fn iter(&self) -> impl Iterator<Item = &LNTerm> {
        self.images.iter().chain(&self.values)
    }
    fn rename(&self, reserved: &FxHashSet<u64>) -> Self {
        let mut names = FxHashMap::default();
        let mut available = (0..=u64::MAX).filter(|i| !reserved.contains(i));
        let mut rename = |t: &LNTerm| {
            t.clone().map_free(&mut |v| {
                *names.entry(v).or_insert_with(|| {
                    LVar::new(
                        "x",
                        v.sort,
                        available.next().expect("bounded variant variables"),
                    )
                })
            })
        };
        Self {
            images: self.images.iter().map(&mut rename).collect(),
            values: self.values.iter().map(rename).collect(),
        }
    }
}

/// A variable-to-variable specialization is safe to discard only when the
/// very same renaming also reproduces every output, without reducing it.
fn subsumes_variable_row(general: &Row, specific: &Row) -> bool {
    let mut names = FxHashMap::default();
    for (a, b) in general.images.iter().zip(&specific.images) {
        let (Term::Lit(Lit::Var(a)), Term::Lit(Lit::Var(b))) = (a, b) else {
            return false;
        };
        if a.sort != b.sort || *names.entry(*a).or_insert(*b) != *b {
            return false;
        }
    }
    general.values.iter().zip(&specific.values).all(|(a, b)| {
        a.clone()
            .map_free(&mut |v| names.get(&v).copied().unwrap_or(v))
            == *b
    })
}

fn prune_variable_instances(rows: &mut Vec<Row>) -> Result<(), Error> {
    let ranks: Vec<_> = rows
        .iter()
        .map(|row| {
            row.images
                .iter()
                .map(|t| match t {
                    Term::Lit(Lit::Var(v)) => Some(*v),
                    _ => None,
                })
                .collect::<Option<FxHashSet<_>>>()
                .map(|vars| vars.len())
        })
        .collect();
    let mut dominated = vec![false; rows.len()];
    for (i, target) in rows.iter().enumerate() {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        if let Some(rank) = ranks[i] {
            dominated[i] = rows.iter().enumerate().any(|(j, general)| {
                ranks[j].is_some_and(|other| other > rank) && subsumes_variable_row(general, target)
            });
        }
    }
    let mut flags = dominated.into_iter();
    rows.retain(|_| !flags.next().unwrap());
    Ok(())
}

impl RuleTable {
    fn join_normal(&self, t: &LNTerm) -> Result<Option<bool>, Error> {
        if self.irreducible_native(t)? {
            return Ok(Some(true));
        }
        if let Some(n) = self.reduce_native(t)? {
            // Normal forms compare modulo B. A component with a normal form
            // in its own B-class is normal (Select.normal_iff_same).
            return Ok(Some(
                super::super::canonical_capture(&n) == super::super::canonical_capture(t),
            ));
        }
        // A known step below the root refutes normality even if this head's
        // reduction is unsupported. No absence of steps follows from deferral.
        if let Term::App(_, xs) = t {
            for x in xs.iter() {
                if self.join_normal(x)? == Some(false) {
                    return Ok(Some(false));
                }
            }
        }
        Ok(None)
    }

    fn single_rows(
        &self,
        keys: &[LVar],
        original: &FxHashSet<u64>,
        app: &LNTerm,
    ) -> Result<Option<Vec<Row>>, Error> {
        let family = if self.dh_peer_factors(app)?.is_some() {
            self.dh_peer_rows(app, false)?
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
        let used: FxHashSet<_> = frees_list(app).into_iter().collect();
        let local_keys: Vec<_> = keys.iter().copied().filter(|v| used.contains(v)).collect();
        let mut rows = Vec::with_capacity(arms.len());
        for arm in arms {
            let subst = Subst::from_list(arm);
            let instance = apply_vterm(&subst, app.clone());
            let Some(value) = self.reduce_native(&instance)? else {
                return Ok(None);
            };
            let mut row = Row {
                images: local_keys
                    .iter()
                    .map(|&v| apply_vterm(&subst, Term::Lit(Lit::Var(v))))
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
            rows.push(row);
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
        let eqs = left
            .images
            .iter()
            .zip(&right.images)
            .map(|(l, r)| Equal {
                lhs: l.clone(),
                rhs: r.clone(),
            })
            .collect();
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
            // A uniform reduction has a stable normal value. Its original
            // variables are still part of the final binding projection.
            if applications.contains(&t)
                || self.stably_normal_native(t)?
                || self.uniform_reduct(t)?.is_some()
            {
                continue;
            }
            applications.push(t);
        }
        let Some((first, others)) = applications.split_first() else {
            return Ok(Outcome::Complete(vec![vec![]]));
        };
        if self.builtin_dh {
            if others.is_empty()
                && let done @ Outcome::Complete(_) = self.dh_peer_rows(query, false)?
            {
                return Ok(done);
            }
            if let done @ Outcome::Complete(_) = self.dh_exponent_variants(query)? {
                return Ok(done);
            }
        }
        let mut keys = frees_list(query);
        let mut seen = BTreeSet::new();
        keys.retain(|v| seen.insert(*v));
        let original = keys.iter().map(|v| v.idx).collect();
        let Some(mut rows) = self.single_rows(&keys, &original, first)? else {
            return Ok(Outcome::Unsupported);
        };
        if others.is_empty() {
            for row in &mut rows {
                *row = row.rename(&original);
            }
        }
        let mut budget = residual::Budget::new();
        let mut remaining = 4096;
        let mut normal = FxHashMap::default();
        let wide_xor = applications
            .iter()
            .any(|t| self.flat_xor_args(t).is_some_and(|args| args.len() > 2));
        for app in others {
            let Some(right) = self.single_rows(&keys, &original, app)? else {
                return Ok(Outcome::Unsupported);
            };
            let mut answers = BTreeSet::new();
            for l in &rows {
                for r in &right {
                    tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                    if remaining == 0
                        || !self.join_rows(
                            l,
                            r,
                            &original,
                            &mut budget,
                            &mut normal,
                            &mut answers,
                        )?
                    {
                        return Ok(Outcome::Unsupported);
                    }
                    remaining -= 1;
                }
            }
            rows = answers.into_iter().collect();
        }
        if wide_xor && !others.is_empty() {
            prune_variable_instances(&mut rows)?;
        }
        Ok(Outcome::Complete(
            rows.into_iter()
                .map(|r| keys.iter().copied().zip(r.images).collect())
                .collect(),
        ))
    }
}
