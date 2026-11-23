//! Normalize a flat XOR by the parity of each Fresh leaf. On its odd free
//! operands the complete variant family is indexed by partial matchings.
use super::RuleTable;
use crate::builtin::zero_const;
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_unification::{initialize, Error, MatchRows, Outcome, LEAN_THREAD};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::maude_types::sort_of_name;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;

use tamarin_algebra_sys::{tamarin_lean_xor_matchings, tamarin_xor_odd};

/// Preserve the usual increasing names and reuse low IDs after wraparound.
pub(super) fn witness_indices(
    highest: u64,
    occupied: impl Fn(u64) -> bool,
) -> impl Iterator<Item = u64> {
    (0..=u64::MAX)
        .map(move |offset| highest.wrapping_add(1).wrapping_add(offset))
        .filter(move |i| !occupied(*i))
}

impl RuleTable {
    pub(super) fn flat_xor_args<'a>(&self, t: &'a LNTerm) -> Option<&'a [LNTerm]> {
        let Term::App(FunSym::Ac(AcSym::Xor), args) = t else {
            return None;
        };
        (self.builtin_xor && args.len() >= 2).then_some(args)
    }

    pub(super) fn flat_xor_reduce(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let Some(args) = self.flat_xor_args(term) else {
            return Ok(None);
        };
        if !args.iter().all(|t| match t {
            Term::Lit(Lit::Var(v)) => v.sort == LSort::Fresh,
            Term::Lit(Lit::Con(n)) => sort_of_name(n) == LSort::Fresh,
            _ => false,
        }) {
            return Ok(None);
        }
        let odd = odd_operands(args)?;
        Ok(Some(if odd.is_empty() {
            zero_const()
        } else if odd.len() == args.len() && args.is_sorted() {
            term.clone()
        } else {
            f_app_ac(AcSym::Xor, odd.into_iter().cloned().collect())
        }))
    }

    pub(super) fn flat_xor_variants(&self, term: &LNTerm) -> Result<Outcome, Error> {
        let Some(args) = self.flat_xor_args(term) else {
            return Ok(Outcome::Unsupported);
        };
        let mut reserved = rustc_hash::FxHashSet::default();
        for t in args {
            let Term::Lit(Lit::Var(v)) = t else {
                return Ok(Outcome::Unsupported);
            };
            if v.sort != LSort::Fresh {
                return Ok(Outcome::Unsupported);
            }
            reserved.insert(v.idx);
        }
        let highest = reserved.iter().copied().max().unwrap_or(0);
        let vars: Vec<_> = odd_operands(args)?
            .into_iter()
            .map(|t| match t {
                Term::Lit(Lit::Var(v)) => *v,
                _ => unreachable!("validated Fresh variables"),
            })
            .collect();
        if vars.is_empty() {
            return Ok(Outcome::Complete(vec![vec![]]));
        }
        LEAN_THREAD.with(|_| {
            // SAFETY: the shim takes only the width. MatchRows owns its result.
            let raw = unsafe { tamarin_lean_xor_matchings(vars.len() as u64) };
            if raw.is_null() {
                return Ok(Outcome::Unsupported);
            }
            let rows = MatchRows::new(raw)?;
            if rows.count() != 1 || rows.rows(0) == 0 {
                return Err(Error::InvalidStatus(255));
            }
            let mut answers = Vec::with_capacity(rows.rows(0));
            let mut partners = vec![0; vars.len()];
            for r in 0..rows.rows(0) {
                tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                if rows.copy_row(0, r, &mut partners)? != vars.len() {
                    return Err(Error::InvalidStatus(255));
                }
                let mut available = witness_indices(highest, |i| reserved.contains(&i));
                let mut arm = Vec::new();
                for (i, &j) in partners.iter().enumerate() {
                    let j = j as usize;
                    if partners.get(j) != Some(&(i as u64)) {
                        return Err(Error::InvalidStatus(255));
                    }
                    if i < j {
                        let last = available.next().ok_or(Error::FreshVariableOverflow)?;
                        let witness = Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, last)));
                        arm.push((vars[i], witness.clone()));
                        arm.push((vars[j], witness));
                    }
                }
                answers.push(arm);
            }
            // The kernel contract specifies membership. Canonicalize multiplicity
            // and order for a standalone caller.
            answers.sort_unstable();
            answers.dedup();
            Ok(Outcome::Complete(answers))
        })
    }
}

/// The Rust term representation normally keeps AC operands sorted. Accept
/// raw applications too, so identical leaves still occupy one run.
pub(super) fn odd_operands(args: &[LNTerm]) -> Result<Vec<&LNTerm>, Error> {
    initialize()?;
    let mut ordered: Vec<_> = args.iter().collect();
    if !ordered.is_sorted() {
        ordered.sort_unstable();
    }
    LEAN_THREAD.with(|_| {
        let mut odd = Vec::with_capacity(ordered.len());
        for group in ordered.chunk_by(|a, b| a == b) {
            // SAFETY: the scalar Lean export returns a native Bool.
            match unsafe { tamarin_xor_odd(group.len() as u64) } {
                0 => {}
                1 => odd.push(group[0]),
                other => return Err(Error::InvalidStatus(other)),
            }
        }
        Ok(odd)
    })
}
