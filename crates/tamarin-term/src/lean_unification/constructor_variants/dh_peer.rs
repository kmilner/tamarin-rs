//! Instantiate the base or exponent images emitted by Lean. Each row has its own
//! witnesses, while observed terms keep the same range variables across the tuple.
use super::{InputDomain, RuleTable};
use crate::builtin::{dh_neutral, exp, inv, mult, one_const};
use crate::function_symbols::{exp_sym, inv_sym, one_sym, AcSym, FunSym};
use crate::lean_unification::{initialize, Error, MatchRows, Outcome, LEAN_THREAD};
use crate::lterm::{frees_list, occurs_free, LNTerm, LSort, LVar};
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::Lit;
use std::collections::{BTreeMap, BTreeSet};

use tamarin_algebra_sys::{
    tamarin_lean_dh_exponent_images, tamarin_lean_dh_peer_images, tamarin_lean_dh_tower_images,
};

fn read_image(
    ops: &[u64],
    mut slot: impl FnMut(u64) -> Result<LNTerm, Error>,
) -> Result<LNTerm, Error> {
    let mut stack = Vec::with_capacity(ops.len());
    for &op in ops {
        let term = match op {
            0..=4 | 9.. => slot(op)?,
            5 => dh_neutral(),
            6 => inv(stack.pop().ok_or(Error::InvalidStatus(255))?),
            7 | 8 => {
                let rhs = stack.pop().ok_or(Error::InvalidStatus(255))?;
                let lhs = stack.pop().ok_or(Error::InvalidStatus(255))?;
                if op == 7 {
                    mult(lhs, rhs)
                } else {
                    exp(lhs, rhs)
                }
            }
        };
        stack.push(term);
    }
    if stack.len() != 1 {
        return Err(Error::InvalidStatus(255));
    }
    stack.pop().ok_or(Error::InvalidStatus(255))
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum RangeName {
    Observed(LVar),
    Witness(u64),
}

// Use the same range variable for every occurrence in the exponent and
// every other observed term. Applying once preserves simultaneous renaming.
fn observed_term(
    term: &LNTerm,
    witness: &mut impl FnMut(RangeName) -> Result<LVar, Error>,
) -> Result<LNTerm, Error> {
    if let Term::Lit(Lit::Var(v)) = term {
        return Ok(Term::Lit(Lit::Var(witness(RangeName::Observed(*v))?)));
    }
    let mut images = Vec::new();
    for v in frees_list(term) {
        images.push((v, Term::Lit(Lit::Var(witness(RangeName::Observed(v))?))));
    }
    Ok(apply_vterm(&Subst::from_list(images), term.clone()))
}

/// Maude can print commutative children in a different order. Names already
/// introduced in the tuple retain their identity in either traversal.
fn fixed_name_order(t: &LNTerm, seen: &mut BTreeSet<LVar>) -> bool {
    match t {
        Term::Lit(Lit::Var(v)) => {
            seen.insert(*v);
            true
        }
        Term::Lit(_) => true,
        Term::App(FunSym::Ac(_) | FunSym::C(_), _) => {
            let mut new = 0;
            for v in frees_list(t) {
                if seen.insert(v) {
                    new += 1;
                }
            }
            new <= 1
        }
        Term::App(_, xs) => xs.iter().all(|x| fixed_name_order(x, seen)),
    }
}

impl RuleTable {
    /// Collect the positive factor occurrences in a received-base power.
    /// Associating powers and flattening exponent products preserve all
    /// multiplicities. A Msg variable could specialize to an inverse or unit.
    pub(super) fn dh_peer_factors<'a>(
        &self,
        t: &'a LNTerm,
    ) -> Result<Option<(LVar, Vec<&'a LNTerm>)>, Error> {
        if !self.builtin_dh {
            return Ok(None);
        }
        let mut base = t;
        let mut factors = Vec::new();
        while let Term::App(FunSym::NoEq(f), args) = base {
            if *f != exp_sym() {
                break;
            }
            let [inner, exponent] = args.as_ref() else {
                return Ok(None);
            };
            let group = match exponent {
                Term::App(FunSym::Ac(AcSym::Mult), xs) if xs.len() >= 2 => xs.as_ref(),
                _ => std::slice::from_ref(exponent),
            };
            if factors.len() + group.len() > 8 {
                return Ok(None);
            }
            factors.extend(group.iter().rev());
            base = inner;
        }
        factors.reverse();
        let Term::Lit(Lit::Var(base)) = base else {
            return Ok(None);
        };
        if base.sort != LSort::Msg || factors.is_empty() {
            return Ok(None);
        }
        for &factor in &factors {
            if !self.stable_dh_factor(*base, factor)? {
                return Ok(None);
            }
        }
        Ok(Some((*base, factors)))
    }

    /// The factor stays normal, non-unit and a single positive occurrence
    /// under every sorted substitution. It may share variables with the
    /// rest of the query, except the variable being bound by these images.
    pub(super) fn stable_dh_factor(&self, bound: LVar, factor: &LNTerm) -> Result<bool, Error> {
        let Some(sort) = self.collect(factor, &mut Vec::new(), InputDomain::Sorted) else {
            return Ok(false);
        };
        if !crate::lean_unification::subsort(sort, LSort::Msg) || occurs_free(&bound, factor) {
            return Ok(false);
        }
        let positive = match factor {
            Term::Lit(Lit::Var(v)) => v.sort != LSort::Msg,
            Term::App(FunSym::Ac(AcSym::Mult), _) => false,
            Term::App(FunSym::NoEq(f), _) => *f != inv_sym() && *f != one_sym(),
            _ => true,
        };
        Ok(positive && self.stably_normal(factor)?)
    }

    pub(super) fn dh_peer_variants(&self, query: &LNTerm) -> Result<Outcome, Error> {
        if !self.builtin_dh {
            return Ok(Outcome::Unsupported);
        }
        let terms = match query {
            Term::App(FunSym::List, args) => args.as_ref(),
            _ => std::slice::from_ref(query),
        };
        let mut candidate = None;
        for t in terms {
            if candidate.as_ref().is_some_and(|(seen, _, _)| *seen == t) {
                continue;
            }
            if self.stably_normal(t)? {
                continue;
            }
            let Some((base, factors)) = self.dh_peer_factors(t)? else {
                return Ok(Outcome::Unsupported);
            };
            if factors.len() != 1 || candidate.replace((t, base, factors)).is_some() {
                return Ok(Outcome::Unsupported);
            }
        }
        let Some((_, base, factors)) = candidate else {
            return Ok(Outcome::Unsupported);
        };
        // Maude visits bindings in query order and numbers range variables
        // on first use within each arm. This ordering is visible when the
        // prover prints a closed rule, even for alpha-equivalent answers.
        let vars = query_vars(query);
        if !matches!(factors[0], Term::Lit(Lit::Var(v)) if v.sort == LSort::Fresh) {
            let mut prior = BTreeSet::new();
            prior.extend(vars.iter().copied().take_while(|v| *v != base));
            if !fixed_name_order(query, &mut BTreeSet::new())
                || !fixed_name_order(factors[0], &mut prior)
            {
                return Ok(Outcome::Unsupported);
            }
        }
        ImageFamily::ReceivedBase(&factors).instantiate(&vars, base)
    }
}

pub(super) fn received_base_rows(
    query: &LNTerm,
    base: LVar,
    factors: &[&LNTerm],
) -> Result<Outcome, Error> {
    ImageFamily::ReceivedBase(factors).instantiate(&query_vars(query), base)
}

pub(super) fn free_exponent_rows(
    query: &LNTerm,
    variable: LVar,
    factor: &LNTerm,
) -> Result<Outcome, Error> {
    ImageFamily::FreeExponent(factor).instantiate(&query_vars(query), variable)
}

fn query_vars(query: &LNTerm) -> Vec<LVar> {
    let mut vars = frees_list(query);
    let mut seen = BTreeSet::new();
    vars.retain(|v| seen.insert(*v));
    vars
}

enum ImageFamily<'a> {
    ReceivedBase(&'a [&'a LNTerm]),
    FreeExponent(&'a LNTerm),
}

impl ImageFamily<'_> {
    fn instantiate(&self, vars: &[LVar], variable: LVar) -> Result<Outcome, Error> {
        let reserved: BTreeSet<_> = vars
            .iter()
            .filter(|v| v.name == "x")
            .map(|v| v.idx)
            .collect();
        let floor = reserved.last().copied().unwrap_or(0);
        initialize()?;
        LEAN_THREAD.with(|_| {
            // SAFETY: the returned array is owned by MatchRows for this thread.
            let raw = match self {
                Self::ReceivedBase([_]) => unsafe { tamarin_lean_dh_peer_images() },
                Self::ReceivedBase(factors) => unsafe {
                    tamarin_lean_dh_tower_images(factors.len() as u64)
                },
                Self::FreeExponent(_) => unsafe { tamarin_lean_dh_exponent_images() },
            };
            if raw.is_null() {
                return Ok(Outcome::Unsupported);
            }
            let rows = MatchRows::new(raw)?;
            if rows.count() != 1 {
                return Err(Error::InvalidStatus(255));
            }
            let mut encoded = Vec::new();
            let mut answers = Vec::with_capacity(rows.rows(0));
            for i in 0..rows.rows(0) {
                let len = rows.row_size(0, i)?;
                if encoded
                    .try_reserve(len.saturating_sub(encoded.len()))
                    .is_err()
                {
                    return Ok(Outcome::Unsupported);
                }
                encoded.resize(len, 0);
                rows.copy_row(0, i, &mut encoded)?;
                let mut names = BTreeMap::new();
                let mut last = floor;
                let mut witness = |key: RangeName| -> Result<LVar, Error> {
                    if let Some(&name) = names.get(&key) {
                        return Ok(name);
                    }
                    // Keep the usual numbering, including when a caller has
                    // occupied the top index but lower indices are available.
                    loop {
                        last = last.wrapping_add(1);
                        if last == floor {
                            return Err(Error::FreshVariableOverflow);
                        }
                        if !reserved.contains(&last) {
                            break;
                        }
                    }
                    let sort = match key {
                        RangeName::Observed(v) => v.sort,
                        RangeName::Witness(_) => LSort::Msg,
                    };
                    let name = LVar::new("x", sort, last);
                    names.insert(key, name);
                    Ok(name)
                };
                let mut answer = Vec::with_capacity(vars.len());
                for &v in vars {
                    let image = if v == variable {
                        read_image(&encoded, |slot| {
                            let name = match (self, slot) {
                                (_, 0) => witness(RangeName::Observed(variable))?,
                                (Self::ReceivedBase([factor]), 1)
                                | (Self::FreeExponent(factor), 1) => {
                                    return observed_term(factor, &mut witness);
                                }
                                (_, 2..=4) => witness(RangeName::Witness(slot))?,
                                (Self::FreeExponent(_), 9) => return Ok(one_const()),
                                (Self::ReceivedBase(factors), i) if i >= 9 => {
                                    let factor = factors
                                        .get((i - 9) as usize)
                                        .ok_or(Error::InvalidStatus(255))?;
                                    return observed_term(factor, &mut witness);
                                }
                                _ => return Err(Error::InvalidStatus(255)),
                            };
                            Ok(Term::Lit(Lit::Var(name)))
                        })?
                    } else {
                        Term::Lit(Lit::Var(witness(RangeName::Observed(v))?))
                    };
                    answer.push((v, image));
                }
                answers.push(answer);
            }
            if !matches!(self, Self::ReceivedBase([_])) {
                // The set contracts admit repeated programs. Distinct occurrence
                // subsets may also instantiate to the same tower image.
                let mut distinct = BTreeSet::new();
                answers.retain(|arm| distinct.insert(arm.clone()));
            }
            Ok(Outcome::Complete(answers))
        })
    }
}
