//! Directional matching of AC patterns with ground factors and sorted captures.
//! Each occurrence of a capture must receive the same nonempty bag of frozen
//! subject factors in every equation. The numeric alphabet is request-local.
use super::{
    ac_sort, canonical_capture, common_children, initialize, match_size, operands, residual,
    subsort, Error, Outcome, RuleTable, Substitutions, WordSlice, LEAN_THREAD,
};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, LNTerm, LVar};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::{is_ground_vterm, Lit};

mod paged;

unsafe extern "C" {
    fn tamarin_lean_ac_bag_match(rows: *const WordSlice, count: usize) -> u8;
    fn tamarin_lean_ac_bag_typed_match(
        rows: *const WordSlice,
        count: usize,
        restrictions: *const WordSlice,
        restricted: usize,
    ) -> u8;
}

struct Row<'a> {
    symbol: AcSym,
    keys: Vec<u64>,
    fixed: Vec<&'a LNTerm>,
    subject: Vec<&'a LNTerm>,
}

impl Row<'_> {
    // Canonicalization concerns only C/AC axioms; subject variables stay rigid.
    fn remainder(&self) -> Result<Option<Vec<LNTerm>>, Error> {
        let subject: Vec<_> = self.subject.iter().map(|t| canonical_capture(t)).collect();
        if self.fixed.is_empty() {
            return Ok(Some(subject));
        }
        let fixed: Vec<_> = self.fixed.iter().map(|t| canonical_capture(t)).collect();
        let (missing, rest) = common_children::residual_refs(&fixed, &subject)?;
        Ok(missing
            .is_empty()
            .then(|| rest.into_iter().cloned().collect()))
    }

    fn linear_match(&self) -> Result<bool, Error> {
        let count = if self.fixed.is_empty() {
            self.subject.len()
        } else if let Some(terms) = self.remainder()? {
            terms.len()
        } else {
            return Ok(false);
        };
        Ok(!match_size::excludes(self.keys.len() as u64, count as u64)?)
    }
}

fn ac_root(t: &LNTerm) -> Option<AcSym> {
    match t {
        Term::App(FunSym::Ac(f), _) => Some(*f),
        _ => None,
    }
}

struct BagRows<'a> {
    symbol: AcSym,
    vars: IdentityTable<LVar>,
    occurrences: usize,
    all_full_sort: bool,
    rows: Vec<Row<'a>>,
}

fn may_apply(pattern: &LNTerm, subject: &LNTerm) -> bool {
    match pattern {
        Term::App(FunSym::Ac(f), args) => {
            args.len() <= residual::MAX_EXPANDED
                && args.iter().any(|t| match t {
                    Term::Lit(Lit::Var(_)) => true,
                    Term::App(FunSym::Ac(g), _) => g == f,
                    _ => false,
                })
        }
        Term::Lit(Lit::Var(_)) => ac_root(subject).is_some(),
        _ => false,
    }
}

impl RuleTable {
    pub(crate) fn may_be_ac_bag_match(eqs: &[Equal<LNTerm>]) -> bool {
        eqs.iter().any(|e| may_apply(&e.rhs, &e.lhs))
    }

    fn prepare_bag_rows<'a>(
        &self,
        eqs: &'a [Equal<LNTerm>],
        orient: impl Fn(&'a Equal<LNTerm>) -> (&'a LNTerm, &'a LNTerm),
    ) -> Result<Option<BagRows<'a>>, Error> {
        let Some(default_head) = eqs
            .iter()
            .map(&orient)
            .find_map(|(p, s)| ac_root(p).or_else(|| ac_root(s)))
        else {
            return Ok(None);
        };
        let mut budget = residual::MAX_EXPANDED;
        if !residual::charge_expansion(
            &mut budget,
            eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]),
            None,
        )? || !self.admits_terms(eqs)
        {
            return Ok(None);
        }
        let mut vars = IdentityTable::default();
        let mut occurrences = 0;
        let mut all_full_sort = true;
        let mut rows = Vec::with_capacity(eqs.len());
        for (pattern_term, subject_term) in eqs.iter().map(orient) {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let symbol = ac_root(pattern_term)
                .or_else(|| ac_root(subject_term))
                .unwrap_or(default_head);
            let sort = ac_sort(symbol);
            if !subsort(sort_of_lterm(subject_term, sort_of_name), sort) {
                return Ok(None);
            }
            let mut pattern = Vec::new();
            operands::flatten(symbol, pattern_term, &mut pattern);
            let mut row = Row {
                symbol,
                keys: Vec::new(),
                fixed: Vec::new(),
                subject: Vec::new(),
            };
            for t in pattern {
                match t {
                    Term::Lit(Lit::Var(v)) => {
                        all_full_sort &= subsort(sort, v.sort);
                        row.keys
                            .push(vars.intern(*v).ok_or(Error::InvalidStatus(255))?);
                    }
                    t if is_ground_vterm(t) => row.fixed.push(t),
                    _ => return Ok(None),
                }
            }
            operands::flatten(symbol, subject_term, &mut row.subject);
            occurrences += row.keys.len();
            rows.push(row);
        }
        Ok(Some(BagRows {
            symbol: default_head,
            vars,
            occurrences,
            all_full_sort,
            rows,
        }))
    }

    /// Public matching orientation is subject on the left, pattern on the right.
    pub(crate) fn ac_bag_has_match(&self, eqs: &[Equal<LNTerm>]) -> Result<Option<bool>, Error> {
        let Some(data) = self.prepare_bag_rows(eqs, |e| (&e.rhs, &e.lhs))? else {
            return Ok(None);
        };
        // Each capture occurs exactly once. No rigid term identities need
        // to cross the ABI on rows without fixed factors.
        if data.all_full_sort
            && data.occurrences == data.vars.len()
            && data.rows.iter().all(|r| !r.keys.is_empty())
        {
            for row in &data.rows {
                if !row.linear_match()? {
                    return Ok(Some(false));
                }
            }
            return Ok(Some(true));
        }
        data.with_packet(false, decide)
    }

    /// The internal tree matcher puts patterns on the left in both public APIs.
    pub(crate) fn ac_bag_answers(&self, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        if !eqs.iter().any(|e| may_apply(&e.lhs, &e.rhs)) {
            return Ok(Outcome::Unsupported);
        }
        let Some(data) = self.prepare_bag_rows(eqs, |e| (&e.lhs, &e.rhs))? else {
            return Ok(Outcome::Unsupported);
        };
        Ok(match data.answers()? {
            Some(arms) => Outcome::Complete(arms),
            None => Outcome::Unsupported,
        })
    }
}

fn decide(
    head: AcSym,
    vars: &IdentityTable<LVar>,
    factors: &IdentityTable<&LNTerm>,
    slices: &[WordSlice],
) -> Result<Option<bool>, Error> {
    let narrow = vars
        .values()
        .iter()
        .enumerate()
        .filter(|(_, v)| !subsort(ac_sort(head), v.sort));
    // Each narrow capture transmits a key followed by the IDs of all eligible
    // singleton factors. The checked inventory currently needs at most 5 × 129
    // words. Bound the attempted construction for inputs outside that domain.
    if narrow.clone().count().saturating_mul(1 + factors.len()) > residual::MAX_EXPANDED {
        return Ok(None);
    }
    let mut restrictions = Vec::new();
    for (key, var) in narrow {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let mut allowed = vec![key as u64];
        for (id, factor) in factors.values().iter().enumerate() {
            if subsort(sort_of_lterm(factor, sort_of_name), var.sort) {
                allowed.push(id as u64);
            }
        }
        restrictions.push(allowed);
    }
    initialize()?;
    let descriptors: Vec<_> = restrictions.iter().map(|row| WordSlice::new(row)).collect();
    // SAFETY: the shim copies both descriptor lists and their words. Only a
    // scalar decision is returned, including for requests with many matches.
    let tag = LEAN_THREAD.with(|_| unsafe {
        if descriptors.is_empty() {
            tamarin_lean_ac_bag_match(slices.as_ptr(), slices.len())
        } else {
            tamarin_lean_ac_bag_typed_match(
                slices.as_ptr(),
                slices.len(),
                descriptors.as_ptr(),
                descriptors.len(),
            )
        }
    });
    tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(false)),
        2 => Ok(Some(true)),
        other => Err(Error::InvalidStatus(other)),
    }
}

impl BagRows<'_> {
    fn answers(self) -> Result<Option<Substitutions>, Error> {
        self.with_packet(Vec::new(), paged::read_answers)
    }

    /// Keep the canonical subject factors and their request-local identities
    /// alive through the entire call, including decoding any returned bags.
    fn with_packet<T>(
        self,
        no_matches: T,
        run: impl FnOnce(
            AcSym,
            &IdentityTable<LVar>,
            &IdentityTable<&LNTerm>,
            &[WordSlice],
        ) -> Result<Option<T>, Error>,
    ) -> Result<Option<T>, Error> {
        // A single bag algebra must interpret repeated images in every row.
        if self.rows.len() > 64 || self.rows.iter().any(|r| r.symbol != self.symbol) {
            return Ok(None);
        }
        let mut residuals = Vec::with_capacity(self.rows.len());
        for row in &self.rows {
            let Some(rest) = row.remainder()? else {
                return Ok(Some(no_matches));
            };
            residuals.push(rest);
        }
        let mut factors = IdentityTable::default();
        let mut packet = Vec::with_capacity(2 * self.rows.len());
        for (row, rest) in self.rows.into_iter().zip(&residuals) {
            packet.push(row.keys);
            packet.push(
                rest.iter()
                    .map(|t| factors.intern(t).ok_or(Error::InvalidStatus(255)))
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }
        let slices: Vec<_> = packet.iter().map(|row| WordSlice::new(row)).collect();
        run(self.symbol, &self.vars, &factors, &slices)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::msg_var;
    use crate::function_symbols::AcSym;
    use crate::lterm::pub_term;
    use crate::maude_sig::mset_maude_sig;
    use crate::term::f_app_ac;

    #[test]
    fn missing_fixed_occurrence_is_exact_and_all_rows_must_be_admitted() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let sum = |ts| f_app_ac(AcSym::Union, ts);
        let (x, y, tag) = (msg_var("x", 0), msg_var("y", 0), pub_term("tag"));
        let missing = Equal {
            lhs: sum(vec![tag.clone(), x.clone(), x.clone(), x.clone()]),
            rhs: sum(vec![tag.clone(), tag.clone(), y.clone()]),
        };
        assert_eq!(
            table
                .ac_bag_has_match(std::slice::from_ref(&missing))
                .unwrap(),
            Some(false)
        );
        let unsupported = Equal {
            lhs: sum(vec![tag.clone(), tag]),
            rhs: crate::builtin::pair(x.clone(), x),
        };
        assert_eq!(
            table.ac_bag_has_match(&[missing, unsupported]).unwrap(),
            None
        );
    }

    #[test]
    fn answer_rows_restore_full_captures_including_identity_and_shared_frozen_ids() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        // First encounter order (z, a) differs from variable sort order.
        let z = LVar::new("z", crate::lterm::LSort::Msg, 7);
        let a = LVar::new("a", crate::lterm::LSort::Msg, 7);
        let var = |v| Term::Lit(Lit::Var(v));
        let sum = |ts| f_app_ac(AcSym::Union, ts);
        let fixed = pub_term("marker");
        let plain = pub_term("frozen");
        // Raw reversed input verifies encounter order for shared captures.
        let pattern = Term::App(
            FunSym::Ac(AcSym::Union),
            vec![var(z), var(a), fixed.clone()].into(),
        );
        let subjects = [var(z), var(a), plain];
        let mut all = subjects.to_vec();
        all.push(fixed);
        let row = Equal {
            lhs: pattern,
            rhs: sum(all),
        };
        let Outcome::Complete(mut arms) = table.ac_bag_answers(std::slice::from_ref(&row)).unwrap()
        else {
            panic!("small bag enumeration deferred");
        };
        let mut expected = Vec::new();
        for mask in 1..7 {
            let (lhs, rhs): (Vec<_>, Vec<_>) = subjects
                .iter()
                .enumerate()
                .partition(|(i, _)| mask & (1 << i) != 0);
            let bag =
                |xs: Vec<(usize, &LNTerm)>| sum(xs.into_iter().map(|(_, t)| t.clone()).collect());
            expected.push(vec![(z, bag(lhs)), (a, bag(rhs))]);
        }
        expected.sort();
        arms.sort();
        assert_eq!(arms, expected);

        let row = Equal {
            lhs: sum(vec![var(z), var(z), var(a)]),
            rhs: sum(subjects.to_vec()),
        };
        assert_eq!(
            table.ac_bag_answers(&[row]).unwrap(),
            Outcome::Complete(vec![])
        );
    }
}
