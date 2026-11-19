//! Boolean matching of AC patterns with ground factors and full-sort captures.
//! Each occurrence of a capture must receive the same nonempty bag of frozen
//! subject factors in every equation. The numeric alphabet is request-local.
use super::{
    ac_sort, canonical_capture, common_children, initialize, match_size, operands, residual,
    subsort, Error, RuleTable, WordSlice, LEAN_THREAD,
};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, LNTerm};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::{is_ground_vterm, Lit};

unsafe extern "C" {
    fn tamarin_lean_ac_bag_match(rows: *const WordSlice, count: usize) -> u8;
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

impl RuleTable {
    // A flat ground row already has a direct equality check. Raw nested AC
    // children can contain captures even when none is visible at the root.
    pub(crate) fn may_be_ac_bag_match(eqs: &[Equal<LNTerm>]) -> bool {
        eqs.iter().any(|eq| match &eq.rhs {
            Term::App(FunSym::Ac(f), args) => {
                args.len() <= residual::MAX_EXPANDED
                    && args.iter().any(|t| match t {
                        Term::Lit(Lit::Var(_)) => true,
                        Term::App(FunSym::Ac(g), _) => g == f,
                        _ => false,
                    })
            }
            Term::Lit(Lit::Var(_)) => ac_root(&eq.lhs).is_some(),
            _ => false,
        })
    }

    /// Public matching orientation is subject on the left, pattern on the right.
    pub(crate) fn ac_bag_has_match(&self, eqs: &[Equal<LNTerm>]) -> Result<Option<bool>, Error> {
        let Some(default_head) = eqs
            .iter()
            .find_map(|e| ac_root(&e.rhs).or_else(|| ac_root(&e.lhs)))
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
        let mut rows = Vec::with_capacity(eqs.len());
        for eq in eqs {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let symbol = ac_root(&eq.rhs)
                .or_else(|| ac_root(&eq.lhs))
                .unwrap_or(default_head);
            let sort = ac_sort(symbol);
            if !subsort(sort_of_lterm(&eq.lhs, sort_of_name), sort) {
                return Ok(None);
            }
            let mut pattern = Vec::new();
            operands::flatten(symbol, &eq.rhs, &mut pattern);
            let mut row = Row {
                symbol,
                keys: Vec::new(),
                fixed: Vec::new(),
                subject: Vec::new(),
            };
            for t in pattern {
                match t {
                    Term::Lit(Lit::Var(v)) if subsort(sort, v.sort) => {
                        row.keys
                            .push(vars.intern(*v).ok_or(Error::InvalidStatus(255))?);
                    }
                    t if is_ground_vterm(t) => row.fixed.push(t),
                    _ => return Ok(None),
                }
            }
            operands::flatten(symbol, &eq.lhs, &mut row.subject);
            occurrences += row.keys.len();
            rows.push(row);
        }
        // Each capture occurs exactly once. No rigid term identities need
        // to cross the ABI on rows without fixed factors.
        if occurrences == vars.len() && rows.iter().all(|r| !r.keys.is_empty()) {
            for row in rows {
                if !row.linear_match()? {
                    return Ok(Some(false));
                }
            }
            return Ok(Some(true));
        }
        // A single bag algebra must interpret repeated images in every row.
        if rows.len() > 64 || rows.iter().any(|r| r.symbol != default_head) {
            return Ok(None);
        }
        let mut residuals = Vec::with_capacity(rows.len());
        for row in &rows {
            let Some(rest) = row.remainder()? else {
                return Ok(Some(false));
            };
            residuals.push(rest);
        }
        let mut factors = IdentityTable::default();
        let mut packet = Vec::with_capacity(2 * rows.len());
        for (row, rest) in rows.into_iter().zip(&residuals) {
            packet.push(row.keys);
            packet.push(
                rest.iter()
                    .map(|t| factors.intern(t).ok_or(Error::InvalidStatus(255)))
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }
        let slices: Vec<_> = packet.iter().map(|row| WordSlice::new(row)).collect();
        initialize()?;
        // SAFETY: both the slice descriptors and their occurrence rows stay
        // live until the shim has copied them. Only a scalar tag is returned.
        let tag = LEAN_THREAD
            .with(|_| unsafe { tamarin_lean_ac_bag_match(slices.as_ptr(), slices.len()) });
        match tag {
            0 => Ok(None),
            1 => Ok(Some(false)),
            2 => Ok(Some(true)),
            other => Err(Error::InvalidStatus(other)),
        }
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
}
