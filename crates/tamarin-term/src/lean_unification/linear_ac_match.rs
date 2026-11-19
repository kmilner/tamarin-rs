//! Decide existence of a directional AC match with distinct full-sort captures.
//! Each capture consumes at least one frozen subject factor; one can consume all
//! additional factors. `Matching.LinearAC` relates the count comparison to
//! the simultaneous matcher, including shared frozen subject variables.
use super::{
    ac_children, ac_sort, canonical_capture, common_children, match_size, operands, residual,
    Error, RuleTable,
};
use crate::function_symbols::FunSym;
use crate::lterm::LNTerm;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::{is_ground_vterm, Lit};
use rustc_hash::FxHashSet;

impl RuleTable {
    // A flat ground row already has a direct equality check. Avoid loading
    // the rule table for it; raw nested AC children may hide a capture.
    pub(crate) fn may_be_linear_ac_match(eqs: &[Equal<LNTerm>]) -> bool {
        eqs.first()
            .and_then(ac_children)
            .is_some_and(|(f, _, pattern)| {
                pattern.len() <= residual::MAX_EXPANDED
                    && pattern.iter().any(|t| match t {
                        Term::Lit(Lit::Var(_)) => true,
                        Term::App(FunSym::Ac(g), _) => *g == f,
                        _ => false,
                    })
            })
    }

    /// Public matching orientation is subject on the left, pattern on the right.
    pub(crate) fn linear_ac_has_match(&self, eqs: &[Equal<LNTerm>]) -> Result<Option<bool>, Error> {
        if eqs.is_empty() {
            return Ok(None);
        }
        let mut budget = residual::MAX_EXPANDED;
        if !residual::charge_expansion(
            &mut budget,
            eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]),
            None,
        )? || !self.admits_terms(eqs)
        {
            return Ok(None);
        }

        let mut captures = FxHashSet::default();
        let mut matched = true;
        for eq in eqs {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some((ac, _, _)) = ac_children(eq) else {
                return Ok(None);
            };
            let mut pattern = Vec::new();
            operands::flatten(ac, &eq.rhs, &mut pattern);
            let before = captures.len();
            let mut fixed = Vec::new();
            for t in pattern {
                match t {
                    Term::Lit(Lit::Var(v)) if v.sort == ac_sort(ac) && captures.insert(*v) => {}
                    t if is_ground_vterm(t) => fixed.push(t),
                    _ => return Ok(None),
                }
            }
            let open = captures.len() - before;
            if open == 0 {
                return Ok(None);
            }
            let mut subject = Vec::new();
            operands::flatten(ac, &eq.lhs, &mut subject);
            let remaining = if fixed.is_empty() {
                subject.len()
            } else {
                // Ground fixed patterns compare modulo B on the same canonical
                // representatives as the frozen subject. Cancel occurrences,
                // including repetitions, before counting the remaining leaves.
                let fixed: Vec<_> = fixed.into_iter().map(canonical_capture).collect();
                let subject: Vec<_> = subject.into_iter().map(canonical_capture).collect();
                let (missing, rest) = common_children::residual_refs(&fixed, &subject)?;
                if !missing.is_empty() {
                    matched = false;
                    continue;
                }
                rest.len()
            };
            matched &= !match_size::excludes(open as u64, remaining as u64)?;
        }
        Ok(Some(matched))
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
                .linear_ac_has_match(std::slice::from_ref(&missing))
                .unwrap(),
            Some(false)
        );
        let nonlinear = Equal {
            lhs: sum(vec![tag.clone(), tag]),
            rhs: sum(vec![x.clone(), x]),
        };
        assert_eq!(
            table.linear_ac_has_match(&[missing, nonlinear]).unwrap(),
            None
        );
    }
}
