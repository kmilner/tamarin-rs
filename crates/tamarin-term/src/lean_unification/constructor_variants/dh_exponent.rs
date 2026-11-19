//! Joint observations of an unconstrained exponent and its product with
//! one positive factor. All varying observations must use the same pair.
//! An opaque power base can never specialize to another power or DH-neutral.
use super::{dh_peer::free_exponent_rows, RuleTable};
use crate::function_symbols::{dh_neutral_sym, exp_sym, AcSym, FunSym};
use crate::lean_unification::{Error, Outcome};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::term::Term;
use crate::vterm::Lit;

fn power(term: &LNTerm) -> Option<(&LNTerm, &LNTerm)> {
    let Term::App(FunSym::NoEq(f), args) = term else {
        return None;
    };
    let [base, exponent] = args.as_ref() else {
        return None;
    };
    (*f == exp_sym()).then_some((base, exponent))
}

fn msg_var(term: &LNTerm) -> Option<LVar> {
    match term {
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => Some(*v),
        _ => None,
    }
}

fn split_product(term: &LNTerm) -> Option<(LVar, &LNTerm)> {
    let Term::App(FunSym::Ac(AcSym::Mult), args) = term else {
        return None;
    };
    let [a, b] = args.as_ref() else { return None };
    msg_var(a)
        .map(|v| (v, b))
        .or_else(|| msg_var(b).map(|v| (v, a)))
}

impl RuleTable {
    fn opaque_dh_base(&self, term: &LNTerm) -> Result<bool, Error> {
        let fixed = match term {
            Term::Lit(Lit::Var(v)) => v.sort != LSort::Msg,
            Term::App(FunSym::NoEq(f), _) => *f != exp_sym() && *f != dh_neutral_sym(),
            _ => true,
        };
        Ok(fixed && self.stably_normal(term)?)
    }

    /// None as the inner factor is an observation of g^Y alone. Its unit
    /// specialization is covered by the same rows as the extended observations.
    fn exponent_observation<'a>(
        &self,
        t: &'a LNTerm,
    ) -> Result<Option<(LVar, Option<&'a LNTerm>)>, Error> {
        let Some((outer, e)) = power(t) else {
            return Ok(split_product(t).map(|(v, r)| (v, Some(r))));
        };
        let (base, observation) = if let Some((base, y)) = power(outer) {
            (base, msg_var(y).map(|v| (v, Some(e))))
        } else {
            (
                outer,
                msg_var(e)
                    .map(|v| (v, None))
                    .or_else(|| split_product(e).map(|(v, r)| (v, Some(r)))),
            )
        };
        if observation.is_some() && self.opaque_dh_base(base)? {
            return Ok(observation);
        }
        Ok(None)
    }

    /// The caller validated the full query and collected its varying leaves.
    /// Witnesses are opened against every variable in the original query.
    pub(super) fn dh_exponent_variants(
        &self,
        query: &LNTerm,
        applications: &[&LNTerm],
    ) -> Result<Outcome, Error> {
        let mut variable = None;
        let mut factor = None;
        for &t in applications {
            let Some((v, next)) = self.exponent_observation(t)? else {
                return Ok(Outcome::Unsupported);
            };
            if variable.replace(v).is_some_and(|old| old != v) {
                return Ok(Outcome::Unsupported);
            }
            if let Some(r) = next
                && factor.replace(r).is_some_and(|old| old != r)
            {
                return Ok(Outcome::Unsupported);
            }
        }
        match (variable, factor) {
            (Some(v), Some(r)) if self.stable_dh_factor(v, r)? => free_exponent_rows(query, v, r),
            _ => Ok(Outcome::Unsupported),
        }
    }
}
