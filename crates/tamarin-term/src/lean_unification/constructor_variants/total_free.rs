//! Contract a total left-linear rule at a free root before reducing its
//! arguments. `TotalFree.factors` accounts for arbitrary earlier child steps.
use super::{InputDomain, RuleTable};
use crate::function_symbols::FunSym;
use crate::lean_unification::{canonical_capture, residual, subsort, Error};
use crate::lterm::LNTerm;
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::Lit;

impl RuleTable {
    pub(super) fn total_free_contract(&self, input: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let Term::App(head @ FunSym::NoEq(_), args) = input else {
            return Ok(None);
        };
        let Some([rule]) = self.ordinary_rules.get(head).map(Vec::as_slice) else {
            return Ok(None);
        };
        let Term::App(_, patterns) = &rule.lhs else {
            return Ok(None);
        };
        let Some((_, slot)) = self.input_declaration(*head, args.len()) else {
            return Ok(None);
        };
        if patterns.len() != args.len() {
            return Ok(None);
        }
        let mut captures = std::collections::BTreeMap::new();
        for (p, arg) in patterns.iter().zip(args.iter()) {
            let Term::Lit(Lit::Var(v)) = p else {
                return Ok(None);
            };
            if !subsort(slot, v.sort) || captures.insert(*v, arg.clone()).is_some() {
                return Ok(None);
            }
        }
        // Even erased arguments must form an application of the declared head.
        if !self.admits_sorted(std::iter::once(input)) {
            return Ok(None);
        }
        let subst = Subst::from_list(captures);
        let mut available = residual::MAX_EXPANDED;
        // Charge every occurrence in a duplicating RHS before materializing
        // it. Erased arguments need no copy in the contractum.
        if !residual::charge_expansion(&mut available, [&rule.rhs], Some(&subst))? {
            return Ok(None);
        }
        let value = canonical_capture(&apply_vterm(&subst, rule.rhs.clone()));
        let valid = self
            .collect(&value, &mut Vec::new(), InputDomain::Sorted)
            .is_some_and(|sort| subsort(sort, slot));
        Ok(valid.then_some(value))
    }
}
