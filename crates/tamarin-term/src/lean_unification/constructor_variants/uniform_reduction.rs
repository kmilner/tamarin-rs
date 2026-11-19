//! Specialize an actual rule at a free root. All competitors must be excluded
//! and both children and result must be normal on the requested domain.
use super::{InputDomain, RuleTable};
use crate::function_symbols::FunSym;
use crate::lean_identity::IdentityTable;
use crate::lean_unification::{
    initialize, subsort, tamarin_lean_reduce_rule_slot, Error, LEAN_THREAD,
};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::rewriting::RRule;
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::{vars_vterm_in_order, Lit};

pub(super) struct FreeRule {
    rule: RRule<LNTerm>,
    keys: Vec<u64>,
    variables: Vec<LVar>,
    row_start: usize,
}

impl FreeRule {
    pub(super) fn compile(rule: &RRule<LNTerm>, row_start: usize) -> Option<Self> {
        // The wire gives literal names a query-local identity. Rule constants
        // shared with inputs must therefore be declared nullary symbols.
        if super::named_literals(&rule.lhs)
            || super::named_literals(&rule.rhs)
            || !rule.lhs.all_fun_syms(|f| matches!(f, FunSym::NoEq(_)))
        {
            return None;
        }
        let variables = vars_vterm_in_order(&rule.lhs);
        if variables.is_empty() || variables.iter().any(|v| v.sort != LSort::Msg) {
            return None;
        }
        let mut ids = IdentityTable::default();
        let keys = variables
            .iter()
            .map(|&v| ids.intern(v))
            .collect::<Option<Vec<_>>>()?;
        if vars_vterm_in_order(&rule.rhs)
            .iter()
            .any(|&v| ids.id(v).is_none())
        {
            return None;
        }
        Some(Self {
            rule: rule.clone(),
            keys,
            variables,
            row_start,
        })
    }

    pub(super) fn instantiate(&self, input: &LNTerm) -> Result<Option<LNTerm>, Error> {
        fn captures<'a>(p: &LNTerm, t: &'a LNTerm, out: &mut Vec<&'a LNTerm>) -> bool {
            match (p, t) {
                (Term::Lit(Lit::Var(_)), _) => {
                    out.push(t);
                    true
                }
                (Term::App(f, ps), Term::App(g, ts)) => {
                    f == g
                        && ps.len() == ts.len()
                        && ps.iter().zip(ts.iter()).all(|(p, t)| captures(p, t, out))
                }
                _ => false,
            }
        }
        let mut values = Vec::with_capacity(self.keys.len());
        if !captures(&self.rule.lhs, input, &mut values) {
            return Ok(None);
        }
        let mut ids = IdentityTable::default();
        let subjects = values
            .iter()
            .map(|&t| ids.intern(t).ok_or(Error::InvalidStatus(255)))
            .collect::<Result<Vec<_>, _>>()?;
        if subjects.len() != self.keys.len() {
            return Err(Error::InvalidStatus(255));
        }
        initialize()?;
        let mut selected = 0;
        let status = LEAN_THREAD.with(|_| {
            // SAFETY: captures emits one subject per compiled variable occurrence.
            // The shim copies the slices and writes at most one result word.
            unsafe {
                tamarin_lean_reduce_rule_slot(
                    self.keys[0],
                    self.keys.as_ptr(),
                    subjects.as_ptr(),
                    subjects.len(),
                    &mut selected,
                )
            }
        });
        match status {
            0 => Ok(None),
            1 if subjects.first() == Some(&selected) => {
                let subst = Subst::from_list(
                    self.variables
                        .iter()
                        .copied()
                        .zip(values.into_iter().cloned()),
                );
                Ok(Some(apply_vterm(&subst, self.rule.rhs.clone())))
            }
            1 => Err(Error::InvalidSubject(selected)),
            other => Err(Error::InvalidStatus(other)),
        }
    }
}

impl RuleTable {
    fn normal_rewrite_operand(&self, t: &LNTerm, stable: bool) -> Result<bool, Error> {
        if self.normal_tree(t, stable, &mut None)? {
            return Ok(true);
        }
        // A concrete projection can expose an irreducible signed product.
        // Uniform variants still require normality under every substitution.
        if !stable && self.builtin_dh && self.dh_product_context(t) {
            return Ok(self.dh_product_normal(t)?.as_ref() == Some(t));
        }
        Ok(false)
    }

    /// A uniform step stays the unique root reduction after any normalized
    /// substitution. Concrete normalization also admits rigid Msg variables.
    pub(super) fn checked_reduct(
        &self,
        term: &LNTerm,
        stable: bool,
    ) -> Result<Option<LNTerm>, Error> {
        let Term::App(FunSym::NoEq(head), args) = term else {
            return Ok(None);
        };
        let (Some(candidates), Some(Some(rows))) =
            (self.free_rules.get(head), self.patterns.get(head))
        else {
            return Ok(None);
        };
        for child in args.iter() {
            if !self.normal_rewrite_operand(child, stable)? {
                return Ok(None);
            }
        }
        for candidate in candidates {
            let (before, rest) = rows.split_at(candidate.row_start);
            let after = &rest[head.arity..];
            if !self.excludes_free_rules(before, args, stable)?
                || !self.excludes_free_rules(after, args, stable)?
            {
                continue;
            }
            // Validate the rule syntax before rebuilding an AC/C application
            // through smart constructors. Both source and result are sorted.
            let mut used = Vec::new();
            if self
                .collect(&candidate.rule.lhs, &mut used, InputDomain::Sorted)
                .is_none()
                || self
                    .collect(&candidate.rule.rhs, &mut used, InputDomain::Sorted)
                    .is_none()
            {
                continue;
            }
            if let Some(value) = candidate.instantiate(term)?
                && self
                    .collect(&value, &mut used, InputDomain::Sorted)
                    .is_some_and(|sort| {
                        self.declaration(FunSym::NoEq(*head))
                            .is_some_and(|(_, _, result)| subsort(sort, result))
                    })
                && self.normal_rewrite_operand(&value, stable)?
            {
                return Ok(Some(value));
            }
        }
        Ok(None)
    }

    pub(super) fn uniform_reduct(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        self.checked_reduct(term, true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{exp, mult, one_const};
    use crate::lterm::pub_term;
    use crate::vterm::var_term;

    #[test]
    fn repeated_rule_slots_share_one_simultaneous_substitution() {
        let x = var_term(LVar::new("x", LSort::Msg, 0));
        let y = var_term(LVar::new("y", LSort::Msg, 0));
        let lhs = exp(exp(x.clone(), y.clone()), x.clone());
        let rhs = exp(y.clone(), mult(x.clone(), y.clone()));
        let rule = FreeRule::compile(&RRule::new(lhs.clone(), rhs), 0).unwrap();
        let a = pub_term("a");
        let inner = exp(y.clone(), a.clone());
        assert_eq!(
            rule.instantiate(&exp(inner.clone(), y.clone())).unwrap(),
            Some(exp(a.clone(), mult(y, a.clone())))
        );
        assert_eq!(rule.instantiate(&exp(inner, a.clone())).unwrap(), None);
        assert!(FreeRule::compile(&RRule::new(lhs.clone(), one_const()), 0).is_some());
        // Numeric name IDs in the rule module need not coincide with those in
        // a later command. A declared nullary symbol has stable identity.
        assert!(FreeRule::compile(&RRule::new(lhs, a.clone()), 0).is_none());
        assert!(FreeRule::compile(&RRule::new(exp(x.clone(), a), x), 0).is_none());
    }
}
