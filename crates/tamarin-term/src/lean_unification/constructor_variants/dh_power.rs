//! Normalize a DH power by root rewrites and normalization of its operands.
use super::RuleTable;
use crate::builtin::exp;
use crate::function_symbols::{exp_sym, FunSym};
use crate::lean_unification::Error;
use crate::lterm::LNTerm;
use crate::term::Term;

fn power_args(t: &LNTerm) -> Option<&[LNTerm]> {
    match t {
        Term::App(FunSym::NoEq(f), args) if *f == exp_sym() && args.len() == 2 => Some(args),
        _ => None,
    }
}

impl RuleTable {
    fn rewrite_power_root(&self, t: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if let Some(rules) = self.free_rules.get(&exp_sym()) {
            for rule in rules {
                if let Some(value) = rule.instantiate(t)? {
                    return Ok(Some(value));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn dh_power_normal(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        if !self.builtin_dh || power_args(term).is_none() {
            return Ok(None);
        }
        let Some(Some(rows)) = self.patterns.get(&exp_sym()) else {
            return Ok(None);
        };
        let mut current = term.clone();
        // Each tower step removes one power from the base. A long tower can
        // defer without publishing the intermediate result as a normal form.
        for _ in 0..64 {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let Some(args) = power_args(&current) else {
                return self.dh_product_normal(&current);
            };
            if power_args(&args[0]).is_some() {
                let Some(next) = self.rewrite_power_root(&current)? else {
                    return Ok(None);
                };
                current = next;
                continue;
            }
            let Some(base) = self.dh_product_normal(&args[0])? else {
                return Ok(None);
            };
            let Some(exponent) = self.dh_product_normal(&args[1])? else {
                return Ok(None);
            };
            let children = [base, exponent];
            let excluded = self.excludes_free_rules(rows, &children, false)?;
            let [base, exponent] = children;
            let value = exp(base, exponent);
            if excluded {
                return Ok(Some(value));
            }
            let Some(next) = self.rewrite_power_root(&value)? else {
                return Ok(None);
            };
            current = next;
        }
        Ok(None)
    }
}
