//! Normalize a DH power by root rewrites and normalization of its operands.
use super::RuleTable;
use crate::builtin::exp;
use crate::function_symbols::{dh_neutral_sym, exp_sym, one_sym, CSym, FunSym};
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
    /// PowerBucket.normal_iff reduces a sorted power's normality check to
    /// its three root rules and normal children. Group heads have their own
    /// corresponding criterion. The caller checks the children in both cases.
    pub(super) fn dh_root_normal(&self, t: &LNTerm) -> Option<bool> {
        if !self.builtin_dh {
            return None;
        }
        let Some(args) = power_args(t) else {
            return self.dh_group_root_normal(t);
        };
        let base_rewrites = matches!(&args[0], Term::App(FunSym::NoEq(f), _)
            if *f == exp_sym() || *f == dh_neutral_sym());
        let exponent_is_unit = matches!(&args[1], Term::App(FunSym::NoEq(f), _) if *f == one_sym());
        Some(!base_rewrites && !exponent_is_unit)
    }

    /// An exact DH inventory gives signed expressions a unique normal value.
    /// A power spine also has a unique value when its base stays normal and
    /// every exponent has a defined signed count under the same substitution.
    /// Bilinear.PowerSpine.caller_power_map also covers a pairing of stable
    /// operands under the exact joint DH and bilinear inventories.
    pub(super) fn dh_unique_instances(&self, t: &LNTerm) -> Result<bool, Error> {
        if !self.builtin_dh {
            return Ok(false);
        }
        let Some(mut args) = power_args(t) else {
            return self.dh_signed_expression(t);
        };
        loop {
            if !self.dh_signed_expression(&args[1])? {
                return Ok(false);
            }
            let Some(inner) = power_args(&args[0]) else {
                if self.builtin_bp
                    && let Term::App(FunSym::C(CSym::EMap), points) = &args[0]
                    && let [left, right] = points.as_ref()
                {
                    return Ok(
                        self.stably_normal_native(left)? && self.stably_normal_native(right)?
                    );
                }
                return self.stably_normal_native(&args[0]);
            };
            args = inner;
        }
    }

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
            let base = if self.builtin_bp
                && let Term::App(FunSym::C(CSym::EMap), points) = &args[0]
                && let [left, right] = points.as_ref()
                && self.join_normal(left)? == Some(true)
                && self.join_normal(right)? == Some(true)
            {
                self.scalar_action_normal(&args[0])?
            } else {
                self.dh_product_normal(&args[0])?
            };
            let Some(base) = base else {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{emap, fst, hash, inv, msg_var, mult};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};

    #[test]
    fn pairing_power_spine_checks_its_operands_and_live_rules() {
        let mut sig = bp_maude_sig().merge(pair_maude_sig());
        let table = RuleTable::new(&sig).unwrap();
        let x = msg_var("x", 0);
        let y = msg_var("y", 1);
        let pairing = emap(x.clone(), x.clone());
        let tower = exp(exp(pairing.clone(), inv(y.clone())), x.clone());
        assert!(table.dh_unique_instances(&tower).unwrap());
        let changing = exp(emap(x.clone(), fst(y.clone())), x.clone());
        assert!(!table.dh_unique_instances(&changing).unwrap());
        sig.st_rules.insert(CtxtStRule::new(
            pairing,
            StRhs {
                positions: vec![vec![0]],
                term: x,
            },
        ));
        let changed = RuleTable::new(&sig).unwrap();
        assert!(!changed.dh_unique_instances(&tower).unwrap());
    }

    #[test]
    fn power_spine_uniqueness_requires_stable_leaves_and_exact_live_rules() {
        let mut sig = dh_maude_sig()
            .merge(hash_maude_sig())
            .merge(pair_maude_sig());
        let table = RuleTable::new(&sig).unwrap();
        let x = msg_var("x", 0);
        let product = mult(x.clone(), hash(x.clone()));
        let power = exp(exp(x.clone(), product.clone()), inv(x.clone()));
        assert!(table.dh_unique_instances(&power).unwrap());
        assert!(!table.dh_unique_instances(&exp(product, x.clone())).unwrap());
        assert!(!table
            .dh_unique_instances(&exp(x.clone(), fst(x.clone())))
            .unwrap());
        sig.st_rules.insert(CtxtStRule::new(
            exp(x.clone(), x.clone()),
            StRhs {
                positions: vec![vec![0]],
                term: x,
            },
        ));
        let changed = RuleTable::new(&sig).unwrap();
        assert!(!changed.dh_unique_instances(&power).unwrap());
    }
}
