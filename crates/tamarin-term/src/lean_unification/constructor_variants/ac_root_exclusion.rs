//! Exclude active AC rewrite rules under all sorted substitutions. The
//! operands must each remain one factor, so a redex must be an instance of
//! a rule on the whole product or one of its multi-operand subbags.
use super::{subgroups::ProperSubgroups, RuleTable};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_unification::{operands::indivisible, residual, Error};
use crate::lterm::{HasFrees, LNTerm, LVar};
use crate::rewriting::Equal;
use crate::term::{f_app_ac, Term};
use rustc_hash::{FxHashMap, FxHashSet};

impl RuleTable {
    /// A binary AC context is transparent if its operands retain their free
    /// heads through rewriting and no active root rule can match either
    /// alignment, even after replacing every argument below those heads.
    pub(super) fn guarded_pair(&self, symbol: AcSym, args: &[LNTerm]) -> bool {
        let [Term::App(left @ FunSym::NoEq(l), _), Term::App(right @ FunSym::NoEq(r), _)] = args
        else {
            return false;
        };
        // Distinct heads recover the two observed slots even modulo AC.
        if l == r || self.patterns.contains_key(l) || self.patterns.contains_key(r) {
            return false;
        }
        let Some(rules) = self.ordinary_rules.get(&FunSym::Ac(symbol)) else {
            return !self.ac_patterns.contains_key(&symbol);
        };
        let compatible = |pattern: &LNTerm, head: &FunSym| match pattern {
            Term::Lit(crate::vterm::Lit::Var(_)) => true,
            Term::App(f, _) => f == head,
            Term::Lit(crate::vterm::Lit::Con(_)) => false,
        };
        rules.iter().all(|rule| {
            let Term::App(_, factors) = &rule.lhs else {
                return false;
            };
            match factors.as_ref() {
                [x, y] => {
                    x == y
                        || !(compatible(x, left) && compatible(y, right)
                            || compatible(x, right) && compatible(y, left))
                }
                // Substitution cannot shrink a nonempty AC factor.
                other => other.len() > 2,
            }
        })
    }

    pub(super) fn excludes_ac_instances(
        &self,
        symbol: AcSym,
        subject: &LNTerm,
        args: &[LNTerm],
        budget: &mut residual::Budget,
    ) -> Result<bool, Error> {
        if args.len() < 2 || !args.iter().all(|t| indivisible(symbol, t)) {
            return Ok(false);
        }
        let Some(rules) = self.ordinary_rules.get(&FunSym::Ac(symbol)) else {
            return Ok(false);
        };
        let mut subject_ids = FxHashSet::default();
        subject.for_each_free(&mut |v| {
            subject_ids.insert(v.idx);
        });
        let mut reserved = subject_ids.clone();
        let mut patterns = Vec::with_capacity(rules.len());
        for rule in rules {
            // Unification assumes well-sorted inputs and the declared Maude
            // sort for every symbol, including the natural-number constant.
            let eq = Equal {
                lhs: rule.lhs.clone(),
                rhs: subject.clone(),
            };
            if !self.admits_terms(std::slice::from_ref(&eq)) {
                return Ok(false);
            }
            // Standardize the rule apart, keeping repeated occurrences of one
            // variable together. Query and rule IDs may overlap, even at MAX.
            let mut names = FxHashMap::default();
            let mut available = (0..=u64::MAX).filter(|i| !subject_ids.contains(i));
            let lhs = eq.lhs.map_free(&mut |v| {
                *names.entry(v).or_insert_with(|| {
                    let idx = available.next().expect("finite rule and subject");
                    reserved.insert(idx);
                    LVar { idx, ..v }
                })
            });
            patterns.push(lhs);
        }

        if !root_excluded(&patterns, subject, args, &reserved, budget)? {
            return Ok(false);
        }
        if args.len() == 2 {
            return Ok(true);
        }
        let Some(mut groups) = ProperSubgroups::new(args.len())? else {
            return Ok(false);
        };
        while let Some(selected) = groups.next()? {
            let factors = args
                .iter()
                .zip(selected)
                .filter_map(|(t, &used)| used.then_some(t.clone()))
                .collect();
            let piece = f_app_ac(symbol, factors);
            let Term::App(_, factors) = &piece else {
                return Err(Error::InvalidStatus(255));
            };
            if !root_excluded(&patterns, &piece, factors, &reserved, budget)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn root_excluded(
    patterns: &[LNTerm],
    piece: &LNTerm,
    args: &[LNTerm],
    reserved: &FxHashSet<u64>,
    budget: &mut residual::Budget,
) -> Result<bool, Error> {
    for pattern in patterns {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let Term::App(FunSym::Ac(_), factors) = pattern else {
            return Ok(false);
        };
        if factors.len() > args.len() {
            // Every pattern factor contributes at least one factor modulo B.
            continue;
        }
        if let ([a, b], [x, y]) = (args, factors.as_ref()) {
            for (left, right) in [(a, b), (b, a)] {
                let equations = vec![
                    Equal {
                        lhs: x.clone(),
                        rhs: left.clone(),
                    },
                    Equal {
                        lhs: y.clone(),
                        rhs: right.clone(),
                    },
                ];
                // Repeated variables share a binding across the two equations.
                if !matches!(residual::solve(equations, reserved, budget)?, Some(answers) if answers.is_empty())
                {
                    return Ok(false);
                }
            }
        } else {
            let eq = Equal {
                lhs: pattern.clone(),
                rhs: piece.clone(),
            };
            if !matches!(residual::solve(vec![eq], reserved, budget)?, Some(answers) if answers.is_empty())
            {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{hash, pair};
    use crate::lterm::{pub_term, LSort};
    use crate::maude_sig::{hash_maude_sig, mset_maude_sig, pair_maude_sig};
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::vterm::Lit;

    #[test]
    fn guarded_pair_checks_both_alignments_and_the_full_active_bucket() {
        let mut sig = mset_maude_sig()
            .merge(hash_maude_sig())
            .merge(pair_maude_sig());
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 1)));
        let h = hash(x.clone());
        let p = pair(x.clone(), pub_term("p"));
        let lhs = f_app_ac(AcSym::Union, vec![h.clone(), pair(x.clone(), x.clone())]);
        let context = RuleTable::new(&sig).unwrap();
        assert!(context.guarded_pair(AcSym::Union, &[h.clone(), p.clone()]));
        sig.st_rules
            .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, x)).unwrap());
        let active = RuleTable::new(&sig.refresh()).unwrap();
        assert!(!active.guarded_pair(AcSym::Union, &[h.clone(), p.clone()]));
        assert!(!active.guarded_pair(AcSym::Union, &[p, h]));
    }
}
