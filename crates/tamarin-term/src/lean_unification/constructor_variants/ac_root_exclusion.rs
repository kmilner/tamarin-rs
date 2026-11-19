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
        let Some(rules) = self.ac_rules.get(&symbol) else {
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
