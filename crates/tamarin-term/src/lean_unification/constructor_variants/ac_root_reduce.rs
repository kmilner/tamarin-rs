//! Ordinary directional matching at a binary AC root. A match binds only
//! rule variables. Both alignments and every active rule must agree before
//! returning a normal value.
use super::{InputDomain, RuleTable};
use crate::function_symbols::FunSym;
use crate::lean_unification::{canonical_capture, open_match, subsort, Error, Outcome};
use crate::lterm::{frees, LNTerm};
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::is_ground_vterm;

// Free constructors align positionally, and query variables at their leaves
// remain rigid. The recursive C/AC matcher requires ground subject children.
fn admissible_operand(t: &LNTerm) -> bool {
    match t {
        Term::Lit(_) => true,
        Term::App(FunSym::NoEq(_), args) => args.iter().all(admissible_operand),
        _ => is_ground_vterm(t),
    }
}

impl RuleTable {
    pub(super) fn ac_root_reduce(&self, term: &LNTerm) -> Result<Option<LNTerm>, Error> {
        let Term::App(FunSym::Ac(ac), _) = term else {
            return Ok(None);
        };
        let Some(rules) = self.ac_rules.get(ac) else {
            return Ok(None);
        };
        let Some(sort) = self.collect(term, &mut Vec::new(), InputDomain::Sorted) else {
            return Ok(None);
        };
        let subject = canonical_capture(term);
        let Term::App(_, operands) = &subject else {
            return Ok(None);
        };
        let [a, b] = operands.as_ref() else {
            return Ok(None);
        };
        for factor in [a, b] {
            if !admissible_operand(factor) || !self.irreducible_native(factor)? {
                return Ok(None);
            }
        }

        let mut output = None;
        let mut budget = 100_000;
        for rule in rules {
            let problem = Equal {
                lhs: rule.lhs.clone(),
                rhs: subject.clone(),
            };
            if !self.admits_terms(std::slice::from_ref(&problem)) {
                return Ok(None);
            }
            let lhs = canonical_capture(&rule.lhs);
            let Term::App(_, pattern) = &lhs else {
                return Ok(None);
            };
            let [p, q] = pattern.as_ref() else {
                // Each occurrence consumes at least one factor. Admission
                // already checked arities, so this pattern is too large.
                continue;
            };
            let alignments = [(a, b), (b, a)];
            let count = if a == b || p == q { 1 } else { 2 };
            for &(first, second) in &alignments[..count] {
                let goals = [
                    Equal {
                        lhs: p.clone(),
                        rhs: first.clone(),
                    },
                    Equal {
                        lhs: q.clone(),
                        rhs: second.clone(),
                    },
                ];
                let Outcome::Complete(arms) =
                    open_match::with_captures_budget(&goals, Vec::new(), &mut budget)?
                else {
                    return Ok(None);
                };
                for arm in arms {
                    // Every variable used by the RHS must have a fixed image,
                    // including one that happens to match itself in the subject.
                    let inputs = frees(&lhs);
                    if frees(&rule.rhs).iter().any(|v| !inputs.contains(v))
                        || self
                            .collect(&rule.rhs, &mut Vec::new(), InputDomain::Sorted)
                            .is_none()
                    {
                        return Ok(None);
                    }
                    let subst = Subst::from_list(arm);
                    if canonical_capture(&apply_vterm(&subst, lhs.clone())) != subject {
                        return Err(Error::InvalidStatus(255));
                    }
                    let value = canonical_capture(&apply_vterm(&subst, rule.rhs.clone()));
                    if let Some(prior) = &output {
                        if prior != &value {
                            return Ok(None);
                        }
                    } else {
                        if !self
                            .collect(&value, &mut Vec::new(), InputDomain::Sorted)
                            .is_some_and(|s| subsort(s, sort))
                            || !self.irreducible_native(&value)?
                        {
                            return Ok(None);
                        }
                        output = Some(value);
                    }
                }
            }
        }
        // A completed search that finds no root rewrite proves normality:
        // two indivisible normal factors have no proper reducible AC subgroup.
        Ok(Some(output.unwrap_or(subject)))
    }
}
