//! Independent components of an ordinary unification problem have independent
//! witness scopes. `IndependentUnification.correctIn` justifies the full
//! Cartesian product after freshening their ranges on the original inputs.
use super::{commutative, operands, residual, Error, Outcome, RuleTable, Substitutions};
use crate::lterm::{HasFrees, LNTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::subst_vfresh::LNSubstVFresh;
use crate::vterm::var_term;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;

#[derive(Default)]
struct Component {
    equations: Vec<Equal<LNTerm>>,
    vars: Vec<LVar>,
}

fn root(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

fn partition_by_variables(equations: &[Equal<LNTerm>], include_subjects: bool) -> Vec<Component> {
    let mut parent: Vec<_> = (0..equations.len()).collect();
    let mut owners = FxHashMap::default();
    for (i, eq) in equations.iter().enumerate() {
        for side in std::iter::once(&eq.lhs).chain(include_subjects.then_some(&eq.rhs)) {
            side.for_each_free(&mut |v| {
                let previous = *owners.entry(*v).or_insert(i);
                let a = root(&mut parent, previous);
                let b = root(&mut parent, i);
                parent[a.max(b)] = a.min(b);
            });
        }
    }
    if (1..equations.len()).all(|i| root(&mut parent, i) == 0) {
        return Vec::new();
    }
    let mut parts = BTreeMap::<usize, Component>::new();
    for (i, eq) in equations.iter().enumerate() {
        parts
            .entry(root(&mut parent, i))
            .or_default()
            .equations
            .push(eq.clone());
    }
    if include_subjects {
        // Ordinary unification reopens witnesses using the component's whole
        // variable scope. Directional matching keeps its subject images frozen.
        for (v, i) in owners {
            parts.get_mut(&root(&mut parent, i)).unwrap().vars.push(v);
        }
        for part in parts.values_mut() {
            part.vars.sort_unstable();
        }
    }
    parts.into_values().collect()
}

fn partition(equations: &[Equal<LNTerm>]) -> Vec<Component> {
    partition_by_variables(equations, true)
}

pub(super) fn pattern_components(equations: &[Equal<LNTerm>]) -> Vec<Vec<Equal<LNTerm>>> {
    partition_by_variables(equations, false)
        .into_iter()
        .map(|c| c.equations)
        .collect()
}

// The local kernel returns ordinary substitutions. If an input survives
// in another input's image, its implicit identity must name the same variable
// before the entire tuple is opened as one existential scope.
fn open_component(arm: Vec<(LVar, LNTerm)>, vars: &[LVar], scope: &[LVar]) -> Subst<Name, LVar> {
    let projected = if arm.len() == vars.len() {
        LNSubstVFresh::from_list(arm)
    } else {
        let identities = vars.iter().map(|&v| (v, var_term(v)));
        LNSubstVFresh::from_list(identities.chain(arm))
    };
    projected.fresh_to_free_avoiding_vars(scope)
}

impl RuleTable {
    pub(crate) fn component_unify(&self, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        let mut input_nodes = residual::MAX_EXPANDED;
        if !(2..=64).contains(&eqs.len())
            || !residual::charge_expansion(
                &mut input_nodes,
                eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]),
                None,
            )?
            || !self.admits_terms(eqs)
        {
            return Ok(Outcome::Unsupported);
        }
        let parts = partition(eqs);
        if parts.is_empty() {
            return Ok(Outcome::Unsupported);
        }
        let mut scope: Vec<_> = parts.iter().flat_map(|c| c.vars.iter().copied()).collect();
        let reserved = scope.iter().map(|v| v.idx).collect();
        let mut budget = residual::Budget::new();
        let mut families = Vec::with_capacity(parts.len());
        let mut count = 1;
        let mut nodes = 0usize;
        for part in parts {
            let mut result = self.whole_unify(&part.equations)?;
            if matches!(result, Outcome::Unsupported) {
                result = operands::solve_branches(
                    std::iter::once(part.equations),
                    &part.vars,
                    &reserved,
                    &mut budget,
                )?;
            }
            let Outcome::Complete(arms) = result else {
                return Ok(Outcome::Unsupported);
            };
            if arms.is_empty() {
                return Ok(Outcome::Complete(Vec::new()));
            }
            let next_count = arms.len().saturating_mul(count);
            if next_count > commutative::SEARCH_LIMIT {
                return Ok(Outcome::Unsupported);
            }

            // Each earlier image will occur once per new arm. Each new
            // image (including an omitted identity) occurs in every prefix.
            let mut left = residual::MAX_EXPANDED;
            for arm in &arms {
                let Some(missing) = part.vars.len().checked_sub(arm.len()) else {
                    return Err(Error::InvalidStatus(255));
                };
                let Some(remaining) = left.checked_sub(missing) else {
                    return Ok(Outcome::Unsupported);
                };
                left = remaining;
                if !residual::charge_expansion(&mut left, arm.iter().map(|(_, t)| t), None)? {
                    return Ok(Outcome::Unsupported);
                }
            }
            nodes = nodes
                .saturating_mul(arms.len())
                .saturating_add(count.saturating_mul(residual::MAX_EXPANDED - left));
            if nodes > residual::MAX_EXPANDED {
                return Ok(Outcome::Unsupported);
            }
            count = next_count;

            // An arm lives in its own VFresh scope. Rename its whole range in
            // one pass, away from every caller key and every earlier family.
            let mut new_names = FxHashSet::default();
            let mut family = Substitutions::with_capacity(arms.len());
            for arm in arms {
                let opened = open_component(arm, &part.vars, &scope);
                for image in opened.range() {
                    image.for_each_free(&mut |v| {
                        new_names.insert(*v);
                    });
                }
                family.push(opened.into_map().into_iter().collect());
            }
            scope.extend(new_names);
            families.push(family);
        }
        let mut answers = Substitutions::with_capacity(count);
        for mut index in 0..count {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let mut arm = Vec::new();
            for family in &families {
                arm.extend_from_slice(&family[index % family.len()]);
                index /= family.len();
            }
            answers.push(arm);
        }
        Ok(Outcome::Complete(answers))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LSort};
    use crate::maude_sig::{mset_maude_sig, pair_maude_sig};
    use crate::term::f_app_ac;

    fn var(name: &str, index: u64) -> LNTerm {
        var_term(LVar::new(name, LSort::Msg, index))
    }

    #[test]
    fn bridge_in_nested_operands_keeps_constraints_on_the_same_caller_together() {
        let table = RuleTable::new(&mset_maude_sig().merge(pair_maude_sig())).unwrap();
        let eq = |lhs, rhs| Equal { lhs, rhs };
        let (x, y, z) = (var("x", 9), var("y", 9), var("z", 9));
        let a = pub_term("a");
        let rows = [
            eq(x.clone(), a.clone()),
            eq(z.clone(), pub_term("b")),
            eq(var("free", 9), var("free", 9)),
            eq(
                crate::builtin::pair(y.clone(), a.clone()),
                crate::builtin::pair(z, a.clone()),
            ),
            eq(
                f_app_ac(AcSym::Union, vec![a.clone(), y]),
                f_app_ac(AcSym::Union, vec![a, x]),
            ),
        ];
        let parts = partition(&rows);
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].equations.len(), 4);
        assert_eq!(
            table.component_unify(&rows).unwrap(),
            Outcome::Complete(Vec::new())
        );
    }

    #[test]
    fn implicit_identity_shares_its_witness_with_every_referencing_image() {
        let [x, y, z] = ["x", "y", "z"].map(|v| LVar::new(v, LSort::Msg, 0));
        let opened = open_component(vec![(x, var_term(y))], &[x, y, z], &[x, y, z]);
        assert_eq!(opened.image_of(&x), opened.image_of(&y));
        assert_ne!(opened.image_of(&y), opened.image_of(&z));
        assert!(opened.image_of(&x).is_some());
    }

    #[test]
    fn ordinary_components_ignore_variant_equations() {
        use crate::builtin::{fst, pair};
        let table = RuleTable::new(&pair_maude_sig()).unwrap();
        let a = pub_term("a");
        let b = pub_term("b");
        let ground = Equal {
            lhs: fst(pair(a.clone(), b)),
            rhs: a,
        };
        let x = var("x", 0);
        let identity = Equal {
            lhs: x.clone(),
            rhs: x,
        };
        assert_eq!(
            table.component_unify(&[identity, ground]).unwrap(),
            Outcome::Complete(Vec::new())
        );
    }

    #[test]
    fn incomplete_component_or_oversized_product_cannot_emit_a_partial_family() {
        let table = RuleTable::new(&mset_maude_sig()).unwrap();
        let sum = |ts| f_app_ac(AcSym::Union, ts);
        let independent = Equal {
            lhs: var("fixed", 0),
            rhs: pub_term("a"),
        };
        let wide = Equal {
            lhs: sum((0..33).map(|i| var("x", i)).collect()),
            rhs: sum(vec![var("y", 0), var("z", 0)]),
        };
        assert_eq!(
            table.component_unify(&[independent, wide]).unwrap(),
            Outcome::Unsupported
        );

        let offsets: Vec<_> = (0..13)
            .map(|i| Equal {
                lhs: sum(vec![var("x", i), pub_term("a")]),
                rhs: sum(vec![var("y", i), pub_term("b")]),
            })
            .collect();
        assert_eq!(
            table.component_unify(&offsets).unwrap(),
            Outcome::Unsupported
        );
    }
}
