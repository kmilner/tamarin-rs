//! Reconcile homogeneous AC answers with the original operands. The Lean
//! contract ProjectedOperands.Correct connects interned occurrences to tagged residuals.
use super::homogeneous::{Allocation, MatrixCache};
use super::{ac_sort, initialize, residual, subsort, Error, Outcome, RuleTable};
use crate::function_symbols::{AcSym, FunSym};
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, HasFrees, LNTerm, LSort, LVar};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) fn indivisible(symbol: AcSym, t: &LNTerm) -> bool {
    match t {
        Term::Lit(Lit::Var(v)) => !subsort(ac_sort(symbol), v.sort),
        Term::Lit(Lit::Con(_)) => true,
        Term::App(f, _) => *f != FunSym::Ac(symbol),
    }
}

pub(super) fn flatten<'a>(symbol: AcSym, t: &'a LNTerm, factors: &mut Vec<&'a LNTerm>) {
    if let Term::App(FunSym::Ac(f), args) = t
        && *f == symbol
    {
        for arg in args.iter() {
            flatten(symbol, arg, factors);
        }
    } else {
        factors.push(t);
    }
}

pub(super) fn allocate<'a>(
    symbol: AcSym,
    eqs: &'a [Equal<LNTerm>],
    reserved: &FxHashSet<u64>,
    matrices: &mut MatrixCache,
    remaining_calls: &mut usize,
) -> Result<Allocation<impl DoubleEndedIterator<Item = Vec<Equal<LNTerm>>> + use<'a>>, Error> {
    let outer = FunSym::Ac(symbol);
    let (matrix, mut pending): (Vec<_>, Vec<_>) = eqs.iter().partition(|e| {
        [&e.lhs, &e.rhs]
            .iter()
            .any(|t| matches!(t, Term::App(f, _) if *f == outer))
    });
    if matrix.len() > 64 {
        return Ok(Allocation::Unsupported);
    }
    let sort = ac_sort(symbol);
    let mut columns = IdentityTable::default();
    let mut rows = Vec::with_capacity(2 * matrix.len());
    let mut factors = Vec::new();
    for t in matrix.iter().flat_map(|e| [&e.lhs, &e.rhs]) {
        if !subsort(sort_of_lterm(t, sort_of_name), sort) {
            return Ok(Allocation::Unsupported);
        }
        flatten(symbol, t, &mut factors);
        let mut row = Vec::with_capacity(factors.len());
        for factor in factors.drain(..) {
            let Some(index) = columns.intern(factor).filter(|&i| i < 32) else {
                return Ok(Allocation::Unsupported);
            };
            row.push(index);
        }
        rows.push(row);
    }
    // An equality between two existing columns can constrain the basis
    // directly, without adding dimensions or introducing an AC residual.
    pending.retain(|e| {
        if rows.len() < 128
            && let (Some(l), Some(r)) = (columns.id(&e.lhs), columns.id(&e.rhs))
        {
            for i in [l, r] {
                rows.push(vec![i]);
            }
            false
        } else {
            true
        }
    });
    let width = columns.len();
    let mut mask = 0u64;
    for (i, term) in columns.values().iter().enumerate() {
        if indivisible(symbol, term) {
            mask |= 1 << i;
        }
    }
    initialize()?;
    let result = matrices.images(remaining_calls, symbol, reserved, width, mask, rows)?;
    Ok(result.map(|branches| {
        branches.into_iter().map(move |branch| {
            columns
                .values()
                .iter()
                .zip(branch)
                .map(|(&t, image)| Equal {
                    lhs: image,
                    rhs: t.clone(),
                })
                .chain(pending.iter().map(|&eq| eq.clone()))
                .collect()
        })
    }))
}

mod forced;
mod ground_branches;
mod pivot;
mod row_clash;
mod size_clash;
pub(super) use ground_branches::split as split_ground;
pub(super) use pivot::{split as split_binary_pivot, split_indivisible, split_owner};
pub(super) use size_clash::refutes as refutes_size;

impl RuleTable {
    /// Use the original caller scope when factoring the stronger presentation.
    /// The extra equations mention only operands in the original request and
    /// are entailed by it (ACForcedEquations.Forced.prepend).
    pub(crate) fn unify_forced_operands(&self, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        let mut expanded = forced::consequences(eqs)?;
        if expanded.is_empty() {
            return Ok(Outcome::Unsupported);
        }
        expanded.extend_from_slice(eqs);
        let Some((bindings, residual)) =
            crate::unification::unify_lterm_factored(&sort_of_name, expanded.clone())
        else {
            return Ok(Outcome::Complete(Vec::new()));
        };
        if bindings.is_empty() {
            return self.unify_operands(&expanded);
        }
        let Outcome::Complete(arms) = self.factored_unify(&expanded, &bindings, &residual)? else {
            return Ok(Outcome::Unsupported);
        };
        Ok(Outcome::Complete(
            crate::maude_proc::compose_checked_factor(eqs, arms, &bindings),
        ))
    }

    /// A contradiction in one conjunct or underneath matching free heads
    /// refutes the full request, even if unrelated factoring exceeds a budget.
    pub(crate) fn refutes_ac_conjunct(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, Error> {
        let mut pending: Vec<_> = eqs.iter().map(|e| (&e.lhs, &e.rhs)).collect();
        let mut attempts = 0;
        while let Some((left, right)) = pending.pop() {
            if left == right {
                continue;
            }
            match (left, right) {
                (Term::App(FunSym::NoEq(f), xs), Term::App(FunSym::NoEq(g), ys)) if f == g => {
                    pending.extend(xs.iter().zip(ys.iter()));
                }
                (Term::App(FunSym::Ac(f), _), Term::App(FunSym::Ac(g), _)) if f == g => {
                    if attempts == 16 {
                        return Ok(false);
                    }
                    attempts += 1;
                    let part = Equal {
                        lhs: left.clone(),
                        rhs: right.clone(),
                    };
                    if matches!(self.unify_operands(&[part])?, Outcome::Complete(arms) if arms.is_empty())
                    {
                        return Ok(true);
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub(crate) fn unify_operands(&self, eqs: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
        self.unify_operands_avoiding(eqs, &[])
    }

    pub(super) fn unify_operands_avoiding(
        &self,
        eqs: &[Equal<LNTerm>],
        reserved: &[LVar],
    ) -> Result<Outcome, Error> {
        let Some((vars, selected)) = self.ac_operand_query(eqs)? else {
            return Ok(Outcome::Unsupported);
        };
        let eqs = selected.as_ref();
        let used: FxHashSet<_> = vars
            .values()
            .iter()
            .chain(reserved)
            .map(|v| v.idx)
            .collect();
        let sides = || eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]);
        let top = sides().find_map(|t| match t {
            Term::App(FunSym::Ac(f), _) => Some(*f),
            _ => None,
        });
        let mut budget = residual::Budget::new();
        if let Some(symbol) = top {
            if eqs.iter().any(refutes_size) || row_clash::refutes(eqs)? {
                return Ok(Outcome::Complete(vec![]));
            }
            if let Allocation::Complete(branches) =
                allocate(symbol, eqs, &used, &mut budget.matrices, &mut 1)?
                && let result @ Outcome::Complete(_) =
                    solve_branches(branches, vars.values(), &used, &mut budget)?
            {
                return Ok(result);
            }
        } else {
            // The AC operator is under a free or commutative constructor.
            return solve_branches(
                std::iter::once(eqs.to_vec()),
                vars.values(),
                &used,
                &mut budget,
            );
        }
        if let Some(branches) = split_ground(eqs)? {
            return solve_branches(branches, vars.values(), &used, &mut budget);
        }
        // A product with many rigid occurrences can exceed the homogeneous
        // matrix limit even though splitting one factor has only linearly many arms.
        if let Some(branches) = pivot::split(eqs, &used)? {
            return solve_branches(branches.into_iter(), vars.values(), &used, &mut budget);
        }
        if let Some(branches) = split_indivisible(eqs)? {
            return solve_branches(branches.into_iter(), vars.values(), &used, &mut budget);
        }
        // Cancellation and free decomposition may expose a smaller product
        // before the residual worklist chooses an owner for an atomic factor.
        solve_branches(
            std::iter::once(eqs.to_vec()),
            vars.values(),
            &used,
            &mut budget,
        )
    }
}

/// All arms in one query project the same variables in the same order. For
/// flat images, a column records every position occupied by one witness,
/// including repetitions. Equal columns pair witnesses by a sort-preserving
/// bijection; the heads and columns then reconstruct each image modulo AC.
#[derive(Hash, PartialEq, Eq)]
struct FlatProductKey {
    heads: Vec<Option<AcSym>>,
    columns: Vec<(LSort, Vec<usize>)>,
}

impl FlatProductKey {
    fn read(arm: &[(LVar, LNTerm)]) -> Option<Self> {
        let mut heads = Vec::with_capacity(arm.len());
        let mut occurrences: FxHashMap<LVar, Vec<usize>> = FxHashMap::default();
        for (i, (_, image)) in arm.iter().enumerate() {
            let (head, factors) = match image {
                Term::Lit(Lit::Var(_)) => (None, std::slice::from_ref(image)),
                Term::App(FunSym::Ac(f), xs) if xs.len() >= 2 => (Some(*f), xs.as_ref()),
                _ => return None,
            };
            heads.push(head);
            for factor in factors {
                let Term::Lit(Lit::Var(v)) = factor else {
                    return None;
                };
                occurrences.entry(*v).or_default().push(i);
            }
        }
        let mut columns: Vec<_> = occurrences
            .into_iter()
            .map(|(v, positions)| (v.sort, positions))
            .collect();
        columns.sort_unstable();
        Some(Self { heads, columns })
    }
}

pub(super) fn solve_branches(
    branches: impl Iterator<Item = Vec<Equal<LNTerm>>>,
    vars: &[LVar],
    used: &FxHashSet<u64>,
    budget: &mut residual::Budget,
) -> Result<Outcome, Error> {
    let mut answers = super::Substitutions::new();
    for equations in branches {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let Some(solutions) = residual::solve(equations, used, budget)? else {
            return Ok(Outcome::Unsupported);
        };
        for solution in solutions {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            // Project onto the original input and rename the entire range
            // simultaneously, including any variables left unconstrained.
            let mut names = FxHashMap::default();
            let mut free = (0..=u64::MAX).filter(|i| !used.contains(i));
            answers.push(
                vars.iter()
                    .map(|&v| {
                        let t = solution
                            .image_of(&v)
                            .cloned()
                            .unwrap_or(Term::Lit(Lit::Var(v)));
                        (
                            v,
                            t.map_free(&mut |w| {
                                *names.entry(w).or_insert_with(|| {
                                    LVar::new(
                                        "x",
                                        w.sort,
                                        free.next().expect("bounded operand result"),
                                    )
                                })
                            }),
                        )
                    })
                    .collect(),
            );
        }
    }
    // Different owner choices can coincide after another equation binds
    // their witnesses. Preserve the first arm and its original spelling.
    if answers.len() > 1 {
        let mut flat = FxHashSet::default();
        let mut exact = FxHashSet::default();
        answers.retain(|arm| match FlatProductKey::read(arm) {
            Some(key) => flat.insert(key),
            None => exact.insert(arm.clone()),
        });
    }
    Ok(Outcome::Complete(answers))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::mult;
    use crate::lterm::pub_term;
    use crate::maude_sig::dh_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_ac;
    use crate::vterm::var_term;

    #[test]
    fn flat_key_preserves_sorts_heads_and_witness_multiplicities_across_images() {
        let key = |left, right| {
            FlatProductKey::read(&[
                (LVar::new("x", LSort::Msg, 0), left),
                (LVar::new("x", LSort::Msg, 1), right),
            ])
        };
        let witness = |sort, i| var_term(LVar::new("w", sort, i));
        let a = witness(LSort::Msg, 2);
        let b = witness(LSort::Msg, 3);
        let pair = mult(a.clone(), b.clone());
        let sample = key(pair.clone(), a.clone());
        assert!(sample.is_some());
        assert!(sample == key(pair.clone(), b.clone()));
        assert!(sample != key(pair.clone(), witness(LSort::Msg, 4)));
        assert!(sample != key(mult(pair.clone(), a.clone()), a.clone()));
        assert!(sample != key(mult(a.clone(), witness(LSort::Fresh, 3)), a.clone()));
        assert!(sample != key(f_app_ac(AcSym::Union, vec![a.clone(), b]), a.clone()));
        assert!(key(mult(a.clone(), pub_term("c")), a).is_none());
    }

    #[test]
    fn repeated_owners_project_each_answer_once() {
        let native = RuleTable::new(&dh_maude_sig()).unwrap();
        let fresh = |i| var_term(LVar::new("v", LSort::Fresh, i));
        let msg = |i| var_term(LVar::new("v", LSort::Msg, i));
        for (a, b, c, v, expected) in [
            (0, 1, 1, 5, 24),
            (1, 1, 1, 6, 52),
            (0, 0, 1, 6, 204),
            (0, 1, 4, 6, 204),
        ] {
            let left = mult(mult(fresh(a), fresh(b)), msg(2));
            let equations = [
                Equal {
                    lhs: left.clone(),
                    rhs: mult(mult(fresh(c), msg(3)), fresh(4)),
                },
                Equal {
                    lhs: left,
                    rhs: mult(mult(msg(5), msg(v)), fresh(7)),
                },
            ];
            let Outcome::Complete(arms) = native.unify_operands(&equations).unwrap() else {
                panic!("repeated owner should be supported");
            };
            assert_eq!(arms.len(), expected);
            for arm in arms {
                let subst = Subst::from_list(arm);
                for eq in &equations {
                    assert_eq!(
                        apply_vterm(&subst, eq.lhs.clone()),
                        apply_vterm(&subst, eq.rhs.clone())
                    );
                }
            }
        }
    }
}
