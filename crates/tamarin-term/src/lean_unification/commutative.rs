//! A binary C root contributes two simultaneous child equations per alignment.
use super::{
    common_children, initialize, tamarin_comm_orientations, unify_by_cancellation, Error, Outcome,
    LEAN_THREAD,
};
use crate::function_symbols::FunSym;
use crate::lean_identity::IdentityTable;
use crate::lterm::{LNTerm, LVar, Name};
use crate::rewriting::Equal;
use crate::subst::Subst;
use crate::term::Term;
use crate::unification::unify_lterm_factored;
use crate::vterm::Lit;

pub(super) const SEARCH_LIMIT: usize = 4096;

fn children(eq: &Equal<LNTerm>) -> Option<[&LNTerm; 4]> {
    let (Term::App(f, left), Term::App(g, right)) = (&eq.lhs, &eq.rhs) else {
        return None;
    };
    if f != g {
        return None;
    }
    let ([a, b], [c, d]) = (left.as_ref(), right.as_ref()) else {
        return None;
    };
    match f {
        FunSym::C(_) => Some([a, b, c, d]),
        FunSym::Ac(ac) => {
            // AtomicACPair.equiv_iff: two indivisible occurrences force the
            // two nonempty opposite images to align as single occurrences.
            // Free/other-AC heads stay distinct from this one. A sorted
            // variable is atomic when its sort cannot contain this product.
            let atomic = |t| super::operands::indivisible(*ac, t);
            ((atomic(a) && atomic(b)) || (atomic(c) && atomic(d))).then_some([a, b, c, d])
        }
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum RigidHead {
    Name(Name),
    Function(FunSym),
}

pub(super) fn orientations([a, b, c, d]: [&LNTerm; 4]) -> Result<u8, Error> {
    let mut table = IdentityTable::default();
    let mut head = |t: &LNTerm| {
        let key = match t {
            Term::Lit(Lit::Var(_)) => return Ok(0),
            Term::Lit(Lit::Con(n)) => RigidHead::Name(*n),
            Term::App(f, _) => RigidHead::Function(*f),
        };
        table
            .intern(key)
            .and_then(|i| i.checked_add(1))
            .ok_or(Error::InvalidStatus(255))
    };
    let priority = if a == b || c == d {
        3
    } else if a == c || b == d {
        1
    } else if a == d || b == c {
        2
    } else {
        0
    };
    let words = [head(a)?, head(b)?, head(c)?, head(d)?];
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the verified export takes and returns native scalar words.
        let [a, b, c, d] = words;
        let mask = unsafe { tamarin_comm_orientations(a, b, c, d, priority) };
        if mask > 3 {
            Err(Error::InvalidStatus(mask))
        } else {
            Ok(mask)
        }
    })
}

// Each leaf receives the ordinary substitutions from all preceding C
// alignments. Witness-bearing AC answers already include that context;
// ground-only answers can be composed before their single freshening.
fn solve_leaf(
    pending: &[Equal<LNTerm>],
    original: &[Equal<LNTerm>],
    bindings: &Subst<Name, LVar>,
    capacity: usize,
) -> Result<Outcome, Error> {
    if pending.is_empty() {
        return Ok(Outcome::Complete(vec![common_children::freshen(
            bindings, original,
        )?]));
    }
    if let result @ Outcome::Complete(_) = super::unify_with_witnesses(pending, original, bindings)?
    {
        return Ok(result);
    }
    let result = match super::unify(pending)? {
        Outcome::Unsupported => unify_by_cancellation(pending)?,
        solved => solved,
    };
    let Outcome::Complete(arms) = result else {
        return Ok(Outcome::Unsupported);
    };
    if arms.len() > capacity {
        return Ok(Outcome::Unsupported);
    }
    let answers = arms
        .into_iter()
        .map(|arm| {
            tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
            let solved = Subst::from_list(arm).compose(bindings);
            common_children::freshen(&solved, original)
        })
        .collect::<Result<_, _>>()?;
    Ok(Outcome::Complete(answers))
}

pub(crate) fn solve(
    equations: &[Equal<LNTerm>],
    original: &[Equal<LNTerm>],
    factored: &Subst<Name, LVar>,
) -> Result<Outcome, Error> {
    let mut work = vec![(equations.to_vec(), factored.clone())];
    let mut answers = Vec::new();
    let mut visited = 0;
    while let Some((mut pending, mut bindings)) = work.pop() {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        visited += 1;
        if visited > SEARCH_LIMIT {
            return Ok(Outcome::Unsupported);
        }
        let reduction = common_children::simplify(&mut pending, &mut bindings)?;
        if matches!(reduction, common_children::Simplification::Contradiction) {
            continue;
        }
        let Some(index) = pending.iter().position(|eq| children(eq).is_some()) else {
            if visited == 1 {
                // Pure AC queries keep their existing solver budgets and
                // answer ordering. The flat AC dispatcher ran before us.
                if matches!(reduction, common_children::Simplification::Unchanged) {
                    return super::unify_with_witnesses(&pending, original, &bindings);
                }
                return solve_leaf(&pending, original, &bindings, usize::MAX);
            }
            let capacity = SEARCH_LIMIT - answers.len();
            let Outcome::Complete(branch) = solve_leaf(&pending, original, &bindings, capacity)?
            else {
                // Dropping any unfinished orientation could lose solutions.
                return Ok(Outcome::Unsupported);
            };
            if branch.len() > capacity {
                return Ok(Outcome::Unsupported);
            }
            answers.extend(branch);
            continue;
        };
        let eq = pending.remove(index);
        let terms @ [a, b, c, d] = children(&eq).expect("selected binary equation");
        let mask = orientations(terms)?;
        for (bit, r, s) in [(2, d, c), (1, c, d)] {
            if mask & bit == 0 {
                continue;
            }
            let mut next = pending.clone();
            for (u, v) in [(a, r), (b, s)] {
                if u != v {
                    next.push(Equal {
                        lhs: u.clone(),
                        rhs: v.clone(),
                    });
                }
            }
            // Factoring the whole conjunction propagates aliases and enforces
            // sorts and occurs checks across both operands and sibling goals.
            if let Some((extra, residual)) =
                unify_lterm_factored(&crate::maude_types::sort_of_name, next)
            {
                work.push((residual, extra.compose(&bindings)));
            }
        }
    }
    answers.sort_unstable();
    answers.dedup();
    Ok(Outcome::Complete(answers))
}
