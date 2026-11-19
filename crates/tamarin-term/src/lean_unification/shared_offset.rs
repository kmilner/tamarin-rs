//! Native-only transport of shared witnesses in x+a=y+b and x+y=z+a.
use super::*;
use crate::lterm::{occurs_free, sort_of_lnterm, HasFrees};
use crate::subst::Subst;
use std::collections::BTreeSet;

fn side(symbol: AcSym, children: &[LNTerm]) -> Option<(LVar, &LNTerm)> {
    let [left, right] = children else { return None };
    let (variable, factor) = match (left, right) {
        (Term::Lit(Lit::Var(v)), r) | (r, Term::Lit(Lit::Var(v))) => (*v, r),
        _ => return None,
    };
    // A persistent non-parent head contributes exactly one AC factor under
    // every substitution. A variable or another parent node could expand.
    match factor {
        Term::Lit(Lit::Var(_)) => return None,
        Term::App(FunSym::Ac(f), _) if *f == symbol => return None,
        _ => {}
    }
    let sort = ac_sort(symbol);
    (variable.sort == sort && subsort(sort_of_lnterm(factor), sort)).then_some((variable, factor))
}

fn distinct_heads(a: &LNTerm, b: &LNTerm) -> bool {
    match (a, b) {
        (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b))) => a != b,
        (Term::App(f, _), Term::App(g, _)) => f != g,
        (Term::Lit(Lit::Con(_)), Term::App(_, _)) | (Term::App(_, _), Term::Lit(Lit::Con(_))) => {
            true
        }
        _ => false,
    }
}

/// Normalize the summand inside an open free factor to packet row zero.
fn dependent_first(x: LVar, y: LVar, factor: &LNTerm) -> Option<[LVar; 2]> {
    if !matches!(factor, Term::App(FunSym::NoEq(_), _)) {
        return None;
    }
    let mut only_x = true;
    let mut only_y = true;
    factor.for_each_free(&mut |v| {
        only_x &= *v == x;
        only_y &= *v == y;
    });
    match (only_x, only_y) {
        (true, false) => Some([x, y]),
        (false, true) => Some([y, x]),
        _ => None,
    }
}

/// Freshening covers every variable visible before cancellation or factoring.
/// Each candidate branch starts at the same floor in its own private scope.
struct Context<'a> {
    floor: u64,
    retained: BTreeSet<LVar>,
    factored: &'a Subst<Name, LVar>,
}

impl<'a> Context<'a> {
    fn new(
        variables: &[LVar],
        factors: &[&LNTerm],
        original: &[Equal<LNTerm>],
        factored: &'a Subst<Name, LVar>,
    ) -> Self {
        let mut floor = variables.iter().map(|v| v.idx).max().unwrap_or(0);
        let mut observe = |v: &LVar| floor = floor.max(v.idx);
        for eq in original {
            eq.lhs.for_each_free(&mut observe);
            eq.rhs.for_each_free(&mut observe);
        }
        factored.for_each_free(&mut observe);
        let mut retained = BTreeSet::new();
        for term in factored.range().chain(factors.iter().copied()) {
            term.for_each_free(&mut |v| {
                if !variables.contains(v) {
                    retained.insert(*v);
                }
            });
        }
        Self {
            floor,
            retained,
            factored,
        }
    }

    fn finish(
        &self,
        bindings: Vec<(LVar, LNTerm)>,
        mut last: u64,
    ) -> Result<Vec<(LVar, LNTerm)>, Error> {
        // Preserve the sharing between each unconstrained query variable and
        // appearances of that variable inside the factored substitution.
        let mut aliases = Vec::with_capacity(self.retained.len());
        for &v in &self.retained {
            aliases.push((v, Term::Lit(Lit::Var(allocate(&mut last, v)?))));
        }
        Ok(Subst::from_list(aliases)
            .compose(&Subst::from_list(bindings))
            .compose(self.factored)
            .to_list())
    }
}

fn allocate(last: &mut u64, v: LVar) -> Result<LVar, Error> {
    *last = last.checked_add(1).ok_or(Error::FreshVariableOverflow)?;
    Ok(LVar { idx: *last, ..v })
}

pub(crate) fn solve(
    residual: &[Equal<LNTerm>],
    original: &[Equal<LNTerm>],
    factored: &Subst<Name, LVar>,
) -> Result<Outcome, Error> {
    let [equation] = residual else {
        return Ok(Outcome::Unsupported);
    };
    let Some((symbol, lhs, rhs)) = ac_children(equation) else {
        return Ok(Outcome::Unsupported);
    };
    let (left, right) = (side(symbol, lhs), side(symbol, rhs));
    let (x, a, y, b) = match (left, right) {
        (Some((x, a)), Some((y, b))) => (x, a, y, b),
        (Some((z, atom)), None) | (None, Some((z, atom))) => {
            let reversed = left.is_some();
            let variables = if reversed { rhs } else { lhs };
            let [Term::Lit(Lit::Var(x)), Term::Lit(Lit::Var(y))] = variables else {
                return Ok(Outcome::Unsupported);
            };
            let sort = ac_sort(symbol);
            if x == y || *x == z || *y == z || x.sort != sort || y.sort != sort {
                return Ok(Outcome::Unsupported);
            }
            let dependent = !crate::vterm::is_ground_vterm(atom);
            let [first, second] = if dependent {
                let Some(order) = dependent_first(*x, *y, atom) else {
                    return Ok(Outcome::Unsupported);
                };
                order
            } else {
                [*x, *y]
            };
            let vars = [first, second, z];
            let context = Context::new(&vars, &[atom], original, factored);
            return allocation_packet(symbol, vars, atom, reversed, dependent, context);
        }
        _ => return Ok(Outcome::Unsupported),
    };
    if x == y
        || !distinct_heads(a, b)
        || [a, b]
            .iter()
            .any(|t| occurs_free(&x, *t) || occurs_free(&y, *t))
    {
        return Ok(Outcome::Unsupported);
    }

    // Distinct persistent heads ensure the two factors cannot unify.
    let atoms = [a, b];
    let context = Context::new(&[x, y], &atoms, original, factored);
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the audited export returns an owned nested numeric array.
        let result = MatchRows::new(unsafe { tamarin_shared_offset(0, 1) })?;
        if result.count() != 2 {
            return Err(Error::InvalidStatus(255));
        }
        // Stable prover case numbering, independent of the candidate's enumeration.
        let mut answers = [None, None];
        for arm in 0..2 {
            if result.rows(arm) != 2 {
                return Err(Error::InvalidStatus(255));
            }
            // All allocations and aliases here belong to this answer alone.
            let mut last = context.floor;
            let mut shared_slot = None;
            let mut bindings = Vec::with_capacity(2 + context.retained.len());
            for (index, variable) in [x, y].into_iter().enumerate() {
                let mut row = [0; 2];
                let len = result.copy_row(arm, index, &mut row)?;
                let atom = match row[0] {
                    0 => atoms[0],
                    1 => atoms[1],
                    id => return Err(Error::InvalidAtom(id)),
                };
                let atom = atom.clone();
                let image = if len == 1 {
                    atom
                } else {
                    let witness = match shared_slot {
                        Some((id, v)) if id == row[1] => v,
                        Some(_) => return Err(Error::InvalidVariable(row[1])),
                        None => {
                            let v = allocate(&mut last, LVar::new("x", ac_sort(symbol), 0))?;
                            shared_slot = Some((row[1], v));
                            v
                        }
                    };
                    f_app_ac(symbol, vec![Term::Lit(Lit::Var(witness)), atom])
                };
                bindings.push((variable, image));
            }
            answers[usize::from(shared_slot.is_some())] = Some(context.finish(bindings, last)?);
        }
        let [Some(ground), Some(shared)] = answers else {
            return Err(Error::InvalidStatus(255));
        };
        Ok(Outcome::Complete(vec![ground, shared]))
    })
}

fn allocation_packet(
    symbol: AcSym,
    variables: [LVar; 3],
    factor: &LNTerm,
    reversed: bool,
    dependent: bool,
    context: Context<'_>,
) -> Result<Outcome, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: Bool is a UInt8 at Lean's C ABI. The export returns an
        // owned array of answer arrays, each containing three numeric rows.
        let result = MatchRows::new(unsafe { tamarin_rigid_allocation(u8::from(reversed)) })?;
        if result.count() != 4 {
            return Err(Error::InvalidStatus(255));
        }
        let mut answers = Vec::with_capacity(4);
        for arm in 0..result.count() {
            if result.rows(arm) != variables.len() {
                return Err(Error::InvalidStatus(255));
            }
            let mut slots = FxHashMap::default();
            let mut last = context.floor;
            let mut witness = |id: u64| -> Result<LVar, Error> {
                Ok(match slots.entry(id) {
                    std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        *entry.insert(allocate(&mut last, LVar::new("x", ac_sort(symbol), 0))?)
                    }
                })
            };
            let mut instance = factor.clone();
            if dependent {
                let mut row = [0; 2];
                let len = result.copy_row(arm, 0, &mut row)?;
                if row[..len].contains(&0) {
                    // An image containing the rigid factor that contains this
                    // same variable would have to contain itself properly.
                    continue;
                }
                if len != 1 {
                    return Err(Error::InvalidStatus(255));
                }
                let fresh = witness(row[0])?;
                instance = instance.map_free(&mut |v| if v == variables[0] { fresh } else { v });
            }
            let mut bindings = Vec::with_capacity(variables.len());
            for (index, v) in variables.into_iter().enumerate() {
                let mut row = [0; 2];
                let len = result.copy_row(arm, index, &mut row)?;
                let mut image = Vec::with_capacity(len);
                for &id in &row[..len] {
                    image.push(if id == 0 {
                        instance.clone()
                    } else {
                        Term::Lit(Lit::Var(witness(id)?))
                    });
                }
                bindings.push((v, f_app_ac(symbol, image)));
            }
            answers.push(context.finish(bindings, last)?);
        }
        if answers.len() != if dependent { 2 } else { 4 } {
            return Err(Error::InvalidStatus(255));
        }
        // Stable prover cases even when the Lean candidate enumerates the
        // packet in a different order. Slots were allocated by first use.
        answers.sort_unstable();
        Ok(Outcome::Complete(answers))
    })
}
