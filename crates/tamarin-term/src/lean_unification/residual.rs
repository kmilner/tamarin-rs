//! Bounded search for the equations left by operand abstraction. Lean selects
//! each equation transformation. The adapter applies ordinary substitutions
//! until the caller projects complete leaves onto the original variables.
use super::{
    ac_children, common_children,
    commutative::{orientations, RigidHead},
    operands, sort_word, Error, LEAN_THREAD,
};
use crate::function_symbols::FunSym;
use crate::lean_identity::IdentityTable;
use crate::lterm::{sort_of_lterm, HasFrees, LNTerm, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::FxHashSet;

unsafe extern "C" {
    fn tamarin_lean_residual_variable(
        right: u8,
        key: u64,
        key_sort: u64,
        kind: u8,
        value_sort: u64,
        ids: *const u64,
        count: usize,
    ) -> u8;
    fn tamarin_lean_residual_rigid(
        left_kind: u8,
        left_head: u64,
        left_children: *const u64,
        left_count: usize,
        right_kind: u8,
        right_head: u64,
        right_children: *const u64,
        right_count: usize,
    ) -> u8;
}

fn kind(t: &LNTerm) -> Result<u8, Error> {
    Ok(match t {
        Term::Lit(Lit::Var(_)) => 0,
        Term::Lit(Lit::Con(_)) => 1,
        Term::App(FunSym::NoEq(_), _) => 2,
        Term::App(FunSym::C(_), _) => 3,
        Term::App(FunSym::Ac(_), _) => 4,
        Term::App(FunSym::List, _) => return Err(Error::InvalidStatus(255)),
    })
}

// Wire actions are defined by Residual.Justified in the fixed Lean contract.
const OPEN_AC: u8 = 0;
const CLASH: u8 = 1;
const DISCARD: u8 = 2;
const BIND_LEFT: u8 = 3;
const BIND_RIGHT: u8 = 4;
const FREE_CHILDREN: u8 = 5;
const COMMUTATIVE: u8 = 6;

// Identities and scratch space last for a single worklist invocation. Occurrences
// share the same identity table as the selected key, including name, index and sort.
#[derive(Default)]
struct OperandInventory {
    heads: IdentityTable<RigidHead>,
    keys: IdentityTable<LVar>,
    occurrences: Vec<u64>,
}

impl OperandInventory {
    fn variable(&mut self, right: bool, key: LVar, value: &LNTerm) -> Result<u8, Error> {
        let id = self.keys.intern(key).ok_or(Error::InvalidStatus(255))?;
        self.occurrences.clear();
        let mut valid = Ok(());
        value.for_each_free(&mut |v| match self.keys.intern(*v) {
            Some(word) => self.occurrences.push(word),
            None => valid = Err(Error::InvalidStatus(255)),
        });
        valid?;
        let kind = kind(value)?;
        let sort = sort_word(sort_of_lterm(value, sort_of_name));
        Ok(LEAN_THREAD.with(|_| unsafe {
            // SAFETY: the shim copies the borrowed occurrence words before returning.
            tamarin_lean_residual_variable(
                right.into(),
                id,
                sort_word(key.sort),
                kind,
                sort,
                self.occurrences.as_ptr(),
                self.occurrences.len(),
            )
        }))
    }
}

fn rigid_root(t: &LNTerm) -> Result<(u8, RigidHead, &[LNTerm]), Error> {
    match t {
        Term::Lit(Lit::Con(n)) => Ok((1, RigidHead::Name(*n), &[])),
        Term::App(f, args) => Ok((kind(t)?, RigidHead::Function(*f), args)),
        Term::Lit(Lit::Var(_)) => Err(Error::InvalidStatus(255)),
    }
}

fn action(a: &LNTerm, b: &LNTerm, inventory: &mut OperandInventory) -> Result<u8, Error> {
    if let Term::Lit(Lit::Var(v)) = a {
        return inventory.variable(false, *v, b);
    }
    if let Term::Lit(Lit::Var(v)) = b {
        return inventory.variable(true, *v, a);
    }
    let (lk, lh, left) = rigid_root(a)?;
    let (rk, rh, right) = rigid_root(b)?;
    let lh = inventory
        .heads
        .intern(lh)
        .ok_or(Error::InvalidStatus(255))?;
    let rh = inventory
        .heads
        .intern(rh)
        .ok_or(Error::InvalidStatus(255))?;
    // The same table encodes both ordered rows, so independent allocations
    // of equal child terms receive the same ID. It borrows only this pair.
    let mut children = IdentityTable::default();
    inventory.occurrences.clear();
    for child in left.iter().chain(right) {
        let id = children.intern(child).ok_or(Error::InvalidStatus(255))?;
        inventory.occurrences.push(id);
    }
    let (ls, rs) = inventory.occurrences.split_at(left.len());
    Ok(LEAN_THREAD.with(|_| unsafe {
        // SAFETY: the rows live for this call and the shim copies their words.
        tamarin_lean_residual_rigid(lk, lh, ls.as_ptr(), ls.len(), rk, rh, rs.as_ptr(), rs.len())
    }))
}

/// Peel injective one-hole contexts to compare the equality inside them.
/// Each step descends to strict children of the original roots. A pair that
/// does not admit another step is still a valid key for the row selector.
pub(super) fn inner_equality<'a>(
    mut lhs: &'a LNTerm,
    mut rhs: &'a LNTerm,
) -> Result<(&'a LNTerm, &'a LNTerm), Error> {
    let mut inventory = OperandInventory::default();
    while let (Term::App(f, left), Term::App(g, right)) = (lhs, rhs) {
        if f != g || left.len() != right.len() || lhs == rhs {
            break;
        }
        let children = match f {
            FunSym::NoEq(_) => {
                let mut changed = left.iter().zip(right.iter()).filter(|(a, b)| a != b);
                let Some(pair) = changed.next() else { break };
                if changed.next().is_some() || action(lhs, rhs, &mut inventory)? != FREE_CHILDREN {
                    break;
                }
                pair
            }
            FunSym::Ac(_) if left.len() >= 2 => {
                let (a, b) = common_children::residual_refs(left.iter(), right.iter())?;
                let ([a], [b]) = (a.as_slice(), b.as_slice()) else {
                    break;
                };
                (*a, *b)
            }
            _ => break,
        };
        (lhs, rhs) = children;
    }
    Ok((lhs, rhs))
}

type Bindings = Subst<Name, LVar>;

#[derive(Clone)]
struct State {
    pending: Vec<Equal<LNTerm>>,
    deferred: Vec<Equal<LNTerm>>,
    bindings: Bindings,
}

// A fork can repeat the full expansion cost of this arm. All matrix arms
// and C orientations draw from one query budget.
pub(super) struct Budget {
    nodes: usize,
    theory_steps: usize,
    commutative_states: usize,
    nested_matrices: usize,
    pub(super) matrices: super::homogeneous::MatrixCache,
}

impl Budget {
    pub(super) fn new() -> Self {
        Self {
            nodes: 1 << 22,
            theory_steps: 1 << 16,
            commutative_states: super::commutative::SEARCH_LIMIT - 1,
            nested_matrices: 64,
            matrices: super::homogeneous::MatrixCache::default(),
        }
    }

    fn charge<'a>(
        &mut self,
        terms: impl IntoIterator<Item = &'a LNTerm>,
        bindings: Option<&Bindings>,
    ) -> Result<bool, Error> {
        charge_expansion(&mut self.nodes, terms, bindings)
    }
}

pub(super) const MAX_EXPANDED: usize = 65_536;

/// Bound an actual simultaneous substitution before materializing it.
/// A mapped variable is charged for its whole image at that occurrence;
/// the image itself is already in solved form. AC flattening can only
/// shorten this count. The per-operation bound also limits traversal of
/// heavily shared input terms when the request is already too large.
pub(super) fn charge_expansion<'a>(
    nodes: &mut usize,
    terms: impl IntoIterator<Item = &'a LNTerm>,
    bindings: Option<&Bindings>,
) -> Result<bool, Error> {
    const MAX_DEPTH: usize = 256;

    fn visit(t: &LNTerm, bindings: Option<&Bindings>, remaining: &mut usize, depth: usize) -> bool {
        if *remaining == 0 || depth > MAX_DEPTH {
            return false;
        }
        if let Term::Lit(Lit::Var(v)) = t
            && let Some(image) = bindings.and_then(|s| s.image_of(v))
        {
            return visit(image, None, remaining, depth);
        }
        *remaining -= 1;
        match t {
            Term::Lit(_) => true,
            Term::App(_, xs) => xs.iter().all(|x| visit(x, bindings, remaining, depth + 1)),
        }
    }

    let limit = MAX_EXPANDED.min(*nodes);
    let mut remaining = limit;
    let fits = terms
        .into_iter()
        .all(|t| visit(t, bindings, &mut remaining, 0));
    *nodes -= limit - remaining;
    tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
    Ok(fits)
}

fn sides(equations: &[Equal<LNTerm>]) -> impl Iterator<Item = &LNTerm> {
    equations.iter().flat_map(|e| [&e.lhs, &e.rhs])
}

fn push_pair(pending: &mut Vec<Equal<LNTerm>>, a: &LNTerm, b: &LNTerm) {
    pending.push(Equal {
        lhs: a.clone(),
        rhs: b.clone(),
    });
}

pub(super) fn solve(
    equations: Vec<Equal<LNTerm>>,
    original: &FxHashSet<u64>,
    budget: &mut Budget,
) -> Result<Option<Vec<Bindings>>, Error> {
    solve_with(equations, original, budget, false)
}

/// Variant joins collect a set of simultaneous instances. They can select
/// a smaller complete pivot before a matrix without exposing branch order.
pub(super) fn solve_join(
    equations: Vec<Equal<LNTerm>>,
    original: &FxHashSet<u64>,
    budget: &mut Budget,
) -> Result<Option<Vec<Bindings>>, Error> {
    solve_with(equations, original, budget, true)
}

fn solve_with(
    mut equations: Vec<Equal<LNTerm>>,
    original: &FxHashSet<u64>,
    budget: &mut Budget,
    pivot_first: bool,
) -> Result<Option<Vec<Bindings>>, Error> {
    super::initialize()?;
    if !budget.charge(sides(&equations), None)? {
        return Ok(None);
    }
    equations.reverse();
    let mut work = vec![State {
        pending: equations,
        deferred: Vec::new(),
        bindings: Bindings::empty(),
    }];
    let mut answers = Vec::new();
    let mut inventory = OperandInventory::default();
    'branches: while let Some(mut state) = work.pop() {
        while let Some(eq) = state.pending.pop() {
            if !budget.charge([&eq.lhs, &eq.rhs], Some(&state.bindings))? {
                return Ok(None);
            }
            let lhs = apply_vterm(&state.bindings, eq.lhs);
            let rhs = apply_vterm(&state.bindings, eq.rhs);
            let next = action(&lhs, &rhs, &mut inventory)?;
            // AC and commutative transformations additionally share a step
            // budget, including rechecks of a suspended pair after a binding.
            if matches!(next, OPEN_AC | COMMUTATIVE) {
                let Some(remaining) = budget.theory_steps.checked_sub(1) else {
                    return Ok(None);
                };
                budget.theory_steps = remaining;
            }
            match next {
                OPEN_AC => {
                    let eq = Equal { lhs, rhs };
                    let Some((symbol, left, right)) = ac_children(&eq) else {
                        return Err(Error::InvalidStatus(OPEN_AC));
                    };
                    let (a, b) = common_children::residuals(left, right)?;
                    if a.len() == left.len() {
                        state.deferred.push(eq);
                    } else {
                        match (a.is_empty(), b.is_empty()) {
                            (true, true) => {}
                            (false, false) => state.pending.push(Equal {
                                lhs: f_app_ac(symbol, a),
                                rhs: f_app_ac(symbol, b),
                            }),
                            _ => continue 'branches,
                        }
                    }
                }
                CLASH => continue 'branches,
                DISCARD => {}
                side @ (BIND_LEFT | BIND_RIGHT) => {
                    let (key, image) = if side == BIND_LEFT {
                        (lhs, rhs)
                    } else {
                        (rhs, lhs)
                    };
                    let Term::Lit(Lit::Var(v)) = key else {
                        return Err(Error::InvalidStatus(side));
                    };
                    let binding = Bindings::from_list([(v, image)]);
                    if !budget.charge(
                        state.bindings.range().chain(binding.range()),
                        Some(&binding),
                    )? {
                        return Ok(None);
                    }
                    state.bindings = binding.compose(&state.bindings);
                    // A binding can make a previously open AC pair identical.
                    // Only a new binding reactivates a deferred equation.
                    state.pending.append(&mut state.deferred);
                }
                FREE_CHILDREN => {
                    let (Term::App(_, a), Term::App(_, b)) = (&lhs, &rhs) else {
                        return Err(Error::InvalidStatus(FREE_CHILDREN));
                    };
                    if a.len() != b.len() {
                        return Err(Error::InvalidStatus(FREE_CHILDREN));
                    }
                    for (x, y) in a.iter().zip(b.iter()).rev() {
                        push_pair(&mut state.pending, x, y);
                    }
                }
                COMMUTATIVE => {
                    let (Term::App(_, left), Term::App(_, right)) = (&lhs, &rhs) else {
                        return Err(Error::InvalidStatus(COMMUTATIVE));
                    };
                    let ([a, b], [c, d]) = (left.as_ref(), right.as_ref()) else {
                        return Err(Error::InvalidStatus(COMMUTATIVE));
                    };
                    let mask = orientations([a, b, c, d])?;
                    if mask == 0 {
                        continue 'branches;
                    }
                    // Every admitted orientation creates a continuation, including
                    // the one processed in place. AC cancellation and rebinding
                    // must not restart the C worklist's shared state budget.
                    let Some(left) = budget
                        .commutative_states
                        .checked_sub(mask.count_ones() as usize)
                    else {
                        return Ok(None);
                    };
                    budget.commutative_states = left;
                    if mask == 3 {
                        if !budget.charge(
                            sides(&state.pending)
                                .chain(sides(&state.deferred))
                                .chain(state.bindings.range())
                                .chain([a, b, c, d]),
                            None,
                        )? {
                            return Ok(None);
                        }
                        let mut crossed = state.clone();
                        push_pair(&mut crossed.pending, b, c);
                        push_pair(&mut crossed.pending, a, d);
                        work.push(crossed);
                    }
                    let (x, y) = if mask == 2 { (d, c) } else { (c, d) };
                    push_pair(&mut state.pending, b, y);
                    push_pair(&mut state.pending, a, x);
                }
                code => return Err(Error::InvalidStatus(code)),
            }
        }
        // A cancelled AC context or a decomposed free head can expose an
        // equality that was already pending at another root.
        super::whole::refine_pending(&mut state.deferred)?;
        let Some(first) = state.deferred.first() else {
            answers.push(state.bindings);
            continue;
        };
        let Some((symbol, _, _)) = ac_children(first) else {
            return Err(Error::InvalidStatus(OPEN_AC));
        };
        if !budget.charge(sides(&state.deferred).chain(state.bindings.range()), None)? {
            return Ok(None);
        }
        // A homogeneous matrix hides variables below operand constructors.
        // Check their contribution to finite term size before allocating it.
        if state.deferred.iter().any(operands::refutes_size) {
            continue;
        }
        // Earlier witnesses may survive only in the image of an original
        // variable. Reusing such a witness would silently constrain that image.
        let mut reserved = original.clone();
        let mut reserve = |v: &LVar| {
            reserved.insert(v.idx);
        };
        state.bindings.for_each_free(&mut reserve);
        for eq in &state.deferred {
            eq.lhs.for_each_free(&mut reserve);
            eq.rhs.for_each_free(&mut reserve);
        }
        let pivot = if pivot_first {
            match operands::split_binary_pivot(&state.deferred, &reserved)? {
                Some(branches) => Some(branches),
                None => operands::split_indivisible(&state.deferred)?,
            }
        } else {
            None
        };
        let branches: Box<dyn DoubleEndedIterator<Item = _>> = if let Some(branches) = pivot {
            Box::new(branches.into_iter())
        } else {
            match operands::allocate(
                symbol,
                &state.deferred,
                &reserved,
                &mut budget.matrices,
                &mut budget.nested_matrices,
            )? {
                super::homogeneous::Allocation::Complete(branches) => Box::new(branches),
                super::homogeneous::Allocation::Exhausted => return Ok(None),
                super::homogeneous::Allocation::Unsupported => {
                    if let Some(branches) = operands::split_ground(&state.deferred)? {
                        Box::new(branches)
                    } else if let Some(branches) = operands::split_indivisible(&state.deferred)? {
                        Box::new(branches.into_iter())
                    } else if let Some(branches) =
                        operands::split_owner(&state.deferred, &reserved)?
                    {
                        Box::new(branches.into_iter())
                    } else {
                        return Ok(None);
                    }
                }
            }
        };
        for mut pending in branches.rev() {
            if !budget.charge(sides(&pending).chain(state.bindings.range()), None)? {
                return Ok(None);
            }
            pending.reverse();
            work.push(State {
                pending,
                deferred: Vec::new(),
                bindings: state.bindings.clone(),
            });
        }
    }
    Ok(Some(answers))
}

impl super::RuleTable {
    /// Interpret variables on the subject side as rigid atoms of their own sort.
    /// The tree matcher keeps subject terms in caller representation, so bound
    /// images already contain the original variables, including self occurrences.
    pub(crate) fn match_rigid_subjects(
        &self,
        equations: &[Equal<LNTerm>],
    ) -> Result<super::Outcome, Error> {
        if !Budget::new().charge(sides(equations), None)? || !self.admits_terms(equations) {
            return Ok(super::Outcome::Unsupported);
        }
        // Check the entire conjunction before spending the search budget on
        // earlier AC partitions. A subject variable is rigid at this point.
        if equations.iter().any(|eq| match (&eq.lhs, &eq.rhs) {
            (Term::Lit(Lit::Var(_)), _) => false,
            (Term::App(f, _), Term::App(g, _)) => f != g,
            (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b))) => a != b,
            _ => true,
        }) {
            return Ok(super::Outcome::Complete(Vec::new()));
        }
        let canonical = equations
            .iter()
            .map(|eq| Equal {
                lhs: super::canonical_capture(&eq.lhs),
                rhs: super::canonical_capture(&eq.rhs),
            })
            .collect::<Vec<_>>();
        // This count is valid on flattened representatives, even when later
        // pattern variables can expand to AC products. B has no empty factor.
        if canonical.iter().any(|e| {
            matches!((&e.lhs, &e.rhs),
            (Term::App(FunSym::Ac(f), ps), Term::App(FunSym::Ac(g), ss))
                if f == g && ps.len() > ss.len())
        }) {
            return Ok(super::Outcome::Complete(Vec::new()));
        }
        super::open_match::with_captures(&canonical, Vec::new())
    }

    /// Bare captures are forced by the ground subjects. Seed the remaining
    /// structural matches with those images, including when a variable also
    /// occurs below a constructor or in several AC partitions.
    pub(crate) fn match_ground_captures(
        &self,
        equations: &[Equal<LNTerm>],
    ) -> Result<super::Outcome, Error> {
        use super::Outcome;
        use crate::vterm::is_ground_vterm;
        if !equations
            .iter()
            .any(|e| matches!(e.lhs, Term::Lit(Lit::Var(_))))
        {
            return Ok(Outcome::Unsupported);
        }
        let mut budget = Budget::new();
        if !budget.charge(sides(equations), None)? {
            return Ok(Outcome::Unsupported);
        }
        let mut keys = FxHashSet::default();
        for eq in equations {
            if !is_ground_vterm(&eq.rhs) {
                return Ok(Outcome::Unsupported);
            }
            if let Term::Lit(Lit::Var(v)) = eq.lhs {
                keys.insert(v);
            }
        }
        if !self.admits_terms(equations) {
            return Ok(Outcome::Unsupported);
        }
        let mut captures = Vec::new();
        let mut patterns = Vec::new();
        for eq in equations {
            let rhs = super::canonical_capture(&eq.rhs);
            if let Term::Lit(Lit::Var(_)) = eq.lhs {
                captures.push(Equal {
                    lhs: eq.lhs.clone(),
                    rhs,
                });
            } else if !is_ground_vterm(&eq.lhs) {
                patterns.push(Equal {
                    lhs: super::canonical_capture(&eq.lhs),
                    rhs,
                });
            } else if super::canonical_capture(&eq.lhs) != rhs {
                // Substitution fixes ground terms. An unequal closed guard
                // refutes the entire conjunction before expanding any image.
                return Ok(Outcome::Complete(vec![]));
            }
        }
        let reserved = keys.iter().map(|v| v.idx).collect();
        let Some(arms) = solve(captures, &reserved, &mut budget)? else {
            return Ok(Outcome::Unsupported);
        };
        if arms.len() > 1 {
            return Ok(Outcome::Unsupported);
        }
        let mut answers = Vec::new();
        for arm in arms {
            let bindings = arm.to_list();
            if bindings.len() != keys.len()
                || !bindings
                    .iter()
                    .all(|(v, t)| keys.contains(v) && is_ground_vterm(t))
            {
                return Ok(Outcome::Unsupported);
            }
            if !patterns.is_empty() {
                // A forced image is ground, so apply it simultaneously only
                // to the pattern. Each occurrence consumes the full image's
                // expansion budget before rebuilding and flattening any AC node.
                if !budget.charge(patterns.iter().map(|eq| &eq.lhs), Some(&arm))? {
                    return Ok(Outcome::Unsupported);
                }
                for eq in &mut patterns {
                    if let Some(specialized) = crate::subst::apply_vterm_changed(&arm, &eq.lhs) {
                        eq.lhs = specialized;
                    }
                }
                return super::open_match::with_captures(&patterns, bindings);
            }
            answers.push(bindings);
        }
        Ok(Outcome::Complete(answers))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::emap;
    use crate::function_symbols::AcSym;
    use crate::lterm::LSort;

    #[test]
    fn independent_pair_bindings_are_charged_by_their_actual_size() {
        let key = |i| LVar::new("x", LSort::Msg, i);
        let image = crate::builtin::pair(crate::lterm::pub_term("a"), crate::lterm::pub_term("b"));
        let equations = (0..32)
            .map(|i| Equal {
                lhs: Term::Lit(Lit::Var(key(i))),
                rhs: image.clone(),
            })
            .collect();
        let arms = solve(equations, &FxHashSet::default(), &mut Budget::new())
            .unwrap()
            .unwrap();
        assert_eq!(arms.len(), 1);
        for i in 0..32 {
            assert_eq!(arms[0].image_of(&key(i)), Some(&image));
        }
    }

    #[test]
    fn exponential_growth_in_earlier_images_defers_the_entire_query() {
        let var = |i| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
        let equations = (0..22)
            .map(|i| Equal {
                lhs: var(i),
                rhs: crate::builtin::pair(var(i + 1), var(i + 1)),
            })
            .collect();
        let mut budget = Budget::new();
        assert_eq!(
            solve(equations, &FxHashSet::default(), &mut budget),
            Ok(None)
        );
        assert!(budget.nodes > 0, "the per-operation limit must apply");
    }

    #[test]
    fn charge_counts_repeated_images_under_simultaneous_substitution() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 1);
        let twice = |v| crate::builtin::pair(Term::Lit(Lit::Var(v)), Term::Lit(Lit::Var(v)));
        let bindings = Bindings::from_list([(x, twice(y)), (y, twice(x))]);
        let input = twice(x);
        for (nodes, fits) in [(6, false), (7, true)] {
            let mut budget = Budget {
                nodes,
                ..Budget::new()
            };
            assert_eq!(budget.charge([&input], Some(&bindings)), Ok(fits));
            assert_eq!(budget.nodes, 0);
        }
    }

    #[test]
    fn cancellation_survives_an_exhausted_initial_size_budget() {
        use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
        let token = CancellationToken::default();
        token.request_cancel();
        let _guard = CancellationGuard::new(Some(token));
        let t = crate::lterm::pub_term("a");
        let mut budget = Budget {
            nodes: 0,
            ..Budget::new()
        };
        assert_eq!(
            solve(
                vec![Equal {
                    lhs: t.clone(),
                    rhs: t
                }],
                &FxHashSet::default(),
                &mut budget
            ),
            Err(Error::Cancelled)
        );
    }

    #[test]
    fn checked_variable_steps_use_full_identities_and_distinguish_proper_occurrences() {
        super::super::initialize().unwrap();
        let mut vars = OperandInventory::default();
        let var = |s, sort| Term::Lit(Lit::Var(LVar::new(s, sort, 17)));
        let x = var("x", LSort::Msg);
        let narrower = var("x", LSort::Fresh);
        let renamed = var("alias", LSort::Msg);
        let independent = crate::builtin::pair(narrower.clone(), renamed.clone());
        let cyclic =
            crate::builtin::pair(renamed, crate::builtin::pair(x.clone(), narrower.clone()));

        assert_eq!(action(&x, &x, &mut vars), Ok(DISCARD));
        assert_eq!(action(&x, &narrower, &mut vars), Ok(BIND_LEFT));
        assert_eq!(action(&narrower, &x, &mut vars), Ok(BIND_RIGHT));
        assert_eq!(action(&x, &independent, &mut vars), Ok(BIND_LEFT));
        assert_eq!(action(&independent, &x, &mut vars), Ok(BIND_RIGHT));
        assert_eq!(action(&cyclic, &x, &mut vars), Ok(CLASH));
        assert_eq!(action(&x, &cyclic, &mut vars), Ok(CLASH));
        assert_eq!(
            action(&narrower, &var("x", LSort::Pub), &mut vars),
            Ok(CLASH)
        );
    }

    #[test]
    fn checked_rigid_steps_compare_roots_and_each_ordered_child() {
        use crate::builtin::{hash, pair};
        use crate::lterm::{fresh_term, pub_term};

        super::super::initialize().unwrap();
        let mut inventory = OperandInventory::default();
        let mut classify = |a: &LNTerm, b: &LNTerm| action(a, b, &mut inventory);
        let x = Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, 17)));
        let y = Term::Lit(Lit::Var(LVar::new("v", LSort::Fresh, 17)));
        let n = pub_term("n");
        assert_eq!(classify(&n, &fresh_term("n")), Ok(CLASH));
        assert_eq!(classify(&n, &n), Ok(DISCARD));
        assert_eq!(classify(&n, &hash(n.clone())), Ok(CLASH));

        let lhs = pair(hash(x.clone()), y.clone());
        let equal = pair(hash(x.clone()), y.clone());
        assert_eq!(classify(&lhs, &equal), Ok(DISCARD));
        assert_eq!(
            classify(&lhs, &pair(y.clone(), hash(x.clone()))),
            Ok(FREE_CHILDREN)
        );
        assert_eq!(classify(&lhs, &emap(x.clone(), y.clone())), Ok(CLASH));
        assert_eq!(
            classify(&emap(x.clone(), n.clone()), &emap(n.clone(), y.clone())),
            Ok(COMMUTATIVE)
        );
        let union = |xs| f_app_ac(AcSym::Union, xs);
        let repeated = union(vec![x.clone(), x.clone(), y.clone()]);
        assert_eq!(
            classify(&repeated, &union(vec![y.clone(), x.clone(), x.clone()])),
            Ok(DISCARD)
        );
        assert_eq!(
            classify(&repeated, &union(vec![x, y.clone(), y])),
            Ok(OPEN_AC)
        );
    }

    #[test]
    fn joined_rigid_pivot_needs_no_general_matrix() {
        use crate::builtin::{hash, msg_var};
        let var = |k| msg_var("x", k);
        let product = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
        let eq = Equal {
            lhs: product(var(0), hash(var(1))),
            rhs: product(var(2), hash(var(3))),
        };
        let used = FxHashSet::from_iter(0..4);
        let mut budget = Budget {
            nested_matrices: 0,
            ..Budget::new()
        };
        let rows = solve_join(vec![eq.clone()], &used, &mut budget)
            .unwrap()
            .unwrap();
        // Either the two hashes match, or the variables supply the opposite
        // hashes with an empty or nonempty common remaining product.
        assert_eq!(rows.len(), 3);
        for row in rows {
            assert_eq!(
                apply_vterm(&row, eq.lhs.clone()),
                apply_vterm(&row, eq.rhs.clone())
            );
        }
    }

    #[test]
    fn exhaustion_discards_finished_orientations_and_stalled_ac_is_retried() {
        let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
        let eq = |lhs, rhs| Equal { lhs, rhs };
        let split = eq(emap(v("a"), v("b")), emap(v("c"), v("d")));
        let second = eq(emap(v("e"), v("f")), emap(v("g"), v("h")));
        let query = vec![split, second];
        // The first two leaves finish before the second orientation needs
        // its own split. A truncated answer set would publish only those two.
        let mut budget = Budget {
            theory_steps: 2,
            ..Budget::new()
        };
        assert_eq!(
            solve(query.clone(), &FxHashSet::default(), &mut budget).unwrap(),
            None
        );
        assert_eq!(
            solve(query, &FxHashSet::default(), &mut Budget::new())
                .unwrap()
                .unwrap()
                .len(),
            4
        );

        let sum = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
        let ac = eq(sum(v("a"), v("b")), sum(v("c"), v("d")));
        let mut no_matrices = Budget {
            nested_matrices: 0,
            ..Budget::new()
        };
        assert_eq!(
            solve(vec![ac.clone()], &FxHashSet::default(), &mut no_matrices).unwrap(),
            None
        );
        let query = vec![ac, eq(v("c"), v("a")), eq(v("d"), v("b"))];
        assert_eq!(
            solve(query, &FxHashSet::default(), &mut no_matrices)
                .unwrap()
                .unwrap()
                .len(),
            1
        );
    }

    #[test]
    fn nested_ground_split_discards_every_branch_on_budget_exhaustion() {
        let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
        let atom = crate::lterm::pub_term;
        let sum = |a, b| f_app_ac(crate::function_symbols::AcSym::Union, vec![a, b]);
        let query = vec![
            Equal {
                lhs: sum(v("x"), v("y")),
                rhs: sum(atom("b"), atom("a")),
            },
            Equal {
                // A distinct AC head prevents the outer matrix from settling
                // both equations in one allocation.
                lhs: f_app_ac(AcSym::Mult, vec![v("x"), atom("a")]),
                rhs: f_app_ac(AcSym::Mult, vec![v("z"), atom("b")]),
            },
        ];
        // x=b finishes by cancellation. x=a still needs a matrix to establish
        // a clash. A budget that cannot settle both must defer the conjunction.
        let run = |limit| {
            solve(
                query.clone(),
                &[0].into_iter().collect(),
                &mut Budget {
                    nested_matrices: limit,
                    ..Budget::new()
                },
            )
            .unwrap()
        };
        assert_eq!(run(1), None);
        assert_eq!(run(2).unwrap().len(), 1);
    }

    #[test]
    fn nested_allocations_share_a_query_budget_across_heads() {
        use crate::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
        let other = AcSym::AcFct(AcFctSym::new(
            b"second",
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        ));
        let twice = |f, name| {
            let v = Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
            f_app_ac(f, vec![v.clone(), v])
        };
        let query = vec![
            Equal {
                lhs: twice(AcSym::Union, "a"),
                rhs: twice(AcSym::Union, "b"),
            },
            Equal {
                lhs: twice(other, "b"),
                rhs: twice(other, "c"),
            },
        ];
        let ids = [0].into_iter().collect();
        let run = |query: &[Equal<LNTerm>], limit| {
            let mut budget = Budget {
                nested_matrices: limit,
                ..Budget::new()
            };
            solve(query.to_vec(), &ids, &mut budget).unwrap()
        };
        // The operators differ, but the two numeric matrices are identical.
        assert_eq!(run(&query, 0), None);
        assert_eq!(run(&query, 1).unwrap().len(), 1);
        let mut different = query;
        let t = Term::Lit(Lit::Var(LVar::new("c", LSort::Msg, 0)));
        different[1].rhs = f_app_ac(other, vec![t.clone(), t.clone(), t]);
        assert_eq!(run(&different, 1), None);
        assert_eq!(run(&different, 2).unwrap().len(), 1);
    }

    #[test]
    fn inner_matrix_cannot_capture_a_witness_only_in_an_earlier_image() {
        use crate::builtin::hash;
        let input = |name| LVar::new(name, LSort::Msg, 0);
        let var = |v| Term::Lit(Lit::Var(v));
        let sum = |a, b| f_app_ac(AcSym::Union, vec![var(input(a)), var(input(b))]);
        // The first witness the allocator would otherwise choose is live in
        // an earlier image and absent from the deferred AC equation.
        let witness = LVar::new("x", LSort::Msg, 1);
        let image = hash(var(witness));
        let query = vec![
            Equal {
                lhs: var(input("outer")),
                rhs: image.clone(),
            },
            Equal {
                lhs: sum("a", "b"),
                rhs: sum("c", "d"),
            },
        ];
        let answers = solve(query, &[0].into_iter().collect(), &mut Budget::new())
            .unwrap()
            .unwrap();
        assert_eq!(answers.len(), 7);
        for arm in answers {
            assert_eq!(arm.image_of(&input("outer")), Some(&image));
            for name in ["a", "b", "c", "d"] {
                apply_vterm(&arm, var(input(name))).for_each_free(&mut |v| assert_ne!(*v, witness));
            }
        }
    }
}
