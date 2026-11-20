//! In-process interface to the experimental verified Lean backend.
//!
//! Native-only ordinary unification uses bounded kernels first and a total
//! mixed free/C/AC fallback over the original equations. Directional matching
//! has a total scoped fallback. Reduction and variants can certify answers
//! on the active rewrite table within explicit search budgets.
//! The Rust encoding and C/Lean runtime boundary remain trusted code.

mod common_children;
mod commutative;
mod components;
mod whole;
pub(crate) use commutative::solve as unify_structured;
pub use whole::variants_for_convergent_theory;
pub(crate) use whole::{total_match, total_unify};
mod constructor_variants;
pub(crate) use constructor_variants::RuleTable;
mod ac_bag_match;
mod component_match;
mod homogeneous;
mod match_size;
mod narrowing;
mod open_match;
mod operands;
mod residual;
mod shared_offset;
pub(crate) use shared_offset::solve as unify_with_witnesses;

use std::fmt;
use std::sync::OnceLock;

use rustc_hash::FxHashMap;

use crate::function_symbols::{nat_one_sym, AcSym, FunSym};
use crate::lterm::{sort_compare, LNTerm, LSort, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;

/// Ordinary substitutions, before the caller converts them to `SubstVFresh`.
pub type Substitutions = Vec<Vec<(LVar, LNTerm)>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Unsupported,
    Complete(Substitutions),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Cancelled,
    Initialization,
    InvalidStatus(u8),
    InvalidAtom(u64),
    InvalidVariable(u64),
    InvalidSubject(u64),
    FreshVariableOverflow,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => f.write_str("request cancelled"),
            Self::FreshVariableOverflow => f.write_str("Lean fresh variable index overflow"),
            Self::Initialization => f.write_str("Lean unification runtime initialization failed"),
            Self::InvalidStatus(status) => {
                write!(f, "Lean unification returned invalid status {status}")
            }
            Self::InvalidVariable(id) => {
                write!(f, "Lean returned an unknown variable ID {id}")
            }
            Self::InvalidSubject(id) => write!(f, "Lean returned an unknown subject ID {id}"),
            Self::InvalidAtom(atom) => write!(f, "Lean unification returned unknown atom {atom}"),
        }
    }
}

impl std::error::Error for Error {}

#[repr(C)]
#[derive(Clone, Copy)]
struct WordSlice {
    data: *const u64,
    size: usize,
}

impl WordSlice {
    fn new(words: &[u64]) -> Self {
        Self {
            data: words.as_ptr(),
            size: words.len(),
        }
    }
}

unsafe extern "C" {
    fn tamarin_lean_cancel_common(
        left: *const u64,
        left_size: usize,
        right: *const u64,
        right_size: usize,
        left_out: *mut u64,
        left_len: *mut usize,
        right_out: *mut u64,
        right_len: *mut usize,
    ) -> u8;
    fn tamarin_lean_sorted_ac_match(
        ac_sort: u64,
        variable_sorts: WordSlice,
        atom_sorts: WordSlice,
        occurrences: WordSlice,
        tail: WordSlice,
        rhs: WordSlice,
    ) -> *mut std::ffi::c_void;
    fn tamarin_lean_flat_ac_match(
        n: u64,
        occ: *const u64,
        occ_length: usize,
        tail: *const u64,
        tail_length: usize,
        rhs: *const u64,
        rhs_length: usize,
    ) -> *mut std::ffi::c_void;
    fn tamarin_lean_exclude_ac_factors(
        rows: *const WordSlice,
        count: usize,
        heads: WordSlice,
    ) -> u8;
    fn tamarin_lean_exclude_root(
        rows: *const u64,
        row_count: usize,
        args: *const u64,
        arity: usize,
    ) -> u8;
    fn tamarin_lean_constructor_variant(
        roots: *const u64,
        root_count: usize,
        used: *const u64,
        used_count: usize,
    ) -> u8;
    fn tamarin_lean_ground_variant(
        holes: *const u64,
        hole_count: usize,
        anchors: *const u64,
        anchor_count: usize,
        deps: *const u64,
        dep_count: usize,
        rigid: u8,
    ) -> u8;
    fn tamarin_lean_reduce_rule_slot(
        slot: u64,
        keys: *const u64,
        subjects: *const u64,
        length: usize,
        out: *mut u64,
    ) -> u8;
    fn tamarin_xor_branches(same: u8) -> u8;
    fn tamarin_comm_orientations(a: u64, b: u64, c: u64, d: u64, priority: u8) -> u8;
    fn tamarin_rigid_allocation(reversed: u8) -> *mut std::ffi::c_void;
    fn tamarin_shared_offset(a: u64, b: u64) -> *mut std::ffi::c_void;
    fn tamarin_lean_match_count(result: *const std::ffi::c_void) -> usize;
    fn tamarin_lean_match_rows(result: *const std::ffi::c_void, answer: usize) -> usize;
    fn tamarin_lean_match_row_size(
        result: *const std::ffi::c_void,
        arm: usize,
        index: usize,
    ) -> usize;
    fn tamarin_lean_match_row(
        result: *const std::ffi::c_void,
        answer: usize,
        variable: usize,
        out: *mut u64,
        capacity: usize,
        length: *mut usize,
    ) -> u8;
    fn tamarin_lean_match_release(result: *mut std::ffi::c_void);
    fn tamarin_reflexive_unify(recognized: u8) -> u8;
    fn tamarin_pairing_variants(has_projection: u8) -> u8;
    fn tamarin_pairing_project(first: u8) -> u8;
    fn tamarin_lean_initialize() -> u8;
    fn tamarin_lean_thread_initialize();
    fn tamarin_lean_thread_finalize();
    fn tamarin_lean_flat_ac_equal(
        lhs: *const u64,
        lhs_length: usize,
        rhs: *const u64,
        rhs_length: usize,
    ) -> u8;
    fn tamarin_lean_flat_ac_residual(
        tail: *const u64,
        tail_length: usize,
        rhs: *const u64,
        rhs_length: usize,
        residual: *mut u64,
        capacity: usize,
        residual_length: *mut usize,
    ) -> u8;
}

struct LeanThread;

impl LeanThread {
    fn initialize() -> Self {
        // SAFETY: runtime/module initialization completed under INIT first.
        // This TLS initializer runs once on each thread entering the backend.
        unsafe { tamarin_lean_thread_initialize() };
        Self
    }
}

impl Drop for LeanThread {
    fn drop(&mut self) {
        // SAFETY: all call-local Lean objects were consumed before returning;
        // this TLS destructor only releases resources belonging to its thread.
        unsafe { tamarin_lean_thread_finalize() };
    }
}

thread_local! {
    static LEAN_THREAD: LeanThread = LeanThread::initialize();
}

static INIT: OnceLock<Result<(), Error>> = OnceLock::new();

fn initialize() -> Result<(), Error> {
    *INIT.get_or_init(|| {
        // SAFETY: OnceLock serializes the module initializer. No Lean calls
        // occur on worker threads until initialization succeeds.
        match unsafe { tamarin_lean_initialize() } {
            0 => Ok(()),
            _ => Err(Error::Initialization),
        }
    })
}

fn flat_ac_equal(lhs: &[u64], rhs: &[u64]) -> Result<u8, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: both slices live for the call, the C wrapper only reads
        // them, and it transfers ownership of its temporary arrays to Lean.
        let status =
            unsafe { tamarin_lean_flat_ac_equal(lhs.as_ptr(), lhs.len(), rhs.as_ptr(), rhs.len()) };
        match status {
            0..=2 => Ok(status),
            other => Err(Error::InvalidStatus(other)),
        }
    })
}

fn flat_ac_residual(tail: &[u64], rhs: &[u64]) -> Result<(u8, Vec<u64>), Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        let mut residual = vec![0; rhs.len()];
        let mut length = 0;
        // SAFETY: buffers live through the call; C checks the result length
        // against capacity before copying and releases its Lean result.
        let status = unsafe {
            tamarin_lean_flat_ac_residual(
                tail.as_ptr(),
                tail.len(),
                rhs.as_ptr(),
                rhs.len(),
                residual.as_mut_ptr(),
                residual.len(),
                &mut length,
            )
        };
        if status > 2 || length > residual.len() {
            return Err(Error::InvalidStatus(status));
        }
        residual.truncate(length);
        Ok((status, residual))
    })
}

#[derive(Default)]
struct Atoms(crate::lean_identity::IdentityTable<Name>);

impl Atoms {
    fn encode(&mut self, name: Name) -> Option<u64> {
        self.0.intern(name)
    }

    fn decode(&self, id: u64) -> Result<LNTerm, Error> {
        self.0
            .get(id)
            .map(|name| Term::Lit(Lit::Con(name)))
            .ok_or(Error::InvalidAtom(id))
    }
}

fn sort_word(s: LSort) -> u64 {
    match s {
        LSort::Pub => 0,
        LSort::Fresh => 1,
        LSort::Msg => 2,
        LSort::Node => 3,
        LSort::Nat => 4,
    }
}

fn subsort(actual: LSort, expected: LSort) -> bool {
    matches!(
        sort_compare(actual, expected),
        Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
    )
}

fn encode_atom(term: &LNTerm, expected_sort: LSort, atoms: &mut Atoms) -> Option<u64> {
    let Term::Lit(Lit::Con(name)) = term else {
        return None;
    };
    if !subsort(sort_of_name(name), expected_sort) {
        return None;
    }
    atoms.encode(*name)
}

fn encode_side(
    terms: &[LNTerm],
    expected_sort: LSort,
    atoms: &mut Atoms,
) -> Option<(Option<LVar>, Vec<u64>)> {
    let mut variable = None;
    let mut tail = Vec::with_capacity(terms.len());
    for term in terms {
        if let Term::Lit(Lit::Var(v)) = term {
            if !subsort(v.sort, expected_sort) || variable.replace(*v).is_some() {
                return None;
            }
        } else {
            tail.push(encode_atom(term, expected_sort, atoms)?);
        }
    }
    Some((variable, tail))
}

enum EquationOutcome {
    Unsupported,
    Unsatisfiable,
    Solved(Option<(LVar, LNTerm)>),
}

fn ac_children(equation: &Equal<LNTerm>) -> Option<(AcSym, &[LNTerm], &[LNTerm])> {
    let (Term::App(FunSym::Ac(symbol), lhs), Term::App(FunSym::Ac(other), rhs)) =
        (&equation.lhs, &equation.rhs)
    else {
        return None;
    };
    (symbol == other && lhs.len() >= 2 && rhs.len() >= 2).then_some((*symbol, lhs, rhs))
}

fn ac_sort(symbol: AcSym) -> LSort {
    if symbol == AcSym::NatPlus {
        LSort::Nat
    } else {
        LSort::Msg
    }
}

fn declaration(f: FunSym, nat: bool) -> Option<(usize, LSort)> {
    match f {
        FunSym::NoEq(f) => Some((
            f.arity,
            if nat && f == nat_one_sym() {
                LSort::Nat
            } else {
                LSort::Msg
            },
        )),
        FunSym::Ac(f) => Some((2, ac_sort(f))),
        FunSym::C(_) => Some((2, LSort::Msg)),
        FunSym::List => None,
    }
}

/// The local factorer reads only root sorts. Use the typed solver if its
/// reading differs from the module declaration or a child has no required sort.
pub(crate) fn requires_typed_unification(t: &LNTerm, nat: bool) -> bool {
    fn compatible_sort(t: &LNTerm, nat: bool) -> Option<LSort> {
        let sort = match t {
            Term::Lit(Lit::Con(n)) => sort_of_name(n),
            Term::Lit(Lit::Var(v)) => v.sort,
            // The Rust factorer handles packed lists position by position.
            Term::App(FunSym::List, items) => {
                return items
                    .iter()
                    .all(|t| compatible_sort(t, nat).is_some())
                    .then_some(LSort::Msg);
            }
            Term::App(f, children) => {
                let (arity, s) = declaration(*f, nat)?;
                let valid = match f {
                    FunSym::Ac(_) => children.len() >= arity,
                    _ => children.len() == arity,
                };
                if !valid
                    || !children
                        .iter()
                        .all(|t| compatible_sort(t, nat).is_some_and(|actual| subsort(actual, s)))
                {
                    return None;
                }
                s
            }
        };
        let local = crate::lterm::sort_of_lterm(t, crate::lterm::sort_of_name);
        (sort == local && (nat || sort != LSort::Nat)).then_some(sort)
    }
    compatible_sort(t, nat).is_none()
}

fn unify_equation(equation: &Equal<LNTerm>, atoms: &mut Atoms) -> Result<EquationOutcome, Error> {
    let Some((symbol, lhs, rhs)) = ac_children(equation) else {
        return Ok(EquationOutcome::Unsupported);
    };
    unify_flat_sides(symbol, lhs, rhs, atoms)
}

// Both slices are nonempty. A singleton after cancellation denotes its child.
fn unify_flat_sides(
    symbol: AcSym,
    lhs: &[LNTerm],
    rhs: &[LNTerm],
    atoms: &mut Atoms,
) -> Result<EquationOutcome, Error> {
    let sort = ac_sort(symbol);
    let Some((lhs_variable, lhs_atoms)) = encode_side(lhs, sort, atoms) else {
        return Ok(EquationOutcome::Unsupported);
    };
    let Some((rhs_variable, rhs_atoms)) = encode_side(rhs, sort, atoms) else {
        return Ok(EquationOutcome::Unsupported);
    };
    let (variable, tail, ground) = match (lhs_variable, rhs_variable) {
        (None, None) => {
            return match flat_ac_equal(&lhs_atoms, &rhs_atoms)? {
                0 => Ok(EquationOutcome::Unsupported),
                1 => Ok(EquationOutcome::Unsatisfiable),
                2 => Ok(EquationOutcome::Solved(None)),
                status => Err(Error::InvalidStatus(status)),
            };
        }
        (Some(_), Some(_)) => return Ok(EquationOutcome::Unsupported),
        (Some(variable), None) => (variable, lhs_atoms, rhs_atoms),
        (None, Some(variable)) => (variable, rhs_atoms, lhs_atoms),
    };
    // A bare variable after cancellation is forced to the entire ground side.
    let (status, residual) = if tail.is_empty() {
        (2, ground)
    } else {
        flat_ac_residual(&tail, &ground)?
    };
    match status {
        0 => Ok(EquationOutcome::Unsupported),
        1 => Ok(EquationOutcome::Unsatisfiable),
        2 => {
            let terms = residual
                .into_iter()
                .map(|id| atoms.decode(id))
                .collect::<Result<Vec<_>, _>>()?;
            if terms.is_empty() {
                return Err(Error::InvalidStatus(status));
            }
            let image = f_app_ac(symbol, terms);
            // Matching.residual_wrong_sort excludes every sorted unifier for
            // this forced image. Singleton products have their atom's sort.
            if !subsort(
                crate::lterm::sort_of_lterm(&image, sort_of_name),
                variable.sort,
            ) {
                return Ok(EquationOutcome::Unsatisfiable);
            }
            Ok(EquationOutcome::Solved(Some((variable, image))))
        }
        other => Err(Error::InvalidStatus(other)),
    }
}

/// Attempt the supported fragment. `Complete([])` is proven unsatisfiable;
/// `Complete([[]])` is the identity solution. Unsupported queries must be
/// dispatched to a backend supporting their theory, rather than closed.
///
/// Conjunction assembly follows `GroundConjunction.complete`: each component
/// determines ground images for all its variables, and the merged answer
/// agrees with every component. Equal shared bindings are coalesced. Distinct
/// bindings defer to Maude rather than assuming syntactic inequality proves
/// inequivalence modulo B (especially across different AC symbols).
/// Reflexive conjunctions instead use `Reflexive.identity_complete`, which
/// covers all variables without assigning any of them. The Rust representation,
/// recognition, and agreement checks remain trusted.
pub fn unify(equations: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    if !equations.is_empty() && equations.iter().all(reflexive_rigid_sort_ac) {
        return reflexive_identity();
    }
    let mut atoms = Atoms::default();
    let mut bindings = Vec::new();
    let mut positions: FxHashMap<LVar, usize> = FxHashMap::default();
    let mut unsatisfiable = false;
    for equation in equations {
        match unify_equation(equation, &mut atoms)? {
            EquationOutcome::Unsupported => return Ok(Outcome::Unsupported),
            // Still inspect later equations: malformed/unsupported inputs
            // retain the fallback's behavior even after a local failure.
            EquationOutcome::Unsatisfiable => unsatisfiable = true,
            EquationOutcome::Solved(None) => {}
            EquationOutcome::Solved(Some((variable, term))) => {
                if equations.len() == 1 {
                    return Ok(Outcome::Complete(vec![vec![(variable, term)]]));
                }
                if let Some(&index) = positions.get(&variable) {
                    if bindings[index] != (variable, term) {
                        return Ok(Outcome::Unsupported);
                    }
                } else {
                    positions.insert(variable, bindings.len());
                    bindings.push((variable, term));
                }
            }
        }
    }
    if unsatisfiable {
        Ok(Outcome::Complete(vec![]))
    } else {
        Ok(Outcome::Complete(vec![bindings]))
    }
}

/// Directional matching: each equation is (pattern, subject). Ground
/// subjects are mandatory here; reversing a nonground equation would silently
/// bind subject variables. The accepted unifier answers have ground observed
/// images. The residual fast path uses Matching.of_ground_unification; general
/// flat rows use FlatMatching.complete and MatchingConjunction.join_complete.
pub fn match_ground(equations: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    if !equations
        .iter()
        .all(|eq| crate::vterm::is_ground_vterm(&eq.rhs))
    {
        return Ok(Outcome::Unsupported);
    }
    let quick = unify(equations)?;
    if quick != Outcome::Unsupported {
        return Ok(quick);
    }
    unify_by_cancellation(equations)
}

/// Match AC leaves over canonical ground free/C/AC factors and join their bindings.
/// Cancel closed factors first so they consume no constructor-selection budget.
pub(crate) fn match_compound_ground(equations: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    let mut remaining_work = 100_000;
    let mut components = Vec::with_capacity(equations.len());
    for eq in equations {
        let Some((symbol, pattern, subject)) = ac_children(eq) else {
            return Ok(Outcome::Unsupported);
        };
        let (Some(pattern), Some(subject)) = (
            open_match::prepare(symbol, pattern, false),
            open_match::prepare(symbol, subject, true),
        ) else {
            return Ok(Outcome::Unsupported);
        };
        let (pattern, subject) = (pattern.as_ref(), subject.as_ref());
        if pattern
            .iter()
            .chain(subject)
            .all(|t| matches!(t, Term::Lit(_)))
        {
            let Outcome::Complete(answers) = ground_component(symbol, pattern, subject)? else {
                return Ok(Outcome::Unsupported);
            };
            components.push(answers);
            continue;
        }
        let Outcome::Complete(answers) =
            open_match::component(symbol, pattern, subject, &mut remaining_work)?
        else {
            return Ok(Outcome::Unsupported);
        };
        components.push(answers);
    }
    join_components(components)
}

/// Solve ground-sided components in either direction after variable cancellation,
/// then test constraints grounded by the resulting shared bindings.
pub(crate) fn unify_by_cancellation(equations: &[Equal<LNTerm>]) -> Result<Outcome, Error> {
    let mut components = Vec::with_capacity(equations.len());
    let mut pending = Vec::new();
    for eq in equations {
        let Some((symbol, lhs, rhs)) = ac_children(eq) else {
            return Ok(Outcome::Unsupported);
        };
        let outcome = if crate::vterm::is_ground_vterm(&eq.rhs) {
            ground_component(symbol, lhs, rhs)?
        } else if crate::vterm::is_ground_vterm(&eq.lhs) {
            ground_component(symbol, rhs, lhs)?
        } else {
            match cancel_variables(symbol, lhs, rhs)? {
                Reduction::GroundSide { pattern, subject } => {
                    ground_component(symbol, &pattern, &subject)?
                }
                Reduction::Incomparable => {
                    pending.push(eq);
                    continue;
                }
                Reduction::Unsupported => return Ok(Outcome::Unsupported),
            }
        };
        let Outcome::Complete(answers) = outcome else {
            return Ok(Outcome::Unsupported);
        };
        components.push(answers);
    }
    let joined = join_components(components)?;
    if pending.is_empty() {
        return Ok(joined);
    }
    let Outcome::Complete(answers) = joined else {
        return Ok(Outcome::Unsupported);
    };
    filter_ground_constraints(answers, &pending)
}

enum Reduction {
    GroundSide {
        pattern: Vec<LNTerm>,
        subject: Vec<LNTerm>,
    },
    Incomparable,
    Unsupported,
}

fn cancel_variables(symbol: AcSym, lhs: &[LNTerm], rhs: &[LNTerm]) -> Result<Reduction, Error> {
    let sort = ac_sort(symbol);
    let mut variables = crate::lean_identity::IdentityTable::default();
    let mut split = |children: &[LNTerm]| {
        let mut ids = Vec::new();
        let mut literals = Vec::new();
        for t in children {
            match t {
                Term::Lit(Lit::Var(v)) if subsort(v.sort, sort) => ids.push(variables.intern(*v)?),
                Term::Lit(Lit::Con(a)) if subsort(sort_of_name(a), sort) => {
                    literals.push(t.clone())
                }
                _ => return None,
            }
        }
        Some((ids, literals))
    };
    let (Some((left, left_atoms)), Some((right, right_atoms))) = (split(lhs), split(rhs)) else {
        return Ok(Reduction::Unsupported);
    };
    // Both variable inventories are nonempty. Only the longer one can have
    // excess occurrences after complete removal of the shorter inventory.
    let (big, mut pattern, small, subject) = if left.len() >= right.len() {
        (left, left_atoms, right, right_atoms)
    } else {
        (right, right_atoms, left, left_atoms)
    };
    if big.len() == small.len() {
        if flat_ac_equal(&big, &small)? != 2 {
            return Ok(Reduction::Incomparable);
        }
    } else {
        let (status, excess) = flat_ac_residual(&small, &big)?;
        // Incomparable inventories may still unify through a shared witness.
        if status != 2 {
            return Ok(Reduction::Incomparable);
        }
        for id in excess {
            let v = variables.get(id).ok_or(Error::InvalidVariable(id))?;
            pattern.push(Term::Lit(Lit::Var(v)));
        }
    }
    Ok(Reduction::GroundSide { pattern, subject })
}

fn ground_component(
    symbol: AcSym,
    pattern: &[LNTerm],
    subject: &[LNTerm],
) -> Result<Outcome, Error> {
    // Empty inventories exist only after cancellation. There is no AC unit.
    if pattern.is_empty() || subject.is_empty() {
        return Ok(Outcome::Complete(
            if pattern.is_empty() && subject.is_empty() {
                vec![vec![]]
            } else {
                vec![]
            },
        ));
    }
    match unify_flat_sides(symbol, pattern, subject, &mut Atoms::default())? {
        EquationOutcome::Solved(binding) => {
            Ok(Outcome::Complete(vec![binding.into_iter().collect()]))
        }
        EquationOutcome::Unsatisfiable => Ok(Outcome::Complete(vec![])),
        EquationOutcome::Unsupported => match_flat(symbol, pattern, subject),
    }
}

/// Other equations may have fixed all variables of a deferred constraint.
/// FlatCancellation.filter_ground_constraints proves that testing each such
/// ground instance preserves completeness of the entire conjunction.
fn filter_ground_constraints(
    answers: Substitutions,
    constraints: &[&Equal<LNTerm>],
) -> Result<Outcome, Error> {
    use crate::subst::{apply_vterm, Subst};
    if answers
        .len()
        .checked_mul(constraints.len())
        .is_none_or(|n| n > 100_000)
    {
        return Ok(Outcome::Unsupported);
    }
    let mut retained = Vec::new();
    for arm in answers {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let substitution = Subst::from_list(arm.iter().cloned());
        let mut keep = true;
        for eq in constraints {
            let lhs = apply_vterm(&substitution, eq.lhs.clone());
            let rhs = apply_vterm(&substitution, eq.rhs.clone());
            if !crate::vterm::is_ground_vterm(&lhs) || !crate::vterm::is_ground_vterm(&rhs) {
                return Ok(Outcome::Unsupported);
            }
            let Some(equal) = equal_ground_images(&lhs, &rhs) else {
                return Ok(Outcome::Unsupported);
            };
            keep &= equal;
        }
        if keep {
            retained.push(arm);
        }
    }
    Ok(Outcome::Complete(retained))
}

fn join_components(components: Vec<Substitutions>) -> Result<Outcome, Error> {
    // MatchingConjunction.join_complete requires all compatible pairs, using
    // exact agreement on shared variables. All images here are ground.
    let mut joined: Substitutions = vec![vec![]];
    for component in components {
        if joined
            .len()
            .checked_mul(component.len())
            .is_none_or(|work| work > 100_000)
        {
            return Ok(Outcome::Unsupported);
        }
        let mut next = Vec::new();
        for left in &joined {
            'branch: for right in &component {
                tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
                let mut merged = left.clone();
                for (variable, value) in right {
                    if let Some((_, previous)) = merged.iter().find(|(v, _)| v == variable) {
                        match equal_ground_images(previous, value) {
                            Some(true) => {}
                            Some(false) => continue 'branch,
                            None => return Ok(Outcome::Unsupported),
                        }
                    } else {
                        merged.push((*variable, value.clone()));
                    }
                }
                merged.sort();
                next.push(merged);
            }
        }
        next.sort();
        next.dedup();
        joined = next;
    }
    Ok(Outcome::Complete(joined))
}

/// Canonical ground terms have a unique representative modulo the declared
/// C and AC axioms, including when a shared image is itself an AC product.
fn equal_ground_images(left: &LNTerm, right: &LNTerm) -> Option<bool> {
    if left == right {
        return Some(true);
    }
    open_match::ground_form(left)
        .zip(open_match::ground_form(right))
        .map(|(l, r)| l == r)
}

struct MatchRows(*mut std::ffi::c_void);
impl MatchRows {
    fn new(raw: *mut std::ffi::c_void) -> Result<Self, Error> {
        if raw.is_null() {
            Err(Error::InvalidStatus(255))
        } else {
            Ok(Self(raw))
        }
    }

    fn count(&self) -> usize {
        // SAFETY: the owned array stays live until Drop.
        unsafe { tamarin_lean_match_count(self.0) }
    }

    fn rows(&self, arm: usize) -> usize {
        // SAFETY: C checks the index before accessing the live array.
        unsafe { tamarin_lean_match_rows(self.0, arm) }
    }

    fn row_size(&self, arm: usize, index: usize) -> Result<usize, Error> {
        match self.raw_row_size(arm, index) {
            0 | usize::MAX => Err(Error::InvalidStatus(255)),
            len => Ok(len),
        }
    }

    fn raw_row_size(&self, arm: usize, index: usize) -> usize {
        // SAFETY: C checks both indices and this guard owns the packet.
        unsafe { tamarin_lean_match_row_size(self.0, arm, index) }
    }

    fn copy_row(&self, arm: usize, var: usize, buf: &mut [u64]) -> Result<usize, Error> {
        let mut len = 0;
        // SAFETY: C checks both indices and capacity before copying to buf.
        let code = unsafe {
            tamarin_lean_match_row(self.0, arm, var, buf.as_mut_ptr(), buf.len(), &mut len)
        };
        if code != 0 || len == 0 || len > buf.len() {
            return Err(Error::InvalidStatus(255));
        }
        Ok(len)
    }
}
impl Drop for MatchRows {
    fn drop(&mut self) {
        // SAFETY: this owns the one result reference returned by the C shim.
        unsafe { tamarin_lean_match_release(self.0) };
    }
}

/// A single variable occurrence uses the forced residual matcher, which already
/// supports subsorts. Several occurrences exercise the sort-indexed partition search.
pub(super) fn uses_sorted_partition(eq: &Equal<LNTerm>) -> bool {
    let Some((symbol, pattern, _)) = ac_children(eq) else {
        return false;
    };
    let sorts = || {
        pattern.iter().filter_map(|t| match t {
            Term::Lit(Lit::Var(v)) => Some(v.sort),
            _ => None,
        })
    };
    sorts().take(2).count() == 2 && sorts().any(|s| s != ac_sort(symbol))
}

const PARTITION_BUDGET: usize = 100_000;

fn partition_work(pattern: usize, variables: usize, rhs: &[u64], budget: usize) -> Option<usize> {
    let exponent = variables.try_into().unwrap_or(u32::MAX);
    let work = match pattern.cmp(&rhs.len()) {
        std::cmp::Ordering::Greater => 0,
        std::cmp::Ordering::Equal => {
            let distinct = rhs.iter().collect::<rustc_hash::FxHashSet<_>>().len();
            // The singleton shortcut also checks that each slot occurs.
            distinct
                .checked_pow(exponent)?
                .max(pattern.checked_mul(variables)?)
        }
        std::cmp::Ordering::Less => {
            // Lean builds the distinct ordered subsequences of each suffix.
            // Prepending an atom creates one new head choice for every old
            // row, replacing the rows that already started with this atom.
            let mut by_head = rustc_hash::FxHashMap::default();
            let mut rows = 1usize; // includes the empty row
            let mut visits = 0usize;
            for atom in rhs.iter().rev() {
                visits = visits.checked_add(rows)?;
                if visits > budget {
                    return None;
                }
                let old_heads = by_head.insert(atom, rows).unwrap_or(0);
                rows = rows.checked_add(rows - old_heads)?;
            }
            // One work allowance bounds each phase. For distinct factors the
            // assignment bound already covers all visited suffix rows.
            visits.max((rows - 1).checked_pow(exponent)?)
        }
    };
    (work <= budget).then_some(work)
}

/// Hybrid's ordered callers can observe Maude's first arm. Keep their former
/// dispatch boundary when the larger distinct-image search finds several arms.
pub(super) fn needs_wider_partition(eq: &Equal<LNTerm>) -> bool {
    let Some((_, pattern, subject)) = ac_children(eq) else {
        return false;
    };
    if pattern.len() >= subject.len() {
        return false;
    }
    let variables: rustc_hash::FxHashSet<_> = pattern
        .iter()
        .filter_map(|term| match term {
            Term::Lit(Lit::Var(v)) => Some(v),
            _ => None,
        })
        .collect();
    1usize
        .checked_shl(subject.len().try_into().unwrap_or(u32::MAX))
        .and_then(|n| (n - 1).checked_pow(variables.len().try_into().unwrap_or(u32::MAX)))
        .is_none_or(|n| n > PARTITION_BUDGET)
}

fn flat_rows(variables: usize, occ: &[u64], tail: &[u64], rhs: &[u64]) -> *mut std::ffi::c_void {
    // SAFETY: the caller initializes the runtime; all buffers live through the call.
    unsafe {
        tamarin_lean_flat_ac_match(
            variables as u64,
            occ.as_ptr(),
            occ.len(),
            tail.as_ptr(),
            tail.len(),
            rhs.as_ptr(),
            rhs.len(),
        )
    }
}

fn match_flat(symbol: AcSym, pattern: &[LNTerm], subject: &[LNTerm]) -> Result<Outcome, Error> {
    let sort = ac_sort(symbol);
    let mut atoms = Atoms::default();
    let mut variable_ids = crate::lean_identity::IdentityTable::default();
    let mut variables = Vec::new();
    let mut occurrences = Vec::new();
    let mut tail = Vec::new();
    for term in pattern.iter() {
        if let Term::Lit(Lit::Var(v)) = term {
            if !subsort(v.sort, sort) {
                return Ok(Outcome::Unsupported);
            }
            let Some(id) = variable_ids.intern(*v) else {
                return Ok(Outcome::Unsupported);
            };
            if id as usize == variables.len() {
                variables.push(*v);
            }
            occurrences.push(id);
        } else {
            let Some(id) = encode_atom(term, sort, &mut atoms) else {
                return Ok(Outcome::Unsupported);
            };
            tail.push(id);
        }
    }
    let Some(rhs) = subject
        .iter()
        .map(|t| encode_atom(t, sort, &mut atoms))
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Outcome::Unsupported);
    };
    // Each occurrence ID was interned from this pattern and every ID occurs.
    // The candidate can therefore reject a shorter subject immediately, and
    // needs only singleton rows on an exact fit. In all cases Lean decides
    // membership. This estimate controls admission to the in-process search.
    if partition_work(pattern.len(), variables.len(), &rhs, PARTITION_BUDGET).is_none() {
        return Ok(Outcome::Unsupported);
    }
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: all borrowed buffers live through the call. The result is a
        // typed nested Lean array, owned locally and released before TLS exit.
        let raw = if variables.iter().all(|v| v.sort == sort) {
            flat_rows(variables.len(), &occurrences, &tail, &rhs)
        } else {
            let variable_sorts: Vec<_> = variables.iter().map(|v| sort_word(v.sort)).collect();
            let atom_sorts: Vec<_> = atoms
                .0
                .values()
                .iter()
                .map(|a| sort_word(sort_of_name(a)))
                .collect();
            // SAFETY: all word slices remain live for the call. None signals a
            // malformed request, whereas an empty array is a complete clash.
            unsafe {
                tamarin_lean_sorted_ac_match(
                    sort_word(sort),
                    WordSlice::new(&variable_sorts),
                    WordSlice::new(&atom_sorts),
                    WordSlice::new(&occurrences),
                    WordSlice::new(&tail),
                    WordSlice::new(&rhs),
                )
            }
        };
        let result = MatchRows::new(raw)?;
        let count = result.count();
        let mut answers = Vec::with_capacity(count);
        for answer in 0..count {
            if result.rows(answer) != variables.len() {
                return Err(Error::InvalidStatus(255));
            }
            let mut bindings = Vec::with_capacity(variables.len());
            for (index, variable) in variables.iter().enumerate() {
                let mut row = vec![0; rhs.len()];
                let length = result.copy_row(answer, index, &mut row)?;
                row.truncate(length);
                let children = row
                    .into_iter()
                    .map(|id| atoms.decode(id))
                    .collect::<Result<Vec<_>, _>>()?;
                bindings.push((*variable, f_app_ac(symbol, children)));
            }
            answers.push(bindings);
        }
        answers.sort();
        answers.dedup();
        Ok(Outcome::Complete(answers))
    })
}

fn reflexive_identity() -> Result<Outcome, Error> {
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: initialized runtime, scalar Bool in the pinned ABI.
        match unsafe { tamarin_reflexive_unify(1) } {
            2 => Ok(Outcome::Complete(vec![vec![]])),
            code => Err(Error::InvalidStatus(code)),
        }
    })
}

/// A variable strictly below the AC result sort cannot split into a product.
/// Each operand is then a singleton even under further sorted specialization.
fn reflexive_rigid_sort_ac(equation: &Equal<LNTerm>) -> bool {
    if equation.lhs != equation.rhs {
        return false;
    }
    let Term::App(FunSym::Ac(symbol), children) = &equation.lhs else {
        return false;
    };
    let sort = ac_sort(*symbol);
    let mut variable = false;
    children.len() >= 2
        && children.iter().all(|t| match t {
            Term::Lit(Lit::Var(v)) => {
                variable = true;
                v.sort != sort && subsort(v.sort, sort)
            }
            Term::Lit(Lit::Con(c)) => subsort(crate::maude_types::sort_of_name(c), sort),
            _ => false,
        })
        && variable
}

/// Admit the two projection equations with arbitrary declared uninterpreted
/// constructors. The Lean proof is parametric in free and AC symbols; extra
/// rewrite equations still require separate correctness/completion proofs.
fn pairing_signature(sig: &crate::maude_sig::MaudeSig) -> bool {
    static PAIRING: OnceLock<crate::maude_sig::MaudeSig> = OnceLock::new();
    let pairing = PAIRING.get_or_init(crate::maude_sig::pair_maude_sig);
    !sig.enable_dh
        && !sig.enable_bp
        && !sig.enable_nat
        && !sig.enable_xor
        && !sig.enable_diff
        && sig.macro_names.is_empty()
        && sig.st_rules == pairing.st_rules
        && pairing.st_fun_syms.is_subset(&sig.st_fun_syms)
}

fn pairing_constructor(t: &LNTerm, sig: &crate::maude_sig::MaudeSig) -> bool {
    let declared = match t {
        Term::Lit(Lit::Var(v)) => return matches!(v.sort, LSort::Pub | LSort::Fresh | LSort::Msg),
        Term::Lit(Lit::Con(n)) => {
            return matches!(sort_of_name(n), LSort::Pub | LSort::Fresh | LSort::Msg);
        }
        Term::App(FunSym::NoEq(f), args) => {
            sig.st_fun_syms.contains(f)
                && *f != crate::function_symbols::fst_sym()
                && *f != crate::function_symbols::snd_sym()
                && args.len() == f.arity
        }
        Term::App(FunSym::Ac(AcSym::Union), args) => sig.enable_mset && args.len() >= 2,
        Term::App(FunSym::Ac(AcSym::AcFct(f)), args) => {
            sig.st_ac_fun_syms.contains(f) && args.len() >= 2
        }
        _ => false,
    };
    let Term::App(_, args) = t else {
        unreachable!()
    };
    declared && args.iter().all(|t| pairing_constructor(t, sig))
}

fn projection_variable(t: &LNTerm) -> Option<(bool, LVar)> {
    let Term::App(FunSym::NoEq(f), args) = t else {
        return None;
    };
    let [Term::Lit(Lit::Var(x))] = args.as_ref() else {
        return None;
    };
    if x.sort != LSort::Msg {
        return None;
    }
    if *f == crate::function_symbols::fst_sym() {
        Some((true, *x))
    } else if *f == crate::function_symbols::snd_sym() {
        Some((false, *x))
    } else {
        None
    }
}

/// Reify the verified variant recipes without text or IPC. A List application
/// is the caller's packed query, not an algebraic pairing symbol. All variable
/// comparisons use full name/sort/index identity. Witnesses are local to each
/// answer; downstream SubstVFresh freshens them against the caller's context.
pub fn pairing_variants(sig: &crate::maude_sig::MaudeSig, term: &LNTerm) -> Result<Outcome, Error> {
    if !pairing_signature(sig) {
        return Ok(Outcome::Unsupported);
    }
    let terms = match term {
        Term::App(FunSym::List, terms) => terms.as_ref(),
        _ => std::slice::from_ref(term),
    };
    let variable = if terms.iter().all(|t| pairing_constructor(t, sig)) {
        None
    } else {
        let Some((first, x)) = terms.iter().find_map(projection_variable) else {
            return Ok(Outcome::Unsupported);
        };
        if !terms
            .iter()
            .all(|t| *t == Term::Lit(Lit::Var(x)) || projection_variable(t) == Some((first, x)))
        {
            return Ok(Outcome::Unsupported);
        }
        Some(x)
    };
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: the runtime is initialized; Bool is 0/1 in the pinned ABI.
        // Only scalar recipe codes cross this boundary; no borrowed objects.
        let recipe = unsafe { tamarin_pairing_variants(u8::from(variable.is_some())) };
        match (recipe, variable) {
            (1, None) => Ok(Outcome::Complete(vec![vec![]])),
            (3, Some(x)) => {
                let a_idx = x.idx.checked_add(1).ok_or(Error::FreshVariableOverflow)?;
                let b_idx = a_idx.checked_add(1).ok_or(Error::FreshVariableOverflow)?;
                let a = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, a_idx)));
                let b = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, b_idx)));
                Ok(Outcome::Complete(vec![
                    vec![],
                    vec![(x, crate::builtin::pair(a, b))],
                ]))
            }
            _ => Err(Error::InvalidStatus(recipe)),
        }
    })
}

// Maude replies pass through the C/AC smart constructors. Public library
// inputs may be built with raw Term::App nodes, even deep inside a capture.
fn canonical_children(head: &FunSym, args: &[LNTerm]) -> bool {
    match head {
        FunSym::Ac(_) => {
            args.is_sorted()
                && !args
                    .iter()
                    .any(|t| matches!(t, Term::App(f, _) if f == head))
        }
        FunSym::C(_) => args.is_sorted(),
        _ => true,
    }
}

fn canonical_capture(term: &LNTerm) -> LNTerm {
    fn canonical(t: &LNTerm) -> bool {
        match t {
            Term::Lit(_) => true,
            Term::App(head, args) => canonical_children(head, args) && args.iter().all(canonical),
        }
    }
    if canonical(term) {
        term.clone()
    } else {
        crate::term::map_lits(term, &mut |lit| *lit)
    }
}

/// Root projection reduction with constructor children. The contract proves
/// the selected result is a normal form reachable by the pairing equations.
/// Nested projections remain explicitly unsupported by this first adapter.
pub fn pairing_reduce(
    sig: &crate::maude_sig::MaudeSig,
    term: &LNTerm,
) -> Result<Option<LNTerm>, Error> {
    if !pairing_signature(sig) {
        return Ok(None);
    }
    let Term::App(FunSym::NoEq(f), outer) = term else {
        return Ok(None);
    };
    let first = if *f == crate::function_symbols::fst_sym() {
        true
    } else if *f == crate::function_symbols::snd_sym() {
        false
    } else {
        return Ok(None);
    };
    let [Term::App(FunSym::NoEq(p), children)] = outer.as_ref() else {
        return Ok(None);
    };
    if *p != crate::function_symbols::pair_sym()
        || children.len() != 2
        || !children.iter().all(|t| pairing_constructor(t, sig))
    {
        return Ok(None);
    }
    initialize()?;
    LEAN_THREAD.with(|_| {
        // SAFETY: initialized runtime and a scalar Bool argument, as above.
        match unsafe { tamarin_pairing_project(u8::from(first)) } {
            1 => Ok(Some(canonical_capture(&children[0]))),
            2 => Ok(Some(canonical_capture(&children[1]))),
            code => Err(Error::InvalidStatus(code)),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{pub_term, NameTag};
    use crate::term::f_app_ac;

    fn equation(lhs: Vec<LNTerm>, rhs: Vec<LNTerm>) -> Equal<LNTerm> {
        Equal {
            lhs: f_app_ac(AcSym::Union, lhs),
            rhs: f_app_ac(AcSym::Union, rhs),
        }
    }

    #[test]
    fn partition_budget_counts_ordered_images_and_every_suffix() {
        use std::collections::BTreeSet;
        // Include interleaved equal atoms and compare with independent
        // positional subset enumeration. The empty choice costs one visit
        // during image construction and is removed before assignment.
        for word in 0..64 {
            let rhs: Vec<_> = (0..6).map(|i| (word >> i) & 1).collect();
            let images = |xs: &[u64]| -> usize {
                (0..1usize << xs.len())
                    .map(|mask| {
                        xs.iter()
                            .enumerate()
                            .filter_map(|(i, &a)| (mask & (1 << i) != 0).then_some(a))
                            .collect::<Vec<_>>()
                    })
                    .collect::<BTreeSet<_>>()
                    .len()
            };
            let work = (images(&rhs) - 1)
                .pow(2)
                .max((1..=rhs.len()).map(|i| images(&rhs[i..])).sum());
            assert_eq!(partition_work(2, 2, &rhs, work), Some(work));
            assert_eq!(partition_work(2, 2, &rhs, work - 1), None);
        }
        assert_eq!(partition_work(2, 1, &[0; 1024], PARTITION_BUDGET), None);
    }

    #[test]
    fn ffi_compares_multisets_and_preserves_multiplicity() {
        assert_eq!(flat_ac_equal(&[1, 2, 1], &[2, 1, 1]), Ok(2));
        assert_eq!(flat_ac_equal(&[1, 2, 1], &[2, 2, 1]), Ok(1));
        assert_eq!(flat_ac_equal(&[], &[]), Ok(0));
        assert_eq!(flat_ac_equal(&[u64::MAX, 0], &[0, u64::MAX]), Ok(2));
    }

    #[test]
    fn foreign_threads_can_enter_and_leave_runtime() {
        let threads: Vec<_> = (0..8)
            .map(|_| {
                std::thread::spawn(|| {
                    for _ in 0..100 {
                        assert_eq!(flat_ac_equal(&[7, 3, 7], &[7, 7, 3]), Ok(2));
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
    }

    #[test]
    fn rust_encoding_preserves_full_name_identity() {
        let public = pub_term("same-spelling");
        let fresh = Term::Lit(Lit::Con(Name::new(NameTag::Fresh, "same-spelling")));
        let anchor = pub_term("anchor");
        assert_eq!(
            unify(&[equation(vec![public, anchor.clone()], vec![fresh, anchor])]),
            Ok(Outcome::Complete(vec![]))
        );
    }

    #[test]
    fn unsupported_inputs_do_not_become_contradictions() {
        let a = pub_term("a");
        let variable = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        assert_eq!(
            unify(&[equation(
                vec![variable.clone(), variable],
                vec![a.clone(), a.clone()]
            )]),
            Ok(Outcome::Unsupported)
        );
        let node = Term::Lit(Lit::Con(Name::new(NameTag::Node, "n")));
        assert_eq!(
            unify(&[equation(vec![node, a.clone()], vec![a.clone(), a.clone()])]),
            Ok(Outcome::Unsupported)
        );
        let malformed = Term::App(FunSym::Ac(AcSym::Union), Vec::new().into());
        assert_eq!(
            unify(&[Equal {
                lhs: malformed.clone(),
                rhs: malformed
            }]),
            Ok(Outcome::Unsupported)
        );
    }

    #[test]
    fn variable_remainder_is_ground_and_unwraps_singletons() {
        let x = LVar::new("x", LSort::Msg, 19);
        let v = Term::Lit(Lit::Var(x));
        let a = pub_term("a");
        let b = pub_term("b");
        assert_eq!(
            unify(&[equation(
                vec![v.clone(), a.clone()],
                vec![b.clone(), a.clone()]
            )]),
            Ok(Outcome::Complete(vec![vec![(x, b.clone())]]))
        );
        let product = f_app_ac(AcSym::Union, vec![a.clone(), b.clone()]);
        // Opposite equation orientation, and a residual with multiplicity.
        assert_eq!(
            unify(&[equation(vec![a.clone(), a.clone(), b], vec![a, v],)]),
            Ok(Outcome::Complete(vec![vec![(x, product)]]))
        );
    }

    #[test]
    fn variable_remainder_cannot_be_empty_or_use_missing_atoms() {
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
        let a = pub_term("a");
        let b = pub_term("b");
        assert_eq!(
            unify(&[equation(
                vec![x.clone(), a.clone(), b.clone()],
                vec![a.clone(), b]
            )]),
            Ok(Outcome::Complete(vec![]))
        );
        assert_eq!(
            unify(&[equation(vec![x, pub_term("missing")], vec![a.clone(), a])]),
            Ok(Outcome::Complete(vec![]))
        );
    }

    #[test]
    fn conjunction_and_empty_problem_have_distinct_empty_conventions() {
        let a = pub_term("a");
        let b = pub_term("b");
        assert_eq!(unify(&[]), Ok(Outcome::Complete(vec![vec![]])));
        assert_eq!(
            unify(&[
                equation(vec![a.clone(), b.clone()], vec![b.clone(), a.clone()]),
                equation(vec![a.clone(), a.clone()], vec![a, b]),
            ]),
            Ok(Outcome::Complete(vec![]))
        );
    }

    #[test]
    fn conjunction_merges_ground_bindings_by_full_variable_identity() {
        let x = LVar::new("x", LSort::Msg, 7);
        let y = LVar::new("same-index", LSort::Msg, 7);
        let a = pub_term("a");
        let b = pub_term("b");
        let c = pub_term("c");
        let bind = |v, tail: LNTerm, values: Vec<LNTerm>| {
            equation(vec![Term::Lit(Lit::Var(v)), tail], values)
        };
        let equations = [
            bind(x, a.clone(), vec![a.clone(), b.clone(), c.clone()]),
            bind(y, c.clone(), vec![a.clone(), c.clone()]),
            // Same x, a different tail, and reversed equation orientation.
            Equal {
                lhs: f_app_ac(AcSym::Union, vec![c.clone(), b.clone(), b.clone()]),
                rhs: f_app_ac(AcSym::Union, vec![Term::Lit(Lit::Var(x)), b.clone()]),
            },
            equation(vec![a.clone(), b.clone()], vec![b.clone(), a.clone()]),
        ];
        assert_eq!(
            unify(&equations),
            Ok(Outcome::Complete(vec![vec![
                (x, f_app_ac(AcSym::Union, vec![b, c])),
                (y, a),
            ]]))
        );
    }

    #[test]
    fn conjunction_defers_conflicting_bindings_and_preserves_unsupported_inputs() {
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 7)));
        let a = pub_term("a");
        let b = pub_term("b");
        let first = equation(vec![x.clone(), a.clone()], vec![a.clone(), b.clone()]);
        let conflict = equation(vec![x.clone(), a.clone()], vec![a.clone(), a.clone()]);
        assert_eq!(unify(&[first.clone(), conflict]), Ok(Outcome::Unsupported));
        let impossible = equation(vec![a.clone(), a.clone()], vec![a.clone(), b]);
        assert_eq!(
            unify(&[first, impossible.clone()]),
            Ok(Outcome::Complete(vec![]))
        );
        let unsupported = equation(vec![x.clone(), x], vec![a.clone(), a]);
        for equations in [
            [impossible.clone(), unsupported.clone()],
            [unsupported, impossible],
        ] {
            assert_eq!(unify(&equations), Ok(Outcome::Unsupported));
        }
    }

    #[test]
    fn shared_bindings_across_symbols_compare_decoded_terms() {
        let x = LVar::new("x", LSort::Msg, 7);
        let query = |symbol, rest: Vec<LNTerm>| {
            let mut ground = vec![pub_term("tail")];
            ground.extend(rest);
            Equal {
                lhs: f_app_ac(symbol, vec![Term::Lit(Lit::Var(x)), pub_term("tail")]),
                rhs: f_app_ac(symbol, ground),
            }
        };
        assert_eq!(
            unify(&[
                query(AcSym::Union, vec![pub_term("a")]),
                query(AcSym::Xor, vec![pub_term("a")]),
            ]),
            Ok(Outcome::Complete(vec![vec![(x, pub_term("a"))]]))
        );
        // Equal atom-ID arrays do not mean equal products across symbols.
        assert_eq!(
            unify(&[
                query(AcSym::Union, vec![pub_term("a"), pub_term("b")]),
                query(AcSym::Xor, vec![pub_term("a"), pub_term("b")]),
            ]),
            Ok(Outcome::Unsupported)
        );
    }
}
