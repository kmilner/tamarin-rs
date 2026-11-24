//! In-process interface to the verified Lean algebra library.
//!
//! Native-only unifies, matches and normalizes through whole-command exports
//! alone: one total unifier for mixed free/C/AC conjunctions, one total scoped
//! matcher with its existence decision, and the checked reducers. The Rust
//! solvers that remain here only propose families of variants, which
//! native-only uses after the Lean certificate checker accepted them. Protocol
//! sessions fall back to the full table under Tamarin's canonical,
//! finite-variant presentation assumptions for reduction and variants.
//! The Rust encoding and C/Lean runtime boundary remain trusted code.

mod common_children;
mod commutative;
mod components;
mod theory;
pub(crate) use theory::Theory;
mod whole;
pub(crate) use whole::{
    kind_level, total_unify, total_unify_exists, unpack_conjunction, Conjunction, FamilyCheck,
    Reduced, ReductionTable, Unifiers, UnifyReplies,
};
pub use whole::{reduction_for_convergent_theory, variants_for_convergent_theory};
mod constructor_variants;
pub(crate) use constructor_variants::RuleTable;
mod ac_bag_match;
mod homogeneous;
mod match_size;
mod narrowing;
mod open_match;
mod operands;
mod residual;

use std::fmt;
use std::sync::{Arc, OnceLock};
use tamarin_algebra_sys::{
    tamarin_lean_flat_ac_equal, tamarin_lean_initialize, tamarin_lean_thread_finalize,
    tamarin_lean_thread_initialize, InterruptWatch,
};
use tamarin_utils::cancellation::{self, CancellationToken};

use crate::function_symbols::{nat_one_sym, AcSym, FunSym};
use crate::lterm::{sort_compare, LNTerm, LSort, LVar, Name};
use crate::maude_types::sort_of_name;
use crate::rewriting::Equal;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;

/// Run ordinary order-sorted unification modulo declared commutative and AC
/// attributes on the original conjunction. Rewrite equations are ignored.
/// All returned bindings in one arm share its fresh-variable scope.
pub fn unify_modulo_attributes(
    sig: &crate::maude_sig::MaudeSig,
    equations: &[Equal<LNTerm>],
) -> Result<Outcome, Error> {
    let Some(theory) = Theory::new(sig) else {
        return Ok(Outcome::Unsupported);
    };
    let theory = Arc::new(theory);
    unpack_conjunction(&theory, equations)?.solve(|rows| {
        match whole::total_unify(&theory, rows, None, 0)?.0 {
            Some(family) => family.named(None, None).map(Outcome::Complete),
            None => Ok(Outcome::Unsupported),
        }
    })
}

/// Match all patterns modulo the signature's declared commutative and AC attributes.
/// Each row has its pattern on the left and its subject on the right. Only pattern
/// variables selected by `bindable` may be assigned. Subject variables keep their
/// original identities, including when they also occur in the pattern.
///
/// An answer contains a binding for every selected pattern variable, including
/// identity bindings. The family can contain duplicates and its order is unspecified.
pub fn match_modulo_attributes(
    sig: &crate::maude_sig::MaudeSig,
    patterns_and_subjects: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Outcome, Error> {
    match Theory::new(sig) {
        Some(theory) => match_in(&Arc::new(theory), patterns_and_subjects, bindable),
        None => Ok(Outcome::Unsupported),
    }
}

/// [`match_modulo_attributes`] over the description of the signature.
pub(crate) fn match_in(
    theory: &Arc<Theory>,
    patterns_and_subjects: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Outcome, Error> {
    unpack_conjunction(theory, patterns_and_subjects)?
        .solve(|rows| whole::total_match(theory, rows, bindable))
}

/// Decide whether [`match_modulo_attributes`] would return an answer, without
/// listing the answers. `None` when the request is outside the module.
pub fn has_match_modulo_attributes(
    sig: &crate::maude_sig::MaudeSig,
    patterns_and_subjects: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Option<bool>, Error> {
    match Theory::new(sig) {
        Some(theory) => has_match_in(&Arc::new(theory), patterns_and_subjects, bindable),
        None => Ok(None),
    }
}

/// [`has_match_modulo_attributes`] over the description of the signature.
pub(crate) fn has_match_in(
    theory: &Arc<Theory>,
    patterns_and_subjects: &[Equal<LNTerm>],
    bindable: impl Fn(&LVar) -> bool,
) -> Result<Option<bool>, Error> {
    match unpack_conjunction(theory, patterns_and_subjects)? {
        Conjunction::Rows(rows) => whole::total_has_match(theory, &rows, bindable),
        Conjunction::Clash => Ok(Some(false)),
        Conjunction::Unsupported => Ok(None),
    }
}

/// A request without tuple wrappers reaches its whole-command export directly.
/// Otherwise Rust first unpacks the tuples through a separate checked kernel.
pub(crate) fn is_single_export(equations: &[Equal<LNTerm>]) -> bool {
    !equations.iter().any(|e| {
        [&e.lhs, &e.rhs]
            .into_iter()
            .any(|t| matches!(t, Term::App(crate::function_symbols::FunSym::List, _)))
    })
}

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
    /// The certificate checker refused a proposed family of variants:
    /// `reason` is 1 when member `member` is not normal, 2 when no member
    /// subsumes the query, and 3 when a narrowing successor of member
    /// `member` is not covered.
    RejectedVariants {
        reason: u8,
        member: u64,
    },
    /// The certificate checker could not decode a proposed family of
    /// variants, for instance because an image lacks the sort of its variable.
    MalformedVariants,
    /// The certificate checker did not decide a proposed family of variants:
    /// the request is outside its domain.
    UncertifiedVariants,
    /// The certificate checker ran out of budget on a proposed family of
    /// variants: a rewrite path longer than `depth`, or more positions to
    /// narrow than `work` (zero for no bound).
    VariantCheckBudget {
        depth: u64,
        work: u64,
    },
    /// One call of an interruptible export asked more questions than its
    /// work bound allows and was stopped. Nothing was decided.
    SearchBudget {
        operation: &'static str,
        work: u64,
    },
    /// No specialised solver covers the query and folding variant narrowing
    /// did not list a family within `work` narrowing sites.
    VariantSearchBudget {
        work: u64,
    },
}

/// One interruptible call of a Lean export.
///
/// The unifier, its existence decision, the single-path reducers and the
/// variant certificate checker ask
/// their caller before every step of a search whether to go on (Lean's
/// `Tamarin.Interrupt`). The bridge answers from this record: stop once the
/// current request is cancelled, or once the call has asked more than `work`
/// questions (zero for no bound). A stopped call returns no reply at all, so
/// [`Self::finish`] is the only way to learn its outcome, and a reply that is
/// read was computed without interruption. The number of questions a call
/// asks is a function of its request, so the bound is deterministic.
pub(crate) struct Watch {
    raw: InterruptWatch,
    operation: &'static str,
    /// Keeps the flag behind `raw.cancel` alive.
    _token: Option<CancellationToken>,
}

/// `TAM_RS_ALGEBRA_SEARCH_REPORT=<n>` prints to stderr every interruptible
/// call that asked at least `n` questions, to choose a work bound.
fn report_threshold() -> u64 {
    static THRESHOLD: OnceLock<u64> = OnceLock::new();
    *THRESHOLD.get_or_init(|| {
        std::env::var("TAM_RS_ALGEBRA_SEARCH_REPORT")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(u64::MAX)
    })
}

impl Watch {
    pub(crate) fn new(operation: &'static str, work: u64) -> Self {
        let token = cancellation::current();
        let cancel = token
            .as_ref()
            .map_or(std::ptr::null(), CancellationToken::flag_ptr);
        Self {
            raw: InterruptWatch {
                cancel,
                budget: work,
                asked: 0,
                stopped: 0,
            },
            operation,
            _token: token,
        }
    }

    /// The record the bridge reads and writes during the call.
    pub(crate) fn raw(&mut self) -> *mut InterruptWatch {
        &mut self.raw
    }

    /// The outcome of the call that just returned. On an error the call
    /// produced no reply.
    pub(crate) fn finish(&self) -> Result<(), Error> {
        if self.raw.asked >= report_threshold() {
            eprintln!(
                "algebra search: {} asked {} questions (stopped: {})",
                self.operation, self.raw.asked, self.raw.stopped
            );
        }
        match self.raw.stopped {
            0 => Ok(()),
            1 => Err(Error::Cancelled),
            _ => Err(Error::SearchBudget {
                operation: self.operation,
                work: self.raw.budget,
            }),
        }
    }
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
            Self::RejectedVariants { reason, member } => {
                f.write_str("the Lean variant checker rejected the proposed family of variants: ")?;
                match reason {
                    1 => write!(f, "member {member} is not normal (reason 1)"),
                    2 => write!(f, "no member subsumes the query (reason 2, index {member})"),
                    3 => write!(
                        f,
                        "a narrowing successor of member {member} is not covered (reason 3)"
                    ),
                    _ => write!(f, "reason {reason}, index {member}"),
                }
            }
            Self::MalformedVariants => f.write_str(
                "the Lean variant checker could not decode the proposed family of variants",
            ),
            Self::UncertifiedVariants => f.write_str(
                "variants not certified: the Lean variant checker did not decide the proposed \
                 family (outside its domain)",
            ),
            Self::VariantCheckBudget { depth, work } => {
                write!(
                    f,
                    "variants not certified: out of budget, the Lean variant checker did not \
                     decide the proposed family within rewrite depth {depth} and "
                )?;
                match work {
                    0 => f.write_str("without a work bound"),
                    _ => write!(
                        f,
                        "work bound {work} (TAM_RS_VARIANT_CHECK_WORK sets the bound, 0 removes it)"
                    ),
                }
            }
            Self::SearchBudget { operation, work } => {
                let variable = if matches!(*operation, "variant check" | "variant search") {
                    "TAM_RS_VARIANT_CHECK_SEARCH"
                } else {
                    "TAM_RS_ALGEBRA_SEARCH_WORK"
                };
                write!(
                    f,
                    "out of budget: one Lean {operation} was stopped after {work} search steps \
                     and decided nothing ({variable} sets the bound, 0 removes it)"
                )
            }
            Self::VariantSearchBudget { work } => write!(
                f,
                "variants not found: out of budget, folding variant narrowing did not finish \
                 within {work} narrowing sites"
            ),
        }
    }
}

impl std::error::Error for Error {}

// Every declaration of the C bridge is generated from its definition by the
// build of `tamarin-algebra-sys`. None is written by hand in this crate (the
// test `bridge_declarations_are_generated` checks that), so a call that
// disagrees with the bridge does not compile.
use tamarin_algebra_sys::WholeWordSlice as WordSlice;

use tamarin_algebra_sys::{
    tamarin_comm_orientations, tamarin_lean_cancel_common, tamarin_lean_constructor_variant,
    tamarin_lean_exclude_ac_factors, tamarin_lean_exclude_root, tamarin_lean_flat_ac_match,
    tamarin_lean_flat_ac_residual, tamarin_lean_ground_variant, tamarin_lean_match_count,
    tamarin_lean_match_release, tamarin_lean_match_row, tamarin_lean_match_row_size,
    tamarin_lean_match_rows, tamarin_lean_reduce_rule_slot, tamarin_lean_sorted_ac_match,
    tamarin_pairing_variants, tamarin_xor_branches,
};

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

#[cfg(test)]
mod tests {
    use super::*;

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

    /// The declarations of the C bridge come from `tamarin-algebra-sys`,
    /// whose build generates them from the C definitions. One written in
    /// this crate would be compared with nothing.
    #[test]
    fn bridge_declarations_are_generated() {
        fn scan(dir: &std::path::Path, found: &mut Vec<String>) {
            // A block of declarations, not the type of a function pointer.
            let marker = concat!("extern ", "\"C\" {");
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    scan(&path, found);
                } else if path.extension().is_some_and(|e| e == "rs") {
                    let text = std::fs::read_to_string(&path).unwrap();
                    for (number, line) in text.lines().enumerate() {
                        if line.contains(marker) {
                            found.push(format!("{}:{}", path.display(), number + 1));
                        }
                    }
                }
            }
        }
        let mut found = Vec::new();
        scan(
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
            &mut found,
        );
        assert!(
            found.is_empty(),
            "foreign declarations written by hand, import them from tamarin_algebra_sys: {found:?}"
        );
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
}
