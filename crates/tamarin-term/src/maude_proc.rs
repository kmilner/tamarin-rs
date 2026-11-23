// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Maude.Process` — an algebra session with optional Maude transport.
//!
//! Spawns `maude -interactive -no-tecla -no-banner -no-wrap -batch`,
//! feeds it a `fmod MSG ... endfm` module describing the term algebra,
//! and exposes `unify`, `match`, `variants`, and `reduce` operations.
//! Native-only sessions create no process: they answer through the Lean
//! library and fail explicitly when a request is outside what it supports.
//!
//! The protocol is line-oriented: every command ends with `.\n` and
//! Maude's response ends with the prompt `Maude> `.

use std::io::{Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use crate::algebra_backend::AlgebraBackend;
#[cfg(feature = "lean-unification")]
use crate::algebra_provenance::VariantRoute;
use crate::algebra_provenance::{Command as Asked, Origin, Provenance};
use crate::lterm::LNTerm;
use crate::maude_parse;
use crate::maude_print::{pp_mterm_into, pp_mterm_list_into, pp_theory};
use crate::maude_sig::MaudeSig;
use crate::maude_types::{lterm_to_mterm_global, mterm_to_lnterm, ConvCtx, MSubst, MTerm};
use crate::rewriting::Equal;
use tamarin_utils::cancellation;
use tamarin_utils::fresh::MonadFresh;

const PROMPT: &[u8] = b"Maude> ";

/// A single open application result and the argument bindings used to obtain
/// it. Range variables are shared between the bindings and the result. A
/// branch is scoped to the query. Rename both together in any larger scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApplicationVariant {
    pub bindings: Vec<(crate::lterm::LVar, LNTerm)>,
    pub value: LNTerm,
}

/// Errors that can arise from the Maude bridge.
#[derive(Debug)]
pub enum MaudeError {
    Cancelled,
    /// Experimental native-only mode cannot complete this operation.
    UnsupportedOperation(&'static str),
    /// A native runtime/packet error invalidated this session.
    NativeFailure(String),
    /// stdin/stdout I/O failure talking to the Maude subprocess.
    Io(std::io::Error),
    /// The `maude` binary could not be launched (e.g. not found on PATH).
    Spawn(String),
    /// Maude's reply could not be parsed.
    Parse(maude_parse::ParseError),
    /// Protocol or term back-conversion error not covered by the above.
    Other(String),
}

impl std::fmt::Display for MaudeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaudeError::UnsupportedOperation(op) => {
                write!(f, "native-only backend does not support {op}")
            }
            MaudeError::NativeFailure(reason) => {
                write!(f, "native algebra backend failed: {reason}")
            }
            MaudeError::Cancelled => f.write_str("request cancelled"),
            MaudeError::Io(e) => write!(f, "io error: {}", e),
            MaudeError::Spawn(s) => write!(f, "spawn error: {}", s),
            MaudeError::Parse(e) => write!(f, "parse error: {}", e),
            MaudeError::Other(s) => write!(f, "{}", s),
        }
    }
}
impl std::error::Error for MaudeError {}
impl From<cancellation::Cancelled> for MaudeError {
    fn from(_: cancellation::Cancelled) -> Self {
        Self::Cancelled
    }
}
impl From<std::io::Error> for MaudeError {
    fn from(e: std::io::Error) -> Self {
        MaudeError::Io(e)
    }
}
impl From<maude_parse::ParseError> for MaudeError {
    fn from(e: maude_parse::ParseError) -> Self {
        MaudeError::Parse(e)
    }
}

// An open natural sum can belong to Maude's kind without having a declared
// sort. The free factorer only looks at an application's result sort.
fn contains_kind_sum(t: &LNTerm) -> bool {
    use crate::function_symbols::{nat_one_sym, AcSym, FunSym};
    use crate::lterm::LSort;
    use crate::maude_types::sort_of_name;
    use crate::term::Term;
    use crate::vterm::Lit;
    let Term::App(f, args) = t else { return false };
    (*f == FunSym::Ac(AcSym::NatPlus)
        && (args.len() < 2
            || args.iter().any(|a| match a {
                Term::Lit(Lit::Var(v)) => v.sort != LSort::Nat,
                Term::Lit(Lit::Con(c)) => sort_of_name(c) != LSort::Nat,
                Term::App(FunSym::NoEq(g), xs) => *g != nat_one_sym() || !xs.is_empty(),
                Term::App(h, _) => *h != FunSym::Ac(AcSym::NatPlus),
            })))
        || args.iter().any(contains_kind_sum)
}

/// The Maude backend's split of a unification request: the unifier of its
/// free part, and the AC/C equations left for the engine with that unifier
/// applied. `None` when the free part alone has no unifier.
fn factor_unification(
    sig: &MaudeSig,
    eqs: &[Equal<LNTerm>],
) -> Option<(
    crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
    Vec<Equal<LNTerm>>,
)> {
    // The free factorer cannot sort an open natural sum: the engine gets the
    // whole request.
    if sig.enable_nat
        && eqs
            .iter()
            .any(|e| contains_kind_sum(&e.lhs) || contains_kind_sum(&e.rhs))
    {
        return Some((crate::subst::Subst::empty(), eqs.to_vec()));
    }
    // HS unifyLTermFactored retains the local bindings and delays AC/C
    // equations in a single traversal. Skolem constants use their wire sort.
    crate::unification::unify_lterm_factored(&crate::maude_types::sort_of_name, eqs.to_vec())
}

/// True if `t` contains any function symbol whose head matches one in
/// `reducible`.  Used as a fast-path predicate for `reduce`: if the
/// term contains no reducible symbols at all, `reduce` is the
/// identity, and we can skip the Maude IPC round-trip.
fn term_has_reducible_sym(t: &LNTerm, reducible: &crate::function_symbols::FunSig) -> bool {
    t.any_fun_sym(|f| reducible.contains(f))
}

/// Both structural reduction shortcuts read derived symbol sets. A caller can
/// edit the source theory after its last refresh. Validate the live rule heads
/// once when the immutable session is opened.
fn reduction_heads_indexed(sig: &MaudeSig) -> bool {
    use crate::function_symbols::{AcSym, FunSym};
    use crate::term::Term;
    sig.rrules().iter().all(|rule| {
        let Term::App(head, _) = &rule.lhs else {
            return false;
        };
        sig.reducible_fun_syms.contains(head)
            && !(matches!(head, FunSym::NoEq(_) | FunSym::Ac(AcSym::AcFct(_)))
                && sig.irreducible_fun_syms.contains(head))
    })
}

/// True if `t` contains NO Ac- or C-headed application anywhere.  Backs
/// the per-rule LHS flags `maude_sig::StRules` carries — behind
/// `MaudeProcessInner::reduce_by_structure` and `norm::go_nf`'s per-rule
/// dispatch: `nf_via_haskell`'s pure st-rule arm matches with the no-AC
/// matcher (`solve_match_lterm_no_ac`), whose `match_raw` raises
/// `NeedsAC` only at Ac-vs-Ac / C-vs-C positions — so the matcher is
/// complete (never misses a match Maude would find) exactly when the
/// PATTERN (the rule LHS) is Ac/C-free.  Rules failing this predicate
/// need the Maude-backed path (`norm::rule_applies_ac`).
pub(crate) fn term_ac_c_free(t: &LNTerm) -> bool {
    use crate::function_symbols::FunSym;
    t.all_fun_syms(|f| !matches!(f, FunSym::Ac(_) | FunSym::C(_)))
}

/// Statistics on Maude operations performed via this handle.
#[derive(Debug, Default, Clone, Copy)]
pub struct MaudeStats {
    pub unify_count: u64,
    /// Unification requests the proved Lean export answered afresh. Always
    /// zero on the Maude backend.
    pub lean_unify_count: u64,
    /// Those among them whose witnesses kept the export's names, because the
    /// family was not the composition the Maude backend builds.
    pub lean_unify_unspelled: u64,
    /// Existence questions for unification the proved Lean existence export
    /// decided afresh, without listing a family. Always zero on the Maude
    /// backend.
    pub lean_unify_exists_count: u64,
    pub match_count: u64,
    pub norm_count: u64,
    pub var_count: u64,
}

/// Hit/miss tallies, per Maude subprocess, against the session's shared
/// memo caches (`SharedMaudeCaches`: `reduce`, `unifiable`, `reply`).  A
/// hit is counted when the cache `get` succeeds; a miss when this process
/// computed the value and inserted it.  The `u64` bumps are always
/// maintained (negligible cost); only the one-line-per-process summary is
/// gated, printed to STDERR (never stdout) from `MaudeProcessInner`'s
/// `Drop` when `TAM_MAUDE_CACHE_STATS` is set.  Diagnostic only — reaches
/// no `--prove` output path.
#[derive(Default)]
struct MaudeCacheStats {
    reduce_hits: u64,
    reduce_misses: u64,
    unifiable_hits: u64,
    unifiable_misses: u64,
    reply_hits: u64,
    reply_misses: u64,
}

/// The memo caches for one theory session, shared (`Arc`) by the
/// session's sequential `file_maude` handle AND every `MaudePool` member
/// (run.rs wires one instance into both).  Under `--processors=N`,
/// parallel tasks draw different pool members; sharing lets a value
/// computed by ANY subprocess satisfy the identical query from every
/// other member of the session.
///
/// BYTE-PARITY: each cache relies on the memo invariant "identical
/// term/command bytes ⇒ identical result", which a single process already
/// depends on across an entire session.  Every sharing subprocess is
/// initialised with the IDENTICAL signature module (`MaudePool` clones
/// one `MaudeSig` per spawn; run.rs passes the same value to
/// `file_maude`), the module is immutable after `start_with_caches()`
/// (every post-load command is a pure `reduce` / `unify` / `match` /
/// `get variants` query — nothing mutates Maude state that later replies
/// depend on), and Maude's reply is a deterministic, command-local
/// function of that module.  So the value any member computes is
/// byte-identical to what the querying member would have computed itself
/// — sharing changes only which process performed the first computation,
/// exactly the member-interchangeability the pool already guarantees.
///
/// LOCK ORDER: a subprocess's inner IPC mutex is always acquired FIRST;
/// each cache mutex here is acquired strictly INSIDE it, held only for
/// the `get` or the `insert` (released before any Maude IPC wait), and
/// acquires nothing itself.  No cycle is possible.
///
/// CONCURRENT MISSES: two members that miss the same key simultaneously
/// both perform the IPC and both insert — last write wins with an
/// identical value (see BYTE-PARITY).  That bounded first-wave
/// duplication is harmless, so there is no single-flight machinery.
#[derive(Default)]
pub struct SharedMaudeCaches {
    /// Latch failures across workers: legacy callers sometimes recover from errors.
    /// Every consumer must check this before publishing any result. It holds the
    /// first native-only runtime failure and the first backend error that a
    /// caller without an error channel had to absorb.
    native_failure: std::sync::OnceLock<NativeFailure>,
    /// Memo for the complete answers of the proved unifier, keyed by the
    /// equations as the caller sent them, with the origin each answer counts
    /// under. The export names its witnesses from the query alone and the
    /// spelling of an answer is a function of the query alone, so the stored
    /// family is the one a repeat of the call would compute. It is emptied
    /// when it outgrows [`UNIFY_MEMO_NODES`]; `unify_replies` then answers.
    #[cfg(feature = "lean-unification")]
    proved_unify: Mutex<UnifyMemo>,
    /// The replies of the total unification export by the words of the
    /// request, which do not depend on how the request names its variables.
    #[cfg(feature = "lean-unification")]
    unify_replies: crate::lean_unification::UnifyReplies,
    /// Memo for completed total-match answers, keyed by the oriented
    /// equations and the bindable variables among them. A match binds
    /// pattern variables to subterms of the subject and introduces no
    /// witness, so the answer is a pure function of this key.
    #[cfg(feature = "lean-unification")]
    total_match: Mutex<
        tamarin_utils::FastMap<
            (Vec<(LNTerm, LNTerm)>, Vec<crate::lterm::LVar>),
            Vec<Vec<(crate::lterm::LVar, LNTerm)>>,
        >,
    >,
    /// Memo for the proved existence decision, under the key of `total_match`.
    #[cfg(feature = "lean-unification")]
    has_match:
        Mutex<tamarin_utils::FastMap<(Vec<(LNTerm, LNTerm)>, Vec<crate::lterm::LVar>), bool>>,
    /// Memo for `reduce(...)` queries.  Maude `reduce` is a pure
    /// function of the input term modulo the (fixed-per-session) theory
    /// signature, so successful reductions can be cached across calls.
    /// `has_non_normal_terms` (contradictions.rs) calls `reduce` on
    /// every candidate subterm of every node, and `is_finished` runs
    /// every search step — so the same subterm gets reduced repeatedly
    /// during a single proof.  Caching cuts those repeat round-trips.
    reduce: Mutex<tamarin_utils::FastMap<LNTerm, (LNTerm, Origin)>>,
    /// The session's rewrite table in wire form with the certifier's verdict,
    /// built on the first normalization that needs it. `Some(None)` records
    /// that the module's rules cannot be encoded.
    #[cfg(feature = "lean-unification")]
    reduction_table: Mutex<Option<Option<Arc<crate::lean_unification::ReductionTable>>>>,
    /// Memo for the families of variants the certificate checker accepted,
    /// keyed by the query and the very family that was submitted, with the
    /// origin the answer counts under. Any other verdict fails the session.
    #[cfg(feature = "lean-unification")]
    variant_checks:
        Mutex<tamarin_utils::FastMap<(LNTerm, crate::lean_unification::Substitutions), Origin>>,
    /// Which component produced each answer of this session.
    provenance: Provenance,
    /// Memo for `unifiable(...)` queries — see `MaudeHandle::unifiable`.
    /// Caches the *boolean* outcome (true = at least one unifier exists).
    /// Native-only stores here what the proved existence export decided; it
    /// reads a family in `proved_unify` first, and never reads an entry of
    /// this memo as a family.
    unifiable: Mutex<tamarin_utils::FastMap<Vec<(LNTerm, LNTerm)>, (bool, Origin)>>,
    /// Memo for the RAW REPLY BYTES of the witness-producing Maude commands
    /// (`unify in MSG`, `get variants in MSG`, and the
    /// two `match in MSG` matchers), keyed by the *exact command
    /// byte-string*.  Maude's reply to one of these
    /// commands is a deterministic, command-local function of the theory
    /// module — which is fixed for the life of the session (`sig` is
    /// immutable after `start_with_caches()`, every sharer loads the
    /// identical module, and `with_swapped_maude` hands out a different
    /// pool handle rather than mutating any module) — so identical
    /// command bytes imply an identical reply, exactly the invariant
    /// `reduce` already relies on.
    ///
    /// This caches ONLY the raw bytes: the per-call back-conversion (per-arm
    /// `ConvCtx` clone, `input_max` seeded from the caller's own bindings) still
    /// runs on every hit, so witness numbering, fresh-counter neutrality, and
    /// arm ordering are bit-for-bit what a real round-trip produces — only the
    /// subprocess round-trip is elided.  The reply embeds fresh-variable names
    /// that the caller renames, but the renaming is a pure function of
    /// `(reply bytes, this call's ctx)` and touches NO global fresh state, so a
    /// hit and a miss consume the reply identically.
    ///
    /// SCOPE / MEMORY: bounded to this `SharedMaudeCaches` — i.e. to one
    /// theory session.  It is freed when the session's last
    /// `Arc<SharedMaudeCaches>` drops at session end; it is NOT a
    /// process-global cache and does not accumulate across sessions.  The
    /// distinct-command population per session is small (a theory issues only a
    /// handful of distinct `get variants` / `unify` queries, and fixpoint
    /// passes re-issue the same `match` commands; the win is from heavy
    /// DUPLICATION of those few), so peak residency stays bounded even
    /// though — like `reduce` — no per-entry eviction is performed.
    reply: Mutex<tamarin_utils::FastMap<Vec<u8>, Vec<u8>>>,
}

/// The spelled answers of the proved unifier by the equations as sent.
#[cfg(feature = "lean-unification")]
#[derive(Default)]
struct UnifyMemo {
    answers: tamarin_utils::FastMap<
        Vec<(LNTerm, LNTerm)>,
        (crate::lean_unification::Substitutions, Origin),
    >,
    /// The term nodes the keys and answers hold.
    nodes: usize,
}

/// The term nodes [`UnifyMemo`] may hold. A request renamed apart from an
/// earlier one misses this memo and keeps its own copy of the answer, so a
/// long search would otherwise hold one copy for each renaming.
#[cfg(feature = "lean-unification")]
const UNIFY_MEMO_NODES: usize = 1 << 20;

#[cfg(feature = "lean-unification")]
impl UnifyMemo {
    fn insert(
        &mut self,
        key: Vec<(LNTerm, LNTerm)>,
        answers: &crate::lean_unification::Substitutions,
        origin: Origin,
    ) {
        use crate::term::TermSize;
        let nodes = key.iter().map(|(l, r)| l.size() + r.size()).sum::<usize>()
            + answers
                .iter()
                .flatten()
                .map(|(_, image)| image.size())
                .sum::<usize>();
        if self.nodes.saturating_add(nodes) > UNIFY_MEMO_NODES {
            self.answers.clear();
            self.nodes = 0;
        }
        self.nodes += nodes;
        self.answers.insert(key, (answers.clone(), origin));
    }
}

/// The operation a raw native-only session reports when the certifier did not
/// accept its rewrite table and the all-paths check left a term undecided.
pub const UNCERTIFIED_TABLE: &str =
    "normalization over a rewrite table the certifier did not accept";

/// `TAM_RS_NATIVE_REFERENCE` selects the operations native-only answers from
/// the whole-command exports alone, where it otherwise does more: `1` for
/// both, `0` for neither, or a comma separated list of `reduce` and
/// `variants`. `TAM_RS_NATIVE_REFERENCE_VARIANTS=1` adds `variants`.
///
/// Unification and matching always use only their proved exports. `reduce`
/// skips the normal-form shortcuts that every backend runs and the memo, and
/// accepts the convergence premise for an uncertified table. `variants`
/// takes the folding export as the only proposer in place of the Rust
/// solvers. Its family goes through the certificate checker like one a
/// Rust solver proposes.
#[cfg(feature = "lean-unification")]
#[derive(Debug, Clone, Copy)]
struct Reference {
    reduce: bool,
    variants: bool,
    /// The work bound of the variant certificate checker. See
    /// [`VARIANT_CHECK_WORK`].
    variant_check_work: u64,
    /// The work bound of one interruptible search. See [`SEARCH_WORK`].
    search_work: u64,
    /// Replaces the family a solver proposed before it is checked.
    #[cfg(test)]
    tamper_variants: Option<fn(&mut crate::lean_unification::Substitutions)>,
}

#[cfg(feature = "lean-unification")]
impl Default for Reference {
    fn default() -> Self {
        Self {
            reduce: false,
            variants: false,
            variant_check_work: VARIANT_CHECK_WORK_DEFAULT,
            search_work: SEARCH_WORK_DEFAULT,
            #[cfg(test)]
            tamper_variants: None,
        }
    }
}

/// Rewrite depth granted to the variant certificate checker.
#[cfg(feature = "lean-unification")]
const VARIANT_CHECK_DEPTH: u64 = 1 << 16;

/// `TAM_RS_VARIANT_CHECK_WORK=<n>` sets the work bound of the variant
/// certificate checker, for experiments; `0` removes the bound.
///
/// Native-only uses a family of variants that a Rust solver proposed only
/// after the Lean certificate checker has accepted it. The checker cannot be
/// interrupted. Its work bound limits the number of positions that are not
/// variables at which it looks for narrowing steps, added up over the
/// members of the family in their listed order: the members within the
/// bound are checked, and the check then stops with an out-of-budget reply
/// unless the whole family fits. That reply fails the session with
/// "variants not certified"; it is never an answer. The checker is complete
/// for a canonical table only without a bound, so a larger bound can turn a
/// refusal into an acceptance and nothing else.
pub const VARIANT_CHECK_WORK: &str = "TAM_RS_VARIANT_CHECK_WORK";

/// The work bound without [`VARIANT_CHECK_WORK`]. See TESTING.md,
/// "Variant check budget", for the measurements behind the value.
#[cfg(feature = "lean-unification")]
const VARIANT_CHECK_WORK_DEFAULT: u64 = 1 << 16;

/// `TAM_RS_ALGEBRA_SEARCH_WORK=<n>` sets the work bound of one call of an
/// interruptible Lean export; `0` removes the bound.
///
/// The total unifier, its existence decision and the single-path reducers
/// can take time, and the unifier memory, exponential in the width of an AC
/// product. Each of them asks before every step of its search whether to go
/// on, and one call is stopped when it has asked more than this number of
/// times, or as soon as its request is cancelled. The count is a function
/// of the request alone, so the bound is deterministic. A call stopped by
/// the bound fails the session with "out of budget"; it is never an answer,
/// and a larger bound can only turn that failure into an answer.
pub const SEARCH_WORK: &str = "TAM_RS_ALGEBRA_SEARCH_WORK";

/// The work bound without [`SEARCH_WORK`]. See TESTING.md, "Search budget",
/// for the measurements behind the value.
#[cfg(feature = "lean-unification")]
const SEARCH_WORK_DEFAULT: u64 = 1 << 24;

#[cfg(feature = "lean-unification")]
impl Reference {
    fn from_env() -> Result<Self, MaudeError> {
        let mut selected = Self::default();
        if let Some(value) = std::env::var_os("TAM_RS_NATIVE_REFERENCE") {
            let value = value.to_string_lossy();
            if value == "1" {
                selected = Self {
                    reduce: true,
                    variants: true,
                    ..Self::default()
                };
            } else {
                let named = value
                    .split(',')
                    .filter(|name| !name.is_empty() && *name != "0");
                for operation in named {
                    match operation {
                        "reduce" => selected.reduce = true,
                        "variants" => selected.variants = true,
                        _ => {
                            return Err(MaudeError::Other(format!(
                                "TAM_RS_NATIVE_REFERENCE: unknown operation {operation:?}"
                            )));
                        }
                    }
                }
            }
        }
        if std::env::var_os("TAM_RS_NATIVE_REFERENCE_VARIANTS").as_deref()
            == Some(std::ffi::OsStr::new("1"))
        {
            selected.variants = true;
        }
        if let Some(value) = std::env::var_os(VARIANT_CHECK_WORK) {
            let value = value.to_string_lossy();
            selected.variant_check_work = value.parse().map_err(|_| {
                MaudeError::Other(format!(
                    "{VARIANT_CHECK_WORK}: expected a number of positions, got {value:?}"
                ))
            })?;
        }
        if let Some(value) = std::env::var_os(SEARCH_WORK) {
            let value = value.to_string_lossy();
            selected.search_work = value.parse().map_err(|_| {
                MaudeError::Other(format!(
                    "{SEARCH_WORK}: expected a number of search steps, got {value:?}"
                ))
            })?;
        }
        Ok(selected)
    }
}

#[derive(Debug)]
enum NativeFailure {
    Unsupported(&'static str),
    #[cfg(feature = "lean-unification")]
    Runtime(String),
    /// A backend error absorbed by a caller that cannot return one.
    Absorbed(String),
}

/// Map a native runtime error. Cancellation stays a clean cancellation and
/// is never latched. Any other error invalidates the session: a caller that
/// recovers from the returned error still cannot publish a result, see
/// [`MaudeHandle::check_backend_status`]. Only native-only reaches Lean.
#[cfg(feature = "lean-unification")]
fn native_runtime_error(
    caches: &SharedMaudeCaches,
    error: crate::lean_unification::Error,
) -> MaudeError {
    if error == crate::lean_unification::Error::Cancelled {
        MaudeError::Cancelled
    } else {
        caches
            .native_failure
            .get_or_init(|| NativeFailure::Runtime(error.to_string()))
            .error()
    }
}

impl NativeFailure {
    fn error(&self) -> MaudeError {
        match self {
            Self::Unsupported(operation) => MaudeError::UnsupportedOperation(operation),
            #[cfg(feature = "lean-unification")]
            Self::Runtime(reason) => MaudeError::NativeFailure(reason.clone()),
            Self::Absorbed(reason) => {
                MaudeError::Other(format!("algebra backend failed: {reason}"))
            }
        }
    }
}

struct MaudeProcessInner {
    /// The caller supplied Tamarin's canonical, finite-variant theory premises.
    #[cfg(feature = "lean-unification")]
    theory_fallback: bool,
    backend: AlgebraBackend,
    maude_path: String,
    child: Arc<Mutex<MaudeChildReaper>>,
    initialized: bool,
    stdin: Option<ChildStdin>,
    stdout: Option<ChildStdout>,
    stats: MaudeStats,
    /// Memo cache hit/miss tallies — see `MaudeCacheStats`.
    cache_stats: MaudeCacheStats,
    /// The theory signature — immutable after `start()`.  Shared (`Arc`) with
    /// the owning `MaudeHandle` so reads via `MaudeHandle::maude_sig()` are a
    /// refcount bump rather than a deep clone taken under this IPC mutex.
    sig: Arc<MaudeSig>,
    /// The session's memo caches — see `SharedMaudeCaches` for the
    /// byte-parity argument and the lock-order invariant (this inner's
    /// IPC mutex is always the outer lock; the cache mutexes are only
    /// ever taken strictly inside it).
    caches: Arc<SharedMaudeCaches>,
    /// The live rule heads permit the symbol-only or structural normal-form
    /// shortcut, respectively. The latter also requires AC/C-free patterns.
    reduce_by_symbol: bool,
    reduce_by_structure: bool,
}

/// Cached `TAM_DBG_MAUDE_IO` / `TAM_DBG_MAUDE_IO_FILTER` configuration.
/// Both env vars are constant for the process; `execute()` is the single
/// chokepoint for every Maude IPC round-trip, so read them once instead
/// of per call.  Returns `(trace_enabled, trace_full, filter)` preserving
/// the exact 3-way `TAM_DBG_MAUDE_IO` semantics (`""` / `"full"` / other)
/// and the substring `filter` value.
fn maude_io_trace_config() -> &'static (bool, bool, String) {
    static CFG: std::sync::OnceLock<(bool, bool, String)> = std::sync::OnceLock::new();
    CFG.get_or_init(|| {
        let trace_mode = std::env::var("TAM_DBG_MAUDE_IO").unwrap_or_default();
        let trace_enabled = !trace_mode.is_empty();
        let trace_full = trace_mode == "full";
        let filter = std::env::var("TAM_DBG_MAUDE_IO_FILTER").unwrap_or_default();
        (trace_enabled, trace_full, filter)
    })
}

impl MaudeProcessInner {
    fn unsupported_native_operation(&self, operation: &'static str) -> MaudeError {
        self.caches
            .native_failure
            .get_or_init(|| NativeFailure::Unsupported(operation))
            .error()
    }

    fn require_maude(&self, operation: &'static str) -> Result<(), MaudeError> {
        if self.backend == AlgebraBackend::NativeOnly {
            return Err(self.unsupported_native_operation(operation));
        }
        Ok(())
    }

    fn with_cancellation<T>(
        &mut self,
        work: impl FnOnce(&mut Self) -> Result<T, MaudeError>,
    ) -> Result<T, MaudeError> {
        cancellation::check()?;
        let child = self.child.clone();
        let _registration = cancellation::current().map(|token| {
            token.on_cancel(move || {
                let mut child = child.lock().unwrap();
                child.kill_and_wait();
                child.restart = true;
            })
        });
        // The timed I/O mutex does not poison on panic. Fail closed if an
        // exchange unwinds, so its unread reply can never reach another job.
        let result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| work(self))) {
            Ok(result) => result,
            Err(panic) => {
                self.initialized = false;
                {
                    let mut child = self.child.lock().unwrap();
                    child.kill_and_wait();
                    child.restart = true;
                }
                std::panic::resume_unwind(panic);
            }
        };
        // Any interrupted or failed exchange invalidates this connection.
        // Keep complete memo entries, but discard its pipes before reuse.
        if result.is_err() {
            self.initialized = false;
            let mut child = self.child.lock().unwrap();
            // A cancellation checkpoint can win the race with deferred
            // callback cleanup. Its registration will be removed on return,
            // so recovery must not depend on that callback being invoked.
            if matches!(&result, Err(MaudeError::Cancelled)) {
                child.restart = true;
            }
            child.kill_and_wait();
        }
        cancellation::check()?;
        result
    }

    fn initialize(&mut self) -> Result<(), MaudeError> {
        self.require_maude("Maude initialization")?;
        {
            let mut reaper = self.child.lock().unwrap();
            cancellation::check()?;
            if reaper.child.is_none() {
                if !reaper.restart {
                    return Err(MaudeError::Other("Maude exited unexpectedly".into()));
                }
                let (stdin, stdout, child) = spawn_maude(&self.maude_path)?;
                self.stdin = Some(stdin);
                self.stdout = Some(stdout);
                reaper.child = Some(child);
                reaper.restart = false;
                self.initialized = false;
            }
        }
        if !self.initialized {
            self.read_until_prompt()?;
            for cmd in [
                "set show command off .\n",
                "set show timing off .\n",
                "set show stats off .\n",
            ] {
                self.execute_raw(cmd.as_bytes())?;
            }
            self.execute_raw(pp_theory(&self.sig).as_bytes())?;
            self.initialized = true;
        }
        Ok(())
    }

    fn execute(&mut self, cmd: &[u8]) -> Result<Vec<u8>, MaudeError> {
        self.require_maude("Maude execution")?;
        self.with_cancellation(|inner| {
            inner.initialize()?;
            inner.execute_raw(cmd)
        })
    }

    fn write_line(&mut self, line: &[u8]) -> Result<(), MaudeError> {
        let stdin = self
            .stdin
            .as_mut()
            .ok_or_else(|| MaudeError::Other("missing Maude stdin".into()))?;
        stdin.write_all(line)?;
        stdin.flush()?;
        Ok(())
    }

    fn read_until_prompt(&mut self) -> Result<Vec<u8>, MaudeError> {
        let mut buf = Vec::new();
        let mut tmp = [0u8; 4096];
        loop {
            // The prompt can only straddle the boundary between bytes read
            // before this iteration and the newly-appended chunk, so scan
            // only `buf[start..]` (keeping `PROMPT.len()-1` bytes of overlap)
            // instead of re-scanning the whole accumulated buffer each read
            // — O(N) total rather than O(N^2).  Result is identical because
            // `find_subseq` returns the first match and earlier prefixes
            // were already scanned (and rejected) on prior iterations.
            let start = buf.len().saturating_sub(PROMPT.len() - 1);
            let n = self
                .stdout
                .as_mut()
                .ok_or_else(|| MaudeError::Other("missing Maude stdout".into()))?
                .read(&mut tmp)?;
            if n == 0 {
                return Err(MaudeError::Other("Maude exited unexpectedly".into()));
            }
            buf.extend_from_slice(&tmp[..n]);
            if let Some(rel) = find_subseq(&buf[start..], PROMPT) {
                // Drop the prompt and everything after it in place; `buf` is
                // local, so truncating it beats copying the reply out.
                buf.truncate(start + rel);
                return Ok(buf);
            }
        }
    }

    fn execute_raw(&mut self, cmd: &[u8]) -> Result<Vec<u8>, MaudeError> {
        // `TAM_DBG_MAUDE_IO=1` — truncated trace (200 chars).
        // `TAM_DBG_MAUDE_IO=full` — full command + response.
        // `TAM_DBG_MAUDE_IO_FILTER=unify` — only dump unify calls
        //   (suppresses set/show/reduce noise).
        let &(trace_enabled, trace_full, ref filter) = maude_io_trace_config();
        // Only materialise the full command string when something will
        // actually read it — i.e. tracing is on, or a non-empty filter
        // needs the `contains` check.  In the common untraced path this
        // skips a heap allocation + byte-for-byte copy of the command.
        let cmd_keep = if trace_enabled || !filter.is_empty() {
            let cmd_str_full: String = cmd.iter().map(|&b| b as char).collect();
            let keep = filter.is_empty() || cmd_str_full.contains(filter.as_str());
            if trace_enabled && keep {
                let cmd_str = if trace_full {
                    cmd_str_full
                } else {
                    cmd_str_full.chars().take(200).collect()
                };
                eprintln!("[maude>] {}", cmd_str.replace('\n', "\\n"));
            }
            keep
        } else {
            true
        };
        self.write_line(cmd)?;
        let result = self.read_until_prompt();
        if trace_enabled && cmd_keep {
            match &result {
                Ok(reply) => {
                    let reply_str_full: String = reply.iter().map(|&b| b as char).collect();
                    let reply_str = if trace_full {
                        reply_str_full
                    } else {
                        reply.iter().take(200).map(|&b| b as char).collect()
                    };
                    eprintln!(
                        "[maude<] {} bytes: {}",
                        reply.len(),
                        reply_str.replace('\n', "\\n")
                    );
                }
                Err(e) => eprintln!("[maude<] ERR: {:?}", e),
            }
        }
        result
    }

    /// `execute` with a raw-reply memo keyed by the exact command bytes.
    /// On a hit the cached reply is returned and the subprocess round-trip is
    /// skipped; on a miss the command is issued, `bump` records the per-command
    /// stat, and the reply is cached.  See `SharedMaudeCaches::reply` for why
    /// a cmd-keyed byte cache is transparent to witness numbering.  The stat
    /// bump (like `reduce` skipping `norm_count` on a hit) only fires on a real
    /// round-trip; `MaudeStats` reaches no `--prove` output path, so this does
    /// not affect stdout either way.  Each cache lock is scoped to a single
    /// statement (the `get` / the `insert`) and thus never held across the
    /// `execute` IPC wait, per the `SharedMaudeCaches` lock-order invariant.
    fn execute_memo(
        &mut self,
        cmd: &[u8],
        asked: Asked,
        bump: impl FnOnce(&mut MaudeStats),
    ) -> Result<Vec<u8>, MaudeError> {
        self.require_maude("Maude execution")?;
        let hit = self.caches.reply.lock().unwrap().get(cmd).cloned();
        // A unification is tallied once by its entry point, which answers
        // without Maude when the free unifier settles it; the other commands
        // end here.
        if let Some(cached) = hit {
            self.cache_stats.reply_hits += 1;
            if asked == Asked::Unify {
                trace_unify(TRACE_MAUDE_CACHED);
            } else {
                self.caches.provenance.record_cached(asked, Origin::Maude);
            }
            return Ok(cached);
        }
        let reply = self.execute(cmd)?;
        bump(&mut self.stats);
        self.cache_stats.reply_misses += 1;
        if asked == Asked::Unify {
            trace_unify(TRACE_MAUDE);
        } else {
            self.caches.provenance.record(asked, Origin::Maude);
        }
        self.caches
            .reply
            .lock()
            .unwrap()
            .insert(cmd.to_vec(), reply.clone());
        Ok(reply)
    }
}

impl Drop for MaudeProcessInner {
    /// When `TAM_MAUDE_CACHE_STATS` is set, emit one summary line per Maude
    /// process to STDERR as this inner is torn down (the shared
    /// `Arc<Mutex<MaudeProcessInner>>` is one per subprocess, so this fires
    /// exactly once per process at session end).  Nothing reaches stdout;
    /// stdout is byte-compared against the Haskell oracle.
    fn drop(&mut self) {
        if tamarin_utils::env_gate!("TAM_MAUDE_CACHE_STATS") {
            let s = &self.cache_stats;
            eprintln!(
                "[MAUDE_CACHE_STATS] reduce={}/{} unifiable={}/{} reply={}/{} unspelled={} lean_exists={} lean_unify={}",
                s.reduce_hits,
                s.reduce_misses,
                s.unifiable_hits,
                s.unifiable_misses,
                s.reply_hits,
                s.reply_misses,
                self.stats.lean_unify_unspelled,
                self.stats.lean_unify_exists_count,
                self.stats.lean_unify_count,
            );
        }
    }
}

impl Drop for SharedMaudeCaches {
    /// With `TAM_MAUDE_CACHE_STATS`, report once per session which component
    /// answered each command. STDERR only, like the per-process line above.
    fn drop(&mut self) {
        if tamarin_utils::env_gate!("TAM_MAUDE_CACHE_STATS") {
            for line in self.provenance.report() {
                eprintln!("{line}");
            }
            #[cfg(feature = "lean-unification")]
            if let Some(table) = self.reduction_table.lock().unwrap().as_ref() {
                let verdict = match table {
                    Some(table) if table.certified() => "certified",
                    Some(_) => "uncertified",
                    None => "unencodable",
                };
                eprintln!("[ALGEBRA_PROVENANCE] rewrite table: {verdict}");
            }
            #[cfg(feature = "lean-unification")]
            {
                let memo = self.proved_unify.lock().unwrap();
                let (replies, words) = self.unify_replies.size();
                let exists = self.unify_replies.existence_replies();
                if replies != 0 || exists != 0 {
                    eprintln!(
                        "[UNIFY_MEMO] answers={} nodes={} replies={replies} words={words} exists={exists}",
                        memo.answers.len(),
                        memo.nodes,
                    );
                }
            }
        }
    }
}

fn spawn_maude(maude_path: &str) -> Result<(ChildStdin, ChildStdout, Child), MaudeError> {
    let mut command = Command::new(maude_path);
    tamarin_utils::process::isolate_process_group(&mut command);
    let mut child = command
        .args([
            "-interactive",
            "-no-tecla",
            "-no-banner",
            "-no-wrap",
            "-batch",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|e| MaudeError::Spawn(format!("{maude_path}: {e}")))?;
    Ok((
        child.stdin.take().expect("piped stdin"),
        child.stdout.take().expect("piped stdout"),
        child,
    ))
}

/// Reaper for the Maude `Child` handle.  Lives in its own `Arc<Mutex<...>>`
/// separate from the I/O mutex so that a watchdog can kill the
/// subprocess WITHOUT contending with a reader thread that's blocked
/// inside `read_until_prompt` while holding the I/O lock.
struct MaudeChildReaper {
    child: Option<Child>,
    // Request cancellation and panicking exchanges ask for transparent recovery.
    // Explicit watchdog kills and unrelated I/O errors retain their error semantics.
    restart: bool,
}

impl MaudeChildReaper {
    fn kill_and_wait(&mut self) {
        if let Some(mut c) = self.child.take() {
            tamarin_utils::process::kill_process_group(&mut c);
            let _ = c.wait();
        }
    }
}

impl Drop for MaudeChildReaper {
    fn drop(&mut self) {
        // Reap the Maude subprocess on handle drop.  `Child::drop`
        // alone DETACHES the process (the rust stdlib's std::process
        // does not kill on drop), leaking zombies.
        self.kill_and_wait();
    }
}

fn find_subseq(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Handle to an algebra session (no subprocess in native-only mode).
/// Cloneable; uses an `Arc<Mutex<...>>`
/// internally to serialize exchanges with the Maude subprocess.
/// The `Child` reaper sits in its OWN mutex so a watchdog can
/// `kill_subprocess()` even while a reader thread is blocked on Maude
/// IPC inside `inner` — without this split, the watchdog deadlocks
/// trying to acquire the same mutex the blocked reader holds.
#[derive(Clone)]
pub struct MaudeHandle {
    backend: AlgebraBackend,
    /// The session caches also held by `inner`. Kept here so the failure
    /// latch is readable without the I/O mutex.
    caches: Arc<SharedMaudeCaches>,
    inner: Arc<parking_lot::Mutex<MaudeProcessInner>>,
    child: Arc<Mutex<MaudeChildReaper>>,
    /// Monotonically-increasing counter for fresh-variable allocation.
    ///
    /// Mirrors Haskell's `MonadFresh` (`FreshT m` in lib/utils): a SINGLE
    /// global counter shared across the entire proof session so that
    /// every `freshLVar` call gets a unique idx.  Without this, two
    /// independent Maude calls can both compute `avoid_max + 1` as the
    /// next witness idx and produce colliding `(name, idx)` LVars at
    /// different sorts (e.g. `~mw:Pub:17` from one call and
    /// `~mw:Msg:17` from another).  Those collisions break our
    /// `(name, sort, idx)` LVar identity, leading to sort-conflated
    /// saved source cases.
    ///
    /// Used by:
    /// - `msubst_to_lnsubst_with_avoid` for Maude witness allocation.
    /// - `freshen_witness_range` (eq_store) for post-unification renames.
    /// - `freshen_rule` (reduction) for rule shift.
    ///
    /// Every consumer first calls `ensure_above(local_avoid_max)` to
    /// guarantee the counter is at least as high as the current system
    /// bounds, then calls `fresh_idx()` to allocate.  The counter NEVER
    /// goes backward, so once a witness/rule idx is allocated it can
    /// never be reused.
    fresh_counter: Arc<AtomicU64>,
    /// The theory signature, shared (`Arc`) with `inner` and across every
    /// `with_fresh_counter_from` clone.  Immutable after `start()`, so
    /// `maude_sig()` hands out a cheap refcount-bumped clone WITHOUT taking the
    /// IPC mutex or deep-cloning the `BTreeSet`s.
    sig: Arc<MaudeSig>,
    /// Operators printed by this native-only session, derived from source declarations.
    native_declarations: Option<Arc<crate::function_symbols::FunSig>>,
    /// Where native-only normalizes or lists variants through the
    /// whole-command exports alone, and the budget of its variant checker.
    #[cfg(feature = "lean-unification")]
    reference: Reference,
    /// Immutable signature data used by native workers without the IPC mutex.
    #[cfg(feature = "lean-unification")]
    native_rules: Arc<std::sync::OnceLock<Option<crate::lean_unification::RuleTable>>>,
}

impl std::fmt::Debug for MaudeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaudeHandle({:?})", self.backend)
    }
}

impl MaudeHandle {
    #[cfg(feature = "lean-unification")]
    fn native_rules(&self) -> Option<&crate::lean_unification::RuleTable> {
        self.native_rules
            .get_or_init(|| crate::lean_unification::RuleTable::new(&self.sig))
            .as_ref()
    }

    /// Narrow one free application on distinct message variables and retain
    /// its normal result. Unsupported inputs use the caller's ordinary path.
    ///
    /// Native-only uses the proposed bindings only after the Lean
    /// certificate checker accepted them as a complete set of variants of
    /// the application, and takes each value from the proved reducer.
    pub fn observed_application_variants(
        &self,
        application: &LNTerm,
    ) -> Result<Option<Vec<ApplicationVariant>>, MaudeError> {
        self.check_backend_status()?;
        cancellation::check()?;
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly
            && let Some(table) = self.native_rules()
        {
            let arms = table
                .observed_application_variants(application)
                .map_err(|e| self.lean_error(e))?;
            return arms
                .map(|arms| self.checked_application_variants(application, arms))
                .transpose();
        }
        let _ = application;
        Ok(None)
    }

    #[cfg(feature = "lean-unification")]
    fn checked_application_variants(
        &self,
        application: &LNTerm,
        mut arms: Vec<ApplicationVariant>,
    ) -> Result<Vec<ApplicationVariant>, MaudeError> {
        let certified = {
            let inner = cancellation::lock(&self.inner)?;
            let family: Vec<_> = arms.iter().map(|arm| arm.bindings.clone()).collect();
            let (origin, cached) = self.checked_family(&inner, application, &family)?;
            if cached {
                let tally = &inner.caches.provenance;
                tally.record_cached(Asked::Variants, origin);
            } else {
                inner.caches.provenance.record(Asked::Variants, origin);
            }
            origin == Origin::Proved
        };
        for arm in &mut arms {
            let bindings = crate::subst::Subst::from_list(arm.bindings.clone());
            let value = self.reduce(&crate::subst::apply_vterm(&bindings, application.clone()))?;
            // A certified table has one normal form, so the proposal must
            // have named it. On any other table the reducer's reduct is used.
            if certified && value != arm.value {
                return Err(self
                    .caches
                    .native_failure
                    .get_or_init(|| {
                        NativeFailure::Runtime(format!(
                            "variants not certified: the proposed value {} of {application} \
                             is not its normal form {value}",
                            arm.value
                        ))
                    })
                    .error());
            }
            arm.value = value;
        }
        Ok(arms)
    }

    /// Start a new Maude process and load the theory module for `sig`,
    /// with a fresh private cache set (see [`Self::start_with_caches`]).
    /// The entry point for standalone handles — one-shot commands, tests,
    /// per-request server handles — that share memo results with nobody.
    pub fn start(maude_path: &str, sig: MaudeSig) -> Result<Self, MaudeError> {
        Self::start_with_caches(maude_path, sig, Arc::new(SharedMaudeCaches::default()))
    }

    /// Start a new Maude process and load the theory module for `sig`,
    /// consulting `caches` for the memo lookups.  Handles that share one
    /// `SharedMaudeCaches` MUST be started with the identical `sig` — see
    /// the struct doc's byte-parity argument.  The per-theory session
    /// (run.rs: `file_maude` plus its `MaudePool` members) is the one
    /// sharing site.
    pub fn start_with_caches(
        maude_path: &str,
        sig: MaudeSig,
        caches: Arc<SharedMaudeCaches>,
    ) -> Result<Self, MaudeError> {
        Self::start_with_backend_and_caches(maude_path, sig, AlgebraBackend::default(), caches)
    }

    pub fn start_with_backend(
        maude_path: &str,
        sig: MaudeSig,
        backend: AlgebraBackend,
    ) -> Result<Self, MaudeError> {
        Self::start_with_backend_and_caches(
            maude_path,
            sig,
            backend,
            Arc::new(SharedMaudeCaches::default()),
        )
    }

    /// Open a protocol theory under Tamarin's equational-theory contract.
    /// The full active presentation must be range-restricted, sort-preserving,
    /// terminating and confluent modulo C/AC, with the finite variant property.
    /// These semantic conditions are supplied by the theory author. Raw sessions
    /// can use `start_with_backend` for certificate-only fallback.
    pub fn start_for_tamarin_theory(
        maude_path: &str,
        sig: MaudeSig,
        backend: AlgebraBackend,
        caches: Arc<SharedMaudeCaches>,
    ) -> Result<Self, MaudeError> {
        let session = Self::start_with_backend_and_caches(maude_path, sig, backend, caches)?;
        #[cfg(feature = "lean-unification")]
        {
            session.inner.lock().theory_fallback = backend == AlgebraBackend::NativeOnly;
        }
        Ok(session)
    }

    /// Start a backend session. Native-only creates no subprocess or pipes.
    /// All handles sharing caches must use the same signature, backend and theory assumptions.
    pub fn start_with_backend_and_caches(
        maude_path: &str,
        sig: MaudeSig,
        backend: AlgebraBackend,
        caches: Arc<SharedMaudeCaches>,
    ) -> Result<Self, MaudeError> {
        backend.validate().map_err(MaudeError::Other)?;
        // Wrap once: `inner`, the handle, and every `with_fresh_counter_from`
        // clone share this single immutable signature.
        let sig = Arc::new(sig);
        // stderr: INHERIT, not pipe.  HS uses `runInteractiveCommand`
        // (System.Process) at Maude/Process.hs, which opens a PIPE for
        // stderr too — the returned `herr` (captured into the `MP` record
        // at Maude/Process.hs) is a real stderr pipe handle.  HS simply
        // never reads/drains that pipe.  We deliberately INHERIT stderr
        // instead, because an undrained stderr pipe would deadlock us:
        // if we pipe stderr but never drain it,
        // Maude eventually fills the ~64KB stderr pipe buffer (e.g.
        // bilinear-pairing examples like `ake/bilinear/Scott.spthy`
        // trigger Maude diagnostic chatter), then blocks in `write(2)`
        // on stderr.  Our reader thread is meanwhile blocked in
        // `read(2)` on stdout waiting for the prompt that Maude will
        // never reach.  Classic pipe-buffer deadlock — verified on
        // Scott.spthy::key_secrecy where the RS process sat at 0% CPU
        // for 55s of a 60s timeout while Maude's wchan was
        // `anon_pipe_write` and the RS reader was `anon_pipe_read`.
        cancellation::check()?;
        let (stdin, stdout, child) = if backend.uses_maude() {
            let (stdin, stdout, child) = spawn_maude(maude_path)?;
            (Some(stdin), Some(stdout), Some(child))
        } else {
            (None, None, None)
        };
        let reaper = Arc::new(Mutex::new(MaudeChildReaper {
            child,
            restart: false,
        }));
        let indexed = reduction_heads_indexed(&sig);
        let mut inner = MaudeProcessInner {
            #[cfg(feature = "lean-unification")]
            theory_fallback: false,
            backend,
            maude_path: maude_path.to_owned(),
            child: reaper.clone(),
            initialized: false,
            stdin,
            stdout,
            stats: MaudeStats::default(),
            cache_stats: MaudeCacheStats::default(),
            reduce_by_symbol: indexed && sig.has_no_ac_operators(),
            reduce_by_structure: indexed && sig.st_lhs_all_ac_c_free(),
            sig: Arc::clone(&sig),
            caches: Arc::clone(&caches),
        };
        if backend.uses_maude() {
            inner.with_cancellation(MaudeProcessInner::initialize)?;
        }
        Ok(MaudeHandle {
            backend,
            caches,
            inner: Arc::new(parking_lot::Mutex::new(inner)),
            child: reaper,
            // The global fresh counter starts at 0 (HS-faithful: HS's
            // `MonadFresh` global counter starts at 0).
            fresh_counter: Arc::new(AtomicU64::new(0)),
            native_declarations: (backend == AlgebraBackend::NativeOnly)
                .then(|| Arc::new(sig.declared_fun_syms())),
            sig,
            #[cfg(feature = "lean-unification")]
            native_rules: Default::default(),
            #[cfg(feature = "lean-unification")]
            reference: if backend == AlgebraBackend::NativeOnly {
                Reference::from_env()?
            } else {
                Reference::default()
            },
        })
    }

    pub fn backend(&self) -> AlgebraBackend {
        self.backend
    }

    /// Normalize and list variants through the whole-command exports alone, or not.
    #[cfg(all(test, feature = "lean-unification"))]
    pub(crate) fn set_reference(&mut self, all: bool) {
        self.reference = Reference {
            reduce: all,
            variants: all,
            ..Reference::default()
        };
    }

    /// Check proposed families with the work bound `work` (zero for none),
    /// after `tamper` has replaced them.
    #[cfg(all(test, feature = "lean-unification"))]
    pub(crate) fn set_variant_check(
        &mut self,
        work: u64,
        tamper: Option<fn(&mut crate::lean_unification::Substitutions)>,
    ) {
        self.reference.variant_check_work = work;
        self.reference.tamper_variants = tamper;
    }

    /// Stop one interruptible Lean search after `work` steps (zero for no
    /// bound), as [`SEARCH_WORK`] does for a whole process.
    #[cfg(feature = "lean-unification")]
    pub fn set_search_work(&mut self, work: u64) {
        self.reference.search_work = work;
    }

    /// Which component has answered each command of this session so far.
    pub fn provenance(&self) -> crate::algebra_provenance::ProvenanceSnapshot {
        self.caches.provenance.snapshot()
    }

    /// Whether this native-only session rests on the theory author's premise
    /// that the equations are convergent: its rewrite table has been built
    /// and the Lean certifier did not accept it, or an answer was already
    /// counted as [`Origin::Assumed`]. The table is built by the first
    /// normalization or variant check, so this is `false` before then, and it
    /// never turns back to `false`. Always `false` on Maude, which makes the
    /// same assumption for every theory without a certifier to consult.
    /// Reads the session state only: it builds nothing and changes no answer.
    pub fn convergence_assumed(&self) -> bool {
        if self.backend != AlgebraBackend::NativeOnly {
            return false;
        }
        #[cfg(feature = "lean-unification")]
        if let Some(Some(table)) = self.caches.reduction_table.lock().unwrap().as_ref()
            && !table.certified()
        {
            return true;
        }
        let seen = self.provenance();
        [Asked::Unify, Asked::Match, Asked::Reduce, Asked::Variants]
            .into_iter()
            .any(|command| {
                seen.fresh(command, Origin::Assumed) + seen.cached(command, Origin::Assumed) != 0
            })
    }

    /// Must succeed before any consumer publishes a result, even if a helper
    /// recovered from a backend error. Applies to every backend: the latch
    /// holds native runtime failures and errors recorded by
    /// [`Self::record_failure`].
    pub fn check_backend_status(&self) -> Result<(), MaudeError> {
        match self.caches.native_failure.get() {
            Some(failure) => Err(failure.error()),
            None => Ok(()),
        }
    }

    /// Latch a backend error that the caller cannot return.
    ///
    /// Some algebra queries sit behind interfaces without an error channel
    /// (normal-form predicates, simplifier closures). Such a caller continues
    /// with a placeholder, and this latch guarantees the placeholder never
    /// becomes a verdict: [`Self::check_backend_status`] fails for every
    /// handle of the session from now on.
    ///
    /// Cancellation is not a failure and is not latched. The cancelled
    /// request's token stays cancelled, so the job boundary discards whatever
    /// was computed from the placeholder.
    pub fn record_failure(&self, error: &MaudeError) {
        if matches!(error, MaudeError::Cancelled) || cancellation::check().is_err() {
            return;
        }
        self.caches
            .native_failure
            .get_or_init(|| NativeFailure::Absorbed(error.to_string()));
    }

    /// The value of `result`, or `placeholder` after latching its error with
    /// [`Self::record_failure`]. Only for callers without an error channel.
    pub fn absorb<T>(&self, result: Result<T, MaudeError>, placeholder: impl FnOnce() -> T) -> T {
        match result {
            Ok(value) => value,
            Err(error) => {
                self.record_failure(&error);
                placeholder()
            }
        }
    }

    /// Return the next unique idx and increment the counter.
    /// Mirrors Haskell's `freshIdent` / `freshLVar` — every call returns
    /// a globally-unique integer across the entire proof session.
    pub fn fresh_idx(&self) -> u64 {
        self.fresh_counter.fetch_add(1, Ordering::SeqCst)
    }

    /// Atomically reserve `n` consecutive idxs from the global counter,
    /// returning the FIRST one.  Used by `freshen_rule` to shift a rule's
    /// vars into a globally unique range without per-call collisions.
    /// Haskell's MonadFresh equivalent: `freshIdents n` (replicates
    /// `freshIdent` n times).
    pub fn reserve_idxs(&self, n: u64) -> u64 {
        if n == 0 {
            return self.fresh_counter.load(Ordering::SeqCst);
        }
        self.fresh_counter.fetch_add(n, Ordering::SeqCst)
    }

    /// Bump the counter so the next allocation is strictly greater than `n`.
    /// No-op if the counter is already > `n`.  Callers use this before
    /// `fresh_idx()` to guarantee new allocations don't collide with
    /// any system var below `n`.  The counter never goes backward.
    pub fn ensure_above(&self, n: u64) {
        let target = n.saturating_add(1);
        let mut cur = self.fresh_counter.load(Ordering::SeqCst);
        while cur < target {
            match self.fresh_counter.compare_exchange(
                cur,
                target,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return,
                Err(actual) => cur = actual,
            }
        }
    }

    /// Current counter value (for diagnostics / probe output).
    pub fn fresh_counter_peek(&self) -> u64 {
        self.fresh_counter.load(Ordering::SeqCst)
    }

    /// Force-set the counter to `n` (overwriting the current value
    /// even if `n` is BELOW current).  Used by `apply_eq_store` to
    /// reset the counter between per-variant Maude calls so each
    /// variant's witness allocation starts from the same baseline —
    /// HS-faithful `evalFreshAvoiding` semantics where each
    /// per-variant `applyBound` call has its own fresh state.
    ///
    /// IMPORTANT: callers MUST advance the counter back to the high
    /// water mark after the per-variant loop or subsequent
    /// allocations could collide with the per-variant outputs.
    pub fn reset_counter_to(&self, n: u64) {
        self.fresh_counter.store(n, Ordering::SeqCst);
    }

    /// Clone this handle but with a FRESH fresh_counter initialised to
    /// `avoid_max + 1`.  Mirrors Haskell's `runReduction _ _ _ (avoid sys)`
    /// — every Reduction starts with a counter that's local to that
    /// Reduction call, computed from the system's current free-var max.
    /// Within the Reduction the counter advances (so sequential calls
    /// don't collide), but the next Reduction starts fresh.
    ///
    /// The Maude PROCESS state (the `inner`/`child` Arcs) is shared —
    /// only the counter is per-handle.  This is safe because Maude itself
    /// is stateless between queries; variable idxs are just Rust-side
    /// labels used when constructing Maude terms, not anything Maude
    /// tracks across calls.
    pub fn with_fresh_counter_from(&self, avoid_max: u64) -> MaudeHandle {
        MaudeHandle {
            backend: self.backend,
            caches: Arc::clone(&self.caches),
            inner: self.inner.clone(),
            child: self.child.clone(),
            fresh_counter: Arc::new(AtomicU64::new(avoid_max.saturating_add(1))),
            sig: Arc::clone(&self.sig),
            native_declarations: self.native_declarations.clone(),
            #[cfg(feature = "lean-unification")]
            native_rules: Arc::clone(&self.native_rules),
            #[cfg(feature = "lean-unification")]
            reference: self.reference,
        }
    }

    /// Like [`with_fresh_counter_from`] but takes the NEXT-draw value
    /// directly (HS `FreshState` units).  HS `avoid sys` (LTerm.hs,
    /// `maybe 0 (succ . snd) . boundsVarIdx`) is legitimately 0 for a
    /// system with NO free variables (e.g. a lemma's root system: closed
    /// formula, no nodes), which the `avoid_max + 1` form cannot express.
    pub fn with_fresh_counter_next(&self, next: u64) -> MaudeHandle {
        MaudeHandle {
            backend: self.backend,
            caches: Arc::clone(&self.caches),
            inner: self.inner.clone(),
            child: self.child.clone(),
            fresh_counter: Arc::new(AtomicU64::new(next)),
            sig: Arc::clone(&self.sig),
            native_declarations: self.native_declarations.clone(),
            #[cfg(feature = "lean-unification")]
            native_rules: Arc::clone(&self.native_rules),
            #[cfg(feature = "lean-unification")]
            reference: self.reference,
        }
    }

    /// The theory signature.  Cheap: a refcount bump on the shared immutable
    /// `Arc<MaudeSig>` — NO IPC-mutex lock and NO deep clone of the signature's
    /// `BTreeSet`s.  Hot proof-search predicates probe `reducible_fun_syms_fast`
    /// etc. through this; returning the `Arc` keeps those reads allocation-free
    /// and lock-free.
    pub fn maude_sig(&self) -> Arc<MaudeSig> {
        Arc::clone(&self.sig)
    }

    /// Kill the underlying Maude subprocess.  Use as a watchdog when a
    /// prove_lemma call is blocked inside a synchronous Maude IPC read
    /// (no internal deadline can catch that — the read just sits there
    /// waiting for stdout bytes).  After kill, any pending read returns
    /// EOF and the worker thread unwinds with an error. The owned process
    /// group is killed before reaping its leader, including wrapper children
    /// holding the pipes open. Repeated calls are harmless.
    ///
    /// Locks ONLY `self.child` (the dedicated reaper mutex), NOT
    /// `self.inner`, so it can fire while a reader thread holds the
    /// I/O mutex inside `read_until_prompt`.  Without this split the
    /// watchdog deadlocks with the very thread it's trying to unblock.
    pub fn kill_subprocess(&self) {
        if let Ok(mut reaper) = self.child.lock() {
            reaper.kill_and_wait();
        }
    }

    /// Snapshot of the per-operation Maude call counters for this handle.
    pub fn stats(&self) -> MaudeStats {
        self.inner.lock().stats
    }

    /// Reduce a term to normal form modulo the theory.  Memoized via
    /// `SharedMaudeCaches::reduce`: `reduce` is a pure function of the
    /// input modulo the fixed-per-session Maude signature, and
    /// `has_non_normal_terms` (called on every search step) calls it
    /// repeatedly for the same subterms.  Cache locks are scoped to the
    /// single `get` / `insert` statement, strictly inside the inner IPC
    /// mutex and never across the IPC wait (lock-order invariant on
    /// `SharedMaudeCaches`).
    pub fn reduce(&self, t: &LNTerm) -> Result<LNTerm, MaudeError> {
        self.check_backend_status()?;
        #[cfg(feature = "lean-unification")]
        if self.reference.reduce {
            let inner = cancellation::lock(&self.inner)?;
            let (result, origin) = self.proved_reduce(&inner, t)?;
            inner.caches.provenance.record(Asked::Reduce, origin);
            return Ok(result);
        }
        // An identity fast path can only return a well-formed term in this module.
        let canonical;
        let t = if self.native_declarations.is_some() {
            match self.command_term_is_canonical(t) {
                Some(true) => t,
                Some(false) => {
                    canonical = crate::term::map_lits(t, &mut |lit| *lit);
                    &canonical
                }
                None => {
                    return Err(self
                        .inner
                        .lock()
                        .unsupported_native_operation("normalization"))
                }
            }
        } else {
            t
        };
        let mut ctx = ConvCtx::new();
        let reply = {
            let mut inner = cancellation::lock(&self.inner)?;
            let hit = inner.caches.reduce.lock().unwrap().get(t).cloned();
            if let Some((cached, origin)) = hit {
                inner.cache_stats.reduce_hits += 1;
                inner.caches.provenance.record_cached(Asked::Reduce, origin);
                return Ok(cached);
            }
            // Fast path: if the term contains NO reducible function
            // symbols anywhere, and the signature passes this path's
            // no-AC/C gate, `reduce` is the identity. Reduction applies
            // rewrite equations by matching; it does not narrow query
            // variables. Avoids the ~0.7ms Maude IPC round-trip on the
            // overwhelming majority of fact-term normalisations we
            // perform during subst_system.
            if inner.reduce_by_symbol && !term_has_reducible_sym(t, &inner.sig.reducible_fun_syms) {
                inner
                    .caches
                    .provenance
                    .record(Asked::Reduce, Origin::SharedRust);
                return Ok(t.clone());
            }
            // Native normal-form fast path for the cases the cheap check
            // above rejects (AC signatures, or terms containing reducible
            // symbols).  `nf_via_haskell` (norm.rs) ports HS `nf'`
            // (Norm.hs `nfViaHaskell`), which upstream asserts coincides
            // with `nfViaMaude t = (t ==) <$> norm t` (`_nfCompare'`,
            // Norm.hs) — `true` means no rewrite rule of this
            // signature fires anywhere in `t`, so Maude's `reduce` is the
            // identity on it.  Its st-rule arm uses the no-AC matcher,
            // complete only for Ac/C-free rule LHSes — hence the
            // structural gate (see `term_ac_c_free`).
            //
            // Returning `t.clone()` is byte-identical to the round-trip
            // because both sides of the comparison are f_app-canonical:
            // reduce inputs are rebuilt through the smart constructors (the
            // `Apply` instance for `VTerm` routes `FunSym::Ac`/`C` through
            // `f_app_ac`/`f_app_c`), and Maude replies are reparsed
            // through the SAME constructors (maude_parse.rs `build_app` →
            // `f_app_ac`/`f_app_c`; maude_types.rs `mterm_to_lnterm` →
            // `f_app`), so for a rewrite fixpoint the reparsed reply can
            // only be `t` itself — Maude's transient AC print order cannot
            // reach the result.  Mirrors the cheap fast path's
            // conventions: no reduce-cache insert, no `norm_count` /
            // cache-stat bump.
            if inner.reduce_by_structure && crate::norm::nf_via_haskell(&inner.sig, t) {
                // `TAM_RS_VERIFY_REDUCE_NF` oracle: ALSO run the real
                // Maude round-trip this fast path elides and panic if
                // Maude's answer differs from `t`.  Dead-cheap when
                // unset; nothing reaches stdout.
                if tamarin_utils::env_gate!("TAM_RS_VERIFY_REDUCE_NF") {
                    let mt = lterm_to_mterm_global(t, &mut ctx);
                    let mut cmd = b"reduce ".to_vec();
                    pp_mterm_into(&mt, &mut cmd);
                    cmd.extend_from_slice(b" .\n");
                    let reply = inner.execute(&cmd)?;
                    let mt_back = maude_parse::parse_reduce_reply_with_sig(&reply, &inner.sig)?;
                    let mut next = 0;
                    let maude_result = mterm_to_lnterm(&mt_back, &mut ctx, "z", &mut next);
                    if maude_result != *t {
                        panic!(
                            "TAM_RS_VERIFY_REDUCE_NF: nf_via_haskell certified \
                             a non-fixpoint as normal form — input {:?} but \
                             Maude reduced it to {:?}",
                            t, maude_result,
                        );
                    }
                }
                inner
                    .caches
                    .provenance
                    .record(Asked::Reduce, Origin::SharedRust);
                return Ok(t.clone());
            }
            // Native-only normalizes through the proved exports alone. The two
            // checks above are Tamarin's own normal-form shortcuts, which the
            // Maude backend runs identically before its round trip.
            #[cfg(feature = "lean-unification")]
            if self.backend == AlgebraBackend::NativeOnly {
                let (result, origin) = self.proved_reduce(&inner, t)?;
                inner.cache_stats.reduce_misses += 1;
                inner
                    .caches
                    .reduce
                    .lock()
                    .unwrap()
                    .insert(t.clone(), (result.clone(), origin));
                inner.caches.provenance.record(Asked::Reduce, origin);
                return Ok(result);
            }
            inner.require_maude("normalization")?;
            let mt = lterm_to_mterm_global(t, &mut ctx);
            let mut cmd = b"reduce ".to_vec();
            pp_mterm_into(&mt, &mut cmd);
            cmd.extend_from_slice(b" .\n");
            let reply = inner.execute(&cmd)?;
            inner.stats.norm_count += 1;
            reply
        };
        let mt_back = maude_parse::parse_reduce_reply_with_sig(&reply, &self.sig)?;
        let mut next = 0;
        let result = mterm_to_lnterm(&mt_back, &mut ctx, "z", &mut next);
        let mut inner = cancellation::lock(&self.inner)?;
        inner.cache_stats.reduce_misses += 1;
        inner
            .caches
            .reduce
            .lock()
            .unwrap()
            .insert(t.clone(), (result.clone(), Origin::Maude));
        inner.caches.provenance.record(Asked::Reduce, Origin::Maude);
        Ok(result)
    }

    /// The session's rewrite table in wire form with the certifier's verdict,
    /// built on first use. `None` when the module's rules cannot be encoded.
    #[cfg(feature = "lean-unification")]
    fn reduction_table(
        &self,
        inner: &MaudeProcessInner,
    ) -> Result<Option<Arc<crate::lean_unification::ReductionTable>>, MaudeError> {
        let mut slot = inner.caches.reduction_table.lock().unwrap();
        match &*slot {
            Some(table) => Ok(table.clone()),
            None => {
                // A cancelled or failed build is not stored.
                let built = crate::lean_unification::ReductionTable::new(&inner.sig)
                    .map_err(|error| native_runtime_error(&inner.caches, error))?
                    .map(Arc::new);
                *slot = Some(built.clone());
                Ok(built)
            }
        }
    }

    /// Normalize through one proved export.
    ///
    /// A table the certifier accepted is terminating and confluent, so the
    /// single rewrite path of the certified export ends in the unique normal
    /// form. For any other table the all-paths export answers only when every
    /// path it explored agrees. When that check is undecided, a session
    /// started for a Tamarin theory follows one rewrite path: the export
    /// proves that its answer is an irreducible reduct of the term with the
    /// sorts of the term, and that this reduct is the normal form is the
    /// author's premise that the equations are convergent, as it is for
    /// Maude. Such an answer is recorded as assumed; a raw session reports
    /// the uncertified table instead.
    #[cfg(feature = "lean-unification")]
    fn proved_reduce(
        &self,
        inner: &MaudeProcessInner,
        t: &LNTerm,
    ) -> Result<(LNTerm, Origin), MaudeError> {
        use crate::lean_unification::Reduced;
        let Some(table) = self.reduction_table(inner)? else {
            return Err(inner.unsupported_native_operation("normalization"));
        };
        let follow_path = inner.theory_fallback || self.reference.reduce;
        match table
            .reduce(&inner.sig, t, follow_path, self.reference.search_work)
            .map_err(|error| native_runtime_error(&inner.caches, error))?
        {
            Reduced::Certified(result) | Reduced::Checked(result) => Ok((result, Origin::Proved)),
            Reduced::Path(result) => Ok((result, Origin::Assumed)),
            Reduced::Unsupported => Err(inner.unsupported_native_operation("normalization")),
            Reduced::Undecided => Err(inner.unsupported_native_operation(UNCERTIFIED_TABLE)),
        }
    }

    /// Submit a family proposed for `query`, by a Rust solver or by the
    /// folding export, to the Lean certificate checker, and return the
    /// origin the answer counts under and whether the verdict came from the
    /// session memo.
    ///
    /// An accepted family is a complete set of variants of the query on a
    /// canonical table (`exportedSessionVariantCheck_certified`). The
    /// certifier establishes that premise for a table it accepted, and the
    /// answer is then proved; for any other table the premise is the theory
    /// author's, and the answer is assumed. No other family is used: the
    /// error names the checker's reason and member for a rejected family, or
    /// reports that the checker ran out of budget or did not decide, and
    /// fails the session.
    #[cfg(feature = "lean-unification")]
    fn checked_family(
        &self,
        inner: &MaudeProcessInner,
        query: &LNTerm,
        family: &[Vec<(crate::lterm::LVar, LNTerm)>],
    ) -> Result<(Origin, bool), MaudeError> {
        use crate::lean_unification::{Error, FamilyCheck};
        let work = self.reference.variant_check_work;
        let key = (query.clone(), family.to_vec());
        if let Some(origin) = inner.caches.variant_checks.lock().unwrap().get(&key) {
            return Ok((*origin, true));
        }
        let Some(table) = self.reduction_table(inner)? else {
            return Err(inner.unsupported_native_operation("variant generation"));
        };
        let trace = tamarin_utils::env_gate!("TAM_DBG_VARIANT_CHECK");
        if trace {
            // What the check would spend without a bound.
            let charge = table
                .variant_check_charge(&inner.sig, query, family)
                .map_err(|error| native_runtime_error(&inner.caches, error))?;
            eprintln!(
                "[variant check] {} members, charge {}, work bound {work}, query {query}",
                family.len(),
                charge.map_or("unknown".to_owned(), |charge| charge.to_string()),
            );
        }
        let start = std::time::Instant::now();
        let verdict = table
            .check_variants(&inner.sig, query, family, VARIANT_CHECK_DEPTH, work)
            .map_err(|error| native_runtime_error(&inner.caches, error))?;
        if trace {
            eprintln!(
                "[variant check] {verdict:?} after {} ms",
                start.elapsed().as_millis()
            );
        }
        let refused = match verdict {
            FamilyCheck::Accepted => {
                let origin = if table.certified() {
                    Origin::Proved
                } else {
                    Origin::Assumed
                };
                inner
                    .caches
                    .variant_checks
                    .lock()
                    .unwrap()
                    .insert(key, origin);
                return Ok((origin, false));
            }
            FamilyCheck::Rejected { reason, member } => Error::RejectedVariants { reason, member },
            FamilyCheck::OutOfBudget => Error::VariantCheckBudget {
                depth: VARIANT_CHECK_DEPTH,
                work,
            },
            FamilyCheck::Undecided => Error::UncertifiedVariants,
        };
        Err(inner
            .caches
            .native_failure
            .get_or_init(|| {
                NativeFailure::Runtime(format!(
                    "{refused}; query {query}, family of {} members",
                    family.len()
                ))
            })
            .error())
    }

    /// Whether *any* unifier of `eqs` exists modulo the signature's AC/C
    /// attributes. Ordinary `unify` ignores the signature's rewrite equations.
    ///
    /// Native-only answers from the proved existence export and the memos
    /// ([`Self::proved_unifiable`]); it lists no family. The Maude
    /// backend first tries the syntactic checks and, on a module without
    /// AC/C operators, the local free unifier; any other query goes to Maude
    /// and is memoised via `SharedMaudeCaches::unifiable`, which is safe
    /// because the result is a context-free boolean (no witness LVars leak
    /// across calls).
    pub fn unifiable(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        self.check_backend_status()?;
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            return self.proved_unifiable(eqs);
        }
        let tally = |origin| self.caches.provenance.record(Asked::Unify, origin);
        if eqs.is_empty() || eqs.iter().all(|eq| eq.lhs == eq.rhs) {
            tally(Origin::SharedRust);
            return Ok(true);
        }
        if self.is_ac_free() {
            let local = crate::unification::unify_lnterm_no_ac(eqs.to_vec());
            tally(Origin::SharedRust);
            return Ok(local.is_ok());
        }
        let key: Vec<(LNTerm, LNTerm)> =
            eqs.iter().map(|e| (e.lhs.clone(), e.rhs.clone())).collect();
        // Cache locks below are scoped to the single `get` / `insert`
        // statement, strictly inside the inner IPC mutex and released
        // before any Maude IPC (lock-order invariant on
        // `SharedMaudeCaches`).
        {
            let mut inner = cancellation::lock(&self.inner)?;
            let hit = inner.caches.unifiable.lock().unwrap().get(&key).copied();
            if let Some((hit, origin)) = hit {
                inner.cache_stats.unifiable_hits += 1;
                inner.caches.provenance.record_cached(Asked::Unify, origin);
                return Ok(hit);
            }
        }
        // `unify` tallies its own answer.
        let answer = !self.unify(eqs)?.is_empty();
        let origin = last_unify_origin();
        let mut inner = cancellation::lock(&self.inner)?;
        inner.cache_stats.unifiable_misses += 1;
        inner
            .caches
            .unifiable
            .lock()
            .unwrap()
            .insert(key, (answer, origin));
        Ok(answer)
    }

    /// Conservative gate for the local Robinson unifiability fast path:
    /// no AC/C operators and an empty `st_rules` set. The latter is an
    /// existing routing restriction, not a requirement of ordinary Maude
    /// unification. `unify in MSG` ignores equations, including those marked
    /// `[variant]`; `variant unify` is the distinct command that uses them
    /// (Maude manual §13.3 and §14.9). This bridge emits ordinary `unify`.
    /// Reconsidering the extra gate requires separate compatibility checks.
    fn is_ac_free(&self) -> bool {
        self.sig.has_no_ac_operators() && self.sig.st_rules.is_empty()
    }

    /// Unify a list of equations modulo the signature's AC/C attributes,
    /// returning one substitution per unifier. This does not perform
    /// unification modulo rewrite equations or variant narrowing.
    ///
    /// Witness numbering is HS-faithful and COUNTER-NEUTRAL: HS's
    /// `unifyViaMaude` (Term/Maude/Process.hs) numbers each reply's
    /// fresh witnesses in a pure per-call scope seeded at
    /// `avoid (M.elems bindings)` — the query's own exported vars — via
    /// `evalFreshAvoiding` (Term/Maude/Types.hs), reading and
    /// writing NO global fresh state.  This method therefore takes NO
    /// `avoid` parameter (there is no HS analogue): the session counter is
    /// never touched by a unify call, and the returned `SubstVFresh`
    /// witnesses are α-scoped per subst.  Collision safety at the eq-store
    /// call sites comes structurally from HS `applyBound`'s
    /// `renameAvoiding` pre-step (EquationStore.hs), mirrored in
    /// `apply_eq_store`'s rhs uniform-shift rename — NOT from inflating the
    /// witness idxs.
    pub fn unify(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            let answers = self.proved_unify(eqs)?;
            trace_unifiers(eqs, &answers);
            return Ok(answers);
        }
        UNIFY_TRACE.set(0);
        let answers = self.unify_with_maude(eqs)?;
        trace_unifiers(eqs, &answers);
        // Maude settled the request if it was consulted, else the free
        // unifier that precedes it.
        let trace = UNIFY_TRACE.get();
        let provenance = &self.caches.provenance;
        if trace & TRACE_MAUDE_CACHED != 0 {
            provenance.record_cached(Asked::Unify, Origin::Maude);
        } else if trace & TRACE_MAUDE != 0 {
            provenance.record(Asked::Unify, Origin::Maude);
        } else {
            provenance.record(Asked::Unify, Origin::SharedRust);
        }
        LAST_UNIFY_ORIGIN.set(trace);
        Ok(answers)
    }

    /// Unify through the proved exports alone: the only unifier of a
    /// native-only session. The existence question has its own export
    /// ([`Self::proved_unifiable`]) and reads this method's memo.
    ///
    /// The total export answers a conjunction of algebraic terms with a
    /// complete family of unifiers modulo the module's C and AC attributes,
    /// and one theorem covers that whole command. Tuple wrappers are not
    /// algebraic terms: a request that carries them is first unpacked by a
    /// separate kernel into such a conjunction, or into a clash of shapes.
    /// Rust composes those two steps, so that answer counts as native Rust.
    ///
    /// The answer is the export's family with its witnesses renamed: spelled
    /// as the Maude backend spells its unifiers ([`spell_as_maude`]), or,
    /// for a family that is not the composition that backend builds, lifted
    /// above the query. Either way an arm says what the export's arm says.
    ///
    /// There are two memos. The export's replies are kept by the words of
    /// the request, which are the same for requests that differ only in the
    /// names of their variables, and a repeat decodes the stored reply
    /// against its own names. The spelled answers are kept under the
    /// equations as sent, for the exact repeats that make up most requests.
    #[cfg(feature = "lean-unification")]
    fn proved_unify(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<crate::lean_unification::Substitutions, MaudeError> {
        use crate::lean_unification::{unpack_conjunction, Conjunction, Outcome};
        self.check_backend_status()?;
        cancellation::check()?;
        let key: Vec<(LNTerm, LNTerm)> =
            eqs.iter().map(|e| (e.lhs.clone(), e.rhs.clone())).collect();
        let hit = self
            .caches
            .proved_unify
            .lock()
            .unwrap()
            .answers
            .get(&key)
            .cloned();
        let provenance = &self.caches.provenance;
        if let Some((answers, origin)) = hit {
            provenance.record_cached(Asked::Unify, origin);
            return Ok(answers);
        }
        let origin = if crate::lean_unification::is_single_export(eqs) {
            Origin::Proved
        } else {
            Origin::NativeRust
        };
        let unsupported = || {
            self.inner
                .lock()
                .unsupported_native_operation("AC/C unification")
        };
        let mut stored = false;
        let answers = match unpack_conjunction(&self.sig, eqs).map_err(|e| self.lean_error(e))? {
            Conjunction::Clash => Vec::new(),
            Conjunction::Unsupported => return Err(unsupported()),
            Conjunction::Rows(rows) => {
                let (outcome, reused) = crate::lean_unification::total_unify(
                    &self.sig,
                    &rows,
                    Some(&self.caches.unify_replies),
                    self.reference.search_work,
                )
                .map_err(|e| self.lean_error(e))?;
                stored = reused;
                match outcome {
                    Outcome::Complete(mut answers) => {
                        match spell_as_maude(&self.sig, eqs, &answers) {
                            Some(spelled) => spelled,
                            None => {
                                lift_witnesses_above_query(eqs, &mut answers);
                                cancellation::lock(&self.inner)?.stats.lean_unify_unspelled += 1;
                                answers
                            }
                        }
                    }
                    Outcome::Unsupported => return Err(unsupported()),
                }
            }
        };
        if stored {
            provenance.record_cached(Asked::Unify, origin);
        } else {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            provenance.record(Asked::Unify, origin);
        }
        self.caches
            .proved_unify
            .lock()
            .unwrap()
            .insert(key, &answers, origin);
        Ok(answers)
    }

    /// Decide through the proved existence export whether `eqs` has a
    /// unifier modulo the module's C and AC attributes, without listing one.
    ///
    /// The export takes the request of the total unifier and is proved to
    /// answer "exists" exactly when a unifier exists, so it agrees with the
    /// emptiness of the family [`Self::proved_unify`] lists. A request with
    /// tuple wrappers is unpacked first by the same kernel as there, and
    /// that composition counts as native Rust here too.
    ///
    /// A family already listed for the request answers by its emptiness,
    /// under the equations as sent or under the words of the request.
    /// Otherwise the decision is kept, under both keys, as a decision only:
    /// [`Self::proved_unify`] reads neither store.
    #[cfg(feature = "lean-unification")]
    fn proved_unifiable(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        use crate::lean_unification::{unpack_conjunction, Conjunction};
        cancellation::check()?;
        let key: Vec<(LNTerm, LNTerm)> =
            eqs.iter().map(|e| (e.lhs.clone(), e.rhs.clone())).collect();
        let origin = if crate::lean_unification::is_single_export(eqs) {
            Origin::Proved
        } else {
            Origin::NativeRust
        };
        let provenance = &self.caches.provenance;
        let listed = self
            .caches
            .proved_unify
            .lock()
            .unwrap()
            .answers
            .get(&key)
            .map(|(answers, _)| !answers.is_empty());
        let decided = listed.or_else(|| Some(self.caches.unifiable.lock().unwrap().get(&key)?.0));
        if let Some(found) = decided {
            provenance.record_cached(Asked::Unify, origin);
            return Ok(found);
        }
        let unsupported = || {
            self.inner
                .lock()
                .unsupported_native_operation("AC/C unification")
        };
        let (found, reused) =
            match unpack_conjunction(&self.sig, eqs).map_err(|e| self.lean_error(e))? {
                Conjunction::Clash => (false, false),
                Conjunction::Unsupported => return Err(unsupported()),
                Conjunction::Rows(rows) => {
                    let (found, reused) = crate::lean_unification::total_unify_exists(
                        &self.sig,
                        &rows,
                        Some(&self.caches.unify_replies),
                        self.reference.search_work,
                    )
                    .map_err(|e| self.lean_error(e))?;
                    (found.ok_or_else(unsupported)?, reused)
                }
            };
        if reused {
            provenance.record_cached(Asked::Unify, origin);
        } else {
            cancellation::lock(&self.inner)?
                .stats
                .lean_unify_exists_count += 1;
            provenance.record(Asked::Unify, origin);
        }
        self.caches
            .unifiable
            .lock()
            .unwrap()
            .insert(key, (found, origin));
        Ok(found)
    }

    #[cfg(feature = "lean-unification")]
    fn lean_error(&self, error: crate::lean_unification::Error) -> MaudeError {
        native_runtime_error(&self.caches, error)
    }

    /// The Maude backend's unifier: HS `unifyLTermFactored` solves the free
    /// part locally and sends Maude only the delayed AC/C equations.
    fn unify_with_maude(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        let Some((factored_m, residual_eqs)) = factor_unification(&self.sig, eqs) else {
            return Ok(Vec::new());
        };
        if residual_eqs.is_empty() {
            // composeVFresh gives aliases shared fresh images, as expected by apply_eq_store.
            let identity = crate::subst_vfresh::LNSubstVFresh::empty();
            let composed = crate::subst_vfresh::compose_vfresh(&identity, &factored_m);
            return Ok(vec![composed.to_list()]);
        }
        self.unify_residuals_with_maude(&residual_eqs, &factored_m)
    }

    fn unify_residuals_with_maude(
        &self,
        maude_eqs: &[Equal<LNTerm>],
        factored_m: &crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.inner.lock().require_maude("AC/C unification")?;
        let mut inner = cancellation::lock(&self.inner)?;
        let mut ctx = ConvCtx::new();
        let cmd = build_conj_eqs_cmd(b"unify in MSG : ", maude_eqs, &mut ctx);
        // Raw-reply memo (see `SharedMaudeCaches::reply`): identical `unify in MSG` command
        // bytes yield an identical reply, and the per-arm back-conversion below
        // still runs on every call, so a hit is bit-for-bit a real round-trip.
        let reply = inner.execute_memo(&cmd, Asked::Unify, |s| s.unify_count += 1)?;
        drop(inner);
        let msubsts = maude_parse::parse_unify_reply_with_sig(&reply, &self.sig)?;
        // HS `avoid (M.elems bindings)` (`runBackConversion`,
        // Term/Maude/Types.hs, via
        // LTerm.hs `avoid = maybe 0 (succ . snd) . boundsVarIdx`):
        // the witness fresh-supply floor is the max idx over ALL of the
        // query's own binding vars — i.e. the vars of `maude_eqs`, which
        // `lterm_to_mterm_global` has registered in `ctx`'s inverse map.
        // This is the ONLY input to witness numbering: HS injects NO
        // system-wide avoid (there is no HS `avoid` parameter on unify), so
        // neither do we.  Each reply arm is converted below in this SAME
        // local scope, never reading or advancing `self`'s session counter.
        let mut input_max = 0u64;
        for lit in ctx.bindings().values() {
            if let crate::vterm::Lit::Var(lv) = lit
                && lv.idx > input_max
            {
                input_max = lv.idx;
            }
        }
        let mut out = Vec::with_capacity(msubsts.len());
        // HS-faithful per-unifier conversion (Term/Maude/Process.hs
        // + Term/Maude/Types.hs).  HS does:
        //   map (msubstToLSubstVFresh bindings) <$> parseUnifyReply ...
        // where each `msubstToLSubstVFresh bindings substMaude` calls
        //   runBackConversion (traverse translate substMaude) bindings
        // and `runBackConversion back bindings =
        //   evalBindT back bindings `evalFreshAvoiding` M.elems bindings`.
        //
        // Every unifier conversion gets:
        //   (a) the SAME initial bind-map `bindings` (the toMaude
        //       conversion's output) — no carryover of witness/FreshVar
        //       allocations from one unifier to the next, AND
        //   (b) a fresh supply seeded LOCALLY at `avoid (M.elems bindings)`
        //       = `input_max + 1` — the SAME base per unifier, drawn ONLY
        //       from the query's own vars.  HS reads NO global fresh state
        //       here and writes NONE back: after `evalFreshAvoiding` the
        //       supply is discarded, so a `unifyViaMaude` call is
        //       counter-neutral (the session `MonadFresh` state is
        //       unchanged across it).
        //
        // This per-unifier same-base restart is load-bearing for arm Ord:
        // on Resp_1 / Init_1 / generate_ltk multi-AC arms
        // (UM_wPFS::wPFS_responder_key + JKL_TS2_2008), the Mult arm's
        // witness gets a lower idx than the "everything-equates" arm's
        // because it traverses fewer distinct FreshVars before the equate
        // target, so HS sorts Mult before Equates under the SubstVFresh Ord.
        //
        // Faithful realisation: convert each arm on its OWN clone of the
        // shared `ctx`, seeding the witness supply at the same local
        // `input_max` via `msubst_to_lnsubst_with_avoid`.  The session
        // counter (`self`) is never passed, never read, never advanced —
        // matching HS's pure `evalFreshAvoiding` scope.  Sharing `ctx` (or
        // the counter) across arms would collapse the per-arm idx
        // differences and mis-order the arms (fallback to VALUE-structure
        // Ord).
        for ms in &msubsts {
            let mut per_arm_ctx = ctx.clone();
            out.push(msubst_to_lnsubst_with_avoid(
                ms,
                &mut per_arm_ctx,
                input_max,
            )?);
        }
        // HS-faithful `removeRenamings` (Maude/Types.hs): HS's
        // `msubstToLSubstVFresh bindings substMaude` ends with
        // `removeRenamings $ substFromListVFresh slist` — drops every
        // entry whose image is just a Var with no role elsewhere in
        // the substitution (`isRenamedVar` in SubstVFresh.hs).
        // RS's `msubst_to_lnsubst_with_avoid` returns the raw slist without
        // that filter, so it is applied here: left in, the trivial rename
        // entries reach the disjunction's substs as extra node-id bindings
        // and drive spurious `setNodes` collisions.
        Ok(compose_residual_arms(out, factored_m))
    }

    #[cfg(feature = "lean-unification")]
    fn total_match(
        &self,
        oriented: &[Equal<LNTerm>],
        bindable: impl Fn(&crate::lterm::LVar) -> bool,
    ) -> Result<Option<crate::lean_unification::Substitutions>, MaudeError> {
        use crate::lterm::HasFrees;
        let mut variables = Vec::new();
        for eq in oriented {
            for side in [&eq.lhs, &eq.rhs] {
                side.for_each_free(&mut |v| {
                    if bindable(v) {
                        variables.push(*v);
                    }
                });
            }
        }
        variables.sort_unstable();
        variables.dedup();
        let key = (
            oriented
                .iter()
                .map(|eq| (eq.lhs.clone(), eq.rhs.clone()))
                .collect::<Vec<_>>(),
            variables,
        );
        let origin = match_origin(oriented);
        let cached = {
            let inner = cancellation::lock(&self.inner)?;
            inner.caches.total_match.lock().unwrap().get(&key).cloned()
        };
        if let Some(answers) = cached {
            self.caches.provenance.record_cached(Asked::Match, origin);
            return Ok(Some(answers));
        }
        match crate::lean_unification::match_modulo_attributes(&self.sig, oriented, bindable)
            .map_err(|e| self.lean_error(e))?
        {
            crate::lean_unification::Outcome::Complete(mut answers) => {
                // The export may list one matcher more than once. A family
                // with the same members is complete for the same request
                // (`Matching.Complete.of_same_members`), so keep one copy of
                // each in a fixed order.
                answers.sort_unstable();
                answers.dedup();
                cancellation::lock(&self.inner)?
                    .caches
                    .total_match
                    .lock()
                    .unwrap()
                    .insert(key, answers.clone());
                self.caches.provenance.record(Asked::Match, origin);
                Ok(Some(answers))
            }
            crate::lean_unification::Outcome::Unsupported => Ok(None),
        }
    }

    /// Decide through the proved existence export whether `oriented` (pattern
    /// on the left) has a matcher that binds only `bindable` variables.
    #[cfg(feature = "lean-unification")]
    fn proved_has_match(
        &self,
        oriented: &[Equal<LNTerm>],
        bindable: impl Fn(&crate::lterm::LVar) -> bool,
        operation: &'static str,
    ) -> Result<bool, MaudeError> {
        use crate::lterm::HasFrees;
        let mut variables = Vec::new();
        for eq in oriented {
            for side in [&eq.lhs, &eq.rhs] {
                side.for_each_free(&mut |v| {
                    if bindable(v) {
                        variables.push(*v);
                    }
                });
            }
        }
        variables.sort_unstable();
        variables.dedup();
        let key = (
            oriented
                .iter()
                .map(|eq| (eq.lhs.clone(), eq.rhs.clone()))
                .collect::<Vec<_>>(),
            variables,
        );
        let origin = match_origin(oriented);
        let cached = {
            let inner = cancellation::lock(&self.inner)?;
            let listed = inner
                .caches
                .total_match
                .lock()
                .unwrap()
                .get(&key)
                .map(|answers| !answers.is_empty());
            listed.or_else(|| inner.caches.has_match.lock().unwrap().get(&key).copied())
        };
        if let Some(found) = cached {
            self.caches.provenance.record_cached(Asked::Match, origin);
            return Ok(found);
        }
        let found =
            crate::lean_unification::has_match_modulo_attributes(&self.sig, oriented, bindable)
                .map_err(|e| self.lean_error(e))?
                .ok_or_else(|| self.inner.lock().unsupported_native_operation(operation))?;
        cancellation::lock(&self.inner)?
            .caches
            .has_match
            .lock()
            .unwrap()
            .insert(key, found);
        self.caches.provenance.record(Asked::Match, origin);
        Ok(found)
    }

    #[cfg(feature = "lean-unification")]
    fn proved_match(
        &self,
        oriented: &[Equal<LNTerm>],
        bindable: impl Fn(&crate::lterm::LVar) -> bool,
        operation: &'static str,
    ) -> Result<crate::lean_unification::Substitutions, MaudeError> {
        self.total_match(oriented, bindable)?
            .ok_or_else(|| self.inner.lock().unsupported_native_operation(operation))
    }

    /// Compute AC matchers for a batch of `(subject, pattern)` problems.
    ///
    /// **Convention — faithful to Haskell.** Each `Equal { lhs, rhs }`
    /// has `lhs = subject` (its variables are rigid) and
    /// `rhs = pattern` (vars bind). This mirrors HS exactly:
    /// `matchWith t p = DelayedMatches [(t, p)]` is `(subject, pattern)`
    /// (`Term/Rewriting/Definitions.hs`), and `matchViaMaude`
    /// turns each pair into `Equal subject pattern` via
    /// `uncurry Equal <$> ms` (`Term/Maude/Process.hs`). The
    /// emitted Maude command is then `match PATTERN <=? SUBJECT`,
    /// i.e. `matchCmd`'s `ppTerms t2s <> " <=? " <> ppTerms t1s` where
    /// `(t1s, t2s) = unzip [(a, b) | Equal a b <- eqs]` so `t2s = b =
    /// pattern` lands on Maude's LEFT (pattern slot) and `t1s = a =
    /// subject` on the RIGHT (subject slot) — `Maude/Process.hs`.
    ///
    /// Maude's `match A <=? B` binds vars in **A (PATTERN, left)** and
    /// leaves variables in **B (SUBJECT, right)** unchanged.
    /// So pattern must go LEFT — which is why
    /// `pp_mterm_list(&pats)` (= `t2s` = each `eq.rhs`) is emitted first.
    ///
    /// NOTE the opposite field order from `Equal` as used by callers
    /// that pass `Equal { lhs = pattern, rhs = subject }`: HS's `Equal`
    /// holds `(subject, pattern)`, and so does this routine. Callers
    /// constructed from `matchFact`/`matchWith` (e.g. `sources.rs`) MUST
    /// therefore put the subject in `lhs` and the pattern in `rhs`.
    /// Each match lists its bindings in variable order, as in HS `substToList`.
    pub fn match_eqs(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        let mut answers = self.match_eqs_impl(eqs)?;
        self.order_native_alternatives(&mut answers);
        Ok(answers)
    }

    /// Source refinement chooses the lexicographically least complete binding
    /// map in the caller's variable and term order, including identity bindings.
    /// This choice is independent of the backend's enumeration order.
    pub fn first_match_eqs(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Option<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        Ok(self.match_eqs_impl(eqs)?.into_iter().min())
    }

    /// The experimental backend exposes the lexicographic order of complete
    /// binding maps in the caller's scope. This also removes repeat answers.
    fn order_native_alternatives(&self, answers: &mut Vec<Vec<(crate::lterm::LVar, LNTerm)>>) {
        if self.backend == AlgebraBackend::NativeOnly && answers.len() > 1 {
            answers.sort_unstable();
            answers.dedup();
        }
    }

    /// Determine whether any match exists, independent of arm order.
    pub fn has_match_eqs(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            self.check_backend_status()?;
            let oriented: Vec<_> = eqs
                .iter()
                .map(|eq| Equal::new(eq.rhs.clone(), eq.lhs.clone()))
                .collect();
            return self.proved_has_match(&oriented, |_| true, "matching");
        }
        self.match_eqs_impl(eqs).map(|answers| !answers.is_empty())
    }

    /// Validate arity and native module membership while checking C/AC child order.
    fn command_term_is_canonical(&self, t: &LNTerm) -> Option<bool> {
        use crate::function_symbols::FunSym;
        use crate::{lterm::LSort, term::Term, vterm::Lit};
        let (f, args) = match t {
            Term::Lit(_) if self.native_declarations.is_none() || self.sig.enable_nat => {
                return Some(true)
            }
            Term::Lit(lit) => {
                let sort = match lit {
                    Lit::Var(v) => v.sort,
                    Lit::Con(n) => crate::maude_types::sort_of_name(n),
                };
                return (sort != LSort::Nat).then_some(true);
            }
            Term::App(f, args) => (f, args),
        };
        // Every module declares the administrative list/cons/nil operators at TOP.
        if *f != FunSym::List
            && self
                .native_declarations
                .as_ref()
                .is_some_and(|symbols| !symbols.contains(f))
        {
            return None;
        }
        let mut sorted = match f {
            FunSym::Ac(_) if args.len() >= 2 => {
                args.is_sorted() && !args.iter().any(|a| matches!(a, Term::App(g, _) if g == f))
            }
            FunSym::C(_) if args.len() == 2 => args[0] <= args[1],
            FunSym::NoEq(head) if args.len() == head.arity => true,
            FunSym::List => true,
            _ => return None,
        };
        for arg in args.iter() {
            sorted &= self.command_term_is_canonical(arg)?;
        }
        Some(sorted)
    }

    // Maude backend only. With no bindable variables, matching reduces to
    // equality modulo C and AC. Smart constructors already produce the canonical
    // representation. A library caller can also supply valid raw trees with
    // unsorted or nested AC children.
    fn rigid_match_equal(
        &self,
        eqs: &[Equal<LNTerm>],
        operation: &'static str,
    ) -> Result<Option<bool>, MaudeError> {
        let mut raw = false;
        for term in eqs.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]) {
            let Some(already_sorted) = self.command_term_is_canonical(term) else {
                // The wire encoder itself rebuilds through smart constructors.
                // Empty or singleton AC nodes have no valid application to send.
                self.inner.lock().require_maude(operation)?;
                return Err(MaudeError::Other(
                    "invalid operator arity in matching query".into(),
                ));
            };
            raw |= !already_sorted;
        }
        // A raw tree goes to Maude, which canonicalizes it.
        Ok((!raw).then(|| eqs.iter().all(|eq| eq.lhs == eq.rhs)))
    }

    fn match_eqs_impl(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        // Native-only answers every match through the proved total matcher.
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            let oriented: Vec<_> = eqs
                .iter()
                .map(|eq| Equal::new(eq.rhs.clone(), eq.lhs.clone()))
                .collect();
            return self.proved_match(&oriented, |_| true, "matching");
        }
        if eqs.is_empty() {
            self.caches
                .provenance
                .record(Asked::Match, Origin::SharedRust);
            return Ok(vec![Vec::new()]);
        }
        let rigid = eqs.iter().all(|eq| crate::vterm::is_ground_vterm(&eq.rhs));
        if rigid && let Some(matched) = self.rigid_match_equal(eqs, "matching")? {
            self.caches
                .provenance
                .record(Asked::Match, Origin::SharedRust);
            return Ok(if matched { vec![Vec::new()] } else { vec![] });
        }
        let mut inner = cancellation::lock(&self.inner)?;
        let mut ctx = ConvCtx::new();
        // `subjs` ← each `eq.lhs` (HS `t1s = a = subject`);
        // `pats`  ← each `eq.rhs` (HS `t2s = b = pattern`).
        inner.require_maude("matching")?;
        let mut subjs: Vec<MTerm> = Vec::with_capacity(eqs.len());
        let mut pats: Vec<MTerm> = Vec::with_capacity(eqs.len());
        for eq in eqs {
            subjs.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            pats.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        // `match in MSG : list(pats) <=? list(subjs) .`
        // Mirrors HS `matchCmd` (`Maude/Process.hs`): PATTERN on the
        // left (vars bind), SUBJECT on the right (its variables stay rigid).
        // `pp_mterm_list` emits `list( cons(t1, cons(t2, nil)) )` style,
        // formatting the borrowed slice directly without a `Vec`+`Arc`
        // round-trip.
        let cmd = pp_match_cmd(&pats, &subjs);
        let reply = inner.execute_memo(&cmd, Asked::Match, |s| s.match_count += 1)?;
        drop(inner);
        let msubsts = maude_parse::parse_match_reply_with_sig(&reply, &self.sig)?;
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            out.push(msubst_to_lnsubst(ms, &mut ctx)?);
        }
        Ok(out)
    }

    /// Match where BOTH the pattern and subject sides have their free
    /// non-pattern-vars skolemized to synthetic constants — using the
    /// SAME mapping for both sides, so that occurrences of the same
    /// LVar in pattern and subject still match each other through
    /// their shared synthetic constant.
    ///
    /// This mirrors HS's `matchTerm` (Guarded.hs) called from
    /// `impliedFormulas` (System.hs): the universal is fully
    /// `skolemizeGuarded`-ed before matching, so every FREE LVar
    /// (universal-non-bound vars, originating from the system context)
    /// becomes a `Con (SkConst x)`, while the universal-bound
    /// (pattern) vars stay `Var x`.  The subject side (the system's
    /// own term) is also skolemized via `skolemizeTerm`, so the same
    /// LVar `y` on both sides maps to the same `SkConst y` constant.
    /// Maude can then match the pattern against the subject without
    /// spuriously binding the pattern's `y` to anything (it's a
    /// constant on both sides).
    ///
    /// Used by `insert_implied_formulas_pass`'s Eq-guard branch to
    /// handle AC-symbol patterns (e.g. multiset `y++z` against
    /// `'1'++y++h(y)`) faithfully.
    /// Each match lists its bindings in the same order as `match_eqs`.
    pub fn match_eqs_skolemize_both(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        use crate::lterm::LVar;
        // Native-only answers every match through the proved total matcher,
        // which takes the scope of bindable variables directly.
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            let mut answers = self.proved_match(
                eqs,
                |v| pattern_vars.contains(&(v.name, v.idx)),
                "rigid-context matching",
            )?;
            self.order_native_alternatives(&mut answers);
            return Ok(answers);
        }
        if eqs.is_empty() {
            self.caches
                .provenance
                .record(Asked::Match, Origin::SharedRust);
            return Ok(vec![Vec::new()]);
        }
        // Skolemization on both sides is injective on the rigid variables, so a
        // query with no bindable pattern variable can compare the original terms.
        fn has_pattern_var(
            t: &LNTerm,
            pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
        ) -> bool {
            use crate::vterm::Lit;
            match t {
                crate::term::Term::Lit(Lit::Var(lv)) => pattern_vars.contains(&(lv.name, lv.idx)),
                crate::term::Term::App(_, args) => {
                    args.iter().any(|a| has_pattern_var(a, pattern_vars))
                }
                _ => false,
            }
        }
        let rigid = eqs.iter().all(|eq| !has_pattern_var(&eq.lhs, pattern_vars));
        if rigid && let Some(matched) = self.rigid_match_equal(eqs, "rigid-context matching")? {
            self.caches
                .provenance
                .record(Asked::Match, Origin::SharedRust);
            return Ok(if matched { vec![Vec::new()] } else { vec![] });
        }
        // Step 1: collect ALL non-pattern free vars from BOTH sides.
        // The same LVar appearing on both sides must skolemize to the
        // same Name so the two occurrences match each other.
        let mut free_vars: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for eq in eqs {
            collect_free_non_pattern_vars(&eq.lhs, pattern_vars, &mut free_vars);
            collect_free_non_pattern_vars(&eq.rhs, pattern_vars, &mut free_vars);
        }
        let (skolem_map, reverse) =
            build_skolem_maps(&free_vars, eqs.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]))?;
        // Step 2: rewrite BOTH sides via the shared skolem_map.
        let rewritten_eqs: Vec<Equal<LNTerm>> = eqs
            .iter()
            .map(|eq| Equal {
                lhs: rewrite_skolem(&eq.lhs, &skolem_map),
                rhs: rewrite_skolem(&eq.rhs, &skolem_map),
            })
            .collect();

        let mut inner = cancellation::lock(&self.inner)?;
        inner.require_maude("rigid-context matching")?;
        let mut ctx = ConvCtx::new();
        let mut pats: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        let mut subjs: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        for eq in &rewritten_eqs {
            pats.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            subjs.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        // Maude's `match A <=? B` syntax means: find σ such that B = σ(A).
        // So A is the PATTERN (left), B is the SUBJECT (right).
        // Callers of THIS routine pass `Equal { lhs = pattern, rhs =
        // subject }`, so the command is `match pattern(lhs) <=?
        // subject(rhs)`.  The plain `match_eqs` uses the OPPOSITE `Equal`
        // field order (`lhs = subject, rhs = pattern`, faithful to HS's
        // `Equal a b = Equal subject pattern`); it still emits
        // `match PATTERN <=? SUBJECT` on the wire, just sourced from the
        // flipped fields.  So both matchers emit pattern-on-the-left,
        // which is what Maude requires (vars bind in the left operand).
        let cmd = pp_match_cmd(&pats, &subjs);
        let reply = inner.execute_memo(&cmd, Asked::Match, |s| s.match_count += 1)?;
        drop(inner);
        let msubsts = maude_parse::parse_match_reply_with_sig(&reply, &self.sig)?;
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            let lnsubst = msubst_to_lnsubst(ms, &mut ctx)?;
            // Un-skolemize all bindings so the caller gets LVars back.
            out.push(unskolemize_subst(lnsubst, &reverse));
        }
        Ok(out)
    }

    #[cfg(feature = "lean-unification")]
    fn bounded_variants(
        &self,
        sig: &MaudeSig,
        query: &LNTerm,
        finite_variants: impl FnOnce() -> bool,
    ) -> Result<(crate::lean_unification::Outcome, VariantRoute), crate::lean_unification::Error>
    {
        use crate::lean_unification::{pairing_variants, Outcome};
        // Every family but the last is assembled by a specialised Rust
        // solver, and is a proposal that the checker has yet to accept.
        let trace = tamarin_utils::env_gate!("TAM_DBG_VARIANTS");
        let rust = |outcome, solver: &str| {
            if trace {
                eprintln!("[variants] solver {solver}");
            }
            Ok((outcome, VariantRoute::Proposer))
        };
        let pairing = pairing_variants(sig, query)?;
        if let Outcome::Complete(_) = pairing {
            return rust(pairing, "pairing");
        }
        let Some(theory) = self.native_rules() else {
            return rust(Outcome::Unsupported, "none");
        };
        if let complete @ Outcome::Complete(_) = theory.fresh_xor_variants(query)? {
            return rust(complete, "fresh_xor");
        }
        match theory.variants(query)? {
            Outcome::Unsupported => match theory.joined_variants(query)? {
                // The checked export is a contract export: a family it
                // returns is complete with unique values on any table
                // (`exportedCheckedVariants_sound`). It is the only solver
                // for kind-level input, where the checker's closure test is
                // exponential in the width of an AC product.
                Outcome::Unsupported => {
                    // No specialised solver covers the query. Folding
                    // variant narrowing proposes a family for any sorted
                    // query; like every proposal it is used only if the
                    // checker accepts it. The search ends only when the
                    // table has the finite variant property, and a call of
                    // it cannot be interrupted, so it runs only where the
                    // certifier proved that property. Kind-level products
                    // stay with the checked export below, and so does every
                    // query on a table the certifier did not accept.
                    if !crate::lean_unification::kind_level(query)
                        && finite_variants()
                        && let Outcome::Complete(family) = theory.fold_variants(sig, query)?
                    {
                        // The search lists the layers in Maude's order. The
                        // witnesses get Maude's numbering, and a family
                        // without AC or C operators Maude's exact order.
                        return rust(
                            Outcome::Complete(theory.maude_listing(sig, query, family)?),
                            "fold",
                        );
                    }
                    if trace {
                        eprintln!("[variants] solver checked_export");
                    }
                    theory
                        .checked_variants(sig, query)
                        .map(|outcome| (outcome, VariantRoute::CheckedExport))
                }
                // The join solver lists a family in the order of its own
                // search. Maude's listing is restored before the check.
                Outcome::Complete(family) => rust(
                    Outcome::Complete(theory.maude_listing(sig, query, family)?),
                    "joined",
                ),
            },
            complete => rust(complete, "rule_table"),
        }
    }

    /// Get one fresh substitution per variant. The native constructor path
    /// returns the identity as an empty substitution. Maude may spell it out
    /// with independent same-sort fresh variables. Each Maude answer has its
    /// own local witness scope.
    pub fn variants(
        &self,
        t: &LNTerm,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        let mut inner = cancellation::lock(&self.inner)?;
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::NativeOnly {
            use crate::lean_unification::Outcome;
            // Folding lists a family for any table. It is a proposal that
            // the checker has yet to accept.
            let reference = || {
                crate::lean_unification::variants_for_convergent_theory(&inner.sig, t).map(|rows| {
                    (
                        rows.map_or(Outcome::Unsupported, Outcome::Complete),
                        VariantRoute::GeneralExport,
                    )
                })
            };
            let (result, route) = if self.reference.variants {
                reference()
            } else {
                // A table the certifier accepted is canonical and has the
                // finite variant property.
                let finite_variants = || {
                    matches!(
                        self.reduction_table(&inner),
                        Ok(Some(table)) if table.certified()
                    )
                };
                self.bounded_variants(&inner.sig, t, finite_variants)
                    .and_then(|result| match result {
                        (Outcome::Unsupported, _) if inner.theory_fallback => reference(),
                        other => Ok(other),
                    })
            }
            .map_err(|error| native_runtime_error(&inner.caches, error))?;
            if route == VariantRoute::GeneralExport && tamarin_utils::env_gate!("TAM_DBG_VARIANTS")
            {
                eprintln!("[variants] solver general_export");
            }
            if let crate::lean_unification::Outcome::Complete(answers) = result {
                #[cfg(test)]
                let answers = {
                    let mut answers = answers;
                    if let Some(tamper) = self.reference.tamper_variants {
                        tamper(&mut answers);
                    }
                    answers
                };
                inner.caches.provenance.record_route(route);
                // The checked export carries its own theorem. Every other
                // family, the folding export's included, is used only as a
                // certificate that the checker accepted: a refusal returns
                // here, before the family.
                let (origin, cached) = match route {
                    VariantRoute::Proposer | VariantRoute::GeneralExport => {
                        self.checked_family(&inner, t, &answers)?
                    }
                    // The theorem needs no certificate. The label stays
                    // conservative all the same: proved only on a table the
                    // certifier accepted.
                    VariantRoute::CheckedExport => {
                        let certified = self
                            .reduction_table(&inner)?
                            .is_some_and(|table| table.certified());
                        let origin = if certified {
                            Origin::Proved
                        } else {
                            Origin::Assumed
                        };
                        (origin, false)
                    }
                };
                if cached {
                    inner
                        .caches
                        .provenance
                        .record_cached(Asked::Variants, origin);
                } else {
                    inner.caches.provenance.record(Asked::Variants, origin);
                }
                trace_variant_family(t, &answers);
                return Ok(answers);
            }
        }
        inner.require_maude("variant generation")?;
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(t, &mut ctx);
        let mut cmd = b"get variants in MSG : ".to_vec();
        pp_mterm_into(&mt, &mut cmd);
        cmd.extend_from_slice(b" .\n");
        // Raw-reply memo (see `SharedMaudeCaches::reply`): `get variants in MSG` replies are
        // command-local and deterministic, and each variant is back-converted
        // on its own `ctx` clone below, so a cached reply is consumed exactly
        // like a fresh one.  This is the biggest single lever on variant-heavy
        // theories (Joux re-issues the same expensive `get variants` twice —
        // once in the derivcheck phase, once at main close).
        let reply = inner.execute_memo(&cmd, Asked::Variants, |s| s.var_count += 1)?;
        drop(inner);
        let msubsts = maude_parse::parse_variants_reply_with_sig(&reply, &self.sig)?;
        let mut out = Vec::with_capacity(msubsts.len());
        // HS-faithful: each variant's back-conversion uses a fresh ctx
        // clone.  Mirrors HS `msubstToLSubstVFresh` (Maude/Types.hs)
        // where each call to `runBackConversion (...) bindings` runs
        // `evalBindT back bindings` with the same INITIAL bindings —
        // augmentations to the binding map are per-call.
        //
        // Without this, the shared `ctx.inverse` causes
        // `MaudeLit::FreshVar(N, sort)` to collide between variants —
        // variant 1's `#1:Msg` and variant 2's `%1:Msg` both parse to
        // `FreshVar(1, Msg)` (`maude_parse.rs::parse_term` collapses
        // # and %) and the second lookup returns the first's LVar.
        //
        // HS-faithful: variant back-conversion uses hint "x" unconditionally
        // (Maude/Types.hs), NOT the perform_split-motivated
        // name-preserve path used by `unify`/`match`.  The variants flow
        // into `composeVFresh`+`pracVariants` rendering; using "x" here
        // matches both HS's printed `~k = ~x.5` form AND HS's variant
        // ordering after the per-variant Ord sort (Ord LVar = idx <> sort
        // <> name puts `~x.N` AFTER same-idx `~na.N`/`~nb.N`).
        for ms in &msubsts {
            let mut variant_ctx = ctx.clone();
            out.push(msubst_to_lnsubst_unify(ms, &mut variant_ctx)?);
        }
        trace_variant_family(t, &out);
        Ok(out)
    }
}

/// `TAM_DBG_UNIFY=1` prints every unification request with its answers as
/// they are handed to the caller, for comparing the two backends.
fn trace_unifiers(eqs: &[Equal<LNTerm>], answers: &[Vec<(crate::lterm::LVar, LNTerm)>]) {
    if !tamarin_utils::env_gate!("TAM_DBG_UNIFY") {
        return;
    }
    let mut text = String::from("[unify] query");
    for eq in eqs {
        text.push_str(&format!(" {} =? {} ;", eq.lhs, eq.rhs));
    }
    text.push_str(&format!("\n[unify] answers {}\n", answers.len()));
    for answer in answers {
        text.push_str("[unify] answer");
        for (variable, image) in answer {
            text.push_str(&format!(" {variable} := {image} ;"));
        }
        text.push('\n');
    }
    eprint!("{text}");
}

/// `TAM_DBG_VARIANTS=1` prints every variant family as it is handed to the
/// caller, one member per line, for comparing the two backends.
fn trace_variant_family(query: &LNTerm, family: &[Vec<(crate::lterm::LVar, LNTerm)>]) {
    if !tamarin_utils::env_gate!("TAM_DBG_VARIANTS") {
        return;
    }
    let mut text = format!(
        "[variants] query {query}\n[variants] members {}\n",
        family.len()
    );
    for member in family {
        text.push_str("[variants] member");
        for (variable, image) in member {
            text.push_str(&format!(" {variable} := {image} ;"));
        }
        text.push('\n');
    }
    eprint!("{text}");
}

/// Convert residual witnesses into the caller's scope and compose with the
/// free substitution obtained by factoring the original equations.
fn compose_residual_arms(
    arms: Vec<Vec<(crate::lterm::LVar, LNTerm)>>,
    factored: &crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
) -> Vec<Vec<(crate::lterm::LVar, LNTerm)>> {
    arms.into_iter()
        .map(|arm| {
            let fresh = crate::subst_vfresh::LNSubstVFresh::from_list(arm).remove_renamings();
            crate::subst_vfresh::compose_vfresh(&fresh, factored).to_list()
        })
        .collect()
}

/// The solver's fresh supply.  HS `Reduction` is
/// `StateT System (FreshT (DisjT (Reader ProofContext)))` (Reduction.hs)
/// and `Control.Monad.Fresh` re-exports the FAST `FreshT`
/// (Control/Monad/Fresh.hs), so the name is ignored and both methods draw
/// from the one counter (Control/Monad/Fresh/Class.hs).
impl MonadFresh for &MaudeHandle {
    fn fresh_ident(&mut self, _name: &str) -> u64 {
        self.reserve_idxs(1)
    }

    fn fresh_idents(&mut self, k: u64) -> u64 {
        self.reserve_idxs(k)
    }
}

/// One-letter sort tag for synthesizing skolem constant names.
fn sort_tag(s: crate::lterm::LSort) -> &'static str {
    use crate::lterm::LSort;
    match s {
        LSort::Msg => "M",
        LSort::Pub => "P",
        LSort::Fresh => "F",
        LSort::Node => "N",
        LSort::Nat => "T",
    }
}

/// Build a conjunction-equation Maude command: `<prefix>lhs =? rhs /\ ... .\n`.
/// Each side is converted via `lterm_to_mterm_global` threading the shared
/// `ctx`, so one wire encoding serves the whole conjunction.
fn build_conj_eqs_cmd(prefix: &[u8], eqs: &[Equal<LNTerm>], ctx: &mut ConvCtx) -> Vec<u8> {
    let mut cmd = prefix.to_vec();
    for (i, eq) in eqs.iter().enumerate() {
        if i > 0 {
            cmd.extend_from_slice(b" /\\ ");
        }
        let lm = lterm_to_mterm_global(&eq.lhs, ctx);
        let rm = lterm_to_mterm_global(&eq.rhs, ctx);
        pp_mterm_into(&lm, &mut cmd);
        cmd.extend_from_slice(b" =? ");
        pp_mterm_into(&rm, &mut cmd);
    }
    cmd.extend_from_slice(b" .\n");
    cmd
}

/// Build a `match in MSG : <pats> <=? <subjs> .\n` command.  Pattern list on the
/// left (variables may bind), subject list on the right (variables stay rigid), as used
/// by both matchers (see `match_eqs`' doc-comment).  `pp_mterm_list_into` is the
/// shared list formatter.
fn pp_match_cmd(pats: &[MTerm], subjs: &[MTerm]) -> Vec<u8> {
    let mut cmd = b"match in MSG : ".to_vec();
    pp_mterm_list_into(pats, &mut cmd);
    cmd.extend_from_slice(b" <=? ");
    pp_mterm_list_into(subjs, &mut cmd);
    cmd.extend_from_slice(b" .\n");
    cmd
}

/// Build the forward (LVar→skolem `Name`) and reverse (`Name`→LVar) skolem maps
/// for `vars`, assigning synthetic constants in BTreeSet iteration order via
/// `skolem_name`, avoiding every original constant and previously allocated
/// identity. A reserved-looking string alone is not a disjoint namespace.
pub(crate) fn build_skolem_maps<'a>(
    vars: &std::collections::BTreeSet<crate::lterm::LVar>,
    terms: impl IntoIterator<Item = &'a LNTerm>,
) -> Result<
    (
        std::collections::BTreeMap<crate::lterm::LVar, crate::lterm::Name>,
        std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
    ),
    MaudeError,
> {
    fn constants(t: &LNTerm, out: &mut std::collections::BTreeSet<crate::lterm::Name>) {
        match t {
            crate::term::Term::Lit(crate::vterm::Lit::Con(name)) => {
                out.insert(*name);
            }
            crate::term::Term::App(_, args) => {
                for arg in args.iter() {
                    constants(arg, out);
                }
            }
            _ => {}
        }
    }
    let mut occupied = std::collections::BTreeSet::new();
    for term in terms {
        constants(term, &mut occupied);
    }
    let mut skolem_map = std::collections::BTreeMap::new();
    let mut reverse = std::collections::BTreeMap::new();
    let mut counter = 0_u64;
    for lv in vars {
        let n = loop {
            let n = skolem_name(counter, lv);
            counter = counter.checked_add(1).ok_or_else(|| {
                MaudeError::Other("rigid matching identity capacity exceeded".into())
            })?;
            if occupied.insert(n) {
                break n;
            }
        };
        skolem_map.insert(*lv, n);
        reverse.insert(n, *lv);
    }
    Ok((skolem_map, reverse))
}

/// Un-skolemize the range of each binding in `sub`, mapping synthetic
/// constants back to their original LVars via `reverse`.  Used by
/// `match_eqs_skolemize_both`'s result loop.
fn unskolemize_subst(
    sub: Vec<(crate::lterm::LVar, LNTerm)>,
    reverse: &std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
) -> Vec<(crate::lterm::LVar, LNTerm)> {
    sub.into_iter()
        .map(|(lv, lt)| (lv, unskolemize(&lt, reverse)))
        .collect()
}

/// Build the synthetic skolem-constant `Name` for a free/subject `LVar`
/// `lv`, using `counter` to keep the id unique across one match call.
///
/// The constant must round-trip through Maude with the SAME order-sorted
/// behaviour HS gives a `SkConst`, whose sort is `lvarSort v`
/// (`sortOfSkol`, Guarded.hs) — i.e. the variable's *own* sort, which may be
/// `Msg`.  Maude's `match A <=? B` requires the pattern's declared sort
/// to be a supersort of the subject's, so encoding a `Msg`-sorted
/// subject variable as `Pub` (a strict subsort of `Msg`) would let it
/// match a `Pub` pattern position that HS would reject — an over-match
/// that can change `--prove` results.
///
/// `NameTag` has no `Msg` variant, and adding one would break the many
/// exhaustive `match`es on it across other crates.  Instead we carry a
/// `Msg`-sorted skolem as a `NameTag::Pub` `Name` whose id begins with
/// `maude_types::SKOLEM_MSG_PREFIX`; `maude_types::sort_of_name`
/// recognises that sentinel and reports `LSort::Msg`, so the emitted
/// Maude constant is `c(i)` (op `c : Nat -> Msg`) rather than `p(i)`.
/// For every other sort the matching `NameTag` already yields the right
/// Maude sort directly.
fn skolem_name(counter: u64, lv: &crate::lterm::LVar) -> crate::lterm::Name {
    use crate::lterm::{LSort, Name, NameTag};
    // Every sort shares the `<prefix><counter>_<name>_<idx>_<sortTag>` id
    // layout, so distinct LVars stay distinct; only `Msg` swaps the prefix
    // for the sentinel `sort_of_name` decodes back to `LSortMsg`.
    let (tag, prefix) = match lv.sort {
        LSort::Msg => (NameTag::Pub, crate::maude_types::SKOLEM_MSG_PREFIX),
        LSort::Pub => (NameTag::Pub, "__sk"),
        LSort::Fresh => (NameTag::Fresh, "__sk"),
        LSort::Nat => (NameTag::Nat, "__sk"),
        LSort::Node => (NameTag::Node, "__sk"),
    };
    let id = format!(
        "{}{}_{}_{}_{}",
        prefix,
        counter,
        lv.name,
        lv.idx,
        sort_tag(lv.sort)
    );
    Name::new(tag, id)
}

/// Walk an `LNTerm` and replace any `Lit::Con(name)` whose `name` is in
/// `reverse` with the corresponding original `Lit::Var(lv)`.  Used to
/// un-skolemize match results from `match_eqs_skolemize_both`. Rebuild AC/C
/// applications canonically: replacing constants with variables changes ordering.
pub(crate) fn unskolemize(
    t: &LNTerm,
    reverse: &std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
) -> LNTerm {
    use crate::vterm::Lit;
    match t {
        crate::term::Term::Lit(Lit::Con(n)) => {
            if let Some(lv) = reverse.get(n) {
                crate::term::Term::Lit(Lit::Var(*lv))
            } else {
                t.clone()
            }
        }
        crate::term::Term::App(sym, args) => {
            let new_args: Vec<LNTerm> = args.iter().map(|a| unskolemize(a, reverse)).collect();
            crate::term::f_app(*sym, new_args)
        }
        _ => t.clone(),
    }
}

/// Collect every free `LVar` in `t` whose `(name, idx)` is NOT in
/// `pattern_vars`, appending into `out`.  `match_eqs_skolemize_both` calls
/// it once per side.
fn collect_free_non_pattern_vars(
    t: &LNTerm,
    pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    out: &mut std::collections::BTreeSet<crate::lterm::LVar>,
) {
    use crate::vterm::Lit;
    match t {
        crate::term::Term::Lit(Lit::Var(lv)) if !pattern_vars.contains(&(lv.name, lv.idx)) => {
            out.insert(*lv);
        }
        crate::term::Term::App(_, args) => {
            for a in args.iter() {
                collect_free_non_pattern_vars(a, pattern_vars, out);
            }
        }
        _ => {}
    }
}

/// Rewrite `t`, replacing each `LVar` bound in `map` with its synthetic
/// skolem `Con` constant (leaving all other subterms untouched).  Shared
/// by `match_eqs_skolemize_both`.
fn rewrite_skolem(
    t: &LNTerm,
    map: &std::collections::BTreeMap<crate::lterm::LVar, crate::lterm::Name>,
) -> LNTerm {
    use crate::vterm::Lit;
    match t {
        crate::term::Term::Lit(Lit::Var(lv)) => {
            if let Some(n) = map.get(lv) {
                crate::term::Term::Lit(Lit::Con(*n))
            } else {
                t.clone()
            }
        }
        crate::term::Term::App(sym, args) => {
            let new_args: Vec<LNTerm> = args.iter().map(|a| rewrite_skolem(a, map)).collect();
            crate::term::Term::App(*sym, new_args.into())
        }
        _ => t.clone(),
    }
}

/// Haskell constructs a map in `msubstToLSubstVFree`. Source refinement
/// traverses it in ascending variable order via `substToList`.
fn order_match_bindings(bindings: &mut [(crate::lterm::LVar, LNTerm)]) {
    bindings.sort_unstable_by_key(|(variable, _)| *variable);
}

/// Decode in wire order, then present the directional match in domain order.
fn msubst_to_lnsubst(
    ms: &MSubst,
    ctx: &mut ConvCtx,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    let mut bindings = msubst_to_lnsubst_with_avoid(ms, ctx, 0)?;
    order_match_bindings(&mut bindings);
    Ok(bindings)
}

/// Decode the witness-bearing variant substitution in wire order.
fn msubst_to_lnsubst_unify(
    ms: &MSubst,
    ctx: &mut ConvCtx,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    msubst_to_lnsubst_with_avoid(ms, ctx, 0)
}

// Whether one unification request of the Maude backend reached Maude or its
// reply memo, on the calling thread.
thread_local! {
    static UNIFY_TRACE: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    static LAST_UNIFY_ORIGIN: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}
const TRACE_MAUDE: u8 = 1;
const TRACE_MAUDE_CACHED: u8 = 2;

fn trace_unify(engine: u8) {
    UNIFY_TRACE.set(UNIFY_TRACE.get() | engine);
}

/// The origin recorded for the unification that just finished on this thread.
fn last_unify_origin() -> Origin {
    if LAST_UNIFY_ORIGIN.get() & (TRACE_MAUDE | TRACE_MAUDE_CACHED) != 0 {
        Origin::Maude
    } else {
        Origin::SharedRust
    }
}

/// A request without tuple wrappers is answered by the total-match export
/// alone. With wrappers, Rust first unpacks them through a separate kernel,
/// which counts as a composition.
#[cfg(feature = "lean-unification")]
fn match_origin(oriented: &[Equal<LNTerm>]) -> Origin {
    if crate::lean_unification::is_single_export(oriented) {
        Origin::Proved
    } else {
        Origin::NativeRust
    }
}

/// The unifiers of the proved export under the witness names the Maude
/// backend gives its own, or `None` when they are not the composition that
/// backend builds. See [`crate::unifier_presentation`].
#[cfg(feature = "lean-unification")]
fn spell_as_maude(
    sig: &MaudeSig,
    eqs: &[Equal<LNTerm>],
    answers: &[Vec<(crate::lterm::LVar, LNTerm)>],
) -> Option<crate::lean_unification::Substitutions> {
    // No unifier: nothing to spell.
    if answers.is_empty() {
        return Some(Vec::new());
    }
    let (factored, residual) = factor_unification(sig, eqs)?;
    crate::unifier_presentation::present(&factored, &residual, answers)
}

/// Number every native witness above the query, as Maude does. This is the
/// spelling of a family that [`spell_as_maude`] declines.
///
/// A unifier's range mentions query variables and fresh witnesses. Maude
/// numbers the witnesses above every variable it was sent, and callers such
/// as `apply_eq_store` keep unrelated system variables below that bound, so
/// a witness never shares a name with a variable outside the query. The
/// decoder of the proved export instead reuses the lowest index the query
/// leaves unused, which can coincide with such a system variable and
/// identify the two.
/// Each arm is shifted uniformly, so the relative order of its witnesses is
/// unchanged; arms that already satisfy the bound are left alone.
#[cfg(feature = "lean-unification")]
fn lift_witnesses_above_query(
    eqs: &[Equal<LNTerm>],
    answers: &mut [Vec<(crate::lterm::LVar, LNTerm)>],
) {
    use crate::lterm::HasFrees;
    let mut query: tamarin_utils::FastSet<crate::lterm::LVar> = Default::default();
    for eq in eqs {
        eq.lhs.for_each_free(&mut |v| {
            query.insert(*v);
        });
        eq.rhs.for_each_free(&mut |v| {
            query.insert(*v);
        });
    }
    let Some(highest) = query.iter().map(|v| v.idx).max() else {
        return;
    };
    for arm in answers {
        let mut lowest = None;
        let mut top = 0;
        for (_, image) in arm.iter() {
            image.for_each_free(&mut |v| {
                if !query.contains(v) {
                    lowest = Some(lowest.map_or(v.idx, |l: u64| l.min(v.idx)));
                    top = top.max(v.idx);
                }
            });
        }
        let Some(lowest) = lowest.filter(|l| *l <= highest) else {
            continue;
        };
        let shift = highest - lowest + 1;
        // A query that already uses the top of the index space leaves no room
        // above it. The solver's own names are still distinct from every
        // query variable, so such an arm is returned as it is.
        if top.checked_add(shift).is_none() {
            continue;
        }
        *arm = std::mem::take(arm)
            .into_iter()
            .map(|(key, image)| {
                let image = image.map_free(&mut |v| {
                    if query.contains(&v) {
                        v
                    } else {
                        crate::lterm::LVar {
                            idx: v.idx + shift,
                            ..v
                        }
                    }
                });
                (key, image)
            })
            .collect();
    }
}

/// Convert one Maude reply substitution to `[(LVar, LNTerm)]`, minting
/// witness idxs in a PURE per-call scope — the faithful port of HS's
/// `msubstToLSubstVFresh bindings` / `msubstToLSubstVFree bindings`, whose
/// `runBackConversion (...) bindings =
///  evalBindT (...) bindings `evalFreshAvoiding` M.elems bindings`
/// (Term/Maude/Types.hs) seeds the fresh supply at
/// `avoid (M.elems bindings)` and reads/writes NO global fresh state.
///
/// `avoid_max` is the caller's `avoid (M.elems bindings)` value (max idx
/// over the query's own binding vars); the witness supply starts at
/// `avoid_max + 1`.  There is deliberately no `MaudeHandle` here: witness
/// numbering must be counter-neutral so that a `unify`/`match` call leaves
/// the session `MonadFresh` state unchanged, exactly as HS's pure
/// `evalFreshAvoiding` scope does.
fn msubst_to_lnsubst_with_avoid(
    ms: &MSubst,
    ctx: &mut ConvCtx,
    avoid_max: u64,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    let mut out = Vec::with_capacity(ms.len());
    // HS `avoid (M.elems bindings) = maybe 0 (succ . snd) . boundsVarIdx`
    // (LTerm.hs): the local fresh supply starts just above the max
    // idx among the query's own binding vars.  `avoid_max` already carries
    // that max (the caller scans ALL of `ctx`'s Var bindings, not just
    // `x`-named ones), so `avoid_max + 1` is the HS seed; the extra scan
    // below is a defensive floor for any `x`-named binding.
    let mut next: u64 = {
        let mut n = avoid_max.saturating_add(1);
        for lit in ctx.bindings().values() {
            if let crate::vterm::Lit::Var(lv) = lit
                && lv.name == "x"
                && lv.idx >= n
            {
                n = lv.idx.saturating_add(1);
            }
        }
        n
    };
    // Fresh witness IDs follow their first occurrence during back-conversion.
    for ((sort, idx), mt) in ms {
        let lv = crate::maude_types::substitute_lookup_var(ctx, *sort, *idx).ok_or_else(|| {
            MaudeError::Other(format!("no binding for Maude variable x{}:{:?}", idx, sort))
        })?;
        // HS-faithful: HS's `msubstToLSubstVFresh` (Maude/Types.hs)
        // UNCONDITIONALLY uses `"x"` as the name hint for Maude-introduced
        // witnesses inside `eqsConj` substitutions.  The commented-out
        // alternative branch at Maude/Types.hs (preserve domain
        // name for `xi → xj` renames) is explicitly marked "seems wrong".
        let name_hint: &str = "x";
        let t = mterm_to_lnterm(mt, ctx, name_hint, &mut next);
        out.push((lv, t));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// MaudePool — a pool of independent Maude subprocesses.
//
// The single shared `MaudeHandle` serialises every query on an internal
// `Mutex<MaudeProcessInner>`.  Under rayon parallelism (rule-variant
// closure, saturate refinement) every worker contends on that mutex,
// capping speedup at the point where one Maude subprocess is fully busy
// (~4 workers in practice).  A pool of M independent Maudes lets each
// worker hold its own subprocess for the duration of its task, so
// workers run truly in parallel.
//
// HS uses a single Maude per ClosedTheory (Term/Maude/Process.hs); this
// pool is a Rust-specific implementation improvement — it doesn't
// change semantics, only removes a serialisation point.  Per-call
// fresh-counter scope (`with_fresh_counter_from`) already guarantees
// HS-faithful witness allocation regardless of which pool member
// handles a given task.
// ---------------------------------------------------------------------------

/// Mutable state of a `MaudePool`, guarded by a single `Mutex`.
struct PoolState {
    /// Idle members available for immediate `pop`.  Released handles are
    /// pushed back here and reused LIFO, concentrating queries onto the
    /// warm (already-spawned) members.
    free: Vec<MaudeHandle>,
    /// Number of members brought into existence so far (in `free` plus the
    /// ones currently borrowed).  Bounded by `size`; grown lazily by
    /// `acquire`/`try_acquire` when no idle member is available.
    spawned: usize,
}

/// Pool of up to `size` independent Maude subprocesses, all initialised
/// with the same `MaudeSig`.  Workers borrow a handle via `acquire()`; the
/// returned `PooledMaude` releases back to the pool on drop.
///
/// Members spawn LAZILY: `new` starts exactly one eagerly (so a failure to
/// launch Maude surfaces as an `Err` from `new`), and the rest are spawned
/// on demand the first time `acquire`/`try_acquire` finds no idle member
/// and the target `size` is not yet reached.  A theory that draws few
/// members never pays for the ones it doesn't use — Maude startup is
/// ~30ms/process (spawn + banner + settings + theory-module load).
///
/// Released handles are reused LIFO (see `PoolState::free`), so under light
/// contention the same warm member serves repeatedly and the lazy members
/// stay unspawned.  Pool members are interchangeable: identical `sig`, and
/// each draw site seeds its own fresh-counter (`with_fresh_counter_next` /
/// `with_fresh_counter_from`), so which member — and how many — handle a
/// task is output-invariant.
///
/// Internally a `Mutex<PoolState>` LIFO works fine — the pool is small
/// (≤ num_cpus) and `acquire` is rare on the hot path (it happens once per
/// parallel task, not per Maude call).
pub struct MaudePool {
    backend: AlgebraBackend,
    state: Mutex<PoolState>,
    notify: Condvar,
    /// Target member count — the ceiling on lazy growth.  Constant after
    /// construction; `size()` returns this, NOT the number spawned so far.
    size: usize,
    /// Maude binary path, retained for lazy spawns.
    path: String,
    /// Theory signature, retained for lazy spawns; cloned per spawn exactly
    /// as the eager first member was.
    sig: MaudeSig,
    /// The session's shared memo caches, retained for lazy spawns: every
    /// member — the eager first and each lazy one — consults the same
    /// `SharedMaudeCaches` the pool was constructed with.
    caches: Arc<SharedMaudeCaches>,
    /// Set once, the first time a lazy spawn fails, to de-duplicate the
    /// warning (see `warn_spawn_failed`).
    spawn_warned: AtomicBool,
}

impl std::fmt::Debug for MaudePool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaudePool(size={})", self.size)
    }
}

impl MaudePool {
    /// Construct a pool targeting `n` Maude subprocesses with `sig`, spawning
    /// exactly ONE eagerly.  Returns `Err` if that first process fails to
    /// start (the caller warns and falls back to the single shared Maude);
    /// the remaining `n - 1` members spawn on demand in `acquire` /
    /// `try_acquire`.  Every member consults `caches`; the session caller
    /// (run.rs) passes the same instance to its `file_maude` handle so the
    /// whole theory session shares one memo set (see `SharedMaudeCaches`).
    pub fn new(
        path: &str,
        sig: MaudeSig,
        n: usize,
        caches: Arc<SharedMaudeCaches>,
    ) -> Result<Self, MaudeError> {
        Self::new_with_backend(path, sig, n, caches, AlgebraBackend::default())
    }

    pub fn new_with_backend(
        path: &str,
        sig: MaudeSig,
        n: usize,
        caches: Arc<SharedMaudeCaches>,
        backend: AlgebraBackend,
    ) -> Result<Self, MaudeError> {
        assert!(n >= 1, "MaudePool::new requires n >= 1");
        let first = MaudeHandle::start_with_backend_and_caches(
            path,
            sig.clone(),
            backend,
            Arc::clone(&caches),
        )?;
        Ok(MaudePool {
            backend,
            state: Mutex::new(PoolState {
                free: vec![first],
                spawned: 1,
            }),
            notify: Condvar::new(),
            size: n,
            path: path.to_string(),
            sig,
            caches,
            spawn_warned: AtomicBool::new(false),
        })
    }

    /// Warn (once per pool) that a lazy member failed to start.  The pool
    /// keeps serving the members already spawned (≥ 1 always exists), so
    /// this is a soft degradation, not a fatal error.
    fn warn_spawn_failed(&self, e: &MaudeError) {
        if !self.spawn_warned.swap(true, Ordering::Relaxed) {
            eprintln!(
                "[warn] MaudePool: lazy Maude spawn failed ({}); \
                continuing with the members already started",
                e
            );
        }
    }

    /// Block until a handle is available, then return it.  Pops an idle
    /// member if one is free; otherwise spawns a new member on demand (up to
    /// `size`) OUTSIDE the lock and hands it back directly — it is
    /// immediately borrowed and never enters `free`.  If a lazy spawn fails,
    /// the reserved slot is released and the caller falls back to waiting
    /// for a release; at least one live member always exists, so that wait
    /// terminates.  The handle is returned to the pool when the
    /// `PooledMaude` is dropped.
    pub fn acquire(&self) -> PooledMaude<'_> {
        // Cleared on a spawn failure: this call then stops attempting lazy
        // spawns and relies on releases, so a persistently failing spawn
        // can't spin the loop hot.
        let mut try_spawn = true;
        let mut state = self.state.lock().unwrap();
        loop {
            let idle = state.free.pop();
            if let Some(h) = idle {
                return PooledMaude {
                    pool: self,
                    inner: Some(h),
                };
            }
            if try_spawn && state.spawned < self.size {
                // Reserve the slot under the lock, then spawn without it so
                // other acquirers aren't blocked for the ~30ms startup.
                state.spawned += 1;
                drop(state);
                match MaudeHandle::start_with_backend_and_caches(
                    &self.path,
                    self.sig.clone(),
                    self.backend,
                    Arc::clone(&self.caches),
                ) {
                    Ok(h) => {
                        return PooledMaude {
                            pool: self,
                            inner: Some(h),
                        };
                    }
                    Err(e) => {
                        try_spawn = false;
                        state = self.state.lock().unwrap();
                        state.spawned -= 1;
                        self.warn_spawn_failed(&e);
                        // A member may have been released while the lock was
                        // dropped for the spawn attempt — its notify_one had
                        // no waiter and was lost.  Re-check `free` under this
                        // relock before waiting, or the release is missed and
                        // this acquire could sleep forever.
                        continue;
                    }
                }
            }
            // Pool at target size (or spawning disabled) and nothing idle:
            // wait for a release.  Atomic with the lock, so no release can
            // slip between the `free` check above and this wait.
            state = self.notify.wait(state).unwrap();
        }
    }

    /// Non-blocking acquire: pop an idle member, else spawn a new one on
    /// demand (up to `size`), else return `None`.  Used by the within-lemma
    /// fan-out so that nested (lemma-level B1 + within-lemma) parallelism
    /// can't deadlock waiting on a pool that the outer lemma tasks have
    /// fully drained: this NEVER waits on the condvar.  It may block ~30ms
    /// while a lazy member spawns — acceptable, as it still cannot wait on a
    /// drained pool.
    pub fn try_acquire(&self) -> Option<PooledMaude<'_>> {
        let mut state = self.state.lock().unwrap();
        if let Some(h) = state.free.pop() {
            return Some(PooledMaude {
                pool: self,
                inner: Some(h),
            });
        }
        if state.spawned < self.size {
            state.spawned += 1;
            drop(state);
            match MaudeHandle::start_with_backend_and_caches(
                &self.path,
                self.sig.clone(),
                self.backend,
                Arc::clone(&self.caches),
            ) {
                Ok(h) => {
                    return Some(PooledMaude {
                        pool: self,
                        inner: Some(h),
                    });
                }
                Err(e) => {
                    let mut relock = self.state.lock().unwrap();
                    relock.spawned -= 1;
                    self.warn_spawn_failed(&e);
                    return None;
                }
            }
        }
        None
    }

    /// Target subprocess count this pool was constructed with — the ceiling
    /// on lazy growth, NOT the number spawned so far (see `spawned`).
    pub fn size(&self) -> usize {
        self.size
    }

    /// Number of backend members created so far (≤ `size`), not subprocesses
    /// in native-only mode. Grows lazily
    /// as `acquire`/`try_acquire` demand members beyond the eager first one.
    pub fn spawned(&self) -> usize {
        self.state.lock().unwrap().spawned
    }
}

/// A borrowed Maude handle from a `MaudePool`.  `Deref`s to
/// `MaudeHandle`; releases back to the pool on `Drop`.
#[must_use = "dropping this guard immediately ends the scope it protects"]
pub struct PooledMaude<'a> {
    pool: &'a MaudePool,
    inner: Option<MaudeHandle>,
}

impl<'a> PooledMaude<'a> {
    /// Borrow the underlying `MaudeHandle` for the lifetime of this guard.
    /// Does NOT consume the guard or transfer ownership: the returned
    /// reference is valid only while the `PooledMaude` lives, and the
    /// handle is released back to the pool in `PooledMaude::drop`.  This
    /// is the same accessor as the `Deref` impl; callers that need an
    /// owned handle (e.g. to clone into a per-task `ProofContext`) should
    /// `.clone()` the returned `&MaudeHandle`.
    pub fn handle(&self) -> &MaudeHandle {
        self.inner
            .as_ref()
            .expect("PooledMaude inner not yet taken")
    }
}

impl<'a> std::ops::Deref for PooledMaude<'a> {
    type Target = MaudeHandle;
    fn deref(&self) -> &MaudeHandle {
        self.inner
            .as_ref()
            .expect("PooledMaude inner not yet taken")
    }
}

impl<'a> Drop for PooledMaude<'a> {
    fn drop(&mut self) {
        if let Some(h) = self.inner.take() {
            let mut state = self.pool.state.lock().unwrap();
            // LIFO reuse: the most recently released (warmest) member is the
            // next one popped, keeping queries concentrated on warm members.
            state.free.push(h);
            // Only one waiter can take the handle we just pushed.
            self.pool.notify.notify_one();
        }
    }
}

#[cfg(test)]
#[path = "maude_proc_tests.rs"]
mod tests;

#[cfg(all(test, feature = "lean-unification"))]
#[path = "lean_unification_integration_tests.rs"]
mod lean_integration_tests;

#[cfg(all(test, feature = "lean-unification"))]
#[path = "lean_ac_feasibility_tests.rs"]
mod ac_feasibility_tests;
