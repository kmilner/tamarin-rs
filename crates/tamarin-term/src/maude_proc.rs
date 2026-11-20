// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Maude.Process` — an algebra session with optional Maude transport.
//!
//! Spawns `maude -interactive -no-tecla -no-banner -no-wrap -batch`,
//! feeds it a `fmod MSG ... endfm` module describing the term algebra,
//! and exposes `unify`, `match`, `variants`, and `reduce` operations.
//! Experimental native-only sessions create no process and fail explicitly
//! when an operation exceeds the supported in-process fragment.
//!
//! The protocol is line-oriented: every command ends with `.\n` and
//! Maude's response ends with the prompt `Maude> `.

use std::io::{Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use crate::algebra_backend::AlgebraBackend;
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
            MaudeError::NativeFailure(reason) => write!(f, "native-only backend failed: {reason}"),
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

/// Match the source declarations printed by `pp_theory`, rather than derived
/// signature caches that a caller may not have refreshed. The native adapter
/// checks term shape/sorts separately; undeclared inputs retain Maude's error
/// behavior instead of being silently accepted by a more permissive algebra.
#[cfg(feature = "lean-unification")]
fn lean_signature_supports(sig: &MaudeSig, equations: &[Equal<LNTerm>]) -> bool {
    use crate::function_symbols::{AcSym, FunSym};
    use crate::lterm::{LSort, NameTag};
    use crate::term::Term;
    use crate::vterm::Lit;

    equations.iter().all(|eq| {
        [&eq.lhs, &eq.rhs].into_iter().all(|term| {
            let Term::App(FunSym::Ac(symbol), children) = term else {
                return false;
            };
            let declared = match symbol {
                AcSym::Mult => sig.enable_dh,
                AcSym::Union => sig.enable_mset,
                AcSym::Xor => sig.enable_xor,
                AcSym::NatPlus => sig.enable_nat,
                AcSym::AcFct(symbol) => sig.st_ac_fun_syms.contains(symbol),
            };
            declared
                && children.iter().all(|child| match child {
                    Term::Lit(Lit::Con(name)) => sig.enable_nat || name.tag != NameTag::Nat,
                    Term::Lit(Lit::Var(var)) => sig.enable_nat || var.sort != LSort::Nat,
                    _ => false,
                })
        })
    })
}

/// Decompose equal declared free heads positionally. Keep AC siblings together.
/// A top-level variable-to-literal equation supplies a forced binding when
/// its domain is independent of the remaining patterns. Source matching
/// includes a node-to-node equation of this kind alongside the fact equations.
#[cfg(feature = "lean-unification")]
fn free_match_children(
    sig: &MaudeSig,
    equations: &[Equal<LNTerm>],
    bindings: &mut std::collections::BTreeMap<crate::lterm::LVar, LNTerm>,
) -> Option<Vec<Equal<LNTerm>>> {
    use crate::lterm::{sort_compare, sort_of_lterm, HasFrees, LSort};
    use crate::{function_symbols::FunSym, lterm::NameTag, term::Term, vterm::Lit};
    let mut pending = Vec::with_capacity(equations.len());
    for eq in equations.iter().rev() {
        if let (Term::Lit(Lit::Var(v)), Term::Lit(_)) = (&eq.lhs, &eq.rhs) {
            let sort = sort_of_lterm(&eq.rhs, crate::maude_types::sort_of_name);
            if (!sig.enable_nat && (v.sort == LSort::Nat || sort == LSort::Nat))
                || !sort_compare(sort, v.sort).is_some_and(|ord| ord.is_le())
                || eq.lhs == eq.rhs
            {
                return None;
            }
            if bindings
                .insert(*v, eq.rhs.clone())
                .is_some_and(|old| old != eq.rhs)
            {
                return None;
            }
        } else {
            pending.push((&eq.lhs, &eq.rhs));
        }
    }
    let mut children = Vec::new();
    while let Some((pattern, subject)) = pending.pop() {
        match (pattern, subject) {
            (Term::App(FunSym::NoEq(f), p), Term::App(FunSym::NoEq(g), s))
                if f == g
                    && sig.st_fun_syms.contains(f)
                    && p.len() == f.arity
                    && s.len() == f.arity =>
            {
                pending.extend(p.iter().zip(s.iter()).rev());
            }
            (Term::Lit(Lit::Con(a)), Term::Lit(Lit::Con(b)))
                if a == b
                    && a.tag != NameTag::Node
                    && (sig.enable_nat || a.tag != NameTag::Nat) => {}
            (Term::App(FunSym::Ac(_), _), Term::App(FunSym::Ac(_), _)) => {
                children.push(Equal {
                    lhs: pattern.clone(),
                    rhs: subject.clone(),
                });
            }
            _ => return None,
        }
    }
    if !bindings.is_empty()
        && children.iter().any(|eq| {
            let mut shared = false;
            eq.lhs
                .for_each_free(&mut |v| shared |= bindings.contains_key(v));
            shared
        })
    {
        return None;
    }
    // All free declarations take Msg arguments. The admitted AC result sorts
    // (Msg and Nat) widen to Msg, as do all admitted literal siblings.
    Some(children)
}

/// Statistics on Maude operations performed via this handle.
#[derive(Debug, Default, Clone, Copy)]
pub struct MaudeStats {
    pub unify_count: u64,
    /// Unification or unifiability batches completed by the in-process Lean backend.
    pub lean_unify_count: u64,
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
    /// Native-only consumers must check this before publishing any result.
    native_failure: std::sync::OnceLock<NativeFailure>,
    /// Completed ground and identity answers keyed by full terms. Native
    /// answers carrying a branch-local witness bypass this cache. Factored
    /// free substitutions are composed afresh by the caller after every hit.
    #[cfg(feature = "lean-unification")]
    lean_unify: Mutex<
        tamarin_utils::FastMap<Vec<(LNTerm, LNTerm)>, Vec<Vec<(crate::lterm::LVar, LNTerm)>>>,
    >,
    /// Memo for `reduce(...)` queries.  Maude `reduce` is a pure
    /// function of the input term modulo the (fixed-per-session) theory
    /// signature, so successful reductions can be cached across calls.
    /// `has_non_normal_terms` (contradictions.rs) calls `reduce` on
    /// every candidate subterm of every node, and `is_finished` runs
    /// every search step — so the same subterm gets reduced repeatedly
    /// during a single proof.  Caching cuts those repeat round-trips.
    reduce: Mutex<tamarin_utils::FastMap<LNTerm, LNTerm>>,
    /// Memo for `unifiable(...)` queries — see `MaudeHandle::unifiable`.
    /// Caches the *boolean* outcome (true = at least one unifier
    /// exists).  Witness LVars produced inside the subst aren't safe
    /// to cache across calls (their indices need fresh-renaming each
    /// time) so we don't memoize substitutions, only the existence
    /// answer.
    unifiable: Mutex<tamarin_utils::FastMap<Vec<(LNTerm, LNTerm)>, bool>>,
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

#[derive(Debug)]
enum NativeFailure {
    Unsupported(&'static str),
    #[cfg(feature = "lean-unification")]
    Runtime(String),
}

impl NativeFailure {
    fn error(&self) -> MaudeError {
        match self {
            Self::Unsupported(operation) => MaudeError::UnsupportedOperation(operation),
            #[cfg(feature = "lean-unification")]
            Self::Runtime(reason) => MaudeError::NativeFailure(reason.clone()),
        }
    }
}

struct MaudeProcessInner {
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
    fn require_maude(&self, operation: &'static str) -> Result<(), MaudeError> {
        if self.backend == AlgebraBackend::NativeOnly {
            let first = self
                .caches
                .native_failure
                .get_or_init(|| NativeFailure::Unsupported(operation));
            return Err(first.error());
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
        bump: impl FnOnce(&mut MaudeStats),
    ) -> Result<Vec<u8>, MaudeError> {
        self.require_maude("Maude execution")?;
        let hit = self.caches.reply.lock().unwrap().get(cmd).cloned();
        if let Some(cached) = hit {
            self.cache_stats.reply_hits += 1;
            return Ok(cached);
        }
        let reply = self.execute(cmd)?;
        bump(&mut self.stats);
        self.cache_stats.reply_misses += 1;
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
                "[MAUDE_CACHE_STATS] reduce={}/{} unifiable={}/{} reply={}/{} lean_unify={}",
                s.reduce_hits,
                s.reduce_misses,
                s.unifiable_hits,
                s.unifiable_misses,
                s.reply_hits,
                s.reply_misses,
                self.stats.lean_unify_count,
            );
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
    pub fn observed_application_variants(
        &self,
        application: &LNTerm,
    ) -> Result<Option<Vec<ApplicationVariant>>, MaudeError> {
        self.check_backend_status()?;
        cancellation::check()?;
        #[cfg(feature = "lean-unification")]
        if self.backend != AlgebraBackend::Maude
            && let Some(table) = self.native_rules()
        {
            return table
                .observed_application_variants(application)
                .map_err(|e| {
                    if self.backend == AlgebraBackend::NativeOnly {
                        self.inner
                            .lock()
                            .caches
                            .native_failure
                            .get_or_init(|| NativeFailure::Runtime(e.to_string()))
                            .error()
                    } else {
                        MaudeError::Other(e.to_string())
                    }
                });
        }
        let _ = application;
        Ok(None)
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

    /// Start a backend session. Native-only creates no subprocess or pipes.
    /// All handles sharing caches must use the same signature and backend.
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
            caches,
        };
        if backend.uses_maude() {
            inner.with_cancellation(MaudeProcessInner::initialize)?;
        }
        Ok(MaudeHandle {
            backend,
            inner: Arc::new(parking_lot::Mutex::new(inner)),
            child: reaper,
            // The global fresh counter starts at 0 (HS-faithful: HS's
            // `MonadFresh` global counter starts at 0).
            fresh_counter: Arc::new(AtomicU64::new(0)),
            sig,
            #[cfg(feature = "lean-unification")]
            native_rules: Default::default(),
        })
    }

    pub fn backend(&self) -> AlgebraBackend {
        self.backend
    }

    /// Must succeed before a native-only consumer publishes a result, even
    /// if a legacy helper recovered from an unsupported-operation error.
    pub fn check_backend_status(&self) -> Result<(), MaudeError> {
        if self.backend == AlgebraBackend::NativeOnly
            && let Some(operation) = self.inner.lock().caches.native_failure.get()
        {
            return Err(operation.error());
        }
        Ok(())
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
            inner: self.inner.clone(),
            child: self.child.clone(),
            fresh_counter: Arc::new(AtomicU64::new(avoid_max.saturating_add(1))),
            sig: Arc::clone(&self.sig),
            #[cfg(feature = "lean-unification")]
            native_rules: Arc::clone(&self.native_rules),
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
            inner: self.inner.clone(),
            child: self.child.clone(),
            fresh_counter: Arc::new(AtomicU64::new(next)),
            sig: Arc::clone(&self.sig),
            #[cfg(feature = "lean-unification")]
            native_rules: Arc::clone(&self.native_rules),
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
        let mut ctx = ConvCtx::new();
        let reply = {
            let mut inner = cancellation::lock(&self.inner)?;
            let hit = inner.caches.reduce.lock().unwrap().get(t).cloned();
            if let Some(cached) = hit {
                inner.cache_stats.reduce_hits += 1;
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
                return Ok(t.clone());
            }
            #[cfg(feature = "lean-unification")]
            if self.backend != AlgebraBackend::Maude {
                let result = crate::lean_unification::pairing_reduce(&inner.sig, t)
                    .and_then(|result| {
                        if result.is_none()
                            && let Some(theory) = self.native_rules()
                        {
                            if self.backend == AlgebraBackend::NativeOnly {
                                match theory.reduce_native(t)? {
                                    Some(value) => Ok(Some(value)),
                                    None => theory.checked_reduction(&inner.sig, t),
                                }
                            } else {
                                theory.reduce(t)
                            }
                        } else {
                            Ok(result)
                        }
                    })
                    .map_err(|error| {
                        if self.backend == AlgebraBackend::NativeOnly {
                            inner
                                .caches
                                .native_failure
                                .get_or_init(|| NativeFailure::Runtime(error.to_string()))
                                .error()
                        } else {
                            MaudeError::Other(error.to_string())
                        }
                    })?;
                if let Some(result) = result {
                    return Ok(result);
                }
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
            .insert(t.clone(), result.clone());
        Ok(result)
    }

    /// Whether *any* unifier of `eqs` exists modulo the signature's AC/C
    /// attributes. Ordinary `unify` ignores the signature's rewrite equations.
    ///
    /// Memoised via `SharedMaudeCaches::unifiable`, so a repeat query skips
    /// the subprocess round-trip.  Safe to cache because the result is a
    /// context-free boolean (no witness LVars leak across calls).
    ///
    /// Fast path: when `is_ac_free()` accepts the signature (no AC/C
    /// operators and no `st_rules`) we answer unifiability with the local
    /// Robinson-style algorithm in `unification.rs`, completely
    /// skipping Maude.  Hashing / asymmetric-encryption / pair-only
    /// protocols hit this fast path almost exclusively, cutting the
    /// per-step Maude call count by orders of magnitude.
    pub fn unifiable(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        self.check_backend_status()?;
        if eqs.is_empty() {
            return Ok(true);
        }
        if eqs.iter().all(|eq| eq.lhs == eq.rhs) {
            return Ok(true);
        }
        #[cfg(feature = "lean-unification")]
        let needs_typed_solver = self.backend != AlgebraBackend::Maude
            && eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]).any(|t| {
                crate::lean_unification::requires_typed_unification(t, self.sig.enable_nat)
            });
        #[cfg(not(feature = "lean-unification"))]
        let needs_typed_solver = false;
        if self.is_ac_free() && !needs_typed_solver {
            return Ok(crate::unification::unify_lnterm_no_ac(eqs.to_vec()).is_ok());
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
            if let Some(hit) = hit {
                inner.cache_stats.unifiable_hits += 1;
                return Ok(hit);
            }
        }
        #[cfg(feature = "lean-unification")]
        let answer = if !needs_typed_solver
            && self.backend != AlgebraBackend::Maude
            && !tamarin_utils::env_gate!("TAM_RS_NO_LEAN_UNIFY")
            && crate::lean_unification::RuleTable::may_be_homogeneous(eqs)
            && let Some(table) = self.native_rules()
            && let Some(answer) = table.graph_feasible(eqs).map_err(|e| self.lean_error(e))?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            answer
        } else {
            !self.unify_for(eqs, false)?.is_empty()
        };
        #[cfg(not(feature = "lean-unification"))]
        let answer = !self.unify_for(eqs, false)?.is_empty();
        #[cfg(feature = "lean-unification")]
        if self.backend == AlgebraBackend::Hybrid
            && tamarin_utils::env_gate!("TAM_RS_VERIFY_LEAN_UNIFY")
            && answer == self.unify_via_maude(eqs)?.is_empty()
        {
            return Err(MaudeError::Other(format!(
                "Lean/Maude unifiability disagreement for {eqs:?}"
            )));
        }
        let mut inner = cancellation::lock(&self.inner)?;
        inner.cache_stats.unifiable_misses += 1;
        inner.caches.unifiable.lock().unwrap().insert(key, answer);
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
        self.unify_for(eqs, true)
    }

    /// A boolean unifiability query observes only whether a complete result
    /// contains an arm. It can consume native families in any order.
    fn unify_for(
        &self,
        eqs: &[Equal<LNTerm>],
        ordered: bool,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        #[cfg(feature = "lean-unification")]
        let use_lean = self.backend != AlgebraBackend::Maude
            && !tamarin_utils::env_gate!("TAM_RS_NO_LEAN_UNIFY");
        #[cfg(not(feature = "lean-unification"))]
        let use_lean = false;
        self.unify_backend(eqs, use_lean, ordered)
    }

    /// Run the existing Maude path for differential tests and benchmarks.
    /// This keeps the same factoring, caches and witness conversion as `unify`.
    #[cfg(feature = "lean-unification")]
    pub fn unify_via_maude(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.inner
            .lock()
            .require_maude("Maude unification oracle")?;
        self.unify_backend(eqs, false, true)
    }

    #[cfg(feature = "lean-unification")]
    fn lean_error(&self, error: crate::lean_unification::Error) -> MaudeError {
        if error == crate::lean_unification::Error::Cancelled {
            MaudeError::Cancelled
        } else if self.backend == AlgebraBackend::NativeOnly {
            self.inner
                .lock()
                .caches
                .native_failure
                .get_or_init(|| NativeFailure::Runtime(error.to_string()))
                .error()
        } else {
            MaudeError::Other(error.to_string())
        }
    }

    fn unify_backend(
        &self,
        eqs: &[Equal<LNTerm>],
        use_lean: bool,
        ordered: bool,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        #[cfg(not(feature = "lean-unification"))]
        let _ = (use_lean, ordered);
        #[cfg(feature = "lean-unification")]
        let lean_error = |error| self.lean_error(error);
        #[cfg(feature = "lean-unification")]
        let deferred_graph = if use_lean && self.backend == AlgebraBackend::NativeOnly {
            cancellation::check()?;
            let result = self
                .native_rules()
                .map(|table| table.try_whole_unify(eqs))
                .transpose()
                .map_err(lean_error)?;
            match result {
                Some((crate::lean_unification::Outcome::Complete(answers), _)) => {
                    cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                    return Ok(answers);
                }
                Some((_, pending)) if ordered => pending,
                _ => None,
            }
        } else {
            None
        };
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        #[cfg(feature = "lean-unification")]
        if use_lean
            && (self.backend == AlgebraBackend::NativeOnly || !ordered)
            && eqs.iter().flat_map(|e| [&e.lhs, &e.rhs]).any(|t| {
                crate::lean_unification::requires_typed_unification(t, self.sig.enable_nat)
            })
        {
            cancellation::check()?;
            if self.sig.enable_nat
                && let Some(table) = self.native_rules()
                && let crate::lean_unification::Outcome::Complete(arms) =
                    table.unify_kind_sum(eqs).map_err(lean_error)?
            {
                cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                return Ok(arms);
            }
            if let Some(arms) = self.total_unify(eqs)? {
                return Ok(arms);
            }
            return self.unify_residuals_with_maude(eqs, &crate::subst::Subst::empty());
        }
        if self.sig.enable_nat
            && eqs
                .iter()
                .any(|e| contains_kind_sum(&e.lhs) || contains_kind_sum(&e.rhs))
        {
            return self.unify_residuals_with_maude(eqs, &crate::subst::Subst::empty());
        }
        // HS unifyRaw delays AC- and C-headed pairs even when the two sides
        // are syntactically equal. The empty substitution is mathematically
        // complete for a reflexive equation. Maude can spell out that same
        // identity using explicit fresh renamings for its input variables.
        // Keep the existing hybrid dispatch except for the checked fragment
        // of reflexive AC equations with rigid literals and strictly subsorted variables.
        // In native-only mode, cancellation and C orientation dominance may
        // also remove reflexive equations in a larger conjunction.
        //
        // Remaining queries use the local non-AC unifier first, mirroring
        // HS's `unifyLTermFactored` (Unification.hs):
        //
        // ```haskell
        // unifyLTermFactored sortOf eqs = reader $ \h ->
        //     solve h $ execRWST unif sortOf M.empty
        //   where
        //     unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
        //     solve _ (Just (m, [])) = (substFromMap m, [emptySubstVFresh])
        // ```
        //
        //   1. Run `unifyRaw` locally (no Maude).
        //   2. Success with no AC residual → return `[emptyVFresh
        //      `composeVFresh` m]`, which is what `flattenUnif (m,
        //      [emptySubstVFresh])` (Unification.hs) evaluates to.
        //   3. Success with AC residuals → dispatch to the selected backend.
        //      The total native fallback takes the original conjunction.
        //   4. Failure → return empty, WITHOUT calling Maude.
        //
        // Step 2's `composeVFresh` is load-bearing, not a formality: it
        // extends the empty VFresh with renamings for `varsRange m`, so a
        // `K → Var(V)` binding becomes the two entries
        // `[K → Var(~Vw), V → Var(~Vw)]` Maude's own unify would produce.
        // Skipping it leaves V in the range but not the domain, and
        // `apply_eq_store`'s lifting then collides its witness with K's
        // renamed target (a SubstVFresh same-target collision, observed as
        // $R=$I on KAS_key_secrecy).
        //
        // This local-first path applies even when `is_ac_free()` is false:
        // it follows HS's factoring and substitution-composition behavior
        // for every signature. The presence of [variant] equations does
        // not change ordinary `unify` semantics; Maude ignores those equations.
        {
            // The Maude wire reserves a Pub-tagged spelling for Msg-sorted
            // skolem constants. Use its true sort for every elimination.
            let result = crate::unification::unify_lterm_no_ac(
                &crate::maude_types::sort_of_name,
                eqs.to_vec(),
            );
            match result {
                Ok(subst) => {
                    // HS-faithful flattenUnif: success, return [vfresh ∘ subst].
                    let empty_vfresh =
                        crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
                    let folded = crate::subst_vfresh::compose_vfresh(&empty_vfresh, &subst);
                    return Ok(vec![folded.to_list()]);
                }
                Err(crate::unification::UnifyError::NoUnifier) => {
                    // HS-faithful: unifyRaw failed. Return empty without
                    // an unnecessary Maude call.
                    return Ok(Vec::new());
                }
                Err(crate::unification::UnifyError::NeedsAC) => {
                    // Fall through to the Maude call below.
                    //
                    // HS-faithful counter-neutrality: the global fresh
                    // counter is NOT raised here.  HS's `unifyViaMaude`
                    // (Term/Maude/Process.hs) numbers each reply's
                    // witnesses in a PURE per-call scope via
                    // `runBackConversion (...) bindings =
                    //  evalBindT (...) bindings `evalFreshAvoiding` M.elems bindings`
                    // (Term/Maude/Types.hs) — the fresh supply is
                    // seeded from `avoid (M.elems bindings)` (the query's own
                    // exported vars) and NO global state is read or written.
                    // The reply conversion below therefore computes its
                    // witness base locally (see `input_max`) and never
                    // touches `self`'s counter.
                }
            }
        }
        // HS-faithful `unifyLTermFactored` (Unification.hs):
        //
        //   unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
        //   solve h (Just (m, leqs)) =
        //       (subst, unifyViaMaude h sortOf $ map (applyVTerm subst <$>) leqs)
        //     where subst = substFromMap m
        //
        // i.e. run the LOCAL non-AC unifier first to extract a non-AC
        // substitution `m` and the residual AC equations `leqs`, then send
        // ONLY the residuals (with `m` applied) to Maude.  Finally
        // `flattenUnif (subst, substs) = map (`composeVFresh` subst) substs`
        // (Unification.hs) composes each Maude arm with `subst = m`.
        //
        // We therefore factor out the non-AC substitution `m` and send only
        // the AC residuals to Maude, so witness idxs are allocated against
        // the residual's vars (matching HS); `m`'s bindings are composed
        // back in below.
        let (factored_m, residual_eqs): (
            crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
            Vec<Equal<LNTerm>>,
        ) = match crate::unification::unify_lterm_factored(
            &crate::maude_types::sort_of_name,
            eqs.to_vec(),
        ) {
            Some((m, leqs)) => (m, leqs),
            // unifyRaw failed during factoring → no unifier (HS `solve _
            // Nothing = (emptySubst, [])` → flattenUnif maps over []).
            None => return Ok(Vec::new()),
        };
        // If factoring already solved everything (no AC residual), HS returns
        // `(substFromMap m, [emptySubstVFresh])`; flattenUnif then yields
        // `[emptyVFresh `composeVFresh` m]`.  Mirror that without a Maude
        // round-trip.
        if residual_eqs.is_empty() {
            let empty_vfresh = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
            let composed = crate::subst_vfresh::compose_vfresh(&empty_vfresh, &factored_m);
            return Ok(vec![composed.to_list()]);
        }
        // The feature is experimental and the Lean kernel explicitly reports
        // unsupported fragments. Only a completed result can replace Maude;
        // a runtime failure remains an error, never a contradiction.
        #[cfg(feature = "lean-unification")]
        let mut lean_expected = if use_lean && lean_signature_supports(&self.sig, &residual_eqs) {
            cancellation::check()?;
            // Shared-witness packets must be decoded in the original query
            // and factoring context. Only the ground/identity path below
            // caches reified substitutions.
            if self.backend == AlgebraBackend::NativeOnly
                && let crate::lean_unification::Outcome::Complete(answers) =
                    crate::lean_unification::unify_with_witnesses(&residual_eqs, eqs, &factored_m)
                        .map_err(lean_error)?
            {
                cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                return Ok(answers);
            }
            let key: Vec<_> = residual_eqs
                .iter()
                .map(|eq| (eq.lhs.clone(), eq.rhs.clone()))
                .collect();
            let cached = {
                let inner = cancellation::lock(&self.inner)?;
                inner.caches.lean_unify.lock().unwrap().get(&key).cloned()
            };
            let outcome = if let Some(arms) = cached {
                crate::lean_unification::Outcome::Complete(arms)
            } else {
                let outcome = crate::lean_unification::unify(&residual_eqs)
                    .and_then(|outcome| {
                        if self.backend == AlgebraBackend::NativeOnly
                            && outcome == crate::lean_unification::Outcome::Unsupported
                        {
                            crate::lean_unification::unify_by_cancellation(&residual_eqs)
                        } else {
                            Ok(outcome)
                        }
                    })
                    .map_err(lean_error)?;
                if let crate::lean_unification::Outcome::Complete(arms) = &outcome {
                    cancellation::lock(&self.inner)?
                        .caches
                        .lean_unify
                        .lock()
                        .unwrap()
                        .insert(key, arms.clone());
                }
                outcome
            };
            match outcome {
                crate::lean_unification::Outcome::Unsupported => None,
                crate::lean_unification::Outcome::Complete(arms) => {
                    // Arms either have ground ranges or are the empty identity
                    // from reflexivity or cancellation. Neither introduces
                    // nonground witness ranges at the SubstVFresh boundary.
                    let result: Vec<_> = arms
                        .into_iter()
                        .map(|arm| {
                            let vfresh = crate::subst_vfresh::LNSubstVFresh::from_list(arm);
                            crate::subst_vfresh::compose_vfresh(&vfresh, &factored_m).to_list()
                        })
                        .collect();
                    cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                    if !tamarin_utils::env_gate!("TAM_RS_VERIFY_LEAN_UNIFY") {
                        return Ok(result);
                    }
                    Some(result)
                }
            }
        } else {
            None
        };
        #[cfg(feature = "lean-unification")]
        let try_structured = use_lean
            && (self.backend == AlgebraBackend::NativeOnly || !ordered)
            && self
                .native_rules()
                .is_some_and(|table| table.admits_terms(eqs));
        #[cfg(feature = "lean-unification")]
        if try_structured
            && let crate::lean_unification::Outcome::Complete(answers) =
                crate::lean_unification::unify_structured(&residual_eqs, eqs, &factored_m)
                    .map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(answers);
        }
        #[cfg(feature = "lean-unification")]
        // Free factoring can expose a simultaneous AC matrix under other constructors.
        // Validate the proposed bindings and residual against the original conjunction
        // before accepting this path, including a complete empty answer set.
        if try_structured
            && residual_eqs != eqs
            && let Some(table) = self.native_rules()
            && let crate::lean_unification::Outcome::Complete(arms) = table
                .factored_unify(eqs, &factored_m, &residual_eqs)
                .map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(compose_checked_factor(eqs, arms, &factored_m));
        }
        #[cfg(feature = "lean-unification")]
        if try_structured
            && self.backend == AlgebraBackend::NativeOnly
            && let Some(table) = self.native_rules()
            && let crate::lean_unification::Outcome::Complete(answers) =
                table.unify_forced_operands(eqs).map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(answers);
        }
        #[cfg(feature = "lean-unification")]
        if try_structured
            && let Some(table) = self.native_rules()
            && let crate::lean_unification::Outcome::Complete(answers) =
                table.unify_operands(eqs).map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(answers);
        }
        #[cfg(feature = "lean-unification")]
        if try_structured
            && let Some(table) = self.native_rules()
            && table.refutes_ac_conjunct(eqs).map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(Vec::new());
        }
        #[cfg(feature = "lean-unification")]
        if try_structured
            && self.backend == AlgebraBackend::NativeOnly
            && let Some(table) = self.native_rules()
            && let crate::lean_unification::Outcome::Complete(answers) =
                table.component_unify(eqs).map_err(lean_error)?
        {
            cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
            return Ok(answers);
        }
        // A certified contradiction has the same empty family in every order.
        // Boolean callers already tried the decision kernel on homogeneous input.
        #[cfg(feature = "lean-unification")]
        if use_lean && lean_expected.is_none() {
            let verdict = if let Some(packet) = deferred_graph {
                packet.graph_feasible().map_err(lean_error)?
            } else if self.backend == AlgebraBackend::Hybrid
                && (ordered || !crate::lean_unification::RuleTable::may_be_homogeneous(eqs))
                && let Some(table) = self.native_rules()
            {
                table.graph_feasible(eqs).map_err(lean_error)?
            } else {
                None
            };
            if verdict == Some(false) {
                cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                if ordered
                    && self.backend == AlgebraBackend::Hybrid
                    && tamarin_utils::env_gate!("TAM_RS_VERIFY_LEAN_UNIFY")
                {
                    lean_expected = Some(Vec::new());
                } else {
                    return Ok(Vec::new());
                }
            }
        }
        #[cfg(feature = "lean-unification")]
        if use_lean
            && (self.backend == AlgebraBackend::NativeOnly || !ordered)
            && lean_expected.is_none()
            && let Some(answers) = self.total_unify(eqs)?
        {
            return Ok(answers);
        }
        let renamed = self.unify_residuals_with_maude(&residual_eqs, &factored_m)?;
        #[cfg(feature = "lean-unification")]
        if let Some(expected) = lean_expected
            && expected != renamed
        {
            return Err(MaudeError::Other(format!(
                "Lean/Maude unifier disagreement: equations {residual_eqs:?}, \
                 Lean {expected:?}, Maude {renamed:?}"
            )));
        }
        Ok(renamed)
    }

    #[cfg(feature = "lean-unification")]
    fn total_unify(
        &self,
        original: &[Equal<LNTerm>],
    ) -> Result<Option<crate::lean_unification::Substitutions>, MaudeError> {
        match crate::lean_unification::total_unify(&self.sig, original)
            .map_err(|e| self.lean_error(e))?
        {
            crate::lean_unification::Outcome::Complete(answers) => {
                cancellation::lock(&self.inner)?.stats.lean_unify_count += 1;
                Ok(Some(answers))
            }
            crate::lean_unification::Outcome::Unsupported => Ok(None),
        }
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
        let reply = inner.execute_memo(&cmd, |s| s.unify_count += 1)?;
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
    fn allow_total_match(&self, ordered: bool) -> bool {
        (self.backend == AlgebraBackend::NativeOnly
            || (self.backend == AlgebraBackend::Hybrid && !ordered))
            && !tamarin_utils::env_gate!("TAM_RS_NO_LEAN_UNIFY")
    }

    #[cfg(feature = "lean-unification")]
    fn needs_typed_matching(&self, eqs: &[Equal<LNTerm>]) -> bool {
        eqs.iter()
            .flat_map(|e| [&e.lhs, &e.rhs])
            .any(|t| crate::lean_unification::requires_typed_unification(t, self.sig.enable_nat))
    }

    #[cfg(feature = "lean-unification")]
    fn total_match(
        &self,
        oriented: &[Equal<LNTerm>],
        bindable: impl Fn(&crate::lterm::LVar) -> bool,
    ) -> Result<Option<crate::lean_unification::Substitutions>, MaudeError> {
        match crate::lean_unification::total_match(&self.sig, oriented, bindable)
            .map_err(|e| self.lean_error(e))?
        {
            crate::lean_unification::Outcome::Complete(answers) => Ok(Some(answers)),
            crate::lean_unification::Outcome::Unsupported => Ok(None),
        }
    }

    /// Match a sorted conjunction in-process. Callers supply explicit
    /// (pattern, subject) orientation; the two public matching APIs differ.
    #[cfg(feature = "lean-unification")]
    fn native_match(
        &self,
        equations: &[Equal<LNTerm>],
        ordered: bool,
    ) -> Result<Option<Vec<Vec<(crate::lterm::LVar, LNTerm)>>>, MaudeError> {
        use crate::function_symbols::FunSym;
        use crate::term::Term;

        if self.backend == AlgebraBackend::Maude || tamarin_utils::env_gate!("TAM_RS_NO_LEAN_UNIFY")
        {
            return Ok(None);
        }
        cancellation::check()?;

        let match_error = |error: crate::lean_unification::Error| {
            if error == crate::lean_unification::Error::Cancelled {
                MaudeError::Cancelled
            } else if self.backend == AlgebraBackend::NativeOnly {
                self.inner
                    .lock()
                    .caches
                    .native_failure
                    .get_or_init(|| NativeFailure::Runtime(error.to_string()))
                    .error()
            } else {
                MaudeError::Other(error.to_string())
            }
        };
        let native_table = (self.backend == AlgebraBackend::NativeOnly)
            .then(|| self.native_rules())
            .flatten();
        let ground_subjects = native_table.is_some()
            && equations
                .iter()
                .all(|e| crate::vterm::is_ground_vterm(&e.rhs));
        let completed = |result| match result {
            crate::lean_unification::Outcome::Complete(mut answers) => {
                for answer in &mut answers {
                    order_match_bindings(answer);
                }
                Some(answers)
            }
            crate::lean_unification::Outcome::Unsupported => None,
        };
        if let Some(table) = native_table {
            let result = if ground_subjects {
                table.match_ground_captures(equations)
            } else {
                table.match_rigid_subjects(equations)
            }
            .map_err(match_error)?;
            if let Some(answers) = completed(result) {
                return Ok(Some(answers));
            }
            // Both enumeration APIs sort the complete NativeOnly family in
            // caller space. Boolean matching has its own cheaper bag kernel.
            if ordered
                && let Some(answers) =
                    completed(table.ac_bag_answers(equations).map_err(match_error)?)
            {
                return Ok(Some(answers));
            }
            if ordered
                && let Some(answers) =
                    completed(table.component_match(equations).map_err(match_error)?)
            {
                return Ok(Some(answers));
            }
        }
        // Keep compound AC leaves after decomposing declared free constructors.
        let children;
        let mut fixed = std::collections::BTreeMap::new();
        let leaves = if equations.iter().all(|eq| {
            matches!(
                (&eq.lhs, &eq.rhs),
                (Term::App(FunSym::Ac(_), _), Term::App(FunSym::Ac(_), _))
            )
        }) {
            equations
        } else {
            let Some(decomposed) = free_match_children(&self.sig, equations, &mut fixed) else {
                // A ground subject can also be matched by the rigid-subject
                // tree search. Restart from the original conjunction; free
                // decomposition can have accumulated partial bindings.
                if let Some(table) = native_table
                    && ground_subjects
                    && !equations
                        .iter()
                        .any(|e| matches!(e.lhs, Term::Lit(crate::vterm::Lit::Var(_))))
                {
                    return Ok(completed(
                        table.match_rigid_subjects(equations).map_err(match_error)?,
                    ));
                }
                return Ok(None);
            };
            children = decomposed;
            &children
        };
        let literal = lean_signature_supports(&self.sig, leaves);
        let result = if literal {
            crate::lean_unification::match_ground(leaves)
        } else if self
            .native_rules()
            .is_some_and(|table| table.admits_terms(equations))
        {
            crate::lean_unification::match_compound_ground(leaves)
        } else {
            return Ok(None);
        }
        .map_err(match_error)?;
        Ok(match result {
            crate::lean_unification::Outcome::Unsupported => None,
            // These searches enumerate a set of alternatives. An ordered
            // hybrid caller can observe Maude's first answer to the full query.
            crate::lean_unification::Outcome::Complete(answers)
                if self.backend == AlgebraBackend::Hybrid
                    && ordered
                    && answers.len() > 1
                    && (!literal
                        || !fixed.is_empty()
                        || leaves
                            .iter()
                            .any(crate::lean_unification::uses_sorted_partition)
                        || leaves
                            .iter()
                            .any(crate::lean_unification::needs_wider_partition)) =>
            {
                None
            }
            crate::lean_unification::Outcome::Complete(mut answers) => {
                if !ordered {
                    // Only has_match_eqs requests an unordered result.
                    answers.truncate(1);
                }
                for answer in &mut answers {
                    answer.extend(fixed.iter().map(|(v, image)| (*v, image.clone())));
                    if ordered {
                        order_match_bindings(answer);
                    }
                }
                Some(answers)
            }
        })
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
        let mut answers = self.match_eqs_impl(eqs, true)?;
        self.order_native_alternatives(&mut answers);
        Ok(answers)
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
        if self.backend == AlgebraBackend::NativeOnly
            && !tamarin_utils::env_gate!("TAM_RS_NO_LEAN_UNIFY")
        {
            let may_be_bags = crate::lean_unification::RuleTable::may_be_ac_bag_match(eqs);
            self.check_backend_status()?;
            if !self.needs_typed_matching(eqs)
                && (may_be_bags || (2..=64).contains(&eqs.len()))
                && let Some(table) = self.native_rules()
            {
                if may_be_bags
                    && let Some(found) = table
                        .ac_bag_has_match(eqs)
                        .map_err(|e| self.lean_error(e))?
                {
                    return Ok(found);
                }
                if let Some(found) = table
                    .component_has_match(eqs)
                    .map_err(|e| self.lean_error(e))?
                {
                    return Ok(found);
                }
            }
        }
        self.match_eqs_impl(eqs, false)
            .map(|answers| !answers.is_empty())
    }

    #[cfg(feature = "lean-unification")]
    fn match_size_excluded(&self, oriented: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        if self.backend == AlgebraBackend::NativeOnly
            && let Some(table) = self.native_rules()
        {
            return table
                .refutes_match_size(oriented)
                .map_err(|e| self.lean_error(e));
        }
        Ok(false)
    }

    // With no bindable variables, matching reduces to equality modulo C and AC.
    // Smart constructors already produce the canonical representation. A library
    // caller can also supply valid raw trees with unsorted or nested AC children.
    fn rigid_match_equal(
        &self,
        eqs: &[Equal<LNTerm>],
        operation: &'static str,
    ) -> Result<Option<bool>, MaudeError> {
        fn canonical(t: &LNTerm) -> Option<bool> {
            use crate::{function_symbols::FunSym, term::Term};
            let Term::App(f, args) = t else {
                return Some(true);
            };
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
                sorted &= canonical(arg)?;
            }
            Some(sorted)
        }

        let mut raw = false;
        for term in eqs.iter().flat_map(|eq| [&eq.lhs, &eq.rhs]) {
            let Some(already_sorted) = canonical(term) else {
                // The wire encoder itself rebuilds through smart constructors.
                // Empty or singleton AC nodes have no valid application to send.
                self.inner.lock().require_maude(operation)?;
                return Err(MaudeError::Other(
                    "invalid operator arity in matching query".into(),
                ));
            };
            raw |= !already_sorted;
        }
        if !raw {
            return Ok(Some(eqs.iter().all(|eq| eq.lhs == eq.rhs)));
        }
        #[cfg(feature = "lean-unification")]
        if self.backend != AlgebraBackend::Maude
            && self
                .native_rules()
                .is_some_and(|table| table.admits_terms(eqs))
        {
            let normalize = |t: &LNTerm| crate::term::map_lits(t, &mut |lit| *lit);
            return Ok(Some(eqs.iter().all(|eq| {
                eq.lhs == eq.rhs || normalize(&eq.lhs) == normalize(&eq.rhs)
            })));
        }
        Ok(None)
    }

    fn match_eqs_impl(
        &self,
        eqs: &[Equal<LNTerm>],
        _ordered: bool,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        self.check_backend_status()?;
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        let rigid = eqs.iter().all(|eq| crate::vterm::is_ground_vterm(&eq.rhs));
        if rigid && let Some(matched) = self.rigid_match_equal(eqs, "matching")? {
            return Ok(if matched { vec![Vec::new()] } else { vec![] });
        }
        #[cfg(feature = "lean-unification")]
        if !rigid || self.allow_total_match(_ordered) {
            let oriented: Vec<_> = eqs
                .iter()
                .map(|eq| Equal {
                    lhs: eq.rhs.clone(),
                    rhs: eq.lhs.clone(),
                })
                .collect();
            if !rigid
                && !self.needs_typed_matching(eqs)
                && let Some(answers) = self.native_match(&oriented, _ordered)?
            {
                return Ok(answers);
            }
            if !rigid && self.match_size_excluded(&oriented)? {
                return Ok(Vec::new());
            }
            if self.allow_total_match(_ordered)
                && let Some(answers) = self.total_match(&oriented, |_| true)?
            {
                return Ok(answers);
            }
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
        let reply = inner.execute_memo(&cmd, |s| s.match_count += 1)?;
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
        if eqs.is_empty() {
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
            return Ok(if matched { vec![Vec::new()] } else { vec![] });
        }
        // The reference accepts a scope directly, including at kind-level
        // positions that the sorted fast paths cannot admit.
        #[cfg(feature = "lean-unification")]
        if self.allow_total_match(true) && (rigid || self.needs_typed_matching(eqs)) {
            if let Some(mut answers) =
                self.total_match(eqs, |v| pattern_vars.contains(&(v.name, v.idx)))?
            {
                self.order_native_alternatives(&mut answers);
                return Ok(answers);
            }
            // Ordered total matching is enabled only in native-only mode.
            self.inner.lock().require_maude("rigid-context matching")?;
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

        #[cfg(feature = "lean-unification")]
        if !rigid
            && !self.needs_typed_matching(eqs)
            && let Some(answers) = self.native_match(&rewritten_eqs, true)?
        {
            let mut answers = answers
                .into_iter()
                .map(|answer| unskolemize_subst(answer, &reverse))
                .collect();
            self.order_native_alternatives(&mut answers);
            return Ok(answers);
        }

        // Use the original shared DAG. Skolemization can rebuild repeated
        // subterms; the unscoped size bound also refutes every scoped matcher.
        #[cfg(feature = "lean-unification")]
        if !rigid && self.match_size_excluded(eqs)? {
            return Ok(Vec::new());
        }

        #[cfg(feature = "lean-unification")]
        if self.allow_total_match(true)
            && let Some(mut answers) =
                self.total_match(eqs, |v| pattern_vars.contains(&(v.name, v.idx)))?
        {
            self.order_native_alternatives(&mut answers);
            return Ok(answers);
        }

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
        let reply = inner.execute_memo(&cmd, |s| s.match_count += 1)?;
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
        if self.backend != AlgebraBackend::Maude {
            let result = crate::lean_unification::pairing_variants(&inner.sig, t)
                .and_then(|result| {
                    if result == crate::lean_unification::Outcome::Unsupported
                        && let Some(theory) = self.native_rules()
                    {
                        if self.backend == AlgebraBackend::NativeOnly
                            && let complete @ crate::lean_unification::Outcome::Complete(_) =
                                theory.fresh_xor_variants(t)?
                        {
                            return Ok(complete);
                        }
                        let result = theory.variants(t)?;
                        if self.backend == AlgebraBackend::NativeOnly
                            && result == crate::lean_unification::Outcome::Unsupported
                        {
                            match theory.joined_variants(t)? {
                                crate::lean_unification::Outcome::Unsupported => {
                                    theory.checked_variants(&inner.sig, t)
                                }
                                complete => Ok(complete),
                            }
                        } else {
                            Ok(result)
                        }
                    } else {
                        Ok(result)
                    }
                })
                .map_err(|error| {
                    if self.backend == AlgebraBackend::NativeOnly {
                        inner
                            .caches
                            .native_failure
                            .get_or_init(|| NativeFailure::Runtime(error.to_string()))
                            .error()
                    } else {
                        MaudeError::Other(error.to_string())
                    }
                })?;
            if let crate::lean_unification::Outcome::Complete(answers) = result {
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
        let reply = inner.execute_memo(&cmd, |s| s.var_count += 1)?;
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
        Ok(out)
    }
}

/// Encode the ordinary composition on the original variables as a fresh-range
/// answer. A variable surviving only in a factor image needs its own row so
/// opening the range later preserves its sharing with that image.
#[cfg(feature = "lean-unification")]
pub(crate) fn compose_checked_factor(
    original: &[Equal<LNTerm>],
    arms: crate::lean_unification::Substitutions,
    factor: &crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
) -> crate::lean_unification::Substitutions {
    use crate::lterm::HasFrees;
    use crate::term::Term;
    use crate::vterm::Lit;

    if arms.is_empty() {
        return arms;
    }
    let mut observed = Vec::new();
    for equation in original {
        equation.lhs.for_each_free(&mut |v| observed.push(*v));
        equation.rhs.for_each_free(&mut |v| observed.push(*v));
    }
    observed.sort_unstable();
    observed.dedup();
    arms.into_iter()
        .map(|arm| {
            let composed = crate::subst::Subst::from_list(arm).compose(factor);
            observed
                .iter()
                .map(|&v| {
                    let image = composed
                        .image_of(&v)
                        .cloned()
                        .unwrap_or(Term::Lit(Lit::Var(v)));
                    (v, image)
                })
                .collect()
        })
        .collect()
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
