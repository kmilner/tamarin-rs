// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Term.Maude.Process` — a subprocess driver for Maude.
//!
//! Spawns `maude -interactive -no-tecla -no-banner -no-wrap -batch`,
//! feeds it a `fmod MSG ... endfm` module describing the term algebra,
//! and exposes `unify`, `match`, `variants`, and `reduce` operations.
//!
//! The protocol is line-oriented: every command ends with `.\n` and
//! Maude's response ends with the prompt `Maude> `.

use std::io::{Read, Write};
use std::ops::Deref;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use crate::lterm::LNTerm;
use crate::maude_parse;
use crate::maude_print::{pp_mterm_into, pp_mterm_list_into, pp_theory};
use crate::maude_sig::MaudeSig;
use crate::maude_types::{lterm_to_mterm_global, mterm_to_lnterm, ConvCtx, MSubst, MTerm};
use crate::rewriting::Equal;
use tamarin_utils::cancellation;
use tamarin_utils::fresh::MonadFresh;

const PROMPT: &[u8] = b"Maude> ";

/// Errors that can arise from the Maude bridge.
#[derive(Debug)]
pub enum MaudeError {
    Cancelled,
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

/// True if `t` contains any function symbol whose head matches one in
/// `reducible`.  Used as a fast-path predicate for `reduce`: if the
/// term contains no reducible symbols at all, `reduce` is the
/// identity, and we can skip the Maude IPC round-trip.
fn term_has_reducible_sym(t: &LNTerm, reducible: &crate::function_symbols::FunSig) -> bool {
    t.any_fun_sym(|f| reducible.contains(f))
}

/// True if `t` contains no Ac- or C-headed application.  The native matcher
/// never needs Maude for such a pattern, so the `reduce` NF fast path is
/// complete when every st-rule LHS passes this.
pub(crate) fn term_ac_c_free(t: &LNTerm) -> bool {
    use crate::function_symbols::FunSym;
    t.all_fun_syms(|f| !matches!(f, FunSym::Ac(_) | FunSym::C(_)))
}

/// Statistics on Maude operations performed via this handle.
#[derive(Debug, Default, Clone, Copy)]
pub struct MaudeStats {
    pub unify_count: u64,
    pub match_count: u64,
    pub norm_count: u64,
    pub var_count: u64,
}

/// The memo caches for one theory session, shared by the session's
/// `file_maude` handle and every `MaudePool` member.
///
/// Each cache relies on "identical command bytes give an identical reply".
/// That holds across members because every member loads the same immutable
/// module and registers variable sorts and names in the same order
/// (`initialize`, `ensure_variable_names`); Maude's name interning is
/// history-dependent, so the module alone would not suffice.
///
/// Each mutex is held for one `get` or `insert` only, never across a Maude
/// round-trip.  Concurrent misses both compute and insert the same value.
#[derive(Default)]
pub struct SharedMaudeCaches {
    /// `reduce` results.
    reduce: Mutex<tamarin_utils::FastMap<LNTerm, LNTerm>>,
    /// `unifiable` answers.  Only the boolean is cached: unifiers carry
    /// witnesses that each call numbers itself.
    unifiable: Mutex<tamarin_utils::FastMap<Vec<(LNTerm, LNTerm)>, bool>>,
    /// Raw reply bytes of `unify`, `get variants` and `match`, keyed by the
    /// exact command bytes.  The back-conversion still runs on every hit, so a
    /// hit is consumed exactly like a fresh reply.  Freed with the session.
    reply: Mutex<tamarin_utils::FastMap<Vec<u8>, Vec<u8>>>,
}

struct MaudeProcessInner {
    maude_path: String,
    child: Arc<Mutex<MaudeChildReaper>>,
    turn: Arc<Turn>,
    initialized: bool,
    /// All x0 .. x{ordered_variables - 1} have been read in a consistent
    /// order. This belongs to the subprocess, not the shared reply cache.
    ordered_variables: u64,
    stdin: ChildStdin,
    stdout: ChildStdout,
    stats: MaudeStats,
    /// The theory signature — immutable after `start()`.  Shared (`Arc`) with
    /// the owning `MaudeHandle` so reads via `MaudeHandle::maude_sig()` are a
    /// refcount bump rather than a deep clone taken under this IPC mutex.
    sig: Arc<MaudeSig>,
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
    fn with_cancellation<T>(
        &mut self,
        work: impl FnOnce(&mut Self) -> Result<T, MaudeError>,
    ) -> Result<T, MaudeError> {
        cancellation::check()?;
        let child = self.child.clone();
        let _registration = cancellation::current().map(|token| {
            token.on_cancel(move || {
                child.lock().unwrap().invalidate();
            })
        });
        // The timed I/O mutex does not poison on panic. Fail closed if an
        // exchange unwinds, so its unread reply can never reach another job.
        let result = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| work(self))) {
            Ok(result) => result,
            Err(panic) => {
                self.initialized = false;
                self.child.lock().unwrap().invalidate();
                std::panic::resume_unwind(panic);
            }
        };
        // Any interrupted or failed exchange invalidates this connection.
        // Keep complete memo entries, but discard its pipes before reuse.
        if result.is_err() {
            self.initialized = false;
            self.child.lock().unwrap().invalidate();
        }
        cancellation::check()?;
        result
    }

    fn initialize(&mut self) -> Result<(), MaudeError> {
        {
            let mut reaper = self.child.lock().unwrap();
            cancellation::check()?;
            if reaper.child.is_none() {
                // An interrupted job gives the process up before a new one
                // is started. The interrupter kills the process under this
                // lock after marking the exchange, so a start that gets
                // past this check is killed in its turn.
                if self.turn.interrupted.load(Ordering::Acquire) {
                    return Err(MaudeError::Other("Maude was interrupted".into()));
                }
                if !reaper.restart {
                    return Err(MaudeError::Other("Maude exited unexpectedly".into()));
                }
                let (stdin, stdout, child) = spawn_maude(&self.maude_path)?;
                self.stdin = stdin;
                self.stdout = stdout;
                reaper.child = Some(child);
                reaper.restart = false;
                self.initialized = false;
            }
        }
        if !self.initialized {
            self.ordered_variables = 0;
            let started = std::time::Instant::now();
            self.read_until_prompt()?;
            for cmd in [
                "set show command off .\n",
                "set show timing off .\n",
                "set show stats off .\n",
            ] {
                self.execute_raw(cmd.as_bytes())?;
            }
            self.execute_raw(pp_theory(&self.sig).as_bytes())?;
            // VariableSymbol's order also depends on when the sort is first
            // used. Register every wire sort, plus the kind used for internal
            // unification variables, before queries can choose that order.
            // Reuse one name: this initializes the theory's finite sort set,
            // not an arbitrary bound on the number of input variables.
            let sorts = ["Msg", "Fresh", "Pub", "Node", "TOP", "[TOP]"];
            let mut cmd = String::from("parse in MSG : ");
            for sort in sorts
                .into_iter()
                .chain(self.sig.enable_nat.then_some("TamNat"))
            {
                cmd.push_str("cons(x0:");
                cmd.push_str(sort);
                cmd.push(',');
            }
            cmd.push_str("nil");
            cmd.extend(std::iter::repeat_n(
                ')',
                sorts.len() + usize::from(self.sig.enable_nat),
            ));
            cmd.push_str(" .\n");
            let reply = self.execute_raw(cmd.as_bytes())?;
            check_name_registration(&reply)?;
            self.ordered_variables = 1;
            #[cfg(test)]
            {
                let preamble = self.turn.preamble.lock().unwrap().clone();
                if !preamble.is_empty() {
                    self.execute_raw(&preamble)?;
                }
            }
            self.initialized = true;
            self.turn
                .startup_micros
                .store(started.elapsed().as_micros() as u64, Ordering::Relaxed);
        }
        Ok(())
    }

    /// Complete an optional worker's admission while it owns the transport.
    fn prepare_worker(&mut self) -> Result<(), MaudeError> {
        let running = self.child.lock().unwrap().is_running();
        let replace = match running {
            Ok(running) => !running,
            // Some kernels cannot observe exit without reaping. A real
            // round trip checks the existing connection under the startup
            // cancellation scope. initialize() checks an uninitialized one.
            Err(_) if self.initialized => self.execute_raw(b"set show timing off .\n").is_err(),
            Err(_) => false,
        };
        if replace {
            self.child.lock().unwrap().invalidate();
        }
        self.initialize()
    }

    fn execute(&mut self, cmd: &[u8], variable_bound: u64) -> Result<Vec<u8>, MaudeError> {
        self.with_cancellation(|inner| {
            inner.initialize()?;
            inner.ensure_variable_names(variable_bound)?;
            inner.execute_raw(cmd)
        })
    }

    /// Maude compares variable names by their process-local intern ids. The
    /// identical theory establishes the same initial order in every worker;
    /// introduce all remaining input names in increasing numeric order before
    /// a query can introduce them in term traversal order. Grow geometrically
    /// so there are only O(log N) extra exchanges over a process's lifetime,
    /// with no fixed bound on the size of a query.
    ///
    /// Maude's own #/% names are separate families: unification's intermediate
    /// fresh variables have kind sorts, and completed substitutions / variants
    /// rename their variables into one fresh family. The generators used by
    /// these commands allocate each family from index zero in increasing order.
    /// Equation variable names are already interned by module loading, before
    /// any fresh names. Positions relative to subsequently introduced input
    /// names need not be fixed; the order within each family does.
    fn ensure_variable_names(&mut self, required: u64) -> Result<(), MaudeError> {
        if required <= self.ordered_variables {
            return Ok(());
        }
        let end = required.checked_next_power_of_two().unwrap_or(required);
        let cmd = name_order_command(self.ordered_variables, end);
        let reply = self.execute_raw(cmd.as_bytes())?;
        check_name_registration(&reply)?;
        self.ordered_variables = end;
        Ok(())
    }

    fn write_line(&mut self, line: &[u8]) -> Result<(), MaudeError> {
        self.stdin.write_all(line)?;
        self.stdin.flush()?;
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
            let n = self.stdout.read(&mut tmp)?;
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
}

/// The least time an exchange may keep a job that a sequential run would
/// visit earlier waiting before that job interrupts it.
const INTERRUPT_FLOOR: std::time::Duration = std::time::Duration::from_millis(250);
/// An interrupt costs a new process. Only pay that for an exchange that has
/// already run this many times as long as a process takes to start.
const INTERRUPT_STARTUPS: u32 = 4;
/// The longest an interrupted job stays away before it tries again, unless
/// an exchange may run for longer than this before it is interrupted.
const BACKOFF_CEILING: std::time::Duration = std::time::Duration::from_secs(4);

/// The exchange in flight on a process, visible to jobs waiting for it.
///
/// Jobs of one parallel map share a process when they have none of their
/// own. Some of them are speculative: a sequential run might never reach
/// them. A speculative exchange must not hold up a job that run would reach
/// first, so such a job may kill the process under it. The interrupted job
/// gives the process up, stays away for a while, and then repeats its
/// command on a new process.
#[derive(Default)]
struct Turn {
    state: parking_lot::Mutex<TurnState>,
    changed: parking_lot::Condvar,
    /// The waiter the process is held for after an interruption, or 0.
    /// Only that waiter may lock the process.
    reserved: AtomicU64,
    /// How long the last process took to start and load the theory.
    startup_micros: AtomicU64,
    /// Interrupted jobs staying away, and how often the process was locked
    /// or unlocked while any of them was.
    away: AtomicU64,
    uses: AtomicU64,
    /// Whether the exchange in flight has been interrupted. Readable
    /// without `state`, by a job that holds the lock on the child.
    interrupted: std::sync::atomic::AtomicBool,
    /// Commands a test has every new process run after loading the theory.
    #[cfg(test)]
    preamble: Mutex<Vec<u8>>,
}

#[derive(Default)]
struct TurnState {
    exchange: Option<Exchange>,
    waiters: u64,
}

struct Exchange {
    rank: Option<tamarin_utils::parallel::Rank>,
    since: std::time::Instant,
    interrupted: bool,
}

/// Marks an exchange as in flight until it is finished or dropped.
struct InFlight<'a>(&'a Turn);

impl InFlight<'_> {
    /// End the exchange and report whether a waiter interrupted it.
    fn finish(self) -> bool {
        let exchange = self.0.end();
        std::mem::forget(self);
        exchange.is_some_and(|exchange| exchange.interrupted)
    }
}

impl Drop for InFlight<'_> {
    fn drop(&mut self) {
        self.0.end();
    }
}

impl Turn {
    fn begin(&self) -> InFlight<'_> {
        let rank = tamarin_utils::parallel::Rank::current();
        self.state.lock().exchange = Some(Exchange {
            rank,
            since: std::time::Instant::now(),
            interrupted: false,
        });
        InFlight(self)
    }

    fn end(&self) -> Option<Exchange> {
        let mut state = self.state.lock();
        self.interrupted.store(false, Ordering::Release);
        state.exchange.take()
    }

    /// Mark the exchange in flight as interrupted. The caller kills its
    /// process next, still holding `state`.
    fn interrupt(&self, state: &mut TurnState) {
        let exchange = state.exchange.as_mut().expect("an exchange is in flight");
        if tamarin_utils::env_gate!("TAM_DBG_MAUDE_INTERRUPT") {
            eprintln!("[maude-interrupt] after {:?}", exchange.since.elapsed());
        }
        exchange.interrupted = true;
        self.interrupted.store(true, Ordering::Release);
    }

    /// How long an exchange may run before an earlier job may interrupt it.
    fn interrupt_after(&self) -> std::time::Duration {
        let startup = std::time::Duration::from_micros(self.startup_micros.load(Ordering::Relaxed));
        INTERRUPT_FLOOR.max(startup * INTERRUPT_STARTUPS)
    }

    /// How long until a job of this rank may interrupt the exchange in
    /// flight. `None` if it may not: there is none, it was interrupted
    /// already, or a sequential run would not reach the job first.
    fn patience(
        &self,
        state: &TurnState,
        rank: Option<&tamarin_utils::parallel::Rank>,
    ) -> Option<std::time::Duration> {
        let exchange = state.exchange.as_ref()?;
        let holder = exchange.rank.as_ref()?;
        (!exchange.interrupted && rank?.precedes(holder)).then(|| {
            self.interrupt_after()
                .saturating_sub(exchange.since.elapsed())
        })
    }

    fn release(&self, waiter: u64) {
        if waiter != 0
            && self
                .reserved
                .compare_exchange(waiter, 0, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
        {
            let _state = self.state.lock();
            self.changed.notify_all();
        }
    }

    /// Wait until the process is no longer held for `other`.
    fn wait_for_release(&self, other: u64) {
        let mut state = self.state.lock();
        if self.reserved.load(Ordering::Acquire) == other {
            self.changed
                .wait_for(&mut state, std::time::Duration::from_millis(50));
        }
    }

    /// Tell jobs that are staying away that the process is in use.
    #[inline]
    fn note_use(&self) {
        if self.away.load(Ordering::Relaxed) != 0 {
            self.uses.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Stay away after an interruption: for `backoff`, or until nobody has
    /// used the process for as long as an exchange may run undisturbed.
    fn stay_away(&self, backoff: std::time::Duration) {
        const POLL: std::time::Duration = std::time::Duration::from_millis(20);
        self.away.fetch_add(1, Ordering::Relaxed);
        let away = std::time::Instant::now();
        let mut quiet = away;
        let mut uses = self.uses.load(Ordering::Relaxed);
        while cancellation::check().is_ok() {
            let other = self.reserved.load(Ordering::Acquire);
            if other != 0 {
                self.wait_for_release(other);
                quiet = std::time::Instant::now();
                continue;
            }
            let seen = self.uses.load(Ordering::Relaxed);
            if seen != uses {
                uses = seen;
                quiet = std::time::Instant::now();
            }
            if away.elapsed() >= backoff || quiet.elapsed() >= self.interrupt_after() {
                break;
            }
            std::thread::sleep(POLL);
        }
        self.away.fetch_sub(1, Ordering::Relaxed);
    }
}

/// The reservation a waiter holds after interrupting an exchange.
struct Waiter<'a> {
    turn: &'a Turn,
    id: u64,
}

impl Drop for Waiter<'_> {
    fn drop(&mut self) {
        self.turn.release(self.id);
    }
}

/// Exclusive use of a process's transport and counters. The lock is given
/// up only while an interrupted command waits to be repeated.
struct InnerGuard<'a> {
    guard: Option<parking_lot::MutexGuard<'a, MaudeProcessInner>>,
    handle: &'a MaudeHandle,
}

impl Deref for InnerGuard<'_> {
    type Target = MaudeProcessInner;
    fn deref(&self) -> &MaudeProcessInner {
        self.guard.as_ref().expect("the process is locked")
    }
}

impl std::ops::DerefMut for InnerGuard<'_> {
    fn deref_mut(&mut self) -> &mut MaudeProcessInner {
        self.guard.as_mut().expect("the process is locked")
    }
}

impl Drop for InnerGuard<'_> {
    fn drop(&mut self) {
        self.guard = None;
        self.handle.turn.note_use();
    }
}

impl InnerGuard<'_> {
    /// Run one command. If a job that needs the process sooner interrupts
    /// it, give the process up and run the command again later.
    fn execute(&mut self, cmd: &[u8], variable_bound: u64) -> Result<Vec<u8>, MaudeError> {
        let turn = &self.handle.turn;
        let mut backoff = turn.interrupt_after();
        loop {
            let exchange = turn.begin();
            let result = MaudeProcessInner::execute(self, cmd, variable_bound);
            if !exchange.finish() || result.is_ok() {
                return result;
            }
            // A job that interrupts once will usually be back. Stay away
            // for longer each time, so that repeating this command does not
            // keep holding it up.
            self.guard = None;
            turn.stay_away(backoff);
            self.guard = Some(self.handle.lock_process()?);
            backoff = (backoff * 2).min(BACKOFF_CEILING.max(turn.interrupt_after()));
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
    // Failed exchanges permit a fresh process on the next request. An explicit
    // watchdog kill keeps this handle offline until returned to the pool.
    restart: bool,
}

impl MaudeChildReaper {
    fn is_running(&mut self) -> std::io::Result<bool> {
        self.child
            .as_mut()
            .map_or(Ok(false), tamarin_utils::process::child_is_running)
    }

    fn invalidate(&mut self) {
        if self.child.is_some() {
            self.restart = true;
            self.kill_and_wait();
        }
    }

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

/// A balanced term keeps Maude's parser stack logarithmic in the number of
/// names being registered. Every MSG module declares cons : TOP TOP -> TOP.
fn name_order_command(start: u64, end: u64) -> String {
    use std::fmt::Write;
    fn tree(start: u64, end: u64, out: &mut String) {
        if end - start == 1 {
            write!(out, "x{start}:Msg").unwrap();
        } else {
            let mid = start + (end - start) / 2;
            out.push_str("cons(");
            tree(start, mid, out);
            out.push(',');
            tree(mid, end, out);
            out.push(')');
        }
    }
    debug_assert!(start < end);
    let mut cmd = String::from("parse in MSG : ");
    tree(start, end, &mut cmd);
    cmd.push_str(" .\n");
    cmd
}

fn check_name_registration(reply: &[u8]) -> Result<(), MaudeError> {
    // Maude reports rejected commands without failing the pipe exchange.
    // Never publish a watermark unless it actually parsed the term.
    if reply.starts_with(b"TOP: cons(")
        || reply.starts_with(b"[TOP]: cons(")
        || reply.starts_with(b"Msg: x")
    {
        Ok(())
    } else {
        Err(MaudeError::Other(format!(
            "Maude rejected variable name registration: {}",
            String::from_utf8_lossy(reply)
        )))
    }
}

/// Handle to a running Maude subprocess. Cloneable; uses an `Arc<Mutex<...>>`
/// internally so calls from multiple owners are serialised.
/// The `Child` reaper sits in its OWN mutex so a watchdog can
/// `kill_subprocess()` even while a reader thread is blocked on Maude
/// IPC inside `inner` — without this split, the watchdog deadlocks
/// trying to acquire the same mutex the blocked reader holds.
#[derive(Clone)]
pub struct MaudeHandle {
    inner: Arc<parking_lot::Mutex<MaudeProcessInner>>,
    child: Arc<Mutex<MaudeChildReaper>>,
    turn: Arc<Turn>,
    caches: Arc<SharedMaudeCaches>,
    /// The solver's fresh supply (HS `MonadFresh` of `Reduction`).  Each
    /// `with_fresh_counter_*` clone gets its own counter.
    fresh_counter: Arc<AtomicU64>,
    /// Every st-rule LHS is Ac/C-free, so `nf_via_haskell` is complete for
    /// `reduce`'s normal-form fast path.  Computed once at start.
    st_lhs_ac_free: bool,
    /// The immutable theory signature.
    sig: Arc<MaudeSig>,
}

impl std::fmt::Debug for MaudeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaudeHandle(running)")
    }
}

impl MaudeHandle {
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
        let (stdin, stdout, child) = spawn_maude(maude_path)?;
        let reaper = Arc::new(Mutex::new(MaudeChildReaper {
            child: Some(child),
            restart: false,
        }));
        let turn = Arc::<Turn>::default();
        let mut inner = MaudeProcessInner {
            maude_path: maude_path.to_owned(),
            child: reaper.clone(),
            turn: turn.clone(),
            initialized: false,
            ordered_variables: 0,
            stdin,
            stdout,
            stats: MaudeStats::default(),
            sig: Arc::clone(&sig),
        };
        inner.with_cancellation(MaudeProcessInner::initialize)?;
        Ok(MaudeHandle {
            inner: Arc::new(parking_lot::Mutex::new(inner)),
            child: reaper,
            turn,
            caches,
            // The global fresh counter starts at 0 (HS-faithful: HS's
            // `MonadFresh` global counter starts at 0).
            fresh_counter: Arc::new(AtomicU64::new(0)),
            st_lhs_ac_free: sig.st_lhs_all_ac_c_free(),
            sig,
        })
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

    /// Share this handle's process with a new fresh supply starting at
    /// `avoid_max + 1`: HS `runReduction ... (avoid sys)` gives each
    /// reduction its own counter.
    pub fn with_fresh_counter_from(&self, avoid_max: u64) -> MaudeHandle {
        self.with_fresh_counter_next(avoid_max.saturating_add(1))
    }

    /// Like [`with_fresh_counter_from`] but takes the NEXT-draw value
    /// directly (HS `FreshState` units).  HS `avoid sys` (LTerm.hs,
    /// `maybe 0 (succ . snd) . boundsVarIdx`) is legitimately 0 for a
    /// system with NO free variables (e.g. a lemma's root system: closed
    /// formula, no nodes), which the `avoid_max + 1` form cannot express.
    pub fn with_fresh_counter_next(&self, next: u64) -> MaudeHandle {
        MaudeHandle {
            inner: self.inner.clone(),
            child: self.child.clone(),
            turn: self.turn.clone(),
            caches: self.caches.clone(),
            fresh_counter: Arc::new(AtomicU64::new(next)),
            st_lhs_ac_free: self.st_lhs_ac_free,
            sig: Arc::clone(&self.sig),
        }
    }

    /// The theory signature (a refcount bump, no lock).
    pub fn maude_sig(&self) -> Arc<MaudeSig> {
        Arc::clone(&self.sig)
    }

    /// Kill the Maude process group, e.g. from a watchdog while a reader is
    /// blocked in IPC.  Locks only the reaper mutex, not `inner`, so it cannot
    /// deadlock with that reader.  Repeated calls are harmless.
    pub fn kill_subprocess(&self) {
        if let Ok(mut reaper) = self.child.lock() {
            reaper.restart = false;
            reaper.kill_and_wait();
        }
    }

    /// Lock the process for this job. A cancelled waiter leaves without it.
    #[inline]
    fn lock_inner(&self) -> Result<InnerGuard<'_>, cancellation::Cancelled> {
        Ok(InnerGuard {
            guard: Some(self.lock_process()?),
            handle: self,
        })
    }

    #[inline]
    fn lock_process(
        &self,
    ) -> Result<parking_lot::MutexGuard<'_, MaudeProcessInner>, cancellation::Cancelled> {
        // Cached operations frequently take an uncontended lock.
        if self.turn.reserved.load(Ordering::Relaxed) == 0
            && let Some(guard) = self.inner.try_lock()
            // An interrupting job may have reserved the process meanwhile.
            && self.turn.reserved.load(Ordering::Acquire) == 0
        {
            self.turn.note_use();
            cancellation::check()?;
            return Ok(guard);
        }
        self.lock_process_contended()
    }

    #[cold]
    fn lock_process_contended(
        &self,
    ) -> Result<parking_lot::MutexGuard<'_, MaudeProcessInner>, cancellation::Cancelled> {
        const POLL: std::time::Duration = std::time::Duration::from_secs(1);
        let turn = &*self.turn;
        let mut waiter = Waiter { turn, id: 0 };
        loop {
            cancellation::check()?;
            // A job waiting for a value this one is building can lend it an
            // earlier rank at any time.
            let rank = tamarin_utils::parallel::Rank::current();
            let reserved = turn.reserved.load(Ordering::Acquire);
            if reserved != 0 && reserved != waiter.id {
                turn.wait_for_release(reserved);
                continue;
            }
            // Wake on unlock, like an ordinary mutex. The timeout bounds
            // cancellation latency and the wait behind a speculative exchange.
            let wait = turn
                .patience(&turn.state.lock(), rank.as_ref())
                .map_or(POLL, |wait| {
                    wait.clamp(std::time::Duration::from_millis(1), POLL)
                });
            if let Some(guard) = self.inner.try_lock_for(wait) {
                let reserved = turn.reserved.load(Ordering::Acquire);
                if reserved != 0 && reserved != waiter.id {
                    continue;
                }
                turn.note_use();
                cancellation::check()?;
                return Ok(guard);
            }
            waiter.id = self.interrupt_exchange(rank.as_ref(), waiter.id);
        }
    }

    /// Kill the exchange in flight if a sequential run would reach `rank`
    /// first and the exchange has had its time, and hold the process for
    /// this waiter. Returns the waiter's reservation: `held`, or a new one.
    fn interrupt_exchange(&self, rank: Option<&tamarin_utils::parallel::Rank>, held: u64) -> u64 {
        let turn = &*self.turn;
        let mut state = turn.state.lock();
        if turn.reserved.load(Ordering::Acquire) != held
            || !turn
                .patience(&state, rank)
                .is_some_and(|left| left.is_zero())
        {
            return held;
        }
        turn.interrupt(&mut state);
        let id = if held == 0 {
            state.waiters += 1;
            turn.reserved.store(state.waiters, Ordering::Release);
            state.waiters
        } else {
            held
        };
        self.child
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .invalidate();
        id
    }

    /// Run a command whose reply depends on the command alone, or return
    /// the reply an identical command got earlier in the session.  The
    /// per-call back-conversion still runs on every hit, so a hit is
    /// consumed exactly like a round-trip.  `bump` records the per-command
    /// stat on a real round-trip only; `MaudeStats` reaches no `--prove`
    /// output.
    fn execute_memo(
        &self,
        cmd: &[u8],
        variable_bound: u64,
        bump: impl FnOnce(&mut MaudeStats),
    ) -> Result<Vec<u8>, MaudeError> {
        cancellation::check()?;
        let cached = || self.caches.reply.lock().unwrap().get(cmd).cloned();
        let hit = match cached() {
            Some(reply) => Some(reply),
            None => {
                let mut inner = self.lock_inner()?;
                // Another job may have run the same command meanwhile.
                match cached() {
                    Some(reply) => Some(reply),
                    None => {
                        let reply = inner.execute(cmd, variable_bound)?;
                        bump(&mut inner.stats);
                        drop(inner);
                        self.caches
                            .reply
                            .lock()
                            .unwrap()
                            .insert(cmd.to_vec(), reply.clone());
                        return Ok(reply);
                    }
                }
            }
        };
        Ok(hit.expect("a cached reply"))
    }

    /// Snapshot of the per-operation Maude call counters for this handle.
    pub fn stats(&self) -> MaudeStats {
        self.inner.lock().stats
    }

    /// HS `normViaMaude`: reduce `t` to normal form, memoised in
    /// `SharedMaudeCaches::reduce`.
    pub fn reduce(&self, t: &LNTerm) -> Result<LNTerm, MaudeError> {
        cancellation::check()?;
        let mut ctx = ConvCtx::new();
        let hit = self.caches.reduce.lock().unwrap().get(t).cloned();
        if let Some(cached) = hit {
            return Ok(cached);
        }
        let reply = {
            // No reducible symbol and no AC operator: `reduce` is the identity.
            if self.sig.has_no_ac_operators()
                && !term_has_reducible_sym(t, &self.sig.reducible_fun_syms)
            {
                return Ok(t.clone());
            }
            // HS asserts `nf'` agrees with `(t ==) <$> norm t` (`_nfCompare'`,
            // Norm.hs), so a normal-form `t` reduces to itself.  The pure
            // `nf_via_haskell` is complete only when no st-rule LHS needs AC
            // matching.  Both `t` and a reparsed reply are in smart-constructor
            // canonical form, so returning `t` is byte-identical.
            if self.st_lhs_ac_free && crate::norm::nf_via_haskell(&self.sig, t) {
                return Ok(t.clone());
            }
            let mt = lterm_to_mterm_global(t, &mut ctx);
            let mut cmd = b"reduce ".to_vec();
            pp_mterm_into(&mt, &mut cmd);
            cmd.extend_from_slice(b" .\n");
            let mut inner = self.lock_inner()?;
            let reply = inner.execute(&cmd, ctx.variable_bound())?;
            inner.stats.norm_count += 1;
            reply
        };
        let mt_back = maude_parse::parse_reduce_reply(&reply, &self.sig)?;
        let mut next = 0;
        let result = mterm_to_lnterm(&mt_back, &mut ctx, "z", &mut next);
        self.caches
            .reduce
            .lock()
            .unwrap()
            .insert(t.clone(), result.clone());
        Ok(result)
    }

    /// Whether *any* unifier of `eqs` exists, modulo the theory.
    ///
    /// Memoised via `SharedMaudeCaches::unifiable`, so a repeat query skips
    /// the subprocess round-trip.  Safe to cache because the result is a
    /// context-free boolean (no witness LVars leak across calls).
    ///
    /// For an AC-free signature the local unifier answers without Maude.
    pub fn unifiable(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        if eqs.is_empty() {
            return Ok(true);
        }
        if eqs.iter().all(|eq| eq.lhs == eq.rhs) {
            return Ok(true);
        }
        if self.is_ac_free() {
            return Ok(crate::unification::unify_lnterm_factored(eqs.to_vec())
                .is_some_and(|(_, residual)| residual.is_empty()));
        }
        let key: Vec<(LNTerm, LNTerm)> =
            eqs.iter().map(|e| (e.lhs.clone(), e.rhs.clone())).collect();
        // Cache locks below are scoped to the single `get` / `insert`
        // statement and released before any Maude IPC (lock-order
        // invariant on `SharedMaudeCaches`).
        cancellation::check()?;
        let hit = self.caches.unifiable.lock().unwrap().get(&key).copied();
        if let Some(hit) = hit {
            return Ok(hit);
        }
        let res = self.unify(eqs)?;
        let answer = !res.is_empty();
        self.caches.unifiable.lock().unwrap().insert(key, answer);
        Ok(answer)
    }

    /// True when the local unifier answers every unifiability query: no AC
    /// operators and no st-rules.  With st-rules, Maude's `unify` narrows
    /// through their `[variant]` equations (e.g. StatVerif's
    /// `true =? checkpcs(...)`), which the local unifier cannot do.
    fn is_ac_free(&self) -> bool {
        self.sig.has_no_ac_operators() && self.sig.st_rules.is_empty()
    }

    /// HS `unifyLTermFactored` + `flattenUnif` (Term/Unification.hs): solve
    /// the non-AC fragment locally, send only the AC residuals to Maude
    /// (`unifyViaMaude`), and compose each Maude unifier with the local
    /// substitution.
    ///
    /// Witness numbering touches no global fresh state: HS numbers witnesses
    /// in a pure per-call scope (`runBackConversion`, Term/Maude/Types.hs).
    pub fn unify(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        // No syntactic-equality fast path: `unifyRaw` delays AC/C pairs even
        // when both sides are equal, and Maude's unifier set for such a pair
        // can be larger than the identity (e.g. `mult(x,y) =? mult(x,y)` also
        // has `x = y`).
        //
        // `unifyRaw` failing means no unifier, without calling Maude, so
        // `[variant]` equations never narrow a free clash.
        let Some((factored_m, residual_eqs)) =
            crate::unification::unify_lnterm_factored(eqs.to_vec())
        else {
            return Ok(Vec::new());
        };
        // HS `solve _ (Just (m, [])) = (substFromMap m, [emptySubstVFresh])`.
        if residual_eqs.is_empty() {
            let empty = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
            return Ok(vec![crate::subst_vfresh::compose_vfresh(
                &empty,
                &factored_m,
            )
            .to_list()]);
        }
        let mut ctx = ConvCtx::new();
        let cmd = build_conj_eqs_cmd(b"unify in MSG : ", &residual_eqs, &mut ctx);
        let reply = self.execute_memo(&cmd, ctx.variable_bound(), |s| s.unify_count += 1)?;
        let msubsts = maude_parse::parse_unify_reply(&reply, &self.sig)?;
        // `flattenUnif (subst, substs) = map (`composeVFresh` subst) substs`.
        Ok(convert_reply(&msubsts, &ctx, BackConv::VFresh)?
            .into_iter()
            .map(|arm| {
                let arm = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::from_list(arm);
                crate::subst_vfresh::compose_vfresh(&arm, &factored_m).to_list()
            })
            .collect())
    }

    /// HS `matchViaMaude`: AC matchers for `(subject, pattern)` problems.
    /// As in HS, each `Equal` holds `lhs = subject, rhs = pattern`, and
    /// `matchCmd` emits `match PATTERN <=? SUBJECT` (Maude binds variables on
    /// the left only).
    pub fn match_eqs(
        &self,
        eqs: &[Equal<LNTerm>],
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        // Ground patterns: the MSG module has only `[comm assoc]` / `[comm]`
        // axioms and AC/C terms are kept canonical, so Maude's answer (one
        // empty matcher or none) is structural equality.  This skips most
        // `match` queries on multiset/natural-number theories.
        if eqs.iter().all(|eq| crate::vterm::is_ground_vterm(&eq.rhs)) {
            return Ok(structural_match(eqs));
        }
        self.match_query(eqs, false)
    }

    /// HS `matchTerm` (Guarded.hs) as `impliedFormulas` (System.hs) uses
    /// it: every free variable outside `pattern_vars`, on either side, is
    /// skolemized to one shared constant (`skolemizeGuarded` /
    /// `skolemizeTerm`), so only the pattern variables bind.  Here each
    /// `Equal` holds `lhs = pattern, rhs = subject`.
    pub fn match_eqs_skolemize_both(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_vars: &std::collections::BTreeSet<(&'static str, u64)>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        use crate::lterm::LVar;
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        // No pattern variable: as in `match_eqs`, the answer is structural
        // equality (skolemizing both sides alike preserves it).
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
        if eqs.iter().all(|eq| !has_pattern_var(&eq.lhs, pattern_vars)) {
            return Ok(structural_match(eqs));
        }
        // One skolem constant per free variable, shared by both sides.
        let mut free_vars: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for eq in eqs {
            collect_free_non_pattern_vars(&eq.lhs, pattern_vars, &mut free_vars);
            collect_free_non_pattern_vars(&eq.rhs, pattern_vars, &mut free_vars);
        }
        let (skolem_map, reverse) = build_skolem_maps(&free_vars);
        let rewritten_eqs: Vec<Equal<LNTerm>> = eqs
            .iter()
            .map(|eq| Equal {
                lhs: rewrite_skolem(&eq.lhs, &skolem_map),
                rhs: rewrite_skolem(&eq.rhs, &skolem_map),
            })
            .collect();
        Ok(self
            .match_query(&rewritten_eqs, true)?
            .into_iter()
            .map(|sub| unskolemize_subst(sub, &reverse))
            .collect())
    }

    /// HS `matchCmd` round trip: `match PATTERN <=? SUBJECT` over `eqs`,
    /// with `pattern_is_lhs` naming the side of each `Equal` that is the
    /// pattern.  Each equation converts `lhs` then `rhs`, so the variable
    /// numbering (and the memoized command) does not depend on that choice.
    fn match_query(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_is_lhs: bool,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        let mut ctx = ConvCtx::new();
        let mut pats: Vec<MTerm> = Vec::with_capacity(eqs.len());
        let mut subjs: Vec<MTerm> = Vec::with_capacity(eqs.len());
        for eq in eqs {
            let lhs = lterm_to_mterm_global(&eq.lhs, &mut ctx);
            let rhs = lterm_to_mterm_global(&eq.rhs, &mut ctx);
            if pattern_is_lhs {
                pats.push(lhs);
                subjs.push(rhs);
            } else {
                pats.push(rhs);
                subjs.push(lhs);
            }
        }
        let cmd = pp_match_cmd(&pats, &subjs);
        let reply = self.execute_memo(&cmd, ctx.variable_bound(), |s| s.match_count += 1)?;
        let msubsts = maude_parse::parse_match_reply(&reply, &self.sig)?;
        convert_reply(&msubsts, &ctx, BackConv::VFree)
    }

    /// Get the variants of a term, one substitution per Maude `[variant]`
    /// (HS `variantsViaMaude`, Maude/Process.hs).
    pub fn variants(
        &self,
        t: &LNTerm,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
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
        let reply = self.execute_memo(&cmd, ctx.variable_bound(), |s| s.var_count += 1)?;
        let msubsts = maude_parse::parse_variants_reply(&reply, &self.sig)?;
        convert_reply(&msubsts, &ctx, BackConv::VFresh)
    }
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
/// LEFT (vars bind), subject list on the RIGHT (ground) — the convention shared
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

/// The matcher set when no pattern variable can bind: one empty matcher if
/// every equation's sides are structurally equal, none otherwise.
fn structural_match(eqs: &[Equal<LNTerm>]) -> Vec<Vec<(crate::lterm::LVar, LNTerm)>> {
    if eqs.iter().all(|eq| eq.lhs == eq.rhs) {
        vec![Vec::new()]
    } else {
        vec![]
    }
}

/// Build the forward (LVar→skolem `Name`) and reverse (`Name`→LVar) skolem maps
/// for `vars`, assigning synthetic constants in BTreeSet iteration order via
/// `skolem_name`.  Used by `match_eqs_skolemize_both`.
fn build_skolem_maps(
    vars: &std::collections::BTreeSet<crate::lterm::LVar>,
) -> (
    std::collections::BTreeMap<crate::lterm::LVar, crate::lterm::Name>,
    std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
) {
    let mut skolem_map = std::collections::BTreeMap::new();
    let mut reverse = std::collections::BTreeMap::new();
    for (counter, lv) in (0_u64..).zip(vars.iter()) {
        let n = skolem_name(counter, lv);
        skolem_map.insert(*lv, n);
        reverse.insert(n, *lv);
    }
    (skolem_map, reverse)
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

/// The skolem constant for `lv`.  HS gives a `SkConst` the variable's own
/// sort (`sortOfSkol`, Guarded.hs).  `NameTag` has no `Msg`, so a
/// `Msg`-sorted skolem is a `Pub` name with the `SKOLEM_MSG_PREFIX` id that
/// `maude_types::sort_of_name` maps back to `Msg`; encoding it as `Pub`
/// would let it match `Msg` pattern positions HS rejects.
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

/// Map skolem constants in `t` back to their original variables.  HS
/// `unskolemizeBTerm` (Guarded.hs) is an `fmapTerm`, so AC and C argument
/// lists are re-sorted under the restored variables.
fn unskolemize(
    t: &LNTerm,
    reverse: &std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
) -> LNTerm {
    use crate::vterm::Lit;
    crate::term::map_lits(t, &mut |l| match l {
        Lit::Con(n) => reverse.get(n).map_or(*l, |lv| Lit::Var(*lv)),
        _ => *l,
    })
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

/// Replace each `LVar` bound in `map` with its skolem constant.  HS
/// `skolemizeTerm` (Guarded.hs) is an `fmapTerm`, so AC and C argument
/// lists are re-sorted under the new literals.
fn rewrite_skolem(
    t: &LNTerm,
    map: &std::collections::BTreeMap<crate::lterm::LVar, crate::lterm::Name>,
) -> LNTerm {
    use crate::vterm::Lit;
    crate::term::map_lits(t, &mut |l| match l {
        Lit::Var(lv) => map.get(lv).map_or(*l, |n| Lit::Con(*n)),
        _ => *l,
    })
}

/// Which HS back-conversion a reply goes through (Maude/Types.hs).
#[derive(Clone, Copy, PartialEq, Eq)]
enum BackConv {
    /// `msubstToLSubstVFresh` (unify, variants): ends with `removeRenamings`.
    VFresh,
    /// `msubstToLSubstVFree` (match).
    VFree,
}

/// Convert every substitution of a Maude reply, as HS `map
/// (msubstToLSubstV* bindings)` does.  Each one runs `runBackConversion`
/// (Maude/Types.hs): from the same initial `bindings` (a clone of `ctx`),
/// in Maude's returned order, naming witnesses `"x"` and numbering them from
/// `avoid (M.elems bindings)`.  No global fresh state is read or written.
fn convert_reply(
    msubsts: &[MSubst],
    ctx: &ConvCtx,
    kind: BackConv,
) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
    use crate::vterm::Lit;
    // `avoid = maybe 0 (succ . snd) . boundsVarIdx` (LTerm.hs).
    let avoid = ctx
        .bindings()
        .values()
        .filter_map(|l| match l {
            Lit::Var(lv) => Some(lv.idx.saturating_add(1)),
            Lit::Con(_) => None,
        })
        .max()
        .unwrap_or(0);
    let mut out = Vec::with_capacity(msubsts.len());
    for ms in msubsts {
        let mut ctx = ctx.clone();
        let mut next = avoid;
        let mut slist = Vec::with_capacity(ms.len());
        for ((sort, idx), mt) in ms {
            let lv =
                crate::maude_types::substitute_lookup_var(&ctx, *sort, *idx).ok_or_else(|| {
                    MaudeError::Other(format!("no binding for Maude variable x{}:{:?}", idx, sort))
                })?;
            slist.push((lv, mterm_to_lnterm(mt, &mut ctx, "x", &mut next)));
        }
        out.push(match kind {
            BackConv::VFresh => crate::subst_vfresh::LSubstVFresh::from_list(slist)
                .remove_renamings()
                .to_list(),
            BackConv::VFree => slist,
        });
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

impl PoolState {
    /// Pop the most recently returned member. One that exited while idle, or
    /// whose last borrower lost it, restarts on its next exchange.
    fn pop(&mut self) -> Option<MaudeHandle> {
        let handle = self.free.pop()?;
        {
            let mut child = handle
                .child
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if matches!(child.is_running(), Ok(false)) {
                child.invalidate();
                child.restart = true;
            }
        }
        Some(handle)
    }

    fn idle_running(&self) -> Option<usize> {
        // A recycled lease may be waiting for its next exchange to restart
        // Maude. Leave it available for callers that can wait for startup.
        self.free.iter().rposition(|handle| {
            handle
                .child
                .try_lock()
                .is_ok_and(|mut child| matches!(child.is_running(), Ok(true)))
        })
    }
}

/// Pool of up to `size` independent Maude subprocesses, all initialised
/// with the same `MaudeSig`.  A lease returns its process to the pool on
/// drop.  Proof search only takes leases that never wait for a release
/// (`try_take_idle_owned`, `try_acquire_ready`) and falls back to the
/// caller's own process; `acquire` blocks and is for work outside it.
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
        assert!(n >= 1, "MaudePool::new requires n >= 1");
        let first = MaudeHandle::start_with_caches(path, sig.clone(), Arc::clone(&caches))?;
        Ok(MaudePool {
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
        if !matches!(e, MaudeError::Cancelled) && !self.spawn_warned.swap(true, Ordering::Relaxed) {
            eprintln!(
                "[warn] MaudePool: starting a Maude process failed ({}); \
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
            if let Some(h) = state.pop() {
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
                match self.spawn_reserved() {
                    Ok(h) => {
                        return PooledMaude {
                            pool: self,
                            inner: Some(h),
                        };
                    }
                    Err(_) => {
                        try_spawn = false;
                        // A member may have been released while the lock was
                        // dropped for the spawn attempt. Re-check `free`
                        // under this relock before waiting.
                        state = self.state.lock().unwrap();
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

    /// Start the member whose slot the caller just reserved in `spawned`.
    /// If startup fails or panics, the slot is released and a blocked
    /// `acquire` is woken so it can use it.
    fn spawn_reserved(&self) -> Result<MaudeHandle, MaudeError> {
        struct Reserved<'a>(&'a MaudePool);
        impl Drop for Reserved<'_> {
            fn drop(&mut self) {
                let mut state = self
                    .0
                    .state
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                state.spawned -= 1;
                self.0.notify.notify_one();
            }
        }
        let reserved = Reserved(self);
        match MaudeHandle::start_with_caches(&self.path, self.sig.clone(), Arc::clone(&self.caches))
        {
            Ok(handle) => {
                std::mem::forget(reserved);
                Ok(handle)
            }
            Err(error) => {
                drop(reserved);
                self.warn_spawn_failed(&error);
                Err(error)
            }
        }
    }

    /// Non-blocking acquire: pop an idle member, else spawn a new one on
    /// demand (up to `size`), else return `None`.  This NEVER waits on the
    /// condvar, so nested parallel work cannot deadlock on a drained pool.
    /// It may block ~30ms while a lazy member spawns.
    pub fn try_acquire(&self) -> Option<PooledMaude<'_>> {
        self.try_borrow().ok().flatten()
    }

    fn try_borrow(&self) -> Result<Option<PooledMaude<'_>>, MaudeError> {
        let mut state = self.state.lock().unwrap();
        if let Some(h) = state.pop() {
            return Ok(Some(PooledMaude {
                pool: self,
                inner: Some(h),
            }));
        }
        if state.spawned < self.size {
            state.spawned += 1;
            drop(state);
            return self.spawn_reserved().map(|h| {
                Some(PooledMaude {
                    pool: self,
                    inner: Some(h),
                })
            });
        }
        Ok(None)
    }

    /// Take an already-running member, or `None`. Never spawns and never
    /// waits for subprocess I/O, so the caller stays interruptible even if a
    /// new Maude would never print its startup prompt.
    pub fn try_take_idle_owned(self: &Arc<Self>) -> Option<OwnedPooledMaude> {
        let mut state = self.state.lock().unwrap();
        let idle = state.idle_running()?;
        let handle = state.free.remove(idle);
        Some(MaudeLease {
            pool: self.clone(),
            inner: Some(handle),
        })
    }

    /// Take a running member, or start one (up to `size`) and finish its
    /// startup under the caller's cancellation scope. Returns `None` when the
    /// pool is fully leased or startup fails or is cancelled; never waits for
    /// a release. The lease can move between threads with its job.
    pub fn try_acquire_ready(self: &Arc<Self>) -> Option<OwnedPooledMaude> {
        if let Some(lease) = self.try_take_idle_owned() {
            return Some(lease);
        }
        let mut borrowed = self.try_borrow().ok()??;
        let lease = MaudeLease {
            pool: self.clone(),
            inner: borrowed.inner.take(),
        };
        let ready = cancellation::lock(&lease.handle().inner)
            .map_err(MaudeError::from)
            .and_then(|mut inner| inner.with_cancellation(MaudeProcessInner::prepare_worker));
        if let Err(error) = ready {
            self.warn_spawn_failed(&error);
            return None;
        }
        Some(lease)
    }

    /// Target subprocess count this pool was constructed with — the ceiling
    /// on lazy growth, NOT the number spawned so far (see `spawned`).
    pub fn size(&self) -> usize {
        self.size
    }

    /// Number of members actually spawned so far (≤ `size`).  Grows lazily
    /// as `acquire`/`try_acquire` demand members beyond the eager first one.
    pub fn spawned(&self) -> usize {
        self.state.lock().unwrap().spawned
    }
}

/// A lease borrowing its pool.
pub type PooledMaude<'a> = MaudeLease<&'a MaudePool>;
/// A lease that keeps its pool alive until the worker returns the process.
pub type OwnedPooledMaude = MaudeLease<Arc<MaudePool>>;

/// Exclusive use of a subprocess until the lease is dropped.
#[must_use = "dropping the lease returns the process to the pool"]
pub struct MaudeLease<P: Deref<Target = MaudePool>> {
    pool: P,
    inner: Option<MaudeHandle>,
}

impl<P: Deref<Target = MaudePool>> MaudeLease<P> {
    /// The leased handle, as `Deref` also returns. A clone of it must not
    /// outlive the lease: the process goes back to the pool on drop.
    pub fn handle(&self) -> &MaudeHandle {
        self.inner
            .as_ref()
            .expect("lease holds its handle until drop")
    }
}

impl<P: Deref<Target = MaudePool>> Deref for MaudeLease<P> {
    type Target = MaudeHandle;
    fn deref(&self) -> &MaudeHandle {
        self.handle()
    }
}

impl<P: Deref<Target = MaudePool>> Drop for MaudeLease<P> {
    fn drop(&mut self) {
        if let Some(h) = self.inner.take() {
            // An IPC error belongs to the borrower that saw it. The slot stays
            // in the pool and `PoolState::pop` restarts it for the next one.
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
