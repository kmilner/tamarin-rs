// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! In-memory store of loaded theories, mirroring Haskell `TheoryMap`.
//!
//! Indexed by integer (1-based, matching Haskell's behaviour) — the
//! frontend reads/writes these indices in URLs like
//! `/thy/trace/<idx>/main/...`.
//!
//! The elaborated typed theory is what [`ProofState::new`] builds the
//! live prover session from, what the web renderers print, and what the
//! accessor helpers (lemma list, restriction count, …) read.
//!
//! Concurrency: `parking_lot::Mutex` protects only short store operations;
//! proof mutations and other blocking prover work run outside it through
//! `tokio::task::spawn_blocking`.

use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::fmt;
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};

use chrono::{DateTime, Local};

use tamarin_theory::theory::Theory as TypedTheory;

use crate::handlers::proof_tree::ProofState;

/// One loaded theory with bookkeeping.
#[derive(Clone)]
pub struct TheoryEntry {
    /// Stable index used in URLs.  Set by `TheoryStore::insert`.
    pub idx: usize,
    /// Elaborated, typed theory — the accessor helpers' source and the
    /// theory the lazily built [`ProofState`] proves.  Wrapped in `Arc`
    /// so we can clone the entry cheaply.
    pub typed_theory: Arc<TypedTheory>,
    /// The signature every Maude process for this theory loads its module
    /// from, taken before the load joins `check_close_intr_rule`'s verdicts
    /// into [`typed_theory`](Self::typed_theory)'s signature.  A symbol's NDC
    /// state is part of its Maude operator name, while the signature's rewrite
    /// rules and the theory's terms keep their untagged symbols, so a module
    /// built from the joined signature declares operators nothing else names.
    pub prover_maude_sig: tamarin_term::maude_sig::MaudeSig,
    /// Where the theory came from.
    pub origin: TheoryOrigin,
    /// Load time for the UI.
    pub loaded_at: DateTime<Local>,
    /// True for the originally loaded copy (vs. ones produced by edits).
    pub primary: bool,
    /// The theory's wellformedness report, computed at load time by the
    /// same pipeline `--prove` runs (`theory_io::load_from_source`, mirroring
    /// `run.rs`'s `checkWellformedness`).  This is the single source of truth
    /// for both wellformedness renderings: the `/* WARNING: ... */` comment in
    /// the `source`/`message` routes (`format_wf_block`) and the
    /// `<div class="wf-warning">` header banner in the `help`/`overview` routes
    /// (`errors_html`).  Empty ⇒ no warnings (theory is well-formed).
    pub wf_report: Vec<tamarin_theory::wellformedness::WfError>,
    /// HTML for the wellformedness warning banner shown in the theory
    /// page header (HS `errorsHtml`, rendered raw via
    /// `preEscapedToMarkup info.errorsHtml` at `src/Web/Theory.hs`).
    /// Populated from [`wf_report`](Self::wf_report) at load time,
    /// mirroring HS `makeWfErrorsHtml` (`src/Web/Handler.hs`), which wraps
    /// `renderHtmlDoc (htmlDoc $ prettyWfErrorReport report)` of the
    /// *closed* theory's wellformedness report in a `<div class="wf-warning">`.
    /// Empty string when the report is empty (HS `makeWfErrorsHtml [] = ""`).
    pub errors_html: String,
    /// The theory's once-per-load NDC-checked intruder cache
    /// (`close_rule::check_close_intr_rule`, run in `theory_io` before
    /// the derivation checks). Injected into the lazily built prover session,
    /// whose context factory reuses it for every operation. `None` when the
    /// load-time Maude boot failed.
    pub ndc_cache: Option<Arc<Vec<tamarin_theory::rule::IntrRuleAC>>>,
    /// Live proof state — built lazily on first request that needs a
    /// materialized snapshot. `None` here means "not yet built"; on first
    /// access we boot Maude and construct the theory-wide context. Sources
    /// and per-lemma systems remain lazy until a proof operation needs them.
    pub proof_state: Option<Arc<ProofState>>,
}

#[derive(Clone, Debug)]
pub enum TheoryOrigin {
    /// Loaded from a path on disk.
    Local(PathBuf),
    /// Uploaded via POST `/`.
    Upload(String),
    /// Generated interactively (e.g. by an edit). Currently never
    /// constructed — placeholder for the unported interactive-edit
    /// path (HS `Interactive`).
    Interactive,
}

impl TheoryOrigin {
    pub fn label(&self) -> String {
        match self {
            TheoryOrigin::Local(p) => p.display().to_string(),
            TheoryOrigin::Upload(n) => n.clone(),
            TheoryOrigin::Interactive => "(interactively created)".into(),
        }
    }
}

#[derive(Default, Clone)]
pub struct TheoryStore {
    inner: Arc<Mutex<TheoryStoreInner>>,
}

#[derive(Default)]
struct TheoryStoreInner {
    by_idx: BTreeMap<usize, StoredTheory>,
}

struct StoredTheory {
    generation: Arc<StoredGeneration>,
    entry: TheoryEntry,
}

/// A store operation failed without conflating absence, prover startup, and a
/// concurrent replacement of the theory being operated on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StoreError {
    NotFound(usize),
    Build(String),
    Stale(usize),
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(idx) => write!(f, "theory index {idx} not found"),
            Self::Build(error) => f.write_str(error),
            Self::Stale(idx) => write!(f, "theory index {idx} changed during the operation"),
        }
    }
}

impl std::error::Error for StoreError {}

/// A consistent theory generation.  The generation token is deliberately
/// private: callers can inspect the entry and pass the whole snapshot back to
/// [`TheoryStore::replace_if_current`], but cannot forge a comparison token.
#[derive(Clone)]
pub struct TheorySnapshot {
    pub entry: TheoryEntry,
    idx: usize,
    generation: Arc<StoredGeneration>,
}

struct StoredGeneration {
    proof: RetryCell<Arc<ProofState>, StoreError>,
}

/// One single-flight attempt at a time. Callers which observed the same slot
/// share its result; a failed slot is replaced so the next request can retry.
struct RetryCell<T, E> {
    attempt: Mutex<Arc<OnceLock<Result<T, E>>>>,
}

impl<T: Clone, E: Clone> RetryCell<T, E> {
    fn new(value: Option<T>) -> Self {
        let attempt = Arc::new(match value {
            Some(value) => OnceLock::from(Ok(value)),
            None => OnceLock::new(),
        });
        Self {
            attempt: Mutex::new(attempt),
        }
    }

    fn get_or_try_init(&self, build: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
        let attempt = self.attempt.lock().clone();
        self.run_attempt(attempt, build)
    }

    fn run_attempt(
        &self,
        attempt: Arc<OnceLock<Result<T, E>>>,
        build: impl FnOnce() -> Result<T, E>,
    ) -> Result<T, E> {
        let result = attempt.get_or_init(build).clone();
        if result.is_err() {
            let mut current = self.attempt.lock();
            if Arc::ptr_eq(&current, &attempt) {
                *current = Arc::new(OnceLock::new());
            }
        }
        result
    }
}

/// Next free store index: Haskell's `M.findMax + 1` (empty → 1).
/// `next_back()` is O(log n) (unlike `keys().last()`, which walks).
fn next_free_idx(inner: &TheoryStoreInner) -> usize {
    inner.by_idx.keys().next_back().map_or(1, |k| k + 1)
}

impl TheoryStore {
    /// Insert a new theory and return the freshly assigned index.
    pub fn insert(&self, mut entry: TheoryEntry) -> usize {
        let mut inner = self.inner.lock();
        // Match Haskell's `M.findMax + 1` (BTreeMap max key); empty → 1.
        let idx = next_free_idx(&inner);
        entry.idx = idx;
        entry.loaded_at = Local::now();
        let generation = Arc::new(StoredGeneration::new(entry.proof_state.clone()));
        inner.by_idx.insert(idx, StoredTheory { generation, entry });
        idx
    }

    /// Capture an entry together with its unforgeable store-generation token.
    pub fn snapshot(&self, idx: usize) -> Result<TheorySnapshot, StoreError> {
        let inner = self.inner.lock();
        let stored = inner.by_idx.get(&idx).ok_or(StoreError::NotFound(idx))?;
        Ok(TheorySnapshot {
            entry: stored.entry.clone(),
            idx,
            generation: stored.generation.clone(),
        })
    }

    pub fn get(&self, idx: usize) -> Option<TheoryEntry> {
        self.inner
            .lock()
            .by_idx
            .get(&idx)
            .map(|stored| stored.entry.clone())
    }

    pub(crate) fn contains(&self, idx: usize) -> bool {
        self.inner.lock().by_idx.contains_key(&idx)
    }

    /// The stored theory's name at `idx`, or `None` when no theory is stored
    /// there.  This is what the handlers that only label a page with the name
    /// take instead of [`get`], whose clone deep-copies `wf_report` and
    /// `errors_html`.
    ///
    /// [`get`]: Self::get
    pub fn name(&self, idx: usize) -> Option<String> {
        self.inner
            .lock()
            .by_idx
            .get(&idx)
            .map(|stored| stored.entry.typed_theory.name.clone())
    }

    pub fn list(&self) -> Vec<TheoryEntry> {
        self.inner
            .lock()
            .by_idx
            .values()
            .map(|stored| stored.entry.clone())
            .collect()
    }

    pub fn remove(&self, idx: usize) -> Option<TheoryEntry> {
        self.inner
            .lock()
            .by_idx
            .remove(&idx)
            .map(|stored| stored.entry)
    }

    /// Fork a version without publishing it. Callers can perform fallible
    /// proof work on the detached value and insert it only after success.
    pub fn detached_fork(
        &self,
        src_idx: usize,
        cfg: &crate::ServerConfig,
    ) -> Result<TheoryEntry, StoreError> {
        let mut clone = self.materialized_snapshot(src_idx, cfg)?;
        let proof = clone
            .proof_state
            .clone()
            .expect("materialized_snapshot always has a proof state");
        clone.proof_state = Some(Arc::new(proof.fork()));
        clone.idx = 0;
        clone.primary = false;
        Ok(clone)
    }

    /// Return one internally consistent, materialised generation of a theory.
    pub fn materialized_snapshot(
        &self,
        idx: usize,
        cfg: &crate::ServerConfig,
    ) -> Result<TheoryEntry, StoreError> {
        loop {
            let mut snapshot = self.snapshot(idx)?;
            match self.ensure_snapshot_proof(&snapshot, cfg) {
                Ok(proof) => {
                    snapshot.entry.proof_state = Some(proof);
                    return Ok(snapshot.entry);
                }
                Err(StoreError::Stale(_)) => continue,
                Err(error) => return Err(error),
            }
        }
    }

    /// Clone a theory without its proof state for an operation that invalidates
    /// every proof, such as deleting a lemma.
    pub fn detached_without_proof(&self, src_idx: usize) -> Result<TheoryEntry, StoreError> {
        let mut clone = self.snapshot(src_idx)?.entry;
        clone.idx = 0;
        clone.primary = false;
        clone.proof_state = None;
        Ok(clone)
    }

    /// Replace a snapshotted entry in place if it is still the current
    /// generation.  Slow reload work can therefore happen without the store
    /// lock while still being unable to overwrite an unloaded/reused index.
    /// Mirrors Haskell `replaceTheory` (`src/Web/Handler.hs`), but rejects a
    /// concurrent removal/replacement rather than recreating or overwriting
    /// the index.  It forces `primary = false` to match `replaceTheory`'s
    /// hard-coded `False`, so a reloaded theory shows as "Modified".
    pub fn replace_if_current(
        &self,
        snapshot: &TheorySnapshot,
        mut entry: TheoryEntry,
    ) -> Result<usize, StoreError> {
        let idx = snapshot.idx;
        let mut inner = self.inner.lock();
        let is_current = inner
            .by_idx
            .get(&idx)
            .is_some_and(|stored| Arc::ptr_eq(&stored.generation, &snapshot.generation));
        if !is_current {
            return Err(StoreError::Stale(idx));
        }
        entry.idx = idx;
        entry.primary = false;
        let generation = Arc::new(StoredGeneration::new(entry.proof_state.clone()));
        inner.by_idx.insert(idx, StoredTheory { generation, entry });
        Ok(idx)
    }

    fn validate_generation(
        &self,
        idx: usize,
        generation: &Arc<StoredGeneration>,
    ) -> Result<(), StoreError> {
        let inner = self.inner.lock();
        match inner.by_idx.get(&idx) {
            Some(stored) if Arc::ptr_eq(&stored.generation, generation) => Ok(()),
            _ => Err(StoreError::Stale(idx)),
        }
    }

    fn ensure_snapshot_proof(
        &self,
        snapshot: &TheorySnapshot,
        cfg: &crate::ServerConfig,
    ) -> Result<Arc<ProofState>, StoreError> {
        let idx = snapshot.idx;
        let generation = snapshot.generation.clone();
        generation.proof.get_or_try_init(|| {
            // A waiter may reach this closure after an earlier builder
            // discovered that reload/removal made the generation stale.
            // Reject it before booting another Maude process; the caller
            // will retry from a fresh snapshot. The post-build check below
            // still closes the race with replacement during the build.
            self.validate_generation(idx, &generation)?;
            let ndc_cache = snapshot
                .entry
                .ndc_cache
                .clone()
                .map(tamarin_theory::constraint::solver::context::IntrRuleCache::from);
            let built = ProofState::new(
                &snapshot.entry.typed_theory,
                snapshot.entry.prover_maude_sig.clone(),
                &cfg.maude_path,
                cfg.stop_on_trace,
                ndc_cache.as_ref(),
            );

            // Publish only into the exact generation that elected this
            // builder.  Removal, reload, and index reuse all replace the Arc.
            let mut inner = self.inner.lock();
            let stored = inner.by_idx.get_mut(&idx).ok_or(StoreError::Stale(idx))?;
            if !Arc::ptr_eq(&stored.generation, &generation) {
                return Err(StoreError::Stale(idx));
            }
            let proof = Arc::new(built.map_err(StoreError::Build)?);
            stored.entry.proof_state = Some(proof.clone());
            Ok(proof)
        })
    }
}

impl StoredGeneration {
    fn new(proof: Option<Arc<ProofState>>) -> Self {
        Self {
            proof: RetryCell::new(proof),
        }
    }
}

/// App-wide state, used by every handler.
pub struct AppState {
    pub cfg: crate::ServerConfig,
    pub store: TheoryStore,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use tamarin_term::maude_sig::minimal_maude_sig;
    use tamarin_theory::theory::OpenProtoRule;

    fn entry(name: &str) -> TheoryEntry {
        let prover_maude_sig = minimal_maude_sig(false);
        let typed_theory = TypedTheory::<OpenProtoRule>::new(name, prover_maude_sig.clone());
        TheoryEntry {
            idx: 0,
            typed_theory: Arc::new(typed_theory),
            prover_maude_sig,
            origin: TheoryOrigin::Interactive,
            loaded_at: Local::now(),
            primary: true,
            wf_report: Vec::new(),
            errors_html: String::new(),
            ndc_cache: None,
            proof_state: None,
        }
    }

    #[test]
    fn stale_snapshot_cannot_replace_reused_index() {
        let store = TheoryStore::default();
        let idx = store.insert(entry("first"));
        let snapshot = store.snapshot(idx).unwrap();

        store.remove(idx);
        assert_eq!(store.insert(entry("second")), idx);

        assert_eq!(
            store.replace_if_current(&snapshot, entry("stale")),
            Err(StoreError::Stale(idx))
        );
        assert_eq!(store.name(idx).as_deref(), Some("second"));
        assert_eq!(
            store.validate_generation(idx, &snapshot.generation),
            Err(StoreError::Stale(idx))
        );
    }

    #[test]
    fn current_snapshot_replaces_in_place_as_modified() {
        let store = TheoryStore::default();
        let idx = store.insert(entry("first"));
        let snapshot = store.snapshot(idx).unwrap();

        assert_eq!(
            store.replace_if_current(&snapshot, entry("replacement")),
            Ok(idx)
        );
        let replacement = store.get(idx).unwrap();
        assert_eq!(replacement.typed_theory.name, "replacement");
        assert!(!replacement.primary);
    }

    #[test]
    fn failed_single_flight_build_can_be_retried() {
        let cell = RetryCell::<usize, &str>::new(None);
        let attempts = AtomicUsize::new(0);

        assert_eq!(
            cell.get_or_try_init(|| {
                attempts.fetch_add(1, Ordering::SeqCst);
                Err::<usize, _>("transient")
            }),
            Err("transient")
        );
        assert_eq!(
            cell.get_or_try_init(|| {
                attempts.fetch_add(1, Ordering::SeqCst);
                Ok::<_, &str>(7)
            }),
            Ok(7)
        );
        assert_eq!(
            cell.get_or_try_init(|| {
                attempts.fetch_add(1, Ordering::SeqCst);
                Ok::<_, &str>(8)
            }),
            Ok(7)
        );
        assert_eq!(attempts.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn seeded_single_flight_value_skips_build() {
        let cell = RetryCell::<usize, ()>::new(Some(7));
        assert_eq!(
            cell.get_or_try_init(|| panic!("seeded cell rebuilt")),
            Ok(7)
        );
    }

    #[test]
    fn concurrent_successful_build_is_single_flight() {
        use std::sync::mpsc;

        let cell = Arc::new(RetryCell::<usize, ()>::new(None));
        let attempts = Arc::new(AtomicUsize::new(0));
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();

        let first_cell = cell.clone();
        let first_attempts = attempts.clone();
        let first = std::thread::spawn(move || {
            first_cell
                .get_or_try_init(|| {
                    first_attempts.fetch_add(1, Ordering::SeqCst);
                    started_tx.send(()).unwrap();
                    release_rx.recv().unwrap();
                    Ok(7)
                })
                .unwrap()
        });
        started_rx.recv().unwrap();

        let second_cell = cell.clone();
        let second_attempts = attempts.clone();
        let second = std::thread::spawn(move || {
            second_cell
                .get_or_try_init(|| {
                    second_attempts.fetch_add(1, Ordering::SeqCst);
                    Ok(8)
                })
                .unwrap()
        });

        release_tx.send(()).unwrap();
        assert_eq!(first.join().unwrap(), 7);
        assert_eq!(second.join().unwrap(), 7);
        assert_eq!(attempts.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn concurrent_callers_share_a_failed_attempt_before_retry() {
        use std::sync::mpsc;

        let cell = Arc::new(RetryCell::<usize, &str>::new(None));
        let attempt = cell.attempt.lock().clone();
        let attempts = Arc::new(AtomicUsize::new(0));
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();

        let first_cell = cell.clone();
        let first_attempt = attempt.clone();
        let first_attempts = attempts.clone();
        let first = std::thread::spawn(move || {
            first_cell.run_attempt(first_attempt, || {
                first_attempts.fetch_add(1, Ordering::SeqCst);
                started_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                Err("transient")
            })
        });
        started_rx.recv().unwrap();

        let second_cell = cell.clone();
        let second_attempts = attempts.clone();
        let second = std::thread::spawn(move || {
            second_cell.run_attempt(attempt, || {
                second_attempts.fetch_add(1, Ordering::SeqCst);
                Ok(8)
            })
        });

        release_tx.send(()).unwrap();
        assert_eq!(first.join().unwrap(), Err("transient"));
        assert_eq!(second.join().unwrap(), Err("transient"));
        assert_eq!(attempts.load(Ordering::SeqCst), 1);
        assert_eq!(
            cell.get_or_try_init(|| {
                attempts.fetch_add(1, Ordering::SeqCst);
                Ok(7)
            }),
            Ok(7)
        );
        assert_eq!(attempts.load(Ordering::SeqCst), 2);
    }
}
