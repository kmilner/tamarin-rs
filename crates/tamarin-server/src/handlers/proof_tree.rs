// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Live proof-tree state — mirror of Haskell's `IncrementalProof` +
//! `applyProverAtPath`.
//!
//! Haskell's interactive UI keeps a mutable proof tree per lemma; user
//! clicks dispatch a `ProofMethod` at a path in that tree and the
//! result is spliced back in. Rust keeps each root lazy until first use and
//! shares materialised roots copy-on-write between theory versions.
//!
//! In the Rust port we model this with:
//!
//! - One lazy, copy-on-write [`ProofNode`] root per lemma.
//! - [`apply_at_path`]: navigate by case-name path, run the requested
//!   `ProofMethod` via `exec_proof_method`, replace that subtree's
//!   children, return the new root.
//!
//! The implementation is intentionally minimal: it doesn't yet drive
//! the full `run_proof_search` loop on click — that's the autoprove
//! button.  Each user-driven step applies exactly one method and
//! returns the resulting cases.  The proof can therefore stay "open"
//! until the user navigates / clicks again.

use std::collections::BTreeMap;
use std::sync::Arc;

use parking_lot::{Mutex, MutexGuard};

use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::solver::goals::{ranking_at_depth, GoalRanking};
use tamarin_theory::constraint::solver::proof_method::{
    exec_proof_method, finished_subterms, is_finished, ProofMethod,
};
use tamarin_theory::constraint::solver::search::{
    candidate_methods_with_expl, rollup_status, NodeStatus, ProofNode, ProofStatus,
};
use tamarin_theory::constraint::system::System;
use tamarin_theory::pretty_system::pretty_non_graph_system;
use tamarin_theory::theory::TheoryItem;

use crate::handlers::path_parse::{encode_sub_path, url_path_escape};

/// The immutable, system-free part of a replayed proof node.
///
/// Both the left-hand index and the source renderer use this lightweight
/// tree, leaving full systems lazy until an interactive proof route needs one.
#[derive(Debug)]
pub(crate) struct ProofIndexNode {
    pub method: ProofMethod,
    pub children: BTreeMap<String, ProofIndexNode>,
    pub annotated: bool,
    status: ProofStatus,
}

/// System-free result of replaying a stored proof. Both overview and source
/// rendering share it, so neither has to retain solver systems or replay the
/// same skeleton independently.
struct ProofSnapshot {
    root: Arc<ProofIndexNode>,
    body: std::sync::OnceLock<Arc<str>>,
}

#[derive(Clone)]
enum LemmaProofState {
    Lazy,
    Snapshot(Arc<ProofSnapshot>),
    // `System` uses thread-local mutation caches and is `Send` but not
    // `Sync`, so the shared root needs its own mutex rather than a bare
    // `Arc<ProofNode>`.
    Live(Arc<Mutex<ProofNode>>),
}

fn copy_on_write(root: &mut Arc<Mutex<ProofNode>>) -> &mut ProofNode {
    if Arc::get_mut(root).is_none() {
        let cloned = root.lock().clone();
        *root = Arc::new(Mutex::new(cloned));
    }
    Arc::get_mut(root)
        .expect("the copied root is uniquely owned")
        .get_mut()
}

impl ProofSnapshot {
    fn from_proof_node(node: &ProofNode) -> Self {
        Self {
            root: Arc::new(ProofIndexNode::from_proof_node(node)),
            body: std::sync::OnceLock::new(),
        }
    }

    fn body(&self) -> Arc<str> {
        self.body
            .get_or_init(|| {
                Arc::from(tamarin_theory::pretty_theory::pretty_proof_body(
                    self.root.as_ref(),
                ))
            })
            .clone()
    }
}

/// The exact data the interactive sub-proof renderer reads. Descendant trees
/// and child systems deliberately cannot escape the proof-state lock.
pub(crate) struct ProofSnippet {
    pub system: Option<System>,
    pub children: Vec<(String, bool)>,
}

impl ProofSnippet {
    fn from_proof_node(node: &ProofNode) -> Self {
        Self {
            system: node.annotated.then(|| node.sys.clone()),
            children: node
                .children
                .iter()
                .map(|(name, child)| (name.clone(), child.annotated))
                .collect(),
        }
    }
}

impl ProofIndexNode {
    fn from_proof_node(node: &ProofNode) -> Self {
        let children: BTreeMap<_, _> = node
            .children
            .iter()
            .map(|(name, child)| (name.clone(), Self::from_proof_node(child)))
            .collect();
        let status = children.values().fold(
            ProofStatus::from_step(&node.method, node.annotated),
            |status, child| status.combine(child.status),
        );
        Self {
            method: node.method.clone(),
            children,
            annotated: node.annotated,
            status,
        }
    }

    /// HS `getProofStatus = foldMap proofStepStatus`, restricted to the
    /// fields retained by the proof index snapshot.
    pub fn proof_status(&self) -> ProofStatus {
        self.status
    }
}

impl tamarin_theory::pretty_theory::ProofBody for ProofIndexNode {
    fn method(&self) -> &ProofMethod {
        &self.method
    }

    fn annotated(&self) -> bool {
        self.annotated
    }

    fn cases(&self) -> Vec<(&String, &Self)> {
        self.children.iter().collect()
    }
}

/// Each theory entry carries one of these. The retained session is the sole
/// theory-wide context owner; proof roots are materialised on first use.
/// Published states are read-only. Mutations are crate-private and operate on
/// one unpublished [`ProofState::fork`], so their expensive solver work needs
/// no optimistic generation/retry machinery.
pub struct ProofState {
    /// One independent lock per lemma. Replay may be expensive, but requests
    /// for unrelated lemmas never wait for it and concurrent requests for the
    /// same lemma share the result.
    by_lemma: BTreeMap<String, Mutex<LemmaProofState>>,
    pub(crate) session: Arc<tamarin_theory::prove::ProverSession>,
    #[cfg(test)]
    replay_calls: std::sync::atomic::AtomicUsize,
}

impl ProofState {
    /// Build the per-theory prover session. Per-lemma roots and contexts stay
    /// lazy until an interactive route asks for them.
    ///
    /// `maude_sig`: the signature this theory's Maude process loads its
    /// module from (`TheoryEntry::prover_maude_sig`) — `typed`'s signature
    /// from before the load's NDC join.
    ///
    /// `ndc_cache`: the theory's once-per-load NDC-checked intruder cache
    /// (`theory_io` ran `check_close_intr_rule` at load), injected into
    /// the session so it does not re-run the check. The borrowed handle is
    /// the same allocation the `TheoryEntry` holds.
    pub(crate) fn new(
        typed: &std::sync::Arc<tamarin_theory::theory::Theory>,
        maude_sig: tamarin_term::maude_sig::MaudeSig,
        maude_path: &str,
        cli_cut: Option<tamarin_theory::constraint::solver::context::CutStrategy>,
        ndc_cache: Option<&tamarin_theory::constraint::solver::context::IntrRuleCache>,
    ) -> Result<Self, String> {
        // Effective cut strategy — HS `closeTheory` precedence
        // (TheoryLoader.hs:742, :759-762): the CLI `--stop-on-trace` wins;
        // the theory's `configuration:` block is consulted only when
        // the flag is absent.  Steers the session's autoprove
        // (`runAutoProver`'s `apCut`) and interactive contexts.
        let config_block = typed.items.iter().find_map(|i| match i {
            TheoryItem::ConfigBlock(c) => Some(c),
            _ => None,
        });
        let cut = match cli_cut {
            Some(c) => c,
            None => match config_block {
                Some(cfg) => tamarin_theory::prove::config_block_options(cfg)?
                    .0
                    .unwrap_or(tamarin_theory::constraint::solver::context::CutStrategy::Dfs),
                None => tamarin_theory::constraint::solver::context::CutStrategy::Dfs,
            },
        };
        let maude = tamarin_term::maude_proc::MaudeHandle::start(maude_path, maude_sig)
            .map_err(|e| format!("maude start: {:?}", e))?;
        let session = tamarin_theory::prove::ProverSession::build_with_heuristic(
            typed.clone(),
            maude,
            None,
            tamarin_theory::prove::CliHeuristic::default(),
            cut,
            ndc_cache,
        )
        .map(Arc::new)
        .map_err(|e| format!("prover session: {e}"))?;
        let by_lemma = typed
            .lemmas()
            .map(|lemma| (lemma.name.clone(), Mutex::new(LemmaProofState::Lazy)))
            .collect();
        Ok(ProofState {
            by_lemma,
            session,
            #[cfg(test)]
            replay_calls: std::sync::atomic::AtomicUsize::new(0),
        })
    }

    /// Apply a `ProofMethod` at `path` in the lemma's proof tree.
    /// Returns the new node status, or an error string for malformed
    /// inputs.
    pub(crate) fn apply_at_path(
        &self,
        lemma: &str,
        path: &[String],
        method: ProofMethod,
    ) -> Result<NodeStatus, String> {
        let ctx = self
            .session
            .context_for_lemma(lemma)
            .map_err(|e| format!("proof context: {e}"))?;
        // Mutation happens only on an unpublished fork. Keep the lemma slot
        // locked, but release the root shared between forks before running a
        // potentially long solver step. `System` cloning is copy-on-write.
        let Some(mut state) = self.live_state(lemma)? else {
            return Err(format!("unknown lemma: {lemma}"));
        };
        let LemmaProofState::Live(root) = &mut *state else {
            return Err(format!("unknown lemma: {lemma}"));
        };
        let root_guard = root.lock();
        let selected =
            navigate_at(&root_guard, path).ok_or_else(|| format!("path not found: {:?}", path))?;
        if !selected.annotated {
            return Err(format!("no annotated system at path: {:?}", path));
        }
        let selected_sys = selected.sys.clone();
        drop(root_guard);
        tamarin_theory::constraint::solver::trace::trace_state_at_path(&selected_sys, path);
        let cases = exec_proof_method(&ctx, &method, &selected_sys)
            .map_err(|error| format!("proof context: {error}"))?;
        let cases = cases.ok_or_else(|| format!("method {:?} not applicable", method))?;
        let (status, children) = if cases.is_empty() {
            (empty_case_status(&method), BTreeMap::new())
        } else {
            let mut children = BTreeMap::new();
            for (name, sys) in cases {
                // Eagerly classify each child as finished / open.
                let (status, leaf_method) = match is_finished(&ctx, &sys)
                    .map_err(|error| format!("proof context: {error}"))?
                {
                    Some(r) => {
                        let s = match &r {
                            tamarin_theory::constraint::solver::proof_method::Result::Solved =>
                                NodeStatus::Solved,
                            tamarin_theory::constraint::solver::proof_method::Result::Contradictory(_) =>
                                NodeStatus::Contradictory,
                            tamarin_theory::constraint::solver::proof_method::Result::Unfinishable =>
                                NodeStatus::Unfinishable,
                        };
                        (s, ProofMethod::Finished(r))
                    }
                    None => (NodeStatus::Sorry, ProofMethod::Sorry(None)),
                };
                let child = ProofNode {
                    method: leaf_method,
                    sys,
                    children: BTreeMap::new(),
                    status,
                    annotated: true,
                };
                children.insert(name, child);
            }
            (rollup_status(&children), children)
        };
        let root = copy_on_write(root);
        let node = navigate_mut(root, path).expect("path was checked before copy-on-write");
        node.method = method;
        node.children = children;
        node.status = status;
        recompute_ancestor_statuses(root, path);
        Ok(status)
    }

    /// Replace one existing proof node with `sorry /* removed */`. A root is
    /// re-annotated from its retained initial system, matching `focus []`;
    /// nested unannotated nodes remain unresolved. Unlike generic method
    /// application this needs no context, ranking, or system clone.
    pub(crate) fn mark_removed_at_path(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Result<bool, String> {
        let Some(mut state) = self.live_state(lemma)? else {
            return Ok(false);
        };
        let LemmaProofState::Live(root) = &mut *state else {
            return Ok(false);
        };
        let root_guard = root.lock();
        let Some(selected) = navigate_at(&root_guard, path) else {
            return Ok(false);
        };
        if !selected.annotated && !path.is_empty() {
            return Ok(false);
        }
        drop(root_guard);
        let root = copy_on_write(root);
        let node = navigate_mut(root, path).expect("path was checked before copy-on-write");
        node.method = ProofMethod::Sorry(Some("removed".to_string()));
        node.children.clear();
        node.status = NodeStatus::Sorry;
        node.annotated = true;
        recompute_ancestor_statuses(root, path);
        Ok(true)
    }

    /// Graft `subtree` into the lemma's proof tree at `path`, replacing
    /// whatever subproof currently sits there; the REST of the tree is
    /// untouched.  Mirrors HS `focus path prover`
    /// (`lib/theory/src/Theory/Proof.hs:602-612`): the prover result is
    /// spliced back at `path` via `modifyAtPath`, and `focus [] prover =
    /// prover` makes the empty path replace the whole proof — our
    /// `path == []` arm.  Errors mirror `modifyAtPath`'s `Nothing` (the
    /// path does not exist), which HS surfaces as prover failure.
    ///
    pub(crate) fn graft_at_path(
        &self,
        lemma: &str,
        path: &[String],
        subtree: ProofNode,
    ) -> Result<(), String> {
        let Some(mut state) = self.live_state(lemma)? else {
            return Err(format!("unknown lemma: {lemma}"));
        };
        let LemmaProofState::Live(root) = &mut *state else {
            return Err(format!("unknown lemma: {lemma}"));
        };
        let root_guard = root.lock();
        let selected =
            navigate_at(&root_guard, path).ok_or_else(|| format!("path not found: {:?}", path))?;
        if !selected.annotated {
            return Err(format!("no annotated system at path: {:?}", path));
        }
        drop(root_guard);
        let root = copy_on_write(root);
        if path.is_empty() {
            *root = subtree;
            return Ok(());
        }
        let node = navigate_mut(root, path).expect("path was checked before copy-on-write");
        *node = subtree;
        recompute_ancestor_statuses(root, path);
        Ok(())
    }

    /// Fork this proof state: share the same session and immutable proof-index
    /// snapshots and materialised roots. A root is cloned only when one fork
    /// first mutates it; unvisited full systems remain lazy in both forks.
    /// Mirrors Haskell `modifyTheory`'s value-typed
    /// `IncrementalProof` semantics: each version-fork sees the source
    /// tree at the moment of fork, then evolves independently.
    pub(crate) fn fork(&self) -> Self {
        let by_lemma = self
            .by_lemma
            .iter()
            .map(|(name, state)| (name.clone(), Mutex::new(state.lock().clone())))
            .collect();
        ProofState {
            by_lemma,
            session: self.session.clone(),
            #[cfg(test)]
            replay_calls: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// Build a session for a modified theory while preserving the proof roots
    /// of every surviving lemma. Deletion is rare, so replay lazy roots against
    /// the old theory first; replaying them against the edited theory could
    /// change proofs that depend on a removed `[reuse]` lemma.
    pub(crate) fn rebase_onto(
        &self,
        typed: &Arc<tamarin_theory::theory::Theory>,
        maude_sig: tamarin_term::maude_sig::MaudeSig,
        maude_path: &str,
        cli_cut: Option<tamarin_theory::constraint::solver::context::CutStrategy>,
        ndc_cache: Option<&tamarin_theory::constraint::solver::context::IntrRuleCache>,
    ) -> Result<Self, String> {
        let mut roots = BTreeMap::new();
        for lemma in typed.lemmas() {
            let Some(slot) = self.by_lemma.get(&lemma.name) else {
                continue;
            };
            let state = slot.lock();
            let root = match &*state {
                LemmaProofState::Live(root) => root.clone(),
                LemmaProofState::Lazy | LemmaProofState::Snapshot(_) => {
                    let Some(root) = self.replay_interactive_root(&lemma.name)? else {
                        continue;
                    };
                    Arc::new(Mutex::new(root))
                }
            };
            roots.insert(lemma.name.clone(), root);
        }
        let rebased = Self::new(typed, maude_sig, maude_path, cli_cut, ndc_cache)?;
        for (name, root) in roots {
            if let Some(slot) = rebased.by_lemma.get(&name) {
                *slot.lock() = LemmaProofState::Live(root);
            }
        }
        Ok(rebased)
    }

    /// Read a root without causing stored-proof replay or allocating its
    /// initial system. Used by overview panes so opening a rules/source page
    /// does not retain every lemma's proof system.
    #[cfg(test)]
    pub(crate) fn peek_root(&self, lemma: &str) -> Option<ProofNode> {
        let state = self.by_lemma.get(lemma)?.lock();
        match &*state {
            LemmaProofState::Live(root) => Some(root.lock().clone()),
            _ => None,
        }
    }

    #[cfg(test)]
    fn get_root(&self, lemma: &str) -> Result<Option<ProofNode>, String> {
        let Some(state) = self.live_state(lemma)? else {
            return Ok(None);
        };
        let LemmaProofState::Live(root) = &*state else {
            unreachable!("live_state materialises its result")
        };
        let root = root.lock().clone();
        Ok(Some(root))
    }

    #[cfg(test)]
    fn state_count(&self, predicate: impl Fn(&LemmaProofState) -> bool) -> usize {
        self.by_lemma
            .values()
            .filter(|state| predicate(&state.lock()))
            .count()
    }

    #[cfg(test)]
    fn with_live_root_mut(&self, lemma: &str, f: impl FnOnce(&mut ProofNode)) {
        let mut state = self.by_lemma.get(lemma).expect("lemma").lock();
        let LemmaProofState::Live(root) = &mut *state else {
            panic!("lemma root is not materialised");
        };
        f(copy_on_write(root));
    }

    /// Return the tree needed by the overview's proof index.
    ///
    /// A live root wins. Otherwise a stored skeleton is checked once, stripped
    /// of every constraint system, and cached in its lightweight form. Lemmas
    /// without a stored proof return `None`, preserving the fresh `by sorry`
    /// fast path without allocating their initial system.
    pub(crate) fn proof_index_root(
        &self,
        lemma: &str,
    ) -> Result<Option<Arc<ProofIndexNode>>, String> {
        let Some(lemma_item) = self.session.theory().lookup_lemma(lemma) else {
            return Ok(None);
        };
        let slot = self
            .by_lemma
            .get(lemma)
            .expect("the proof-state map covers every session lemma");
        let mut state = slot.lock();
        match &*state {
            LemmaProofState::Live(root) => Ok(Some(Arc::new(ProofIndexNode::from_proof_node(
                &root.lock(),
            )))),
            LemmaProofState::Snapshot(snapshot) if lemma_item.proof.is_some() => {
                Ok(Some(snapshot.root.clone()))
            }
            LemmaProofState::Snapshot(_) => Ok(None),
            LemmaProofState::Lazy if lemma_item.proof.is_none() => Ok(None),
            LemmaProofState::Lazy => {
                let Some(snapshot) = self.snapshot_locked(lemma, &mut state)? else {
                    return Ok(None);
                };
                Ok(Some(snapshot.root.clone()))
            }
        }
    }

    /// Render a lemma proof without cloning or retaining any solver systems.
    pub(crate) fn proof_body(&self, lemma: &str) -> Result<Option<Arc<str>>, String> {
        if self.session.theory().lookup_lemma(lemma).is_none() {
            return Ok(None);
        }
        let slot = self
            .by_lemma
            .get(lemma)
            .expect("the proof-state map covers every session lemma");
        let mut state = slot.lock();
        match &*state {
            LemmaProofState::Snapshot(snapshot) => Ok(Some(snapshot.body())),
            LemmaProofState::Live(root) => {
                let root = root.lock();
                Ok(Some(Arc::from(
                    tamarin_theory::pretty_theory::pretty_proof_body(&*root),
                )))
            }
            LemmaProofState::Lazy => {
                let Some(snapshot) = self.snapshot_locked(lemma, &mut state)? else {
                    return Ok(None);
                };
                Ok(Some(snapshot.body()))
            }
        }
    }

    /// Clone only the selected system and immediate child metadata.
    pub(crate) fn get_snippet_at(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Result<Option<ProofSnippet>, String> {
        self.filter_map_node_at(lemma, path, |node| {
            Some(ProofSnippet::from_proof_node(node))
        })
    }

    /// Read the selected method for page titles without cloning its subtree.
    pub(crate) fn get_method_at(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Result<Option<ProofMethod>, String> {
        self.filter_map_node_at(lemma, path, |node| Some(node.method.clone()))
    }

    /// Lock and materialise a known lemma in one lookup.
    fn live_state(&self, lemma: &str) -> Result<Option<MutexGuard<'_, LemmaProofState>>, String> {
        let Some(slot) = self.by_lemma.get(lemma) else {
            return Ok(None);
        };
        let mut state = slot.lock();
        self.materialize_locked(lemma, &mut state)?;
        Ok(Some(state))
    }

    fn materialize_locked(&self, lemma: &str, state: &mut LemmaProofState) -> Result<(), String> {
        if matches!(state, LemmaProofState::Live(_)) {
            return Ok(());
        }
        let Some(root) = self.replay_interactive_root(lemma)? else {
            return Err(format!("unknown lemma: {lemma}"));
        };
        *state = LemmaProofState::Live(Arc::new(Mutex::new(root)));
        Ok(())
    }

    /// Replay and cache the system-free representation of a lazy proof.
    fn snapshot_locked(
        &self,
        lemma: &str,
        state: &mut LemmaProofState,
    ) -> Result<Option<Arc<ProofSnapshot>>, String> {
        if let LemmaProofState::Snapshot(snapshot) = state {
            return Ok(Some(snapshot.clone()));
        }
        let LemmaProofState::Lazy = state else {
            return Ok(None);
        };
        let Some((root, _)) = self.replay_root(lemma)? else {
            return Ok(None);
        };
        let snapshot = Arc::new(ProofSnapshot::from_proof_node(&root));
        *state = LemmaProofState::Snapshot(snapshot.clone());
        Ok(Some(snapshot))
    }

    fn replay_interactive_root(&self, lemma: &str) -> Result<Option<ProofNode>, String> {
        self.replay_root(lemma).map(|replayed| {
            replayed.map(|(mut root, has_stored_proof)| {
                // The interactive tree historically treats a lemma with no
                // parsed skeleton as an open root (so its action links are
                // enabled). Batch replay labels the equivalent bare leaf
                // `Sorry`; retain the web status while leaving genuine
                // stored-proof replay untouched.
                prepare_interactive_root(&mut root, has_stored_proof);
                root
            })
        })
    }

    fn replay_root(&self, lemma: &str) -> Result<Option<(ProofNode, bool)>, String> {
        #[cfg(test)]
        self.replay_calls
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let Some(lemma_item) = self.session.theory().lookup_lemma(lemma) else {
            return Ok(None);
        };
        let has_stored_proof = lemma_item.proof.is_some();
        tamarin_theory::prove::check_and_extend_lemma_in_session(&self.session, lemma, usize::MAX)
            .map(|root| Some((root, has_stored_proof)))
            .map_err(|error| format!("initial proof for {lemma}: {error}"))
    }

    pub(crate) fn template_context(&self) -> &ProofContext {
        self.session.template_context()
    }

    pub(crate) fn context_for_lemma(&self, lemma: &str) -> Result<ProofContext, String> {
        self.session
            .context_for_lemma(lemma)
            .map_err(|e| format!("proof context: {e}"))
    }

    pub(crate) fn context_for_sources(
        &self,
        kind: tamarin_theory::constraint::system::SourceKind,
    ) -> Result<ProofContext, String> {
        self.session
            .context_for_sources(kind)
            .map_err(|error| format!("proof context: {error}"))
    }

    /// Find the system at the given path (root if empty).
    pub(crate) fn get_system_at(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Result<Option<tamarin_theory::constraint::system::System>, String> {
        self.filter_map_node_at(lemma, path, |node| node.annotated.then(|| node.sys.clone()))
    }

    fn filter_map_node_at<R>(
        &self,
        lemma: &str,
        path: &[String],
        f: impl FnOnce(&ProofNode) -> Option<R>,
    ) -> Result<Option<R>, String> {
        let Some(state) = self.live_state(lemma)? else {
            return Ok(None);
        };
        let LemmaProofState::Live(root) = &*state else {
            unreachable!("live_state materialises its result")
        };
        let root = root.lock();
        let Some(node) = navigate_at(&root, path) else {
            return Ok(None);
        };
        Ok(f(node))
    }
}

fn prepare_interactive_root(root: &mut ProofNode, has_stored_proof: bool) {
    if !has_stored_proof && matches!(root.method, ProofMethod::Sorry(_)) && root.children.is_empty()
    {
        root.status = NodeStatus::Open;
    }
}

/// Walk `path`'s case names down from `node` (the node itself for an empty
/// path); `None` when a segment names no child.
pub(crate) fn navigate_at<'a>(node: &'a ProofNode, path: &[String]) -> Option<&'a ProofNode> {
    let mut cur = node;
    for seg in path {
        cur = cur.children.get(seg)?;
    }
    Some(cur)
}

/// Port of HS `getProofPaths` (`Web/Theory.hs:2209-2213`):
///
/// ```haskell
/// getProofPaths proof = ([], psMethod . root $ proof) : go proof
///   where
///     go = concatMap paths . M.toList . children
///     paths (lbl, prf) = ([lbl], psMethod . root $ prf)
///                        : map (first (lbl:)) (go prf)
/// ```
///
/// Pre-order over the lightweight proof index. Each entry pairs its case-name
/// path with its proof method. `BTreeMap` order matches Haskell's `M.toList`.
pub(crate) fn get_proof_index_paths(root: &ProofIndexNode) -> Vec<(Vec<String>, ProofMethod)> {
    let mut out = vec![(Vec::new(), root.method.clone())];
    proof_index_paths_go(root, &mut Vec::new(), &mut out);
    out
}

fn proof_index_paths_go(
    node: &ProofIndexNode,
    prefix: &mut Vec<String>,
    out: &mut Vec<(Vec<String>, ProofMethod)>,
) {
    for (name, child) in &node.children {
        prefix.push(name.clone());
        out.push((prefix.clone(), child.method.clone()));
        proof_index_paths_go(child, prefix, out);
        prefix.pop();
    }
}

/// Port of HS `isInterestingMethod` (`Web/Theory.hs:1968-1972`): the proof
/// methods that `nextSmartThyPath`/`prevSmartThyPath` stop on — an open
/// `Sorry` leaf, or a `Finished` `Solved`/`Unfinishable` terminal.
pub(crate) fn is_interesting_method(m: &ProofMethod) -> bool {
    use tamarin_theory::constraint::solver::proof_method::Result as R;
    matches!(
        m,
        ProofMethod::Sorry(_)
            | ProofMethod::Finished(R::Solved)
            | ProofMethod::Finished(R::Unfinishable)
    )
}

fn navigate_mut<'a>(node: &'a mut ProofNode, path: &[String]) -> Option<&'a mut ProofNode> {
    let mut cur = node;
    for seg in path {
        cur = cur.children.get_mut(seg)?;
    }
    Some(cur)
}

/// Refresh the aggregate status of every strict ancestor of `path`, deepest
/// first. The selected node already carries the result of the mutation.
fn recompute_ancestor_statuses(root: &mut ProofNode, path: &[String]) {
    let Some((child_name, tail)) = path.split_first() else {
        return;
    };
    let Some(child) = root.children.get_mut(child_name) else {
        return;
    };
    recompute_ancestor_statuses(child, tail);
    root.status = rollup_status(&root.children);
}

/// Status of an executed method whose case map is empty. An explicit sorry
/// stays incomplete; every real proof method closed the branch.
fn empty_case_status(method: &ProofMethod) -> NodeStatus {
    match method {
        ProofMethod::Sorry(_) => NodeStatus::Sorry,
        ProofMethod::Finished(result) => {
            tamarin_theory::constraint::solver::search::node_status_of(result)
        }
        ProofMethod::Simplify | ProofMethod::SolveGoal(_) | ProofMethod::Induction => {
            NodeStatus::Contradictory
        }
        ProofMethod::Invalidated => NodeStatus::Open,
    }
}

/// Render the per-path sub-proof snippet.  Mirrors Haskell's
/// `subProofSnippet` (`src/Web/Theory.hs:519-617`; the methods section follows
/// `prettyApplicableProofMethods`, `Web/Theory.hs:519-617, see line 546`).  Emits:
///
///   1. The Applicable Proof Methods section — delegated to
///      `write_applicable_methods`.  It emits the numbered method links
///      together with the `a.`/`b.`/`s.` autoprove links, OR, when no method
///      applies, the `<h3>Constraint System is Solved/Unfinishable</h3>`
///      fallback.
///   2. `<h3>Constraint system</h3>`
///      `<dynamic-graph graphSrc="…">` (when the system has nodes/edges)
///      `<div class="preformatted sequent">…prettyNonGraphSystem…</div>`
///   3. `<h3>N sub-case(s)</h3>`
///      `<h4>case <name></h4>` + `<static-graph graphSrc="…">` per child.
pub(crate) fn render_sub_proof_snippet(
    idx: usize,
    lemma: &str,
    proof_path: &[String],
    snippet: &ProofSnippet,
    ctx: &ProofContext,
) -> Result<String, String> {
    // HS renders the whole `subProofSnippet` through the `HtmlDoc Doc`
    // transformer + `renderHtmlDoc` (`htmlThyPath`'s `pp`): every fragment is
    // entity-escaped + span-marked and postprocessed once.  Build HtmlDoc mode
    // for the whole pane (so the sequent + method keywords render spanned).
    let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
    // HS `subProofSnippet` (`Web/Theory.hs:530-531`): an unannotated node
    // (`psInfo == Nothing` — a close-time-replay divergence kept verbatim
    // via `noSystemPrf`) has NO constraint system to render; HS emits the
    // single fallback line instead of the methods/sequent/sub-case blocks:
    //   text $ "no annotated constraint system / " ++ nCases ++ " sub-case(s)"
    // RS's unannotated `ProofNode` carries an empty sentinel `sys`
    // (replay.rs `parsed_to_unannotated`) that MUST NOT be rendered.
    let Some(system) = snippet.system.as_ref() else {
        return Ok(tamarin_theory::pretty_hpj::postprocess_html(&format!(
            "no annotated constraint system / {} sub-case(s)",
            snippet.children.len()
        )));
    };
    let url_path = encode_sub_path(proof_path);
    // HS `subProofSnippet = vcat [ …proofMethods…, text "", <h3>Constraint
    // system</h3>, [dynamic-graph], sequent, <h3>N sub-case(s)</h3>, …subCases ]`
    // — each element is a `vcat` line; join with `\n`, then postprocess once.
    let mut parts: Vec<String> = Vec::new();
    // Applicable Proof Methods (ranked at this node's proof depth, HS
    // `subProofSnippet` uses `length proofPath`).
    write_applicable_methods(
        &mut parts,
        idx,
        lemma,
        &url_path,
        proof_path.len(),
        system,
        ctx,
    )?;
    // HS `text ""` — a blank line before the Constraint-system header.
    parts.push(String::new());
    parts.push("<h3>Constraint system</h3>".to_string());
    if has_graph_content(system) {
        // HS `refDotInteractiveDynamicPath` → `<dynamic-graph graphSrc=…>`
        // pointing at `InteractiveDotGraphR` = the `intdot` route (the HTML
        // shell that in turn fetches `interactive-graph-def`), NOT the raw
        // DOT route directly (`Web/Theory.hs:180-181`).
        let src = format!(
            "/thy/trace/{idx}/intdot/proof/{lemma}{path}",
            idx = idx,
            lemma = url_path_escape(lemma),
            path = url_path,
        );
        parts.push(format!(
            "<dynamic-graph graphSrc=\"{}\"></dynamic-graph>",
            src
        ));
    }
    // HS `preformatted (Just "sequent") (prettyNonGraphSystem se)` =
    // `withTag "div" [("class","preformatted sequent")] …` (no `<pre>`); the
    // sequent renders escaped + span-marked under the guard.
    parts.push(format!(
        "<div class=\"preformatted sequent\">{}</div>",
        pretty_non_graph_system(system)
    ));
    // Sub-cases.
    let n_cases = snippet.children.len();
    parts.push(format!("<h3>{} sub-case(s)</h3>", n_cases));
    for (case_name, child_annotated) in &snippet.children {
        let mut child_path = proof_path.to_vec();
        child_path.push(case_name.clone());
        let child_url = encode_sub_path(&child_path);
        // HS `withTag "h4" [] (text "Case" <-> text name)` = `<h4>Case NAME</h4>`.
        parts.push(format!(
            "<h4>Case {}</h4>",
            tamarin_theory::pretty_hpj::escape_html_entities(case_name)
        ));
        // HS `refSubCase` (`Web/Theory.hs:612-617`): an unannotated child
        // (`psInfo == Nothing`) gets `text "no proof state available"`
        // instead of the static-graph reference.
        if !child_annotated {
            parts.push("no proof state available".to_string());
            continue;
        }
        // HS `refDotInteractiveStaticPath` → `<static-graph graphSrc=…>`.
        let src = format!(
            "/thy/trace/{idx}/intdot/proof/{lemma}{path}",
            idx = idx,
            lemma = url_path_escape(lemma),
            path = child_url,
        );
        parts.push(format!(
            "<static-graph graphSrc=\"{}\"></static-graph>",
            src
        ));
    }
    Ok(tamarin_theory::pretty_hpj::postprocess_html(
        &parts.join("\n"),
    ))
}

/// Mirror of Haskell `nonEmptyGraph` (`System.hs:1928-1932`):
///
/// ```text
/// nonEmptyGraph sys = not $
///     M.null sNodes && null (unsolvedActionAtoms sys) &&
///     null (unsolvedChains sys) &&
///     S.null sEdges && S.null sLessAtoms
/// ```
///
/// i.e. the dotted graph is non-empty iff ANY of: nodes, unsolved
/// action atoms, unsolved chains, edges, or less-atoms is present.
/// `unsolvedActionAtoms` / `unsolvedChains` are the unsolved-status
/// `ActionG` / `ChainG` goals (`System.hs:1569-1573,1602-1606`).
fn has_graph_content(sys: &System) -> bool {
    if !sys.nodes.is_empty() || !sys.edges.is_empty() || !sys.less_atoms.is_empty() {
        return true;
    }
    sys.goals
        .iter()
        .any(|(g, st)| !st.solved && (g.is_action() || g.is_chain()))
}

fn write_applicable_methods(
    out: &mut Vec<String>,
    idx: usize,
    lemma: &str,
    url_path: &str,
    depth: usize,
    sys: &System,
    ctx: &ProofContext,
) -> Result<(), String> {
    use tamarin_theory::pretty_hpj::{self as hpj, Doc};
    // The ranking used at this proof depth (HS `subProofSnippet`:
    // `ranking = useHeuristic heuristic (length proofPath)`,
    // `Web/Theory.hs:606-608`).
    let ranking = ranking_at_depth(Some(ctx), depth);
    // Match Haskell `rankProofMethods` (`ProofMethod.hs:519-534`):
    //   stoppingMethod = Finished <$> isFinished ctxt sys
    //   in execMethods $ maybe proofMethods ((:[]) . (,"")) stoppingMethod
    // When `isFinished` yields a verdict the WHOLE method list is replaced
    // by the single stopping method `[Finished r]` (and `execProofMethod
    // (Finished _) = Just M.empty` always survives the `execMethods`
    // filter).  Otherwise the list is `proofMethods` (Simplify / Induction
    // / SolveGoal), filtered by `execProofMethod`.  In Rust,
    // `candidate_methods` is that un-filtered `proofMethods` list (used by
    // the search loop which tries each in order); for the UI we filter via
    // `exec_proof_method` so the user-visible numbering matches the actual
    // click semantics.
    // Each entry is `(method, expl)` — `expl` is HS's `rankProofMethods`
    // explanation string (`"nr. N …"` for SolveGoal, `""` otherwise),
    // rendered by `prettyPM` as a trailing `// <expl>` line comment.
    // `candidate_methods_with_expl` performs the terminal check itself, so a
    // finished system yields its one `Finished` method without a duplicate
    // contradiction sweep here.
    let mut methods = Vec::new();
    for candidate in
        candidate_methods_with_expl(sys, ctx, depth).map_err(|error| error.to_string())?
    {
        // HS-faithful WHNF-depth applicability (Web/Theory.hs:546-552 via
        // ProofMethod.hs:282-299, see line 298). Must stay in lockstep with
        // `theory::apply_method`'s method-number filter.
        if tamarin_theory::constraint::solver::proof_method::is_applicable_for_display(
            ctx,
            &candidate.0,
            sys,
        )
        .map_err(|error| error.to_string())?
        {
            methods.push(candidate);
        }
    }
    if methods.is_empty() {
        // Mirror Haskell `prettyApplicableProofMethods` (`Web/Theory.hs:546-548`):
        //   [] | finishedSubterms ctxt sys -> "Constraint System is Solved"
        //   []                             -> "Constraint System is Unfinishable"
        // We only reach here when `is_finished` returned `None` (the
        // `Some` case produced a non-empty `[Finished r]` above), so the
        // Solved/Unfinishable choice MUST come from `finished_subterms`
        // exactly as HS does — not from `is_finished` (which is `None`
        // here and would always pick "Solved").
        let solved = finished_subterms(ctx, sys);
        if solved {
            out.push("<h3>Constraint System is Solved</h3>".to_string());
        } else {
            out.push("<h3>Constraint System is Unfinishable</h3>".to_string());
        }
        return Ok(());
    }
    // HS `subProofSnippet` (`Web/Theory.hs:550-551`):
    //   withTag "h3" [] (text "Applicable Proof Methods:" <-> comment_ (goalRankingName ranking))
    // `comment_` wraps the ranking name in an `hl_comment` span (identity in
    // plain mode); the name text is entity-escaped by `Doc::text`.
    let h3 = Doc::text("Applicable Proof Methods:")
        .beside_sp(hpj::comment_(&ranking.ranking_name()))
        .render();
    out.push(format!("<h3>{h3}</h3>"));
    // HS `preformatted (Just "methods") (numbered' $ zipWith prettyPM [1..] pms)`
    // = `withTag "div" [("class","preformatted methods")] …` (no `<pre>`).
    // Mirror Haskell `Web.Theory.subProofSnippet` (`Web/Theory.hs:599-603`):
    // each ranked method N (1-based) emits
    //   <a class="internal-link proof-method"
    //      href="/thy/trace/<idx>/main/method/<lemma>/<N>/<sub>">label</a>
    // The frontend's `mainDisplay.applyProofMethod` keyboard shortcuts
    // (1..9) target `div.methods a.internal-link`, and the click handler
    // for `internal-link` posts the URL via `server.handleJson` —
    // landing on our `/main/method/...` route which dispatches to
    // `theory::apply_method` and returns a `{redirect}`.
    // HS lays the whole list out as ONE HtmlDoc (`numbered' $ zipWith
    // prettyPM [1..] pms`, Web/Theory.hs:519-617, see line 552): each item is
    // `flushRight nW (show i) <> ". " <> (link (prettyProofMethod m) <->
    // lineComment_ expl)` — so the method text wraps (a) at HTML-ENTITY
    // fill widths (renderHtmlDoc), (b) beside-shifted by the `N. ` prefix
    // (nW+2 cols), and (c) with the trailing `// expl` comment
    // participating in the last line's fits check.  Reproduce that layout
    // per item: build the method Doc under the entity-width guard and lay
    // it with `render_at(100, 67, nW+2)` (the beside-shift budget), then
    // split the never-wrapped `<->`-joined comment back off to place the
    // `</a>` boundary.  (Continuation-line indent bytes and the blank line
    // `numbered'` inserts between items are whitespace the parity gate
    // canonicalizes; the break POSITIONS are what must match.)
    // HS `numbered' $ zipWith prettyPM [1..] pms` (Web/Theory.hs:519-617, see line 552):
    //   pp (i, d) = text (flushRight nW (show i)) <> text ". " <> d
    //   d        = withTag "a" [("class",…),("href",…)] (prettyProofMethod m)
    //              <-> (if null expl then emptyDoc else lineComment_ expl)
    // and `numbered'` separates the items by a blank line (`intersperse (text "")`).
    // Each item is built as ONE Doc (so the `N. ` prefix beside-shifts a wrapped
    // method's continuation lines, the method carries its `hl_keyword` span, and
    // the trailing `// expl` comment participates in the fill), then rendered
    // under the active HtmlDoc guard.
    let nw = methods.len().to_string().len();
    let mut method_blocks: Vec<String> = Vec::with_capacity(methods.len());
    for (i, (m, expl)) in methods.iter().enumerate() {
        let nr = i + 1;
        let href = format!(
            "/thy/trace/{idx}/main/method/{lemma}/{nr}{path}",
            idx = idx,
            lemma = url_path_escape(lemma),
            nr = nr,
            path = url_path
        );
        let link = hpj::with_tag(
            "a",
            &[("class", "internal-link proof-method"), ("href", &href)],
            tamarin_theory::pretty_theory::pretty_proof_method_doc(m),
        );
        let item = if expl.is_empty() {
            link
        } else {
            // `<-> lineComment_ expl`.
            link.beside_sp(hpj::line_comment_(expl))
        };
        let prefix = format!("{:>nw$}. ", nr);
        method_blocks.push(Doc::text(prefix).beside(item).render());
    }
    // `numbered'` blank-line separator → join item blocks with a blank line.
    out.push(format!(
        "<div class=\"preformatted methods\">{}</div>",
        method_blocks.join("\n\n")
    ));
    // Autoprove menu links (a./b./[o.]/s.) — self-contained block.
    write_autoprove_links(out, idx, &url_path_escape(lemma), url_path, ctx);
    Ok(())
}

/// Emit the `a.`/`b.`/`[o.]`/`s.` autoprove menu links that trail the
/// numbered method list — a faithful port of HS `subProofSnippet`'s
/// `autoProverLinks` (`Web/Theory.hs:553-597`), in HS order a, b, [o], s.
/// Each `AutoProverR tidx cut bound oracleBool path` renders as
///   /thy/trace/<idx>/autoprove/<cut>/<bound>/<oracleBool>/<path>
/// with cut ∈ {idfs=CutDFS, characterize=CutNothing}; `AutoProverAllR`
/// omits the oracle flag.  `linkToPath` prepends the `internal-link`
/// class (the gate sorts class tokens, so ordering is immaterial).
/// `lemma_esc` is the already-`url_path_escape`d lemma segment.
fn write_autoprove_links(
    out: &mut Vec<String>,
    idx: usize,
    lemma_esc: &str,
    url_path: &str,
    ctx: &ProofContext,
) {
    use tamarin_theory::pretty_hpj as hpj;
    let l = lemma_esc;
    let p = url_path;
    let bound = 5; // HS `fromMaybe 5 (apBound ti.autoProver)` — default depth bound.
                   // HS `autoProverLinks` (Web/Theory.hs:563-597) wraps each link's visible
                   // text in `keyword_` — an `hl_keyword` span in HtmlDoc mode, plain text
                   // otherwise.  `kw` renders that span under the active guard.  The line is
                   // assembled by `hsep` (single-space separators); the `b.`/`s.` suffixes are
                   // separate `text " …"` literals that BEGIN with a space (`boundDesc`,
                   // `allProve`), so `hsep`'s separator space PLUS the literal's leading space
                   // give the TWO spaces before "with"/"for".  `allProve = " for all lemmas "`
                   // also has a TRAILING space.  These are matched verbatim here (confirmed
                   // against the HS oracle).
    let kw = |s: &str| hpj::keyword_(s).render();
    // a. autoprove  (A. for all solutions)   [nameSuffix = emptyDoc]
    out.push(format!(
        "a. <a class=\"internal-link autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/False/proof/{l}{p}\">{ap}</a> \
         (A. <a class=\"internal-link characterization\" href=\"/thy/trace/{idx}/autoprove/characterize/0/False/proof/{l}{p}\">{fas}</a>)",
        ap = kw("autoprove"), fas = kw("for all solutions"),
    ));
    // b. bounded autoprove  (B. for all solutions)  with proof-depth bound N
    out.push(format!(
        "b. <a class=\"internal-link bounded-autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/{bound}/False/proof/{l}{p}\">{ap}</a> \
         (B. <a class=\"internal-link bounded-characterization\" href=\"/thy/trace/{idx}/autoprove/characterize/{bound}/False/proof/{l}{p}\">{fas}</a>)  with proof-depth bound {bound}",
        ap = kw("autoprove"), fas = kw("for all solutions"),
    ));
    // o. oracle autoprove — only when the heuristic uses an oracle
    // (`nameSuffix = "until oracle returns nothing"`, no leading space, so a
    // single hsep separator).
    if uses_oracle(ctx) {
        out.push(format!(
            "o. <a class=\"internal-link oracle-autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/True/proof/{l}{p}\">{ap}</a> until oracle returns nothing",
            ap = kw("autoprove"),
        ));
    }
    // s. autoprove for all lemmas  (S. for all solutions)  for all lemmas<trailing space>
    out.push(format!(
        "s. <a class=\"internal-link autoprove-all\" href=\"/thy/trace/{idx}/autoproveAll/idfs/0/proof/{l}{p}\">{ap}</a> \
         (S. <a class=\"internal-link characterization-all\" href=\"/thy/trace/{idx}/autoproveAll/characterize/0/proof/{l}{p}\">{fas}</a>)  for all lemmas ",
        ap = kw("autoprove"), fas = kw("for all solutions"),
    ));
}

/// HS `usesOracle` (lib/theory/src/Theory/Constraint/System.hs:536-537):
/// `all isOracleRanking rs`, where `isOracleRanking` is True for
/// `OracleRanking`, `OracleSmartRanking` AND `InternalTacticRanking`
/// (our `GoalRanking::Tactic`).  Gates the "o. autoprove ... until oracle
/// returns nothing" menu entry (src/Web/Theory.hs:555-556), so it must
/// also fire for `[heuristic={tactic}]` lemmas.  `all` over an empty
/// ranking list would be vacuously true; guard with `!h.is_empty()`.
fn uses_oracle(ctx: &ProofContext) -> bool {
    ctx.heuristic.as_ref().is_some_and(|h| {
        !h.is_empty()
            && h.iter().all(|r| {
                matches!(
                    r,
                    GoalRanking::Oracle { .. }
                        | GoalRanking::OracleSmart { .. }
                        | GoalRanking::Tactic { .. }
                )
            })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_test_support::require_maude_path;

    fn proof_state_from_source(src: &str, mp: &str) -> ProofState {
        let entry = crate::theory_io::load_from_source(
            src,
            crate::state::TheoryOrigin::Upload("trivial.spthy".to_string()),
            mp,
            0,
        )
        .expect("load");
        ProofState::new(
            &entry.typed_theory,
            entry.prover_maude_sig.clone(),
            mp,
            None,
            entry
                .ndc_cache
                .clone()
                .map(tamarin_theory::constraint::solver::context::IntrRuleCache::from)
                .as_ref(),
        )
        .expect("build state")
    }

    /// The theory that the two `ProofState` tests below use.  It has one
    /// rule and one exists-trace lemma.  The function closes it against `mp`.
    fn trivial_proof_state(mp: &str) -> ProofState {
        let src = r#"
theory T begin
rule Setup: [Fr(~k)] --[Setup(~k)]-> [Out(~k)]
lemma trivial: exists-trace
  "Ex k #i. Setup(k) @ #i"
lemma second: exists-trace
  "Ex k #i. Setup(k) @ #i"
lemma stored: exists-trace
  "Ex k #i. Setup(k) @ #i"
  simplify
  by sorry
end
"#;
        proof_state_from_source(src, mp)
    }

    fn roots_are_shared(left: &ProofState, right: &ProofState, lemma: &str) -> bool {
        let left = left.by_lemma[lemma].lock();
        let right = right.by_lemma[lemma].lock();
        let (LemmaProofState::Live(left), LemmaProofState::Live(right)) = (&*left, &*right) else {
            panic!("both roots should be live");
        };
        Arc::ptr_eq(left, right)
    }

    #[test]
    fn build_state_for_trivial_theory() {
        let mp = match require_maude_path() {
            Some(p) => p,
            None => return,
        };
        let state = trivial_proof_state(&mp);
        assert_eq!(state.state_count(|s| matches!(s, LemmaProofState::Lazy)), 3);
        assert!(state.peek_root("trivial").is_none());
        let root = state
            .get_root("trivial")
            .expect("replay trivial root")
            .expect("trivial root");
        assert!(matches!(root.method, ProofMethod::Sorry(_)));
        assert!(matches!(root.status, NodeStatus::Open));
        assert!(state
            .proof_index_root("trivial")
            .expect("live proof index")
            .is_some());
        assert_eq!(
            state.state_count(|s| matches!(s, LemmaProofState::Live(_))),
            1
        );
        assert!(state.peek_root("second").is_none());
        assert!(state.get_root("missing").unwrap().is_none());
        assert!(state.get_system_at("missing", &[]).unwrap().is_none());
    }

    #[test]
    fn apply_simplify_step() {
        let mp = match require_maude_path() {
            Some(p) => p,
            None => return,
        };
        let state = trivial_proof_state(&mp);
        // Apply simplify at the root.
        let path: Vec<String> = Vec::new();
        let r = state.apply_at_path("trivial", &path, ProofMethod::Simplify);
        assert!(r.is_ok(), "simplify should succeed: {:?}", r);
        let root = state
            .get_root("trivial")
            .expect("replay root")
            .expect("root");
        // Method should now be Simplify (not Sorry).
        assert!(
            matches!(root.method, ProofMethod::Simplify),
            "root method after simplify: {:?}",
            root.method
        );
    }

    #[test]
    fn applying_sorry_remains_incomplete() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);
        let status = state
            .apply_at_path("trivial", &[], ProofMethod::Sorry(None))
            .expect("sorry applies");
        assert_eq!(status, NodeStatus::Sorry);
        assert_eq!(
            state
                .get_root("trivial")
                .expect("replay root")
                .expect("root")
                .status,
            NodeStatus::Sorry
        );
    }

    #[test]
    fn removing_a_step_replaces_its_subtree() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);
        state.get_root("trivial").expect("materialize root");
        state.with_live_root_mut("trivial", |root| {
            root.children.insert(
                "child".to_string(),
                ProofNode {
                    method: ProofMethod::Sorry(None),
                    sys: System::empty(),
                    children: BTreeMap::new(),
                    status: NodeStatus::Sorry,
                    annotated: false,
                },
            );
        });

        assert_eq!(state.mark_removed_at_path("missing", &[]), Ok(false));
        assert_eq!(
            state.mark_removed_at_path("trivial", &["missing".to_string()]),
            Ok(false)
        );
        assert_eq!(
            state.mark_removed_at_path("trivial", &["child".to_string()]),
            Ok(false)
        );
        state.with_live_root_mut("trivial", |root| root.annotated = false);
        assert_eq!(state.mark_removed_at_path("trivial", &[]), Ok(true));

        let root = state.get_root("trivial").unwrap().unwrap();
        assert_eq!(root.status, NodeStatus::Sorry);
        assert!(root.annotated);
        assert!(root.children.is_empty());
        assert!(matches!(
            root.method,
            ProofMethod::Sorry(Some(ref reason)) if reason == "removed"
        ));
    }

    #[test]
    fn proof_index_replays_stored_proof_without_materializing_systems() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);

        let root = {
            let _html = tamarin_theory::pretty_hpj::HtmlDocGuard::enable();
            state
                .proof_index_root("stored")
                .expect("stored proof replay")
                .expect("stored proof index")
        };
        assert!(matches!(root.method, ProofMethod::Simplify));
        assert!(state.peek_root("stored").is_none());
        assert_eq!(
            state.state_count(|s| matches!(s, LemmaProofState::Live(_))),
            0
        );
        assert_eq!(
            state.state_count(|s| matches!(s, LemmaProofState::Snapshot(_))),
            1
        );
        {
            let snapshot = state.by_lemma["stored"].lock();
            let LemmaProofState::Snapshot(snapshot) = &*snapshot else {
                panic!("stored proof should have a system-free snapshot");
            };
            assert!(snapshot.body.get().is_none());
        }
        let body = state
            .proof_body("stored")
            .expect("stored proof body")
            .expect("stored lemma");
        assert!(body.starts_with("simplify\n"));
        assert!(body.contains("by sorry"));
        assert!(!body.contains("<span"));
        assert!(state.peek_root("stored").is_none());
        {
            let snapshot = state.by_lemma["stored"].lock();
            let LemmaProofState::Snapshot(snapshot) = &*snapshot else {
                panic!("stored proof should have a system-free snapshot");
            };
            assert!(snapshot.body.get().is_some());
        }

        // The immutable snapshot is reused until an interactive route asks
        // for the live system-bearing tree.
        let again = state
            .proof_index_root("stored")
            .expect("cached proof replay")
            .expect("cached proof index");
        assert!(Arc::ptr_eq(&root, &again));
        let live = state
            .get_root("stored")
            .expect("replay live stored proof")
            .expect("live stored proof");
        assert_eq!(
            body.as_ref(),
            tamarin_theory::pretty_theory::pretty_proof_body(&live)
        );
        assert_eq!(
            root.proof_status(),
            tamarin_theory::constraint::solver::search::proof_status(&live)
        );
        assert!(state.peek_root("stored").is_some());
        assert_eq!(
            state.state_count(|s| matches!(s, LemmaProofState::Snapshot(_))),
            0
        );
    }

    #[test]
    fn concurrent_stored_proof_requests_replay_once() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);
        let barrier = std::sync::Barrier::new(4);
        let roots = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..4)
                .map(|_| {
                    scope.spawn(|| {
                        barrier.wait();
                        state
                            .proof_index_root("stored")
                            .expect("stored proof replay")
                            .expect("stored proof index")
                    })
                })
                .collect();
            workers
                .into_iter()
                .map(|worker| worker.join().expect("proof worker"))
                .collect::<Vec<_>>()
        });

        assert!(roots
            .iter()
            .skip(1)
            .all(|root| Arc::ptr_eq(&roots[0], root)));
        assert_eq!(
            state
                .replay_calls
                .load(std::sync::atomic::Ordering::Relaxed),
            1
        );
    }

    #[test]
    fn rebase_preserves_unvisited_surviving_proofs_from_the_old_theory() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);
        let mut typed = state.session.theory().clone();
        assert!(typed.remove_lemma("second"));
        let maude_sig = typed.signature.clone();
        let typed = Arc::new(typed);

        let rebased = state
            .rebase_onto(&typed, maude_sig, &mp, None, None)
            .expect("rebase");

        assert!(state.peek_root("stored").is_none());
        assert!(rebased.peek_root("trivial").is_some());
        assert!(rebased.peek_root("stored").is_some());
        assert!(rebased.peek_root("second").is_none());
    }

    #[test]
    fn source_proof_body_reports_fresh_lemma_conversion_errors() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = proof_state_from_source(
            r#"theory T begin
rule R: [] --[ A('a') ]-> []
lemma bad: "All x y #i. A(x) @ #i ==> x = y"
end"#,
            &mp,
        );

        assert!(state.proof_body("bad").is_err());
        assert!(state.proof_body("bad").is_err());
        assert_eq!(state.state_count(|s| matches!(s, LemmaProofState::Lazy)), 1);
        assert_eq!(
            state
                .replay_calls
                .load(std::sync::atomic::Ordering::Relaxed),
            2
        );
        assert!(state.peek_root("bad").is_none());
    }

    #[test]
    fn fork_copies_only_materialized_roots_and_keeps_them_independent() {
        let mp = match require_maude_path() {
            Some(p) => p,
            None => return,
        };
        let state = trivial_proof_state(&mp);
        state.get_root("trivial").expect("trivial root");
        let fork = state.fork();

        assert!(fork.peek_root("trivial").is_some());
        assert!(roots_are_shared(&state, &fork, "trivial"));
        assert_eq!(
            state.mark_removed_at_path("trivial", &["missing".to_string()]),
            Ok(false)
        );
        assert!(roots_are_shared(&state, &fork, "trivial"));
        assert!(fork.peek_root("second").is_none());
        state.get_root("second").expect("second root");
        assert!(fork.peek_root("second").is_none());

        state
            .apply_at_path("trivial", &[], ProofMethod::Simplify)
            .expect("simplify original");
        assert!(!roots_are_shared(&state, &fork, "trivial"));
        assert!(matches!(
            fork.get_root("trivial")
                .expect("replay fork root")
                .expect("fork root")
                .method,
            ProofMethod::Sorry(_)
        ));
    }

    #[test]
    fn unannotated_nodes_have_no_usable_system() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);
        state.get_root("trivial").expect("materialize root");
        state.with_live_root_mut("trivial", |root| root.annotated = false);

        assert!(state
            .get_system_at("trivial", &[])
            .expect("get system")
            .is_none());
        assert!(state
            .apply_at_path("trivial", &[], ProofMethod::Sorry(None))
            .is_err());
        let replacement = ProofNode {
            method: ProofMethod::Sorry(None),
            sys: System::empty(),
            children: BTreeMap::new(),
            status: NodeStatus::Sorry,
            annotated: true,
        };
        assert!(state.graft_at_path("trivial", &[], replacement).is_err());
    }

    #[test]
    fn mutation_rolls_status_up_to_the_root() {
        let leaf = |status| ProofNode {
            method: ProofMethod::Sorry(None),
            sys: System::empty(),
            children: BTreeMap::new(),
            status,
            annotated: true,
        };
        let mut middle = leaf(NodeStatus::Open);
        middle
            .children
            .insert("leaf".into(), leaf(NodeStatus::Sorry));
        let mut root = leaf(NodeStatus::Contradictory);
        root.children.insert("middle".into(), middle);

        recompute_ancestor_statuses(&mut root, &["middle".into(), "leaf".into()]);
        assert_eq!(root.children["middle"].status, NodeStatus::Sorry);
        assert_eq!(root.status, NodeStatus::Sorry);

        let mixed = BTreeMap::from([
            ("closed".into(), leaf(NodeStatus::Contradictory)),
            ("open".into(), leaf(NodeStatus::Sorry)),
        ]);
        assert_eq!(rollup_status(&mixed), NodeStatus::Sorry);

        let witness_and_open = BTreeMap::from([
            ("witness".into(), leaf(NodeStatus::Solved)),
            ("open".into(), leaf(NodeStatus::Sorry)),
        ]);
        assert_eq!(rollup_status(&witness_and_open), NodeStatus::Solved);
    }
}
