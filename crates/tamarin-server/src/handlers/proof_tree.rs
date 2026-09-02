// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Live proof-tree state — mirror of Haskell's `IncrementalProof` +
//! `applyProverAtPath`.
//!
//! Haskell's interactive UI keeps a mutable proof tree per lemma; user
//! clicks dispatch a `ProofMethod` at a path in that tree and the
//! result is spliced back in.
//!
//! In the Rust port we model this with:
//!
//! - [`LemmaProofState`]: per-lemma `ProofNode` root + the system at
//!   the root (the lemma's initial negated formula).
//! - [`apply_at_path`]: navigate by case-name path, run the requested
//!   `ProofMethod` via `exec_proof_method`, replace that subtree's
//!   children, return the new root.
//! - [`render_proof_tree_html`]: render the tree as nested HTML
//!   matching Haskell's `prettyProof` indentation.
//!
//! The implementation is intentionally minimal: it doesn't yet drive
//! the full `run_proof_search` loop on click — that's the autoprove
//! button.  Each user-driven step applies exactly one method and
//! returns the resulting cases.  The proof can therefore stay "open"
//! until the user navigates / clicks again.

use std::collections::BTreeMap;
use std::sync::Arc;

use parking_lot::Mutex;

use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::solver::goals::{ranking_at_depth, GoalRanking};
use tamarin_theory::constraint::solver::proof_method::{
    exec_proof_method, finished_subterms, is_finished, ProofMethod,
};
use tamarin_theory::constraint::solver::search::{
    candidate_methods_with_expl, NodeStatus, ProofNode, ProofStatus,
};
use tamarin_theory::constraint::system::System;
use tamarin_theory::pretty_system::pretty_non_graph_system;
use tamarin_theory::theory::TheoryItem;

use crate::handlers::path_parse::{encode_sub_path, url_path_escape};
use crate::handlers::root::html_escape;

/// Per-lemma live proof state, held inside [`TheoryEntry`].
pub(crate) struct LemmaProofState {
    pub root: ProofNode,
}

/// The immutable part of a proof node needed by the left-hand proof index.
///
/// In particular, this cannot retain a [`System`]. A stored proof can be
/// replayed once for faithful first-page rendering and then reduced to this
/// lightweight tree, leaving full systems lazy until an interactive proof
/// route actually needs one.
#[derive(Debug, Clone)]
pub(crate) struct ProofIndexNode {
    pub method: ProofMethod,
    pub children: BTreeMap<String, ProofIndexNode>,
    pub annotated: bool,
}

impl ProofIndexNode {
    fn from_proof_node(node: &ProofNode) -> Self {
        Self {
            method: node.method.clone(),
            children: node
                .children
                .iter()
                .map(|(name, child)| (name.clone(), Self::from_proof_node(child)))
                .collect(),
            annotated: node.annotated,
        }
    }

    /// HS `getProofStatus = foldMap proofStepStatus`, restricted to the
    /// fields retained by the proof index snapshot.
    pub fn proof_status(&self) -> ProofStatus {
        fn step(node: &ProofIndexNode) -> ProofStatus {
            if !node.annotated {
                return ProofStatus::Undetermined;
            }
            match &node.method {
                ProofMethod::Finished(
                    tamarin_theory::constraint::solver::proof_method::Result::Solved,
                ) => ProofStatus::TraceFound,
                ProofMethod::Finished(
                    tamarin_theory::constraint::solver::proof_method::Result::Unfinishable,
                ) => ProofStatus::Unfinishable,
                ProofMethod::Sorry(_) => ProofStatus::Incomplete,
                ProofMethod::Invalidated => ProofStatus::Invalidated,
                _ => ProofStatus::Complete,
            }
        }
        fn combine(a: ProofStatus, b: ProofStatus) -> ProofStatus {
            use ProofStatus::*;
            match (a, b) {
                (Invalidated, _) | (_, Invalidated) => Invalidated,
                (TraceFound, _) | (_, TraceFound) => TraceFound,
                (Incomplete, _) | (_, Incomplete) => Incomplete,
                (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
                (Complete, _) | (_, Complete) => Complete,
                (Undetermined, Undetermined) => Undetermined,
            }
        }

        self.children.values().fold(step(self), |status, child| {
            combine(status, child.proof_status())
        })
    }
}

/// Each theory entry carries one of these. The retained session is the sole
/// theory-wide context owner; proof roots are materialised on first use.
pub struct ProofState {
    pub(crate) by_lemma: Arc<Mutex<BTreeMap<String, LemmaProofState>>>,
    proof_index_by_lemma: Arc<Mutex<BTreeMap<String, Arc<ProofIndexNode>>>>,
    pub session: Arc<tamarin_theory::prove::ProverSession>,
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
    pub fn new(
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
        Ok(ProofState {
            by_lemma: Arc::new(Mutex::new(BTreeMap::new())),
            proof_index_by_lemma: Arc::new(Mutex::new(BTreeMap::new())),
            session,
        })
    }

    /// Apply a `ProofMethod` at `path` in the lemma's proof tree.
    /// Returns the new node status, or an error string for malformed
    /// inputs.
    pub fn apply_at_path(
        &self,
        lemma: &str,
        path: &[String],
        method: ProofMethod,
    ) -> Result<NodeStatus, String> {
        self.materialize_root(lemma)?;
        let ctx = self
            .session
            .context_for_lemma(lemma)
            .map_err(|e| format!("proof context: {e}"))?;
        let mut by_lemma = self.by_lemma.lock();
        let lp = by_lemma
            .get_mut(lemma)
            .ok_or_else(|| format!("unknown lemma: {}", lemma))?;
        let node = navigate_mut(&mut lp.root, path)
            .ok_or_else(|| format!("path not found: {:?}", path))?;
        // Run the method against the node's current system.
        let cases = exec_proof_method(&ctx, &method, &node.sys)
            .ok_or_else(|| format!("method {:?} not applicable", method))?;
        node.method = method;
        node.children.clear();
        if cases.is_empty() {
            // Empty case-list = contradiction closes the branch.
            node.status = NodeStatus::Contradictory;
        } else {
            let mut any_open = false;
            for (name, sys) in cases {
                // Eagerly classify each child as finished / open.
                let (status, leaf_method) = match is_finished(&ctx, &sys) {
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
                    None => {
                        any_open = true;
                        (NodeStatus::Open, ProofMethod::Sorry(None))
                    }
                };
                let child = ProofNode {
                    method: leaf_method,
                    sys,
                    children: BTreeMap::new(),
                    status,
                    annotated: true,
                };
                node.children.insert(name, child);
            }
            node.status = if any_open {
                NodeStatus::Open
            } else {
                // Rollup: prefer Solved → Sorry → Unfinishable →
                // Contradictory, matching Haskell's `ProofStatus`
                // semigroup.
                let mut s = NodeStatus::Contradictory;
                for c in node.children.values() {
                    s = combine_status(s, c.status.clone());
                }
                s
            };
        }
        Ok(node.status.clone())
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
    /// Like [`apply_at_path`](Self::apply_at_path), ancestor `status`
    /// fields are NOT recomputed — HS derives proof status lazily from
    /// the tree, and RS's per-node statuses above the mutation point are
    /// already stale in the single-step path; renderers read per-node
    /// method/status, so the grafted subtree displays correctly.
    pub fn graft_at_path(
        &self,
        lemma: &str,
        path: &[String],
        subtree: ProofNode,
    ) -> Result<(), String> {
        self.materialize_root(lemma)?;
        let mut by_lemma = self.by_lemma.lock();
        let lp = by_lemma
            .get_mut(lemma)
            .ok_or_else(|| format!("unknown lemma: {}", lemma))?;
        if path.is_empty() {
            lp.root = subtree;
            return Ok(());
        }
        let node = navigate_mut(&mut lp.root, path)
            .ok_or_else(|| format!("path not found: {:?}", path))?;
        *node = subtree;
        Ok(())
    }

    /// Fork this proof state: share the same session and immutable proof-index
    /// snapshots, but deep-copy only roots that have actually been
    /// materialised. Unvisited full systems remain lazy in both forks.
    /// Mirrors Haskell `modifyTheory`'s value-typed
    /// `IncrementalProof` semantics: each version-fork sees the source
    /// tree at the moment of fork, then evolves independently.
    pub fn fork(&self) -> Self {
        let src = self.by_lemma.lock();
        let clone: BTreeMap<String, LemmaProofState> = src
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    LemmaProofState {
                        root: v.root.clone(),
                    },
                )
            })
            .collect();
        ProofState {
            by_lemma: Arc::new(Mutex::new(clone)),
            proof_index_by_lemma: Arc::new(Mutex::new(self.proof_index_by_lemma.lock().clone())),
            session: self.session.clone(),
        }
    }

    /// Read a root without causing stored-proof replay or allocating its
    /// initial system. Used by overview panes so opening a rules/source page
    /// does not retain every lemma's proof system.
    pub fn peek_root(&self, lemma: &str) -> Option<ProofNode> {
        self.by_lemma.lock().get(lemma).map(|lp| lp.root.clone())
    }

    /// Return the tree needed by the overview's proof index.
    ///
    /// A live root wins. Otherwise a stored skeleton is checked once, stripped
    /// of every constraint system, and cached in its lightweight form. Lemmas
    /// without a stored proof return `None`, preserving the fresh `by sorry`
    /// fast path without allocating their initial system.
    pub(crate) fn proof_index_root(&self, lemma: &str) -> Option<Arc<ProofIndexNode>> {
        {
            let live = self.by_lemma.lock();
            if let Some(root) = live.get(lemma) {
                return Some(Arc::new(ProofIndexNode::from_proof_node(&root.root)));
            }
        }
        if let Some(root) = self.proof_index_by_lemma.lock().get(lemma).cloned() {
            return Some(root);
        }
        let _stored_proof = self.session.theory.lookup_lemma(lemma)?.proof.as_ref()?;
        let root = tamarin_theory::prove::check_and_extend_lemma_in_session(
            &self.session,
            lemma,
            usize::MAX,
        )
        .ok()?;
        let snapshot = Arc::new(ProofIndexNode::from_proof_node(&root));
        // Replay ran without either map lock. Lock in the same order as
        // materialize_root below: a concurrent live edit wins; otherwise the
        // first concurrent snapshot wins.
        let live = self.by_lemma.lock();
        if let Some(root) = live.get(lemma) {
            return Some(Arc::new(ProofIndexNode::from_proof_node(&root.root)));
        }
        let snapshot = self
            .proof_index_by_lemma
            .lock()
            .entry(lemma.to_string())
            .or_insert(snapshot)
            .clone();
        drop(live);
        Some(snapshot)
    }

    /// Read the root ProofNode for a lemma, materialising and replaying its
    /// stored proof on first access.
    pub fn get_root(&self, lemma: &str) -> Option<ProofNode> {
        self.materialize_root(lemma).ok()?;
        self.peek_root(lemma)
    }

    fn materialize_root(&self, lemma: &str) -> Result<(), String> {
        if self.by_lemma.lock().contains_key(lemma) {
            return Ok(());
        }
        let has_stored_proof = self
            .session
            .theory
            .lookup_lemma(lemma)
            .ok_or_else(|| format!("unknown lemma: {lemma}"))?
            .proof
            .is_some();
        let mut root = tamarin_theory::prove::check_and_extend_lemma_in_session(
            &self.session,
            lemma,
            usize::MAX,
        )
        .map_err(|e| format!("initial proof for {lemma}: {e}"))?;
        // The interactive tree historically treats a lemma with no parsed
        // skeleton as an open root (so its action links are enabled). Batch
        // replay labels the equivalent bare leaf `Sorry`; retain the web
        // status while leaving genuine stored-proof replay untouched.
        if !has_stored_proof
            && matches!(root.method, ProofMethod::Sorry(_))
            && root.children.is_empty()
        {
            root.status = NodeStatus::Open;
        }
        // Replay happens outside the map lock. A concurrent request may have
        // installed or even edited the root meanwhile; preserve that winner.
        self.by_lemma
            .lock()
            .entry(lemma.to_string())
            .or_insert(LemmaProofState { root });
        // The live root now supplies the proof index too.
        self.proof_index_by_lemma.lock().remove(lemma);
        Ok(())
    }

    pub fn template_context(&self) -> &ProofContext {
        self.session.template_context()
    }

    pub fn context_for_lemma(&self, lemma: &str) -> Result<ProofContext, String> {
        self.session
            .context_for_lemma(lemma)
            .map_err(|e| format!("proof context: {e}"))
    }

    pub fn context_for_raw_sources(&self) -> ProofContext {
        self.session
            .context_for_sources(tamarin_theory::constraint::system::SourceKind::RawSources)
            .expect("raw source materialisation is infallible")
    }

    /// Find the system at the given path (root if empty).
    pub fn get_system_at(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Option<tamarin_theory::constraint::system::System> {
        self.materialize_root(lemma).ok()?;
        let by_lemma = self.by_lemma.lock();
        let lp = by_lemma.get(lemma)?;
        let node = navigate_at(&lp.root, path)?;
        Some(node.sys.clone())
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
/// Pre-order over the proof tree: each entry pairs the case-name path from
/// the root with the proof method stored at that node.  RS's `children` is a
/// `BTreeMap`, whose iteration order matches HS's `M.toList` (sorted by
/// `CaseName`).  Used by `next`/`prev` (`nextThyPath`/`nextSmartThyPath`) to
/// enumerate the navigable proof positions in order.
pub(crate) fn get_proof_paths(root: &ProofNode) -> Vec<(Vec<String>, ProofMethod)> {
    let mut out = vec![(Vec::new(), root.method.clone())];
    proof_paths_go(root, &mut Vec::new(), &mut out);
    out
}

/// `go` of [`get_proof_paths`], carrying the root-relative prefix down instead
/// of prepending each label on the way back up.
fn proof_paths_go(
    node: &ProofNode,
    prefix: &mut Vec<String>,
    out: &mut Vec<(Vec<String>, ProofMethod)>,
) {
    for (lbl, child) in &node.children {
        prefix.push(lbl.clone());
        out.push((prefix.clone(), child.method.clone()));
        proof_paths_go(child, prefix, out);
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

/// Combine two child statuses, mirroring Haskell's `instance Semigroup
/// ProofStatus` (`lib/theory/src/Theory/Proof.hs:409-420`).  Precedence:
/// `Solved` (TraceFound) > `Sorry` (IncompleteProof) > `Unfinishable`
/// (UnfinishableProof) > `Contradictory` (CompleteProof) > `Open`
/// (UndeterminedProof, the lowest).
fn combine_status(a: NodeStatus, b: NodeStatus) -> NodeStatus {
    use NodeStatus::*;
    match (&a, &b) {
        (Solved, _) | (_, Solved) => Solved,
        (Sorry, _) | (_, Sorry) => Sorry,
        (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
        (Contradictory, _) | (_, Contradictory) => Contradictory,
        _ => Open,
    }
}

/// Parse a slash-separated proof method path piece, mirroring
/// Haskell's interactive URL.
///
/// Examples:
///   - `simplify`              → `Simplify`
///   - `induction`             → `Induction`
///   - `sorry`                 → `Sorry(None)`
///   - `solve/<goal-id>`       → `SolveGoal(g)` where `g` is the
///     `goal-id`-th goal in the target system (1-based, matching
///     Haskell's `goalNr` rendering).
///
/// The method-string is split from the path-tail at the LAST segment
/// by the caller; this fn just parses the head segment + an optional
/// goal-id segment for `solve`.
pub(crate) fn parse_method(
    segments: &[String],
    sys: &tamarin_theory::constraint::system::System,
) -> Option<ProofMethod> {
    let head = segments.first()?.to_lowercase();
    match head.as_str() {
        "simplify" => Some(ProofMethod::Simplify),
        "induction" => Some(ProofMethod::Induction),
        "sorry" => Some(ProofMethod::Sorry(None)),
        "solve" => {
            let id: usize = segments.get(1)?.parse().ok()?;
            // 1-based — Haskell `goalNr` starts at 1.
            let (g, _st) = sys
                .goals
                .iter()
                .filter(|(_, st)| !st.solved)
                .nth(id.saturating_sub(1))?;
            Some(ProofMethod::SolveGoal(g.clone()))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------
// HTML rendering of the proof tree
// ---------------------------------------------------------------------

/// Render the proof tree for a lemma as nested HTML — mirrors
/// Haskell's `prettyProof`.
pub(crate) fn render_proof_tree_html(idx: usize, lemma: &str, root: &ProofNode) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "<h2>Proof of <code>{}</code></h2>\n",
        html_escape(lemma),
    ));
    let path: Vec<String> = Vec::new();
    render_node(&mut out, idx, lemma, &path, root);
    out
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
    node: &ProofNode,
    ctx: &ProofContext,
) -> String {
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
    // RS's unannotated `ProofNode` carries a placeholder parent `sys`
    // (replay.rs `parsed_to_unannotated`) that MUST NOT be rendered.
    if !node.annotated {
        return tamarin_theory::pretty_hpj::postprocess_html(&format!(
            "no annotated constraint system / {} sub-case(s)",
            node.children.len()
        ));
    }
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
        &node.sys,
        ctx,
    );
    // HS `text ""` — a blank line before the Constraint-system header.
    parts.push(String::new());
    parts.push("<h3>Constraint system</h3>".to_string());
    if has_graph_content(&node.sys) {
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
        pretty_non_graph_system(&node.sys)
    ));
    // Sub-cases.
    let n_cases = node.children.len();
    parts.push(format!("<h3>{} sub-case(s)</h3>", n_cases));
    for (case_name, child) in node.children.iter() {
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
        if !child.annotated {
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
    tamarin_theory::pretty_hpj::postprocess_html(&parts.join("\n"))
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
) {
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
    let methods: Vec<(ProofMethod, String)> = match is_finished(ctx, sys) {
        Some(r) => vec![(ProofMethod::Finished(r), String::new())],
        // HS-faithful WHNF-depth applicability (Web/Theory.hs:546-552 via
        // ProofMethod.hs:282-299, see line 298): never forces the SolveGoal fan-out —
        // see `is_applicable_for_display`.  Must stay in lockstep with
        // `apply_method_and_redirect`'s index filter (method numbering).
        None => match candidate_methods_with_expl(sys, ctx, depth) {
            Ok(methods) => methods
                .into_iter()
                .filter(|(m, _)| {
                    tamarin_theory::constraint::solver::proof_method::is_applicable_for_display(
                        ctx, m, sys,
                    )
                })
                .collect(),
            Err(error) => {
                out.push(format!(
                    "<div class=\"preformatted methods\">{}</div>",
                    html_escape(&error.to_string())
                ));
                return;
            }
        },
    };
    if methods.is_empty() {
        // Mirror Haskell `prettyApplicableProofMethods` (`Web/Theory.hs:546-548`):
        //   [] | finishedSubterms ctxt sys -> "Constraint System is Solved"
        //   []                             -> "Constraint System is Unfinishable"
        // We only reach here when `is_finished` returned `None` (the
        // `Some` case produced a non-empty `[Finished r]` above), so the
        // Solved/Unfinishable choice MUST come from `finished_subterms`
        // exactly as HS does — not from `is_finished` (which is `None`
        // here and would always pick "Solved").
        if finished_subterms(ctx, sys) {
            out.push("<h3>Constraint System is Solved</h3>".to_string());
        } else {
            out.push("<h3>Constraint System is Unfinishable</h3>".to_string());
        }
        return;
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
    // `apply_method_and_redirect` and returns a `{redirect}`.
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

fn render_node(out: &mut String, idx: usize, lemma: &str, path: &[String], node: &ProofNode) {
    let url_path = encode_sub_path(path);
    out.push_str("<div class=\"proof-node\">");
    // Method line with status badge.
    let badge = status_badge(&node.status);
    out.push_str(&format!(
        "<span class=\"proof-method\">{}</span> {}",
        html_escape(&method_label(&node.method)),
        badge,
    ));
    // Action links: depending on method/status, offer apply links.
    if matches!(
        node.method,
        ProofMethod::Sorry(_) | ProofMethod::Invalidated
    ) && matches!(node.status, NodeStatus::Open)
    {
        // Offer Simplify / Induction / Solve links.
        out.push_str(" <span class=\"proof-actions\">");
        out.push_str(&action_link(
            idx,
            lemma,
            &url_path,
            "simplify",
            "[simplify]",
        ));
        out.push_str(&action_link(
            idx,
            lemma,
            &url_path,
            "induction",
            "[induction]",
        ));
        // Solve links — list the unsolved goals at this node, capped
        // at 8 so the UI doesn't blow up on systems with many open
        // goals.
        // Haskell's `goalNr` is 1-based over the UNSOLVED goals only.
        for (i, (g, _)) in node
            .sys
            .goals
            .iter()
            .filter(|(_, st)| !st.solved)
            .take(8)
            .enumerate()
        {
            let nr = i + 1;
            let goal_label = goal_summary(g);
            out.push_str(&action_link(
                idx,
                lemma,
                &url_path,
                &format!("solve/{}", nr),
                &format!("[solve {}: {}]", nr, html_escape(&goal_label)),
            ));
        }
        out.push_str("</span>");
    }
    out.push_str("</div>");
    // Children indented underneath.  Mirror Haskell's
    // `<h4>case <name></h4>` per child shape (Web/Theory.hs:612-617),
    // wrapped in a single `<div class="proof-children">` so the indent
    // reads consistently.
    if !node.children.is_empty() {
        out.push_str("<div class=\"proof-children\" style=\"margin-left:1.5em\">");
        for (case_name, child) in &node.children {
            let mut child_path = path.to_vec();
            child_path.push(case_name.clone());
            out.push_str(&format!("<h4>Case {}</h4>\n", html_escape(case_name)));
            render_node(out, idx, lemma, &child_path, child);
        }
        out.push_str("</div>");
    }
}

/// Port of Haskell's `prettyProofMethod`
/// (`lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs:1173-1186`).
pub(crate) fn method_label(m: &ProofMethod) -> String {
    // Delegate to the byte-faithful `--prove` renderer (HS `prettyProofMethod`)
    // so the interactive method labels carry the same fact spacing
    // (`!KU( ~ltk )`), LVar dots (`#vk.2`), and contradiction reasons as the
    // text proof.  The hand-rolled `goal_summary` below drops the fact
    // multiplicity `!`, the inner-paren spaces, and the LVar index dot, so it
    // is unsuitable here.
    tamarin_theory::pretty_theory::pretty_proof_method_inline(m)
}

fn status_badge(s: &NodeStatus) -> String {
    let (color, label) = match s {
        NodeStatus::Solved => ("#138a36", "✓ verified"),
        NodeStatus::Contradictory => ("#138a36", "✓ closed"),
        NodeStatus::Unfinishable => ("#8a6213", "? unfinishable"),
        NodeStatus::Sorry => ("#8a1313", "✗ sorry"),
        NodeStatus::Open => ("#136a8a", "○ open"),
    };
    format!(
        "<span class=\"proof-status\" style=\"color:{}\">{}</span>",
        color, label
    )
}

fn action_link(idx: usize, lemma: &str, url_path: &str, method: &str, label: &str) -> String {
    format!(
        "<a class=\"ajax-action proof-step\" href=\"/thy/trace/{idx}/proof-step/{lemma}{path}/{method}\">{label}</a> ",
        idx = idx,
        lemma = url_path_escape(lemma),
        path = url_path,
        method = method,
        label = label,
    )
}

fn goal_summary(g: &Goal) -> String {
    use tamarin_term::pretty::pretty_lnterm;
    match g {
        Goal::Action(nid, fa) => {
            let tag = tamarin_theory::fact::fact_tag_name(&fa.tag);
            let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
            format!("{}({}) @ #{}{}", tag, args.join(","), nid.name, nid.idx)
        }
        Goal::Chain(src, tgt) => format!(
            "Chain #{}{} -> #{}{}",
            src.0.name, src.0.idx, tgt.0.name, tgt.0.idx
        ),
        Goal::Premise(np, fa) => {
            let tag = tamarin_theory::fact::fact_tag_name(&fa.tag);
            let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
            format!(
                "{}({}) @ prem #{}{}",
                tag,
                args.join(","),
                np.0.name,
                np.0.idx
            )
        }
        // Mirror Haskell `prettyGoal` (`Constraints.hs:285-286`):
        //   prettyGoal (SplitG x) = "splitEqs" <> parens (show (unSplitId x))
        Goal::Split(s) => format!("splitEqs({})", s.0),
        // Mirror Haskell `prettyGoal` (`Constraints.hs:281-283`):
        //   DisjG (Disj [])  -> text "Disj" <-> operator_ "(⊥)"   (`<->` = `<+>` inserts a space)
        //   DisjG (Disj gfs) -> punctuate "  ∥" (map (parens . prettyGuarded) gfs)
        Goal::Disj(d) => {
            if d.0.is_empty() {
                "Disj (\u{22A5})".to_string()
            } else {
                let parts: Vec<String> =
                    d.0.iter()
                        .map(|c| format!("({})", tamarin_theory::pretty_formula::pretty_guarded(c)))
                        .collect();
                parts.join("  \u{2225} ")
            }
        }
        Goal::Subterm((a, b)) => format!("{} \u{2291} {}", pretty_lnterm(a), pretty_lnterm(b)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_test_support::require_maude_path;

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

    #[test]
    fn build_state_for_trivial_theory() {
        let mp = match require_maude_path() {
            Some(p) => p,
            None => return,
        };
        let state = trivial_proof_state(&mp);
        assert!(state.by_lemma.lock().is_empty());
        assert!(state.peek_root("trivial").is_none());
        let root = state.get_root("trivial").expect("trivial root");
        assert!(matches!(root.method, ProofMethod::Sorry(_)));
        assert!(matches!(root.status, NodeStatus::Open));
        assert_eq!(state.by_lemma.lock().len(), 1);
        assert!(state.peek_root("second").is_none());
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
        let root = state.get_root("trivial").expect("root");
        // Method should now be Simplify (not Sorry).
        assert!(
            matches!(root.method, ProofMethod::Simplify),
            "root method after simplify: {:?}",
            root.method
        );
    }

    #[test]
    fn proof_index_replays_stored_proof_without_materializing_systems() {
        let Some(mp) = require_maude_path() else {
            return;
        };
        let state = trivial_proof_state(&mp);

        let root = state
            .proof_index_root("stored")
            .expect("stored proof index");
        assert!(matches!(root.method, ProofMethod::Simplify));
        assert!(state.peek_root("stored").is_none());
        assert_eq!(state.by_lemma.lock().len(), 0);
        assert_eq!(state.proof_index_by_lemma.lock().len(), 1);

        // The immutable snapshot is reused until an interactive route asks
        // for the live system-bearing tree.
        let again = state
            .proof_index_root("stored")
            .expect("cached proof index");
        assert!(Arc::ptr_eq(&root, &again));
        let live = state.get_root("stored").expect("live stored proof");
        assert_eq!(
            root.proof_status(),
            tamarin_theory::constraint::solver::search::proof_status(&live)
        );
        assert!(state.peek_root("stored").is_some());
        assert!(state.proof_index_by_lemma.lock().is_empty());
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
        assert!(fork.peek_root("second").is_none());
        state.get_root("second").expect("second root");
        assert!(fork.peek_root("second").is_none());

        state
            .apply_at_path("trivial", &[], ProofMethod::Simplify)
            .expect("simplify original");
        assert!(matches!(
            fork.get_root("trivial").expect("fork root").method,
            ProofMethod::Sorry(_)
        ));
    }

    #[test]
    fn parse_method_simplify_induction_sorry() {
        let sys = tamarin_theory::constraint::system::System::empty();
        assert!(matches!(
            parse_method(&["simplify".into()], &sys),
            Some(ProofMethod::Simplify)
        ));
        assert!(matches!(
            parse_method(&["induction".into()], &sys),
            Some(ProofMethod::Induction)
        ));
        assert!(matches!(
            parse_method(&["sorry".into()], &sys),
            Some(ProofMethod::Sorry(None))
        ));
        assert!(parse_method(&["solve".into()], &sys).is_none());
        assert!(parse_method(&["bogus".into()], &sys).is_none());
    }

    /// The complete document that [`render_proof_tree_html`] emits for an
    /// open, childless root.  The document holds the `<h2>` header and the
    /// method line with its status badge.  It also holds the two goal-free
    /// action links, because the node is `Sorry`/`Open`.  Each link addresses
    /// this node's own proof path, which is empty.  A system with unsolved
    /// goals adds `[solve N: …]` links here.
    #[test]
    fn render_proof_tree_html_for_an_open_root() {
        let root = ProofNode {
            method: ProofMethod::Sorry(None),
            sys: tamarin_theory::constraint::system::System::empty(),
            children: BTreeMap::new(),
            status: NodeStatus::Open,
            annotated: true,
        };
        assert_eq!(
            render_proof_tree_html(1, "L", &root),
            concat!(
                "<h2>Proof of <code>L</code></h2>\n",
                "<div class=\"proof-node\">",
                "<span class=\"proof-method\">sorry</span> ",
                "<span class=\"proof-status\" style=\"color:#136a8a\">\u{25cb} open</span>",
                " <span class=\"proof-actions\">",
                "<a class=\"ajax-action proof-step\" \
                 href=\"/thy/trace/1/proof-step/L/simplify\">[simplify]</a> ",
                "<a class=\"ajax-action proof-step\" \
                 href=\"/thy/trace/1/proof-step/L/induction\">[induction]</a> ",
                "</span></div>",
            )
        );
    }

    // --- HS-parity pretty-printing regression tests --------------------
    //
    // Each pins a byte-for-byte form of a shared Haskell printer.

    #[test]
    fn sorry_method_label_has_no_initial_comment() {
        // HS `unproven = sorry Nothing` (Theory/Proof.hs:255-256) renders via
        // `prettyProofMethod (Sorry Nothing)` (ProofMethod.hs:1179-1180)
        // as a plain `sorry` (no `/* ... */` reason).  Confirmed against
        // the repo HS prover: an unproven lemma prints `by sorry`.
        assert_eq!(method_label(&ProofMethod::Sorry(None)), "sorry");
        // The fresh root built by ProofState::new must be Sorry(None).
        // (We only assert the label form here; building a full ProofState
        // requires Maude and is covered by build_state_for_trivial_theory.)
    }

    #[test]
    fn empty_disj_goal_summary_has_space() {
        use tamarin_theory::constraint::constraints::{Disj, Goal};
        // HS `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`
        // (Constraints.hs:273-288, see line 281).  `<->` = HughesPJ `<+>`
        // (Text/PrettyPrint/Class.hs:172-187, see line 176),
        // which inserts a single space: `Disj (⊥)`.
        assert_eq!(goal_summary(&Goal::Disj(Disj(vec![]))), "Disj (\u{22A5})");
    }
}
