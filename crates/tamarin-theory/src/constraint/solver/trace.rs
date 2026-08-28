// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! RS-only diagnostic tracing for the constraint solver.
//!
//! These traces have no counterpart in the canonical Haskell tree; they
//! diff against a locally instrumented Haskell build, so their labels
//! have no `Simplify.hs` / `Goals.hs` / `Reduction.hs` citations.
//!
//! `TAM_RS_TRACE_STATE=1` emits, before each `solveGoal` dispatch, one
//! `[STATE]` line summarising the system and one `[PICK]` line naming
//! the chosen goal.  Var indices are suppressed in both, so two
//! structurally identical systems compare equal across HS/Rust index
//! drift.  The env var is read once through `env_gate!`, so the check
//! costs nothing when the trace is off.
//!
//! The op-label thread-local below serves the `[rs-aes]` trace in
//! `tools::equation_store`, which attributes each `apply_eq_store` call
//! to the Reduction operation that made it.

use std::cell::RefCell;

thread_local! {
    /// Stack of case-names from proof tree root to current node.
    /// Pushed/popped by `case_path_push` / `case_path_pop` in
    /// `search.rs::expand` and HS analog `solve`.  Emitted by
    /// `trace_state` so each [STATE] line can be matched by the
    /// EXACT proof path that produced it — solves the HS Disj-monad
    /// branch-interleaving problem where the same goal-shape appears
    /// at many proof positions.
    static CASE_PATH: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };

    /// Current operation label, set by callers of apply_eq_store/add_eqs.
    /// RS-only.  Used by [rs-aes]
    /// trace to attribute each apply_eq_store call to the originating
    /// Reduction operation (solveTermEqs, solveFactEqs, chain_extend,
    /// ENU.kuActions, etc.) so HS↔RS apply_eq_store call counts can
    /// be diffed per-label rather than per-line-number.
    static CURRENT_OP_LABEL: RefCell<String> =
        RefCell::new(String::from("unlabeled"));
}

/// Cached: `true` iff a trace that *consumes* the op-label is enabled.
///
/// The op-label is only ever read into output by the `[rs-aes]` trace,
/// which is gated on `TAM_RS_DBG_APPLY_EQ_STORE` (see `equation_store.rs`,
/// `aes_dbg()` — the only output consumer of `current_op_label()`).  When
/// that flag is unset the entire label machinery (`set_op_label` /
/// `current_op_label` / `OpLabelGuard`) is pure overhead — each guard
/// clones a thread-local `String` and runs `label.to_string()` — so the
/// operations below early-return as no-ops.  Byte-safe: when the consuming
/// flag IS set the label machinery runs in full; when it is unset the
/// label is never observed, so skipping the clones changes nothing.
pub fn op_label_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_EQ_STORE")
}

/// Set the current operation label.  Callers wrap their apply_eq_store
/// / add_eqs call sites with `set_op_label` to associate the call with
/// a semantic name.  Use `OpLabelGuard::new(...)` for scope-based
/// management so the label restores on drop.
pub fn set_op_label(label: &str) -> String {
    if !op_label_enabled() {
        return String::new();
    }
    CURRENT_OP_LABEL.with(|l| {
        let prev = l.borrow().clone();
        *l.borrow_mut() = label.to_string();
        prev
    })
}

/// Get the current operation label.  Used by apply_eq_store's [rs-aes]
/// trace to print the site label.
pub fn current_op_label() -> String {
    if !op_label_enabled() {
        return String::new();
    }
    CURRENT_OP_LABEL.with(|l| l.borrow().clone())
}

/// RAII guard for op label: sets label on creation, restores previous
/// on drop.  Use as `let _g = OpLabelGuard::new("solveTermEqs");` at
/// the start of a scope.
///
/// **Default semantics**: if an outer label is already set (anything
/// other than "unlabeled"), the outer label is PRESERVED — this lets
/// chain-extend/ENU.kuActions/etc. flow through solve_term_eqs without
/// being overwritten, matching HS's `addEqsLabeled` semantics where
/// the OUTERMOST caller's label sticks.  Use `OpLabelGuard::force`
/// for cases where you want to override even an outer label
/// (e.g. simp passes adding their own prefix).
#[must_use = "dropping this guard immediately ends the scope it protects"]
pub struct OpLabelGuard {
    prev: String,
}

impl OpLabelGuard {
    pub fn new(label: &str) -> Self {
        // No consuming trace => the label is never read; skip the
        // thread-local clone + `to_string` entirely (Drop also no-ops).
        if !op_label_enabled() {
            return Self {
                prev: String::new(),
            };
        }
        let outer = current_op_label();
        if outer == "unlabeled" {
            let prev = set_op_label(label);
            Self { prev }
        } else {
            // Outer label sticks; we don't change anything but still
            // return a guard so the call-site doesn't need to special-case.
            Self { prev: outer }
        }
    }

    /// Force override the label (used by simp passes that prepend to
    /// the outer label, e.g. `simpAbstractFun@<outer>`).
    pub fn force(label: &str) -> Self {
        if !op_label_enabled() {
            return Self {
                prev: String::new(),
            };
        }
        let prev = set_op_label(label);
        Self { prev }
    }
}

impl Drop for OpLabelGuard {
    fn drop(&mut self) {
        if !op_label_enabled() {
            return;
        }
        let prev = std::mem::take(&mut self.prev);
        CURRENT_OP_LABEL.with(|l| {
            *l.borrow_mut() = prev;
        });
    }
}

pub fn case_path_push(name: &str) {
    CASE_PATH.with(|p| p.borrow_mut().push(name.to_string()));
}

pub fn case_path_pop() {
    CASE_PATH.with(|p| {
        p.borrow_mut().pop();
    });
}

pub(crate) fn case_path_string() -> String {
    CASE_PATH.with(|p| {
        let v = p.borrow();
        if v.is_empty() {
            "/".to_string()
        } else {
            format!("/{}", v.join("/"))
        }
    })
}

/// Snapshot the current case-path stack — used by parallel `expand`
/// to seed worker threads with the parent thread's proof-tree path so
/// trace output remains coherent across thread boundaries.
pub(crate) fn case_path_snapshot() -> Vec<String> {
    CASE_PATH.with(|p| p.borrow().clone())
}

/// Overwrite this thread's case-path stack — used at the start of each
/// rayon worker task to seed it with the parent's snapshot.
pub fn case_path_set(path: &[String]) {
    CASE_PATH.with(|p| {
        let mut v = p.borrow_mut();
        v.clear();
        v.extend_from_slice(path);
    });
}

fn state_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_STATE")
}

/// Emit a `[STATE]` line summarising the system state in a form designed
/// to diff against the equivalent state trace in the private instrumented
/// HS build.  RS-only.  Fields:
///
/// - `nodes`: sorted, count-compressed list of rule-case-names
///   (e.g. `I_2×1, I_1×1, Register_pk×3, isend×2, Fresh×4, Secrecy_claim×1`).
///   Var idxs are suppressed so two structurally-identical systems compare
///   equal across HS/Rust idx allocation drift.
/// - `goals`: sorted list of UNSOLVED goal kinds with canonical fact heads:
///   `Action(KU(aenc)), Premise(Secret), Disj[Ku(t)∥Out_R_1]`. The fact head
///   uses the same canonicalisation as the private instrumented HS build's
///   goal-kind trace.
/// - `formulas` / `solved_formulas`: counts only (full bodies elided to
///   keep the line readable; depth dumps available via other flags).
///
/// Called right before each `solveGoal` dispatch (paired with the
/// `[EXEC] solveGoal ...` line) so we can see exactly what state HS / Rust
/// had when each ranking decision was made.
pub fn trace_state(sys: &crate::constraint::system::System) {
    if !state_flag() {
        return;
    }
    eprintln!(
        "[STATE] path={} nodes={} goals={} formulas={} solved_formulas={}",
        case_path_string(),
        canonical_nodes(sys),
        canonical_open_goals(sys),
        sys.formulas.len(),
        sys.solved_formulas.len()
    );
}

/// One-line digest of a goal's shape (tag/arity for fact goals, a bare
/// label otherwise).  Shared by [`trace_pick`] and `canonical_open_goals`.
fn goal_digest(g: &crate::constraint::constraints::Goal) -> String {
    use crate::constraint::constraints::Goal;
    match g {
        Goal::Action(_, fa) => format!("Action({}/{})", fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Premise(_, fa) => format!("Premise({}/{})", fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Chain(_, _) => "Chain".to_string(),
        Goal::Split(_) => "Split".to_string(),
        Goal::Disj(d) => format!("Disj[{}]", disj_heads(d)),
        Goal::Subterm(_) => "Subterm".to_string(),
    }
}

/// Emit a [PICK] line indicating which goal was selected for this dispatch.
/// RS-only; paired with the equivalent goal-pick trace in the private
/// instrumented HS build so we can compare goal-ranking decisions.
pub fn trace_pick(g: &crate::constraint::constraints::Goal) {
    if !state_flag() {
        return;
    }
    let s = goal_digest(g);
    eprintln!("[PICK] {}", s);
}

fn canonical_nodes(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::solver::reduction::rule_case_name;
    let mut names: Vec<String> = sys.nodes.iter().map(|(_, r)| rule_case_name(r)).collect();
    names.sort();
    compress_dups(&names)
}

fn canonical_open_goals(sys: &crate::constraint::system::System) -> String {
    let mut digests: Vec<String> = sys
        .goals
        .iter()
        .filter(|(_, st)| !st.solved)
        .map(|(g, _)| goal_digest(g))
        .collect();
    digests.sort();
    format!("[{}]", digests.join(","))
}

fn fact_tag_short(t: &crate::fact::FactTag) -> String {
    use crate::fact::FactTag;
    match t {
        FactTag::Ku => "KU".to_string(),
        FactTag::Kd => "KD".to_string(),
        FactTag::Fresh => "Fr".to_string(),
        FactTag::Out => "Out".to_string(),
        FactTag::In => "In".to_string(),
        FactTag::Proto(_, name, _) => name.to_string(),
        _ => "?".to_string(),
    }
}

fn disj_heads(d: &crate::constraint::constraints::Disj<crate::guarded::Guarded>) -> String {
    let heads: Vec<String> = d.0.iter().map(guarded_head).collect();
    heads.join("|")
}

fn guarded_head(g: &crate::guarded::Guarded) -> String {
    use crate::guarded::Guarded;
    match g {
        // The private instrumented HS build's guarded-head trace returns
        // just the literal `"Atom"` — no atom contents.  Keep Rust aligned
        // for byte-equivalent diff.
        Guarded::Atom(_) => "Atom".to_string(),
        Guarded::Conj(_) => "Conj".to_string(),
        Guarded::Disj(_) => "Disj".to_string(),
        // Format matches that HS build's guarded-head trace: `<Quantifier><N>v`
        // (e.g. `Ex1v`).  Suppresses bound-var names so HS/Rust line up.
        Guarded::GGuarded { qua, vars, .. } => format!("{:?}{}v", qua, vars.len()),
    }
}

fn compress_dups(sorted: &[String]) -> String {
    if sorted.is_empty() {
        return "[]".to_string();
    }
    let mut out = String::from("[");
    let mut iter = sorted.iter().peekable();
    while let Some(first) = iter.next() {
        let mut count = 1usize;
        while iter.peek().map(|s| s.as_str()) == Some(first.as_str()) {
            iter.next();
            count += 1;
        }
        if count > 1 {
            out.push_str(&format!("{}×{}", first, count));
        } else {
            out.push_str(first);
        }
        if iter.peek().is_some() {
            out.push(',');
        }
    }
    out.push(']');
    out
}
