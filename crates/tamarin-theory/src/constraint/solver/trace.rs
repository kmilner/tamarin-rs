// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! RS-only diagnostic tracing for the constraint solver.
//!
//! These traces have no counterpart in the canonical Haskell tree; they
//! diff against a locally instrumented Haskell build, so their labels
//! have no `Simplify.hs` / `Goals.hs` / `Reduction.hs` citations.
//!
//! `TAM_RS_TRACE_STATE=1` emits one `[STATE]` line for every evaluated proof
//! node and a `[PICK]` line when ranking selects a goal. Var indices are
//! suppressed in both, so two
//! structurally identical systems compare equal across HS/Rust index
//! drift.  The env var is read once through `env_gate!`, so the check
//! costs nothing when the trace is off.

use std::cell::RefCell;

thread_local! {
    /// Stack of case-names from proof tree root to current node.
    /// Scoped by `CasePathGuard` in `search.rs::expand` and HS analog
    /// `solve`. Emitted by
    /// `trace_state` so each [STATE] line can be matched by the
    /// EXACT proof path that produced it — solves the HS Disj-monad
    /// branch-interleaving problem where the same goal-shape appears
    /// at many proof positions.
    static CASE_PATH: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
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
pub(crate) fn case_path_snapshot() -> Option<Vec<String>> {
    state_flag().then(|| CASE_PATH.with(|p| p.borrow().clone()))
}

pub(crate) struct CasePathGuard(RestoreCasePath);

enum RestoreCasePath {
    Inactive,
    Pop,
    Replace(Vec<String>),
}

impl CasePathGuard {
    /// Append one proof-tree component for this scope and pop it on every
    /// exit (including unwinding).
    pub(crate) fn push(name: &str) -> Self {
        Self::push_if(name, state_flag())
    }

    fn push_if(name: &str, enabled: bool) -> Self {
        if !enabled || name.is_empty() {
            return Self(RestoreCasePath::Inactive);
        }
        CASE_PATH.with(|current| current.borrow_mut().push(name.to_string()));
        Self(RestoreCasePath::Pop)
    }

    pub(crate) fn set_child(path: Option<Vec<String>>, name: &str) -> Self {
        let Some(mut path) = path else {
            return Self(RestoreCasePath::Inactive);
        };
        if !name.is_empty() {
            path.push(name.to_owned());
        }
        let previous =
            CASE_PATH.with(|current| std::mem::replace(&mut *current.borrow_mut(), path));
        Self(RestoreCasePath::Replace(previous))
    }
}

impl Drop for CasePathGuard {
    fn drop(&mut self) {
        match std::mem::replace(&mut self.0, RestoreCasePath::Inactive) {
            RestoreCasePath::Inactive => {}
            RestoreCasePath::Pop => CASE_PATH.with(|current| {
                current.borrow_mut().pop();
            }),
            RestoreCasePath::Replace(previous) => CASE_PATH.with(|current| {
                *current.borrow_mut() = previous;
            }),
        }
    }
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
/// Called for every evaluated proof node, before terminal and method
/// selection, so searches that stop without dispatching a goal are visible.
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

/// Emit a state snapshot for an externally-driven proof-tree path without
/// leaking that path into later work on the same thread.
pub fn trace_state_at_path(sys: &crate::constraint::system::System, path: &[String]) {
    if !state_flag() {
        return;
    }
    let _path = CasePathGuard::set_child(Some(path.to_vec()), "");
    trace_state(sys);
}

/// One-line digest of a goal's shape (tag/arity for fact goals, a bare
/// label otherwise).  Shared by [`trace_pick`] and `canonical_open_goals`.
fn goal_digest(g: &crate::constraint::constraints::Goal) -> String {
    use crate::constraint::constraints::Goal;
    match g {
        Goal::Action(_, fa) => format!("Action({}/{})", fact_tag_short(&fa.tag), fa.arity()),
        Goal::Premise(_, fa) => format!("Premise({}/{})", fact_tag_short(&fa.tag), fa.arity()),
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

#[cfg(test)]
mod tests {
    use super::{case_path_string, CasePathGuard};

    #[test]
    fn case_path_guards_restore_pushes_and_replacements() {
        let root = CasePathGuard::set_child(Some(vec!["root".into()]), "");
        {
            let _child = CasePathGuard::push_if("child", true);
            assert_eq!(case_path_string(), "/root/child");
            {
                let _worker = CasePathGuard::set_child(Some(vec!["worker".into()]), "");
                assert_eq!(case_path_string(), "/worker");
            }
            assert_eq!(case_path_string(), "/root/child");
        }
        assert_eq!(case_path_string(), "/root");
        drop(root);
        assert_eq!(case_path_string(), "/");
    }

    #[test]
    fn empty_case_path_component_is_a_noop() {
        let root = CasePathGuard::set_child(Some(vec!["root".into()]), "");
        {
            let _empty = CasePathGuard::push_if("", true);
            assert_eq!(case_path_string(), "/root");
        }
        assert_eq!(case_path_string(), "/root");
        drop(root);
        assert_eq!(case_path_string(), "/");
    }
}
