// Currently GPL 3.0 until granted permission by the following authors:
//   Simon Meier, Philip Lukert, Jannik Dreier, Benedikt Schmidt, Charlie
//   Jacomme, Robert Künnemann, Niklas Medinger, Felix Linker, Yavor Ivanov,
//   "ValentinYuri" (github), and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver/Goals.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Simplify.hs

//! RS-only execution-trace diagnostic scaffolding.
//!
//! This is a Rust-only facility with no counterpart in the canonical
//! Haskell tree.  It was designed to diff against a *private/local*
//! instrumented build of the Haskell tamarin-prover; the matching
//! Haskell side (an `[EXEC]`-style `traceExecM` patch) was never
//! committed upstream, so the labels below have no canonical
//! `Simplify.hs` / `Goals.hs` / `Reduction.hs` / `Trace.hs`
//! counterparts to cite.
//!
//! Set `TAM_RS_TRACE_EXEC=1` to enable.  Each major solver entry point
//! emits a single `[EXEC] <function> <canonical-data>` line via
//! [`trace_exec`].  The output is intended to be diffed against an
//! equivalently-instrumented Haskell build to locate the first
//! execution divergence between the implementations.
//!
//! Design choices:
//! - The env var is read once via `std::sync::OnceLock` so the check
//!   is essentially free when the trace is disabled.
//! - No sequence numbers in the output — keeps the diff focused on
//!   trace-content drift instead of counter drift.
//! - Data is normalised to suppress fresh-var indices (use canonical
//!   sort prefix + name only).

use std::sync::OnceLock;
use std::cell::RefCell;
use tamarin_term::lterm::sort_prefix;

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
/// flag IS set the label behaves exactly as before; when it is unset the
/// label is never observed, so skipping the clones changes nothing.
pub fn op_label_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_EQ_STORE")
}

/// Set the current operation label.  Callers wrap their apply_eq_store
/// / add_eqs call sites with `set_op_label` to associate the call with
/// a semantic name.  Use `OpLabelGuard::new(...)` for scope-based
/// management so the label restores on drop.
pub fn set_op_label(label: &str) -> String {
    if !op_label_enabled() { return String::new(); }
    CURRENT_OP_LABEL.with(|l| {
        let prev = l.borrow().clone();
        *l.borrow_mut() = label.to_string();
        prev
    })
}

/// Get the current operation label.  Used by apply_eq_store's [rs-aes]
/// trace to print the site label.
pub fn current_op_label() -> String {
    if !op_label_enabled() { return String::new(); }
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
        if !op_label_enabled() { return Self { prev: String::new() }; }
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
        if !op_label_enabled() { return Self { prev: String::new() }; }
        let prev = set_op_label(label);
        Self { prev }
    }
}

impl Drop for OpLabelGuard {
    fn drop(&mut self) {
        if !op_label_enabled() { return; }
        let prev = std::mem::take(&mut self.prev);
        CURRENT_OP_LABEL.with(|l| { *l.borrow_mut() = prev; });
    }
}

pub fn case_path_push(name: &str) {
    CASE_PATH.with(|p| p.borrow_mut().push(name.to_string()));
}

pub fn case_path_pop() {
    CASE_PATH.with(|p| { p.borrow_mut().pop(); });
}

pub fn case_path_string() -> String {
    CASE_PATH.with(|p| {
        let v = p.borrow();
        if v.is_empty() { "/".to_string() } else { format!("/{}", v.join("/")) }
    })
}

/// Snapshot the current case-path stack — used by parallel `expand`
/// to seed worker threads with the parent thread's proof-tree path so
/// trace output remains coherent across thread boundaries.
pub fn case_path_snapshot() -> Vec<String> {
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

/// TAM_RS_TRACE_FORM=1 emits `[FORMULA_ADD] path=... kind=... <repr>` lines
/// for each formula insertion into sys.formulas / sys.goals.  RS-only; pairs
/// with the equivalent insertion trace in the private instrumented HS build
/// for finding insertion divergences.
pub fn form_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_FORM")
}

/// `repr` is a thunk so the (recursive, allocating) `guarded_repr` dump is
/// built only when `TAM_RS_TRACE_FORM` is set — unset in every
/// production/gate/bench run.  When the flag is set, the closure runs and
/// produces the same `[FORMULA_ADD]` line as an eagerly-built string, so
/// the trace stream is byte-identical.
pub fn trace_form(kind: &str, repr: impl FnOnce() -> String) {
    if form_flag() {
        eprintln!("[FORMULA_ADD] path={} kind={} {}", case_path_string(), kind, repr());
    }
}

/// Canonicalized representation of a Guarded formula for [FORMULA_ADD]
/// tracing — recursive structural dump with full bound-term content
/// (var idxs suppressed via name-only LVar rendering) so HS/Rust diffs
/// can distinguish formulas with the same head shape but different
/// instantiation of free vars (e.g., `KU(ni:42)` vs `KU(ni:44)`).
pub fn guarded_repr(g: &crate::guarded::Guarded) -> String {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => format!("Atom({})", atom_repr(a)),
        Guarded::Conj(items) => {
            let s: Vec<String> = items.iter().map(guarded_repr).collect();
            format!("Conj[{}]", s.join(","))
        }
        Guarded::Disj(items) => {
            let s: Vec<String> = items.iter().map(guarded_repr).collect();
            format!("Disj[{}]", s.join("|"))
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            let g_strs: Vec<String> = guards.iter().map(atom_repr).collect();
            format!("{:?}{}v[{}]({})", qua, vars.len(), g_strs.join(","), guarded_repr(body))
        }
    }
}

fn atom_repr(a: &crate::guarded::GAtom) -> String {
    use crate::guarded::GAtom;
    match a {
        GAtom::Eq(s, t) => format!("Eq({},{})", term_repr(s), term_repr(t)),
        GAtom::Less(s, t) => format!("Less({},{})", term_repr(s), term_repr(t)),
        GAtom::LessMset(s, t) => format!("LMset({},{})", term_repr(s), term_repr(t)),
        GAtom::Subterm(s, t) => format!("Subterm({},{})", term_repr(s), term_repr(t)),
        GAtom::Last(s) => format!("Last({})", term_repr(s)),
        GAtom::Action(f, t) => format!("{}({})@{}",
            f.name, f.args.iter().map(term_repr).collect::<Vec<_>>().join(","),
            term_repr(t)),
        GAtom::Pred(f) => format!("Pred({})", f.name),
    }
}

fn term_repr(t: &crate::guarded::GTerm) -> String {
    use crate::guarded::{GTerm, BVar};
    match t {
        GTerm::Var(BVar::Free(v)) => format!("{}{}#{}", match v.sort {
            tamarin_parser::ast::SortHint::Fresh => "~",
            tamarin_parser::ast::SortHint::Pub   => "$",
            tamarin_parser::ast::SortHint::Node  => "#",
            tamarin_parser::ast::SortHint::Nat   => "%",
            tamarin_parser::ast::SortHint::Msg   => "",
            _ => "?",
        }, v.name, v.idx),
        GTerm::Var(BVar::Bound(n)) => format!("B{}", n),
        GTerm::App(name, args) => format!("{}({})", name,
            args.iter().map(term_repr).collect::<Vec<_>>().join(",")),
        GTerm::Pair(args) =>
            format!("<{}>", args.iter().map(term_repr).collect::<Vec<_>>().join(",")),
        GTerm::AlgApp(name, a, b) => format!("{}({},{})", name, term_repr(a), term_repr(b)),
        GTerm::Diff(a, b) => format!("diff({},{})", term_repr(a), term_repr(b)),
        GTerm::BinOp(op, a, b) => format!("{:?}({},{})", op, term_repr(a), term_repr(b)),
        GTerm::PubLit(s) => format!("'{}'", s),
        GTerm::FreshLit(s) => format!("~'{}'", s),
        GTerm::NatLit(s) => format!("%'{}'", s),
        GTerm::Number(n) => format!("{}", n),
        GTerm::NumberOne => "1".to_string(),
        GTerm::NatOne => "%1".to_string(),
        GTerm::DhNeutral => "1g".to_string(),
        GTerm::PatMatch(t) => format!("=({})", term_repr(t)),
    }
}

fn flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_EXEC")
}

/// Public view of the cached `TAM_RS_TRACE_EXEC` gate (`flag()`), so
/// `trace_exec` call sites can skip building their `format!(...)`
/// argument on the common (untraced) path.  Returns the same cached
/// `OnceLock<bool>` that `trace_exec` itself checks, so enabling the
/// trace still produces byte-identical output.
#[inline]
pub fn exec_enabled() -> bool {
    flag()
}

/// Static-string trace labels that the (private) instrumented Haskell
/// build emits exactly once per program run due to GHC CSE on the
/// literal `String` argument to the trace call.  These four labels
/// correspond to fixed string literals on the HS side (as opposed to
/// labels concatenated with `show n` / a rule name, which are distinct
/// per call and emit per-invocation):
///
///   - `simplifySystem`
///   - `solveChain ENTER`
///   - `FrNarrow`
///   - `exploitPrem InFact`
///
/// Rust's `trace_exec` would otherwise emit per call for these too —
/// diverging from the instrumented HS build even though the underlying
/// work matches.  Dedup here on first emission per program run.
///
/// NOTE: these labels reference a private/local Haskell instrumentation
/// patch that is not part of the canonical upstream tree, so there are
/// no canonical `Simplify.hs` / `Goals.hs` / `Reduction.hs` line
/// citations to give.
fn is_cse_deduplicated_label(label: &str) -> bool {
    matches!(label,
        "simplifySystem"
        | "solveChain ENTER"
        | "FrNarrow"
        | "exploitPrem InFact"
    )
}

/// Has this CSE-deduplicated label already been emitted in this
/// program run?  Returns `true` if already seen (skip emission),
/// `false` and records it if first time.
// static emitted-label dedup set; membership only, never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn check_and_mark_emitted(label: &str) -> bool {
    use std::collections::HashSet;
    use std::sync::Mutex;
    static EMITTED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let set = EMITTED.get_or_init(|| Mutex::new(HashSet::new()));
    // `insert` returns true when the label is newly added (first emission)
    // and false when it was already present — negate to get "already seen".
    !set.lock().unwrap().insert(label.to_string())
}

/// Emit a `[EXEC] <label>` line to stderr when `TAM_RS_TRACE_EXEC=1`.
/// No-op otherwise.  Keep `label` in the same canonical form as the
/// (private) instrumented Haskell build so the outputs diff cleanly.
///
/// For labels the instrumented HS build deduplicates via GHC CSE (see
/// [`is_cse_deduplicated_label`]), emit only on first occurrence per
/// program run — matching its effective once-per-program emission for
/// those literal-string trace callsites.
#[inline]
pub fn trace_exec(label: &str) {
    if !flag() { return; }
    if is_cse_deduplicated_label(label) && check_and_mark_emitted(label) {
        return;
    }
    eprintln!("[EXEC] {}", label);
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
    if !state_flag() { return; }
    eprintln!("[STATE] path={} nodes={} goals={} formulas={} solved_formulas={}",
        case_path_string(),
        canonical_nodes(sys),
        canonical_open_goals(sys),
        sys.formulas.len(),
        sys.solved_formulas.len());
    if state_full_flag() {
        // Additional [STATE_FULL] emission for fine-grained lockstep
        // diff: dumps the FULL action terms with var idxs suppressed
        // (canonical form for clean HS-Rust diff).
        eprintln!("[STATE_FULL] node_actions={}", canonical_node_actions(sys));
        eprintln!("[STATE_FULL] open_actions={}", canonical_open_actions(sys));
    }
    if state_eqs_flag() {
        // `TAM_RS_TRACE_STATE_EQS=1`: dump canonical eq_store contents
        // for HS vs Rust binding-divergence diagnosis.  Idxs suppressed
        // so the diff catches semantic divergences (different name
        // unifications) rather than idx-allocation drift.
        eprintln!("[STATE_EQS] path={} subst={} conj={}",
            case_path_string(),
            canonical_eq_store_subst(sys),
            sys.eq_store.conj.len());
        // Dump each disjunct's substs for diff against HS — WITH IDXS
        for (di, d) in sys.eq_store.conj.iter().enumerate() {
            for (si, s) in d.substs.iter().enumerate() {
                let entries: Vec<String> = s.to_list().into_iter().map(|(k, v)| {
                    let k_str = format!("{}{}.{}", sort_prefix(k.sort), k.name, k.idx);
                    let v_str = format!("{:?}", v).chars().take(120).collect::<String>();
                    format!("{}→{}", k_str, v_str)
                }).collect();
                eprintln!("[STATE_EQS]   disj[{}].subst[{}]={:?} [{}]",
                    di, si, d.split_id, entries.join(", "));
            }
        }
    }
    if state_forms_flag() {
        // `TAM_RS_TRACE_STATE_FORMS=1`: dump full formula content at
        // each [STATE] checkpoint.  Used when state counts diverge from
        // HS (e.g., HS has more formulas than Rust at the same path):
        // shows which specific formulas Rust is missing relative to HS.
        for (i, f) in sys.formulas.iter().enumerate() {
            eprintln!("[STATE_FORM] path={} formulas[{}]={}",
                case_path_string(), i, guarded_repr(f));
        }
        for (i, f) in sys.solved_formulas.iter().enumerate() {
            eprintln!("[STATE_FORM] path={} solved[{}]={}",
                case_path_string(), i, guarded_repr(f));
        }
    }
    if state_nodes_flag() {
        // `TAM_RS_TRACE_STATE_NODES=1`: dump each node with its full
        // rule case-name + ALL actions (with var idxs preserved) so
        // HS↔Rust diff can detect missing chain levels (e.g.
        // Helper_Loop_and_success: HS has Loop(~n, f(f(k.1)), kOrig)
        // at parent path; Rust only has Loop(~n, k, kOrig) / Loop(~n,
        // f(k), kOrig) — missing the third chain level).
        for (id, rule) in sys.nodes.iter() {
            let rc = crate::constraint::solver::reduction::rule_case_name(rule);
            let acts: Vec<String> = rule.actions.iter()
                .map(canonical_fact_with_idx).collect();
            eprintln!("[STATE_NODE] path={} {}.{}={} actions=[{}]",
                case_path_string(), id.name, id.idx, rc, acts.join(", "));
        }
        for e in &sys.edges {
            eprintln!("[STATE_EDGE] path={} {}.{}/{} -> {}.{}/{}",
                case_path_string(),
                e.src.0.name, e.src.0.idx, e.src.1.0,
                e.tgt.0.name, e.tgt.0.idx, e.tgt.1.0);
        }
        // Also dump open Action goals with their idx-preserved fact
        // content (the canonical [STATE] line above suppresses idxs).
        // These are Ex-decomposed action atoms that haven't been folded
        // into nodes yet — they participate in `impl_formulas` matching
        // and are critical for diagnosing IH-Forall-fires-but-misses-
        // gfalse divergences at case-3 (Helper_Loop_and_success).
        use crate::constraint::constraints::Goal;
        for (g, st) in sys.goals.iter() {
            if st.solved { continue; }
            if let Goal::Action(node, fa) = g {
                eprintln!("[STATE_GOAL] path={} Action@{}.{}={}",
                    case_path_string(), node.name, node.idx,
                    canonical_fact_with_idx(fa));
            }
        }
        // Dump less_atoms and last_atom — these drive HS's `Cyclic`
        // contradiction detection (cycles in the Less/Edge graph).
        // Critical for diagnosing Gen_Stop/Gen_Start cyclic-firing
        // divergences in Helper_Loop_and_success.
        for la in &sys.less_atoms {
            eprintln!("[STATE_LESS] path={} {}.{} < {}.{}",
                case_path_string(),
                la.smaller.name, la.smaller.idx,
                la.larger.name, la.larger.idx);
        }
        if let Some(la) = &sys.last_atom {
            eprintln!("[STATE_LAST] path={} last={}.{}",
                case_path_string(), la.name, la.idx);
        }
    }
}

fn state_nodes_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_STATE_NODES")
}

/// Like `canonical_fact` but KEEPS the LVar idx so diffs reveal node
/// chain depth (which would otherwise canonicalise to the same shape).
fn canonical_fact_with_idx(fa: &crate::fact::LNFact) -> String {
    let terms: Vec<String> = fa.terms.iter().map(canonical_lnterm_with_idx).collect();
    format!("{}({})", fact_tag_short(&fa.tag), terms.join(","))
}

/// Shared canonical LNTerm renderer for the diagnostic traces.  The
/// `var_fmt` closure decides how a variable literal is rendered — the
/// two callers differ ONLY there: `canonical_lnterm_with_idx` keeps the
/// LVar idx (`name#idx`) while `canonical_lnterm` suppresses it and
/// shows the sort (`name:sort`).  Constant / application arms are
/// identical for both.
fn write_lnterm_canon(
    t: &tamarin_term::lterm::LNTerm,
    var_fmt: &impl Fn(&tamarin_term::lterm::LVar) -> String,
) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match t {
        Term::Lit(Lit::Var(v)) => var_fmt(v),
        Term::Lit(Lit::Con(n)) => {
            let nm = &n.id.0;
            match n.tag {
                tamarin_term::lterm::NameTag::Pub => format!("'{}'", nm),
                tamarin_term::lterm::NameTag::Fresh => format!("~'{}'", nm),
                tamarin_term::lterm::NameTag::Nat => format!("%{}", nm),
                tamarin_term::lterm::NameTag::Node => format!("#'{}'", nm),
            }
        }
        Term::App(sym, args) => {
            let head = match sym {
                FunSym::NoEq(s) => String::from_utf8_lossy(s.name).to_string(),
                FunSym::C(_) => "C".to_string(),
                FunSym::Ac(_) => "AC".to_string(),
                FunSym::List => "List".to_string(),
            };
            let args_s: Vec<String> =
                args.iter().map(|a| write_lnterm_canon(a, var_fmt)).collect();
            format!("{}({})", head, args_s.join(","))
        }
    }
}

fn canonical_lnterm_with_idx(t: &tamarin_term::lterm::LNTerm) -> String {
    write_lnterm_canon(t, &|v: &tamarin_term::lterm::LVar| {
        format!("{}{}#{}", sort_prefix(v.sort), v.name, v.idx)
    })
}

fn state_forms_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_STATE_FORMS")
}

fn state_full_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_STATE_FULL")
}

fn state_eqs_flag() -> bool {
    tamarin_utils::env_gate!("TAM_RS_TRACE_STATE_EQS")
}

/// Canonical dump of `sys.eq_store.subst`: sorted list of canonical
/// `var → term` bindings, var idxs suppressed.  RS-only; mirrors the
/// equivalent dump in the private instrumented HS build so the lines
/// diff line-by-line.
fn canonical_eq_store_subst(sys: &crate::constraint::system::System) -> String {
    let mut entries: Vec<String> = sys.eq_store.subst.to_list().into_iter().map(|(k, v)| {
        let k_str = format!("{}{}:{:?}", sort_prefix(k.sort), k.name, k.sort);
        let v_str = canonical_lnterm(&v);
        format!("{}→{}", k_str, v_str)
    }).collect();
    entries.sort();
    format!("[{}]", entries.join(", "))
}

/// Canonicalize an LNTerm by suppressing LVar idxs.  Keeps name+sort,
/// strips the numeric idx.  Same shape on HS / Rust => diff-able.
fn canonical_lnterm(t: &tamarin_term::lterm::LNTerm) -> String {
    write_lnterm_canon(t, &|v: &tamarin_term::lterm::LVar| {
        format!("{}{}:{:?}", sort_prefix(v.sort), v.name, v.sort)
    })
}

fn canonical_fact(fa: &crate::fact::LNFact) -> String {
    let terms: Vec<String> = fa.terms.iter().map(canonical_lnterm).collect();
    format!("{}({})", fact_tag_short(&fa.tag), terms.join(","))
}

fn canonical_node_actions(sys: &crate::constraint::system::System) -> String {
    // Dump all action atoms from sys.nodes — same iteration order as
    // Haskell's `allActions sys` (M.toList sNodes <- rActs).  Idxs
    // suppressed for clean diff.
    let mut acts: Vec<String> = Vec::new();
    for (_, rule) in sys.nodes.iter() {
        for a in &rule.actions {
            acts.push(canonical_fact(a));
        }
    }
    acts.sort();
    
    compress_dups(&acts)
}

fn canonical_open_actions(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::constraints::Goal;
    let mut acts: Vec<String> = Vec::new();
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let Goal::Action(_, fa) = g {
            acts.push(canonical_fact(fa));
        }
    }
    acts.sort();
    
    compress_dups(&acts)
}

/// One-line digest of a goal's shape (tag/arity for fact goals, a bare
/// label otherwise).  Shared by [`trace_pick`] and `canonical_open_goals`.
fn goal_digest(g: &crate::constraint::constraints::Goal) -> String {
    use crate::constraint::constraints::Goal;
    match g {
        Goal::Action(_, fa)  => format!("Action({}/{})",
            fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Premise(_, fa) => format!("Premise({}/{})",
            fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Chain(_, _)    => "Chain".to_string(),
        Goal::Split(_)       => "Split".to_string(),
        Goal::Disj(d)        => format!("Disj[{}]", disj_heads(d)),
        Goal::Subterm(_)     => "Subterm".to_string(),
    }
}

/// Emit a [PICK] line indicating which goal was selected for this dispatch.
/// RS-only; paired with the equivalent goal-pick trace in the private
/// instrumented HS build so we can compare goal-ranking decisions.
pub fn trace_pick(g: &crate::constraint::constraints::Goal) {
    use crate::constraint::constraints::Goal;
    if !state_flag() { return; }
    let s = goal_digest(g);
    // For Disj goals, also dump the full alternatives (with var idxs
    // preserved) so HS↔Rust comparison can catch dispatch-order
    // divergences — e.g. Helper_Loop_and_success at case_3 has 2
    // Disj goals with identical PICK heads (`Disj[Atom(Eq)|Atom(Less)
    // |Ex1v]`) but DIFFERENT alternatives (one has ChainKey(k#1) in
    // its Ex body, the other has ChainKey(f(k#1))).  HS picks the
    // f-wrapped one first; Rust picks the bare-k#1 one — causing the
    // case_3 over-split.
    if let Goal::Disj(d) = g {
        if tamarin_utils::env_gate!("TAM_RS_TRACE_PICK_DISJ") {
            let alts: Vec<String> = d.0.iter().map(guarded_repr).collect();
            eprintln!("[PICK_DISJ] Disj[{}]", alts.join(" || "));
        }
    }
    // TAM_RS_TRACE_PICK_TERM=1 also emits the full picked-fact term repr
    // for Action/Premise goals.  Used to compare HS↔Rust goal-ranking
    // when [PICK] heads agree but the picked goal-term differs.
    if tamarin_utils::env_gate!("TAM_RS_TRACE_PICK_TERM") {
        use tamarin_term::pretty::pretty_lnterm;
        let term_repr = match g {
            Goal::Action(_, fa) | Goal::Premise(_, fa) => {
                let ts: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
                format!("{}({})", fact_tag_short(&fa.tag), ts.join(", "))
            }
            _ => String::new(),
        };
        if !term_repr.is_empty() {
            eprintln!("[PICK_TERM] {}", term_repr);
        }
    }
    eprintln!("[PICK] {}", s);
}

fn canonical_nodes(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::solver::reduction::rule_case_name;
    let mut names: Vec<String> = sys.nodes.iter()
        .map(|(_, r)| rule_case_name(r))
        .collect();
    names.sort();
    compress_dups(&names)
}

fn canonical_open_goals(sys: &crate::constraint::system::System) -> String {
    let mut digests: Vec<String> = sys.goals.iter()
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
        // Format matches that HS build's guarded-head trace: `<Quant><N>v`
        // (e.g. `Ex1v`).  Suppresses bound-var names so HS/Rust line up.
        Guarded::GGuarded { qua, vars, .. } => format!("{:?}{}v",
            qua, vars.len()),
    }
}

fn compress_dups(sorted: &[String]) -> String {
    if sorted.is_empty() { return "[]".to_string(); }
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
        if iter.peek().is_some() { out.push(','); }
    }
    out.push(']');
    out
}
