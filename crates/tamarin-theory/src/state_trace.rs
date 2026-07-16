//! Canonical state tracer for cross-solver (Haskell vs Rust) comparison.
//!
//! Emitting a one-line summary at each major solver event lets us
//! diff two proof runs (Haskell's `tamarin-prover` vs our Rust port)
//! side-by-side and localize where the two diverge.  Format is
//! deliberately compact and stable.  The comparison relies on a
//! SEPARATE, local Haskell instrumentation patch (mirroring this
//! format in the `Theory.Constraint.Solver.Sources` and
//! `Theory.Constraint.Solver.Goals` modules) which is NOT checked into
//! this repository; apply that patch to the Haskell tree to produce a
//! trace that lines up with this one.
//!
//! ## Usage
//!
//! Set `TAM_TRACE_STATE=1` and run the prover; lines go to stderr.
//! For TLS investigation:
//!
//! ```sh
//! TAM_TRACE_STATE=1 cargo run -p tamarin-theory --release --example probe_lemma \
//!     -- examples/classic/TLS_Handshake.spthy session_key_setup_possible 200 \
//!     2>/tmp/rust.trace
//! TAM_TRACE_STATE=1 tamarin-prover --prove=session_key_setup_possible \
//!     examples/classic/TLS_Handshake.spthy 2>/tmp/haskell.trace
//! diff /tmp/haskell.trace /tmp/rust.trace
//! ```
//!
//! ## Format
//!
//! One event per line, bracketed:
//!
//! ```text
//! [STATE path=<path> step=<step> op=<op> goal=<goal_summary> <fingerprint>]
//! ```
//!
//! Case-selection points (`emit_case`) add a `case=<name>` field after
//! `op=`:
//!
//! ```text
//! [STATE path=<path> step=<step> op=<op> case=<name> goal=<goal_summary> <fingerprint>]
//! ```
//!
//! Fields:
//! - `<path>`: the current case path (see `solver::trace`).
//! - `<step>`: monotonically-increasing per-process counter (never
//!   reset; one lemma is proved per process on the probe examples, so
//!   side-by-side line `N` of the two traces are comparable when the
//!   first divergence is at step `N`).
//! - `<op>`: short verb identifying the event (`expand`, `pick`,
//!   `case`, `applySource`, `simplify_in`, `simplify_out`, …).
//! - `<goal_summary>`: compact form of the current goal (or `-`).
//! - `<fingerprint>`: `n=<#nodes> e=<#edges> gO=<#open-goals>`
//!   ` f=<#formulas> sf=<#solved-formulas> eqs=<#subst-entries>`
//!   ` la=<Y|N>`.
//!
//! Keeping the format identical on both sides lets us use `diff` /
//! `comm` / `paste` to localize the first divergence.

use std::sync::atomic::{AtomicU64, Ordering};

static STEP: AtomicU64 = AtomicU64::new(0);

/// Whether tracing is enabled (env var `TAM_TRACE_STATE` set).
/// `emit`/`emit_case` call this from solver inner loops (thousands of
/// times per proof), so cache the read once per process behind a
/// `OnceLock<bool>` — the disabled-path emit calls then stay free.
pub fn enabled() -> bool {
    tamarin_utils::env_gate!("TAM_TRACE_STATE")
}

/// Compact one-line summary of a `System`'s shape.  Mirrors the
/// format produced by the separate (out-of-tree) Haskell
/// instrumentation patch described in the module header.
pub fn fingerprint(sys: &crate::constraint::system::System) -> String {
    let n = sys.nodes.len();
    let e = sys.edges.len();
    let g_open = sys.goals.iter().filter(|(_, st)| !st.solved).count();
    let f = sys.formulas.len();
    let sf = sys.solved_formulas.len();
    let eqs = sys.eq_store.subst.to_list().len();
    let la = if sys.last_atom.is_some() { 'Y' } else { 'N' };
    format!(
        "n={} e={} gO={} f={} sf={} eqs={} la={}",
        n, e, g_open, f, sf, eqs, la
    )
}

/// Short label for a `FactTag` as used by the tracer (`KU`, `KD`, the
/// protocol fact name, `Fr`, `In`, `Out`, `Ded`, `Term`).
fn fact_tag_label(tag: &crate::fact::FactTag) -> String {
    use crate::fact::FactTag;
    match tag {
        FactTag::Ku => "KU".to_string(),
        FactTag::Kd => "KD".to_string(),
        FactTag::Proto(_, name, _) => name.to_string(),
        FactTag::Fresh => "Fr".to_string(),
        FactTag::In => "In".to_string(),
        FactTag::Out => "Out".to_string(),
        FactTag::Ded => "Ded".to_string(),
        FactTag::Term => "Term".to_string(),
    }
}

/// Compact one-line summary of a `Goal` (or `-` when no goal).
pub fn goal_summary(g: Option<&crate::constraint::constraints::Goal>) -> String {
    use crate::constraint::constraints::Goal;
    let tag_label = |fa: &crate::fact::LNFact, prefix: &str| -> String {
        format!("{}{}({})", prefix, fact_tag_label(&fa.tag), terms_summary(&fa.terms))
    };
    match g {
        None => "-".into(),
        Some(Goal::Action(_, fa)) => tag_label(fa, ""),
        Some(Goal::Premise(_, fa)) => tag_label(fa, "Pre/"),
        Some(Goal::Chain(_, _)) => "Chain".into(),
        Some(Goal::Disj(_)) => "Disj".into(),
        Some(Goal::Split(_)) => "Split".into(),
        Some(Goal::Subterm(_)) => "Subterm".into(),
    }
}

/// Compact summary of a term list — preserves function symbols but
/// elides arguments for compactness.
fn terms_summary(ts: &[tamarin_term::lterm::LNTerm]) -> String {
    let mut out = String::new();
    for (i, t) in ts.iter().enumerate() {
        if i > 0 { out.push(','); }
        out.push_str(&term_summary(t));
    }
    out
}

/// Compact summary of a single term.  Preserves the head symbol,
/// abbreviates vars to `name:sort:idx` (sort as a 1-char code),
/// shows `<...>` for pair sub-trees.
pub fn term_summary(t: &tamarin_term::lterm::LNTerm) -> String {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match t {
        Term::Lit(Lit::Var(v)) => {
            let sort_ch = match v.sort {
                LSort::Msg => 'M',
                LSort::Pub => 'P',
                LSort::Fresh => 'F',
                LSort::Nat => 'N',
                LSort::Node => 'I',
            };
            // Include the idx for every var so the trace is uniform
            // and diffable — this disambiguates identical-looking
            // names that differ only by idx (sort-conflation debugging).
            format!("{}:{}:{}", v.name, sort_ch, v.idx)
        }
        Term::Lit(Lit::Con(c)) => format!("'{}'", c.id.0),
        Term::App(FunSym::NoEq(noeq), args) => {
            let name = String::from_utf8_lossy(noeq.name);
            if name == "pair" {
                let mut inner = Vec::new();
                fn flatten<'a>(t: &'a tamarin_term::lterm::LNTerm,
                               out: &mut Vec<&'a tamarin_term::lterm::LNTerm>) {
                    if let Term::App(FunSym::NoEq(ns), args) = t {
                        if ns.name == b"pair" {
                            flatten(&args[0], out);
                            flatten(&args[1], out);
                            return;
                        }
                    }
                    out.push(t);
                }
                flatten(t, &mut inner);
                let s: Vec<String> = inner.iter().map(|x| term_summary(x)).collect();
                format!("<{}>", s.join(","))
            } else {
                let s: Vec<String> = args.iter().map(term_summary).collect();
                format!("{}({})", name, s.join(","))
            }
        }
        Term::App(FunSym::List, args) => {
            let s: Vec<String> = args.iter().map(term_summary).collect();
            format!("[{}]", s.join(","))
        }
        Term::App(FunSym::Ac(_), _) | Term::App(FunSym::C(_), _) => "AC?".into(),
    }
}

/// Bump the step counter and return its previous value.
fn next_step() -> u64 {
    STEP.fetch_add(1, Ordering::SeqCst)
}

/// Whether full goal/formula dumps are enabled (`TAM_TRACE_DUMP=1`).
fn dump_enabled() -> bool {
    tamarin_utils::env_gate!("TAM_TRACE_DUMP")
}

/// Dump system goals and formulas to stderr — useful when fingerprint
/// counts diverge and we need to know exactly what's on each side.
fn dump_sys(sys: &crate::constraint::system::System) {
    if !dump_enabled() { return; }
    eprintln!("  goals:");
    for (g, st) in sys.goals.iter() {
        eprintln!("    [{}{}] {}",
            if st.solved { "S" } else { "-" },
            if st.looping { "L" } else { "-" },
            goal_summary(Some(g)));
    }
    eprintln!("  nodes:");
    for (id, rule) in sys.nodes.iter() {
        eprintln!("    {}:{} prems=[{}] concs=[{}] acts=[{}]",
            id.name, id.idx,
            rule.premises.iter().map(state_trace_fact_brief).collect::<Vec<_>>().join(","),
            rule.conclusions.iter().map(state_trace_fact_brief).collect::<Vec<_>>().join(","),
            rule.actions.iter().map(state_trace_fact_brief).collect::<Vec<_>>().join(","));
    }
    eprintln!("  edges: {}", sys.edges.len());
}

fn state_trace_fact_brief(fa: &crate::fact::LNFact) -> String {
    let label = fact_tag_label(&fa.tag);
    let args: Vec<String> = fa.terms.iter().map(term_summary).collect();
    format!("{}({})", label, args.join(","))
}

/// Emit one trace event line.
pub fn emit(op: &str, goal: Option<&crate::constraint::constraints::Goal>,
            sys: &crate::constraint::system::System) {
    if !enabled() { return; }
    let s = next_step();
    let path = crate::constraint::solver::trace::case_path_string();
    eprintln!("[STATE path={} step={} op={} goal={} {}]",
        path, s, op, goal_summary(goal), fingerprint(sys));
    dump_sys(sys);
}

/// Emit a trace event with an extra `case=<name>` tag (used by
/// case-selection points like the SolveGoal filter).
pub fn emit_case(op: &str, case_name: &str,
                 goal: Option<&crate::constraint::constraints::Goal>,
                 sys: &crate::constraint::system::System) {
    if !enabled() { return; }
    let s = next_step();
    let path = crate::constraint::solver::trace::case_path_string();
    eprintln!("[STATE path={} step={} op={} case={} goal={} {}]",
        path, s, op, case_name, goal_summary(goal), fingerprint(sys));
    dump_sys(sys);
}
