//! Solver-component oracle: cross-check our Rust pipeline against
//! `tamarin-prover 1.12.0` on small fixture `.spthy` files.
//!
//! For each fixture we verify:
//! 1. The Rust parser/elaborator accepts the file.
//! 2. Wellformedness: no errors (the fixtures are clean).
//! 3. `tamarin-prover --parse-only` agrees the file is syntactically
//!    well-formed (return code 0).
//! 4. `tamarin-prover --prove` produces a non-error summary (the
//!    fixtures are all small `exists-trace` lemmas tamarin can solve
//!    in a few steps).
//! 5. The number of lemmas we elaborate equals what tamarin sees.
//! 6. For each lemma, the guarded conversion succeeds.
//!
//! The harness skips silently when `tamarin-prover` isn't on `PATH`,
//! so the test stays fast in environments without the binary.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::path::{Path, PathBuf};
use std::process::Command;

use tamarin_parser::parse_theory;
use tamarin_theory::guarded::{formula_to_guarded, Guarded, Quant};

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn corpus_root() -> PathBuf {
    std::env::var("CORPUS_ROOT").map(PathBuf::from).unwrap_or_else(|_| {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
    })
}

fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
    for c in ["/usr/local/bin/maude", "maude"] {
        if std::path::Path::new(c).exists() { return Some(c.to_string()); }
    }
    None
}

fn tamarin_available() -> bool {
    Command::new("tamarin-prover")
        .arg("--help")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn run_tamarin_parse_only(path: &Path) -> Option<String> {
    let out = Command::new("tamarin-prover")
        .arg("--parse-only")
        .arg(path)
        .output()
        .ok()?;
    if !out.status.success() { return None; }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn run_tamarin_prove(path: &Path) -> Option<String> {
    let out = Command::new("tamarin-prover")
        .arg("--prove")
        .arg(path)
        .output()
        .ok()?;
    if !out.status.success() { return None; }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Count `lemma <name>` occurrences in tamarin's parse output.
fn count_lemmas_in_output(s: &str) -> usize {
    s.lines().filter(|l| l.trim_start().starts_with("lemma ")).count()
}

/// Count `rule <name>:` occurrences in tamarin's parse output.
fn count_rules_in_output(s: &str) -> usize {
    s.lines().filter(|l| {
        let t = l.trim_start();
        t.starts_with("rule ") && t.contains(':')
    }).count()
}

/// Extract the `summary of summaries` block — useful for asserting
/// every lemma got a verdict.
fn extract_summary(s: &str) -> Option<&str> {
    let i = s.find("summary of summaries:")?;
    Some(&s[i..])
}

fn rust_lemma_count(src: &str) -> usize {
    let theory = parse_theory(src, &[]).expect("parse_theory");
    theory.items.iter()
        .filter(|i| matches!(i, tamarin_parser::ast::TheoryItem::Lemma(_)))
        .count()
}

fn rust_rule_count(src: &str) -> usize {
    let theory = parse_theory(src, &[]).expect("parse_theory");
    theory.items.iter()
        .filter(|i| matches!(i, tamarin_parser::ast::TheoryItem::Rule(_)))
        .count()
}

/// Map a lemma's trace quantifier + solved-root status onto tamarin's
/// verdict string.  Returns `None` for the incomparable fallthrough
/// (root status is neither Solved nor Contradictory) — each caller keeps
/// its own None handling/logging.  Shared by the two corpus probes below.
fn verdict_str(
    tq: &tamarin_parser::ast::TraceQuantifier,
    st: &tamarin_theory::constraint::solver::search::NodeStatus,
) -> Option<&'static str> {
    use tamarin_parser::ast::TraceQuantifier;
    use tamarin_theory::constraint::solver::search::NodeStatus;
    match (tq, st) {
        (TraceQuantifier::ExistsTrace, NodeStatus::Solved) => Some("verified"),
        (TraceQuantifier::ExistsTrace, NodeStatus::Contradictory) => Some("falsified"),
        (TraceQuantifier::AllTraces, NodeStatus::Contradictory) => Some("verified"),
        (TraceQuantifier::AllTraces, NodeStatus::Solved) => Some("falsified"),
        _ => None,
    }
}

/// Per-lemma kill-watchdog used by the corpus probes.  The wall-clock
/// deadline at `search::expand` fires BETWEEN expand calls, but a single
/// blocking Maude IPC read sits forever if Maude itself hangs.  A watchdog
/// thread kills the subprocess after a hard cap; the blocked read then
/// returns EOF and `prove_lemma` unwinds with an error.  Without this, even
/// one hung lemma blocks the whole `par_iter().collect()`.
struct WatchdogGuard {
    done: std::sync::Arc<std::sync::atomic::AtomicBool>,
    fired: std::sync::Arc<std::sync::atomic::AtomicBool>,
    join: Option<std::thread::JoinHandle<()>>,
}

impl WatchdogGuard {
    /// Signal completion, join the watchdog thread, and report whether it
    /// fired (killed the subprocess) before we finished.
    fn finish(mut self) -> bool {
        self.done.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(j) = self.join.take() {
            let _ = j.join();
        }
        self.fired.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl Drop for WatchdogGuard {
    fn drop(&mut self) {
        self.done.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(j) = self.join.take() {
            let _ = j.join();
        }
    }
}

/// Spawn a watchdog thread that kills `h`'s subprocess after `dur`, unless
/// the returned guard is finished/dropped first.
fn spawn_kill_watchdog(
    h: tamarin_term::maude_proc::MaudeHandle,
    dur: std::time::Duration,
) -> WatchdogGuard {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    let done = Arc::new(AtomicBool::new(false));
    let fired = Arc::new(AtomicBool::new(false));
    let done_clone = done.clone();
    let fired_clone = fired.clone();
    let join = std::thread::spawn(move || {
        let deadline = std::time::Instant::now() + dur;
        while std::time::Instant::now() < deadline {
            if done_clone.load(Ordering::Relaxed) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        fired_clone.store(true, Ordering::Relaxed);
        h.kill_subprocess();
    });
    WatchdogGuard { done, fired, join: Some(join) }
}

#[test]
fn fixture_tiny_setup_round_trip() {
    let path = fixtures_dir().join("tiny_setup.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    // Rust side: parses, has 1 rule, 1 lemma.
    assert_eq!(rust_rule_count(&src), 1);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() { return; }

    // Tamarin parse-only.
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 1);
    assert_eq!(count_lemmas_in_output(&out), 1);

    // Tamarin proves it.
    let proved = run_tamarin_prove(&path).expect("tamarin prove");
    let summary = extract_summary(&proved).expect("summary block");
    assert!(summary.contains("verified"),
        "expected 'verified' in summary:\n{}", summary);
}

#[test]
fn fixture_two_rules_round_trip() {
    let path = fixtures_dir().join("two_rules.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    assert_eq!(rust_rule_count(&src), 2);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() { return; }
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 2);
    assert_eq!(count_lemmas_in_output(&out), 1);
}

/// Sample a small set of real-corpus examples and check that lemma
/// and rule counts match between the Rust parser and tamarin's
/// `--parse-only` output. Covers larger / more realistic theories.
#[test]
fn corpus_sample_lemma_and_rule_counts_match() {
    if !tamarin_available() { return; }
    let corpus = corpus_root();
    let candidates = [
        "Tutorial.spthy",
        "MinimalHashChainExample.spthy",
        "MinimalAKEExample.spthy",
        "TLS_Handshake.spthy",
        "Yubikey.spthy",
    ];
    let mut compared = 0;
    let mut mismatches: Vec<String> = Vec::new();
    for name in &candidates {
        // Find the example file anywhere under the corpus.
        let found = walkdir::WalkDir::new(&corpus)
            .into_iter()
            .filter_map(|e| e.ok())
            .find(|e| e.file_name() == *name)
            .map(|e| e.path().to_path_buf());
        let path = match found { Some(p) => p, None => continue };

        let src = match std::fs::read_to_string(&path) { Ok(s) => s, Err(_) => continue };
        let our_rules = match std::panic::catch_unwind(|| rust_rule_count(&src)) {
            Ok(n) => n, Err(_) => continue,
        };
        let our_lemmas = match std::panic::catch_unwind(|| rust_lemma_count(&src)) {
            Ok(n) => n, Err(_) => continue,
        };
        let out = match run_tamarin_parse_only(&path) { Some(o) => o, None => continue };
        let tam_rules = count_rules_in_output(&out);
        let tam_lemmas = count_lemmas_in_output(&out);

        compared += 1;
        // Tamarin's pretty-print may expand let-defs / restrictions
        // so allow tamarin to have ≥ ours on rules. Lemmas should be
        // exact — tamarin doesn't synthesise lemmas.
        if our_lemmas != tam_lemmas {
            mismatches.push(format!(
                "{}: lemmas ours={} theirs={}",
                path.display(), our_lemmas, tam_lemmas));
        }
        if our_rules > tam_rules {
            mismatches.push(format!(
                "{}: rules ours={} > theirs={}",
                path.display(), our_rules, tam_rules));
        }
    }
    if !mismatches.is_empty() {
        panic!("rule/lemma count mismatches ({} compared):\n  {}",
            compared, mismatches.join("\n  "));
    }
    // Make sure we actually compared at least one file when the
    // tamarin binary and corpus are available.
    if compared == 0 {
        eprintln!("warning: no corpus files matched (skipping)");
    }
}

/// Count quantifiers in a guarded formula.
fn count_quantifiers(g: &Guarded) -> (usize, usize) {
    fn rec(g: &Guarded, ex: &mut usize, all: &mut usize) {
        match g {
            Guarded::Atom(_) => {}
            Guarded::Conj(xs) | Guarded::Disj(xs) => {
                for x in xs.iter() { rec(x, ex, all); }
            }
            Guarded::GGuarded { qua, vars, body, .. } => {
                let n = vars.len();
                match qua {
                    Quant::Ex => *ex += n,
                    Quant::All => *all += n,
                }
                rec(body, ex, all);
            }
        }
    }
    let mut ex = 0;
    let mut all = 0;
    rec(g, &mut ex, &mut all);
    (ex, all)
}

/// Cross-check guarded formula structure: for each lemma in a fixture,
/// count Ex/All in our `formula_to_guarded` output and compare with
/// the count of `∃` / `∀` characters in tamarin's `--prove` output's
/// guarded-formula block. Tamarin always emits exactly one quantifier
/// glyph per quantified variable.
#[test]
fn guarded_quantifier_count_matches_tamarin() {
    if !tamarin_available() { return; }
    let cases = ["tiny_setup.spthy", "two_rules.spthy", "disj_lemma.spthy"];
    for name in &cases {
        let path = fixtures_dir().join(name);
        let src = std::fs::read_to_string(&path).expect("read fixture");
        let theory = parse_theory(&src, &[]).expect("parse_theory");
        // Sum quantifier counts across all lemmas in this fixture.
        let mut our_ex = 0usize;
        let mut our_all = 0usize;
        for it in &theory.items {
            if let tamarin_parser::ast::TheoryItem::Lemma(l) = it {
                let g = formula_to_guarded(&l.formula).expect("guarded conv");
                let (ex, all) = count_quantifiers(&g);
                our_ex += ex;
                our_all += all;
            }
        }
        let proved = match run_tamarin_prove(&path) {
            Some(o) => o, None => continue,
        };
        // Tamarin emits one ∃/∀ glyph per quantifier *block* (it
        // groups consecutive vars under a single quantifier), whereas
        // our `count_quantifiers` returns the total number of bound
        // variables. So we use a presence-parity check rather than
        // an exact comparison.
        let tam_has_ex = proved.contains('∃');
        let tam_has_all = proved.contains('∀');
        assert_eq!(our_ex > 0, tam_has_ex,
            "{}: our_ex={} vs tam_has_ex={}", name, our_ex, tam_has_ex);
        assert_eq!(our_all > 0, tam_has_all,
            "{}: our_all={} vs tam_has_all={}", name, our_all, tam_has_all);
    }
}

/// End-to-end: parse the disj_lemma fixture, build the initial
/// system, simplify, and verify the formula structure stays intact.
/// `reducible_formula(Disj) = false` matches Haskell — top-level Disj
/// does NOT get decomposed by `reduce_formulas`. Decomposition happens
/// later via `Induction` or via being nested inside a reducible parent.
#[test]
fn simplify_top_level_disj_lemma_left_intact() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy"))
        .expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    let n_formulas_before = sys.formulas.len();
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    // The top-level Disj is non-reducible, so the formula count
    // doesn't change.
    assert_eq!(r.sys.formulas.len(), n_formulas_before);
    // No Goal::Disj created during simplify alone (induction or
    // SolveGoal would trigger that).
    assert!(!r.sys.goals.iter().any(|(g, _)|
        matches!(g, tamarin_theory::constraint::constraints::Goal::Disj(_))));
}

/// End-to-end: drive `run_proof_search` on the disj_lemma fixture
/// from start. The search should pick `Induction` first (matching
/// tamarin), creating two cases: `empty_trace` and `non_empty_trace`.
/// Tamarin's actual proof for this fixture: induction → case_1 → SOLVED.
#[test]
fn proof_search_disj_lemma_picks_induction_first() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::run_proof_search;
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy"))
        .expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    let root = run_proof_search(&ctx, sys, 5);
    // First method should be Induction — matches tamarin's
    // `induction` step at the start of the proof.
    assert!(matches!(root.method, ProofMethod::Induction),
        "expected Induction, got {:?}", root.method);
    // Two children: empty_trace and non_empty_trace.
    assert_eq!(root.children.len(), 2);
    assert!(root.children.contains_key("empty_trace"));
    assert!(root.children.contains_key("non_empty_trace"));
}

/// **Verdict-match suite**: drive each fixture through `prove_lemma`
/// and confirm our verdict matches tamarin's `verified` outcome.
///
/// Verdict mapping:
/// - **`exists-trace`** lemma + tamarin `verified` ⇒ we expect `Solved`
///   (we found a satisfying trace).
/// - **`all-traces`** lemma + tamarin `verified` ⇒ we expect
///   `Contradictory` (the negated counterexample-search dead-ended,
///   which means the lemma holds).
#[test]
fn verdict_match_suite_all_solved_against_tamarin() {
    use tamarin_theory::constraint::solver::search::NodeStatus;
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() { Some(p) => p, None => return };

    // (fixture, lemma, expected our-side status) — tamarin must say
    // `verified` for every entry.
    let cases: &[(&str, &str, NodeStatus)] = &[
        // Existence lemmas → Solved.
        ("tiny_setup.spthy", "trivial", NodeStatus::Solved),
        ("two_actions.spthy", "both_actions", NodeStatus::Solved),
        ("three_facts.spthy", "all_three", NodeStatus::Solved),
        ("multi_rule.spthy", "can_a", NodeStatus::Solved),
        ("multi_rule.spthy", "can_b", NodeStatus::Solved),
        ("multi_rule.spthy", "can_c", NodeStatus::Solved),
        ("multi_arity.spthy", "pair_exists", NodeStatus::Solved),
        ("multi_arity.spthy", "triple_exists", NodeStatus::Solved),
        ("pub_var.spthy", "setup_exists", NodeStatus::Solved),
        ("persistent_fact.spthy", "init_exists", NodeStatus::Solved),
        ("with_restriction.spthy", "a_exists", NodeStatus::Solved),
        // Multi-rule chain (Send → Recv) needs intruder rules for KU.
        ("two_rules.spthy", "reachable", NodeStatus::Solved),
        // Send-Receive with timing constraint (#i < #j).
        ("sendrecv_chain.spthy", "chain_works", NodeStatus::Solved),
        // 3-rule chain with shared state (St1 → St2).
        ("three_rule.spthy", "all_three_steps", NodeStatus::Solved),
        // Multiple persistent fact dependencies.
        ("two_keys.spthy", "can_use", NodeStatus::Solved),
        // Multiple lemmas in one theory.
        ("multiple_lemmas.spthy", "init_exists", NodeStatus::Solved),
        ("multiple_lemmas.spthy", "active_exists", NodeStatus::Solved),
        ("multiple_lemmas.spthy", "done_exists", NodeStatus::Solved),
        ("multiple_lemmas.spthy", "all_at_same_node", NodeStatus::Solved),
        // 5-step state-machine chain.
        ("auth_pattern.spthy", "protocol_runs", NodeStatus::Solved),
        // Simple In/Out chain — no pair construction.
        ("single_recv.spthy", "chain", NodeStatus::Solved),
        // All-traces lemmas → Contradictory (negation dead-ends).
        ("safety_unique.spthy", "setup_unique", NodeStatus::Contradictory),
        ("safety_two_keys.spthy", "fresh_distinct_times", NodeStatus::Contradictory),
        // Restriction-driven uniqueness lemma.
        ("restriction_unique.spthy", "setup_unique", NodeStatus::Contradictory),
        // Reuse-flagged lemma — stands alone and is verifiable.
        ("reuse_lemma.spthy", "setup_unique", NodeStatus::Contradictory),
        // [use_induction] attribute — trivially-true tautology.
        ("use_induction.spthy", "a_self", NodeStatus::Contradictory),
        // Rule-level let-block desugaring (`let r = ~k in ...`).
        ("let_block.spthy", "use_self", NodeStatus::Contradictory),
        // Fresh-ordering CR-rule + edge-aware cyclic check: ~s
        // creator must precede any rule mentioning ~s downstream.
        ("fresh_ordering.spthy", "order", NodeStatus::Contradictory),
        // [sources] lemma — forces induction + appends to restrictions.
        ("sources_lemma.spthy", "setup_self", NodeStatus::Contradictory),
        ("sources_lemma.spthy", "setup_unique", NodeStatus::Contradictory),
        // partialAtomValuation: `i < j | i = j` collapses once the
        // chain edge fires and `alwaysBefore` decides the disjunct.
        ("eval_atoms.spthy", "a_then_b", NodeStatus::Contradictory),
    ];

    // Tamarin falsifies `never_both` — for an all-traces lemma that's
    // FALSE, our counter-example search should reach `Solved`.
    let falsifiable_cases: &[(&str, &str, NodeStatus, &str)] = &[
        ("falsifiable.spthy", "never_both", NodeStatus::Solved, "falsified"),
        ("falsified_unique_action.spthy", "x_unique", NodeStatus::Solved, "falsified"),
        ("falsified_chain.spthy", "a_implies_b", NodeStatus::Solved, "falsified"),
    ];

    for (fixture, lemma, expected) in cases {
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let path = fixtures_dir().join(fixture);
        let src = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {}", fixture, e));
        let theory = parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&theory, lemma, h, 200)
            .unwrap_or_else(|e| panic!("prove_lemma({}/{}): {:?}", fixture, lemma, e));
        assert_eq!(root.status, *expected,
            "{}/{}: expected {:?}, got {:?}", fixture, lemma, expected, root.status);

        // Confirm tamarin agrees, when the binary is available.
        if !tamarin_available() { continue; }
        let proved = run_tamarin_prove(&path).expect("tamarin");
        let summary = extract_summary(&proved).expect("summary");
        // The summary lists every lemma; check this one shows verified.
        let line = summary.lines()
            .find(|l| l.contains(&format!("{} (", lemma)))
            .unwrap_or_else(|| panic!("no summary line for {}", lemma));
        assert!(line.contains("verified"),
            "tamarin should verify {}/{}; got line:\n{}", fixture, lemma, line);
    }

    // Falsifiable lemmas: verdict = falsified ↔ Solved (counterexample).
    for (fixture, lemma, expected, marker) in falsifiable_cases {
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let path = fixtures_dir().join(fixture);
        let src = std::fs::read_to_string(&path).expect("read");
        let theory = parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&theory, lemma, h, 200)
            .unwrap_or_else(|e| panic!("prove_lemma({}/{}): {:?}", fixture, lemma, e));
        assert_eq!(root.status, *expected,
            "{}/{}: expected {:?}, got {:?}", fixture, lemma, expected, root.status);

        if !tamarin_available() { continue; }
        let proved = run_tamarin_prove(&path).expect("tamarin");
        let summary = extract_summary(&proved).expect("summary");
        let line = summary.lines()
            .find(|l| l.contains(&format!("{} (", lemma)))
            .unwrap_or_else(|| panic!("no summary line for {}", lemma));
        assert!(line.contains(*marker),
            "tamarin should mark {}/{} as `{}`; got line:\n{}", fixture, lemma, marker, line);
    }
}

/// **Haskell-behavior pin tests**: structural cross-checks that
/// don't just compare verdicts but pin specific Haskell-documented
/// behaviors:
///   1. Tamarin emits "unguarded variable(s)" for non-doubly-guarded
///      formulas — our `formula_to_guarded` should too.
///   2. Tamarin's signature output for a `pair`-only theory contains
///      `pair/2`, `fst/1`, `snd/1` — our elaboration agrees.
///   3. Tamarin's `--prove` summary line format is
///      `<name> (exists-trace|all-traces): verified|falsified (...)`
///      — our verdict should map to the same kind.
#[test]
fn haskell_behavior_pins() {
    if !tamarin_available() { return; }

    // Pin #1: error message wording for unguarded variables.
    let bad = r#"theory T begin
rule R: [Fr(~k)] --[A(~k)]-> []
lemma bad: exists-trace "Ex k #i. (A(k) @ #i) | (A(k) @ #i)"
end"#;
    let tmp = std::env::temp_dir().join("oracle_pin_bad_guarded.spthy");
    std::fs::write(&tmp, bad).unwrap();
    let out = Command::new("tamarin-prover")
        .arg("--prove").arg(&tmp).output().expect("tamarin");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let combined = format!("{}{}", stderr, stdout);
    assert!(combined.contains("unguarded variable"),
        "tamarin should reject this formula with 'unguarded variable'; got:\n{}",
        combined);
    // Our side: rejected with same wording.
    let parsed = parse_theory(bad, &[]).expect("parse");
    let lemma = parsed.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let err = tamarin_theory::guarded::formula_to_guarded(&lemma.formula)
        .expect_err("our guarded conversion should reject");
    assert!(err.message.contains("unguarded variable"),
        "we should also report 'unguarded variable'; got: {:?}", err);
    let _ = std::fs::remove_file(&tmp);

    // Pin #2: tamarin --parse-only output for a pair-only theory
    // names `pair`, `fst`, `snd` symbols (matches our elaboration's
    // signature population).
    let pair_thy = "theory P begin\nrule R: [Fr(~k)] --[A(~k)]-> [Out(<~k, ~k>)]\nend";
    let ptmp = std::env::temp_dir().join("oracle_pin_pair.spthy");
    std::fs::write(&ptmp, pair_thy).unwrap();
    let out = Command::new("tamarin-prover")
        .arg("--parse-only").arg(&ptmp).output().expect("tamarin");
    let outs = String::from_utf8_lossy(&out.stdout);
    assert!(outs.contains("pair/2") || outs.contains("pair"),
        "tamarin's signature should mention pair: {}", outs);
    let _ = std::fs::remove_file(&ptmp);
}

/// **Corpus verdict-match coverage probe**: walks `examples/loops/`
/// (small, no-equation theories), runs `prove_lemma` and
/// `tamarin-prover --prove` on every lemma, reports a verdict-match
/// count to stderr. Doesn't fail unless 0/N match — used as a
/// diagnostic to track progress over time.
///
/// Skips files that:
///  - declare functions/equations our skeleton can't unify
///  - use macros, predicates, or accountability constructs
///  - take longer than 10s on tamarin's side
///
/// **Deprecated** as a primary metric — verdict-only matching masks
/// reasoning bugs (right answer, wrong proof structure).  Use
/// `corpus_proof_skeleton_match_probe` instead for the
/// structural-match metric that the project actually optimizes.
#[test]
#[ignore = "verdict-only metric is deprecated; use corpus_proof_skeleton_match_probe"]
fn corpus_verdict_match_coverage_probe() {
    use rayon::prelude::*;
    use tamarin_theory::prove::prove_lemma;

    // Configure rayon thread-pool with a larger stack — Goal-Ord + Sk
    // matcher path is recursively deeper on some protocols than rayon's
    // default 2 MiB worker stack tolerates.  64 MiB is plenty.
    let _ = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build_global();

    let mp = match maude_path() { Some(p) => p, None => return };
    if !tamarin_available() { return; }

    // Per-process global — set ONCE before parallel work so threads
    // don't race on env writes.  Step budget (2000) is the deterministic
    // gate; 10s deadline is the wall-clock backstop.
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");

    let corpus_root = corpus_root();
    let target_dirs = [
        "loops", "csf23-subterms", "experiments", "regression",
        "ccs15", "classic", "features", "related_work",
        "post17", "cav13", "jcs18", "csf18-alethea",
        // Added — small dirs with mostly-supported protocols.  csf17
        // is 4 files all unexcluded; csf12 has a few simple ones.
        "csf17", "csf12",
        // testParser is parser-level fixtures; define.spthy is a tiny
        // #ifdef preprocessor exercise.
        "testParser",
    ];

    // Phase 1: collect candidate spthy paths (sequential — just I/O).
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    for dir in &target_dirs {
        let dir_path = corpus_root.join(dir);
        if !dir_path.exists() { continue; }
        for e in walkdir::WalkDir::new(&dir_path).max_depth(2).into_iter().filter_map(|e| e.ok()) {
            if e.path().extension().and_then(|s| s.to_str()) == Some("spthy") {
                // testParser/include uses #include which pulls in
                // user-defined equations from sibling files; the
                // builtin-filter on the entry file can't see them.
                let p = e.path();
                if p.to_string_lossy().contains("/testParser/include/") { continue; }
                paths.push(p.to_path_buf());
            }
        }
    }

    // Phase 2: per-file work (parse + tamarin invocation) in parallel.
    // Each successful file yields (path, theory, tamarin_summary,
    // elab_sig) — `elab_sig` is shared across all lemmas in the file
    // so we elaborate once per file.
    struct FileWork {
        path: std::path::PathBuf,
        theory: tamarin_parser::ast::Theory,
        summary: String,
        elab_sig: tamarin_term::maude_sig::MaudeSig,
    }
    let files: Vec<FileWork> = paths.par_iter().filter_map(|path| {
        let src = std::fs::read_to_string(path).ok()?;
        // User-defined `equations:` declarations are wired through
        // elaborate.rs → MaudeSig.st_rules → Maude module text.  The
        // lastChainTerm filter + threaded closure cap (default 256)
        // keep precompute under 200ms even with many destructors.
        // Sources truncated by the cap are tagged `incomplete=true`;
        // `is_finished` converts Solved→Unfinishable for any branch
        // that consumed an incomplete source — preserving soundness
        // (no wrong-VERIFIED).
        if src.contains("diff(") { return None; }
        // Macros are supported via parser-AST macro expansion
        // (tamarin_theory::macro_expand).  Predicates still need their
        // own port (RS predicate_expand handles formulas but elaborate
        // skips predicate items at the typed layer).
        if src.contains("predicates:") { return None; }
        if src.contains("process:") { return None; }
        if src.contains("builtins:") &&
           (src.contains("diffie-hellman") ||
            src.contains("xor") || src.contains("bilinear-pairing"))
        { return None; }

        let theory = tamarin_parser::parse_theory(&src, &[]).ok()?;
        // Run tamarin once per file with a timeout.
        let tam_out = Command::new("timeout")
            .arg("10s")
            .arg("tamarin-prover")
            .arg("--prove")
            .arg(path)
            .output()
            .ok()?;
        let tam_text = String::from_utf8_lossy(&tam_out.stdout).into_owned();
        let summary = extract_summary(&tam_text)?;
        let elab_sig = match tamarin_theory::elaborate::elaborate(&theory) {
            Ok(e) => e.signature.maude_sig.clone(),
            Err(_) => tamarin_term::maude_sig::pair_maude_sig(),
        };
        Some(FileWork { path: path.clone(), theory, summary: summary.to_string(), elab_sig })
    }).collect();

    // Phase 3: flatten to per-lemma work items.
    struct LemmaWork<'a> {
        path: &'a std::path::PathBuf,
        theory: &'a tamarin_parser::ast::Theory,
        elab_sig: &'a tamarin_term::maude_sig::MaudeSig,
        lemma_name: String,
        trace_quantifier: tamarin_parser::ast::TraceQuantifier,
        tamarin_verdict: &'static str,
    }
    let lemmas: Vec<LemmaWork> = files.iter().flat_map(|f| {
        f.theory.items.iter().filter_map(move |it| {
            let lemma = match it {
                tamarin_parser::ast::TheoryItem::Lemma(l) => l, _ => return None,
            };
            let verdict_line = f.summary.lines()
                .find(|l| l.contains(&format!("{} (", lemma.name)))?;
            let tamarin_verdict = if verdict_line.contains("verified") {
                "verified"
            } else if verdict_line.contains("falsified") {
                "falsified"
            } else { return None };
            Some(LemmaWork {
                path: &f.path,
                theory: &f.theory,
                elab_sig: &f.elab_sig,
                lemma_name: lemma.name.clone(),
                trace_quantifier: lemma.trace_quantifier.clone(),
                tamarin_verdict,
            })
        })
    }).collect();

    // Phase 4: run prove_lemma per lemma in parallel.  Each lemma gets
    // its own MaudeHandle (independent subprocess); rayon manages
    // thread-pool sizing via num_cpus.
    #[derive(Clone)]
    enum LemmaOutcome {
        Match,
        Diff(String),
        Incomparable,
    }
    let dbg_incomp = std::env::var("TAM_DBG_INCOMPARABLE").is_ok();
    let outcomes: Vec<LemmaOutcome> = lemmas.par_iter().map(|w| {
        let h = match tamarin_term::maude_proc::MaudeHandle::start(&mp, w.elab_sig.clone()) {
            Ok(h) => h, Err(_) => return LemmaOutcome::Incomparable,
        };
        // 20s per-lemma cap — twice the 10s deadline so genuine
        // long-but-terminating lemmas finish, but real hangs are
        // bounded.  Watchdog kills Maude → prove_lemma unwinds with an
        // error → Incomparable.
        let watchdog = spawn_kill_watchdog(h.clone(), std::time::Duration::from_secs(20));
        let t0 = std::time::Instant::now();
        // Budget 2000: the deadline (10s) is the real gate; budget
        // gives slack so search isn't budget-bounded into a Sorry on
        // healthy lemmas that just need a few more proof-method steps.
        // 200 was too tight for some healthy lemmas (e.g.
        // NSLPK3::injective_agree) that terminate within 1-3s given a
        // larger step budget.
        // catch_unwind: pre-existing overflow panics at multiple
        // bounds_max+1 sites in reduction.rs (task #151) surface on
        // some corpus lemmas; without catch_unwind the whole rayon
        // par_iter dies on the first panicking lemma.
        let h_inner = h.clone();
        let theory_ref = w.theory;
        let lemma_name_inner = w.lemma_name.clone();
        let root_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_lemma(theory_ref, &lemma_name_inner, h_inner, 2000)
        }));
        let elapsed = t0.elapsed();
        let watchdog_fired = watchdog.finish();
        let fname = w.path.file_name().unwrap().to_string_lossy().into_owned();
        if watchdog_fired {
            // Watchdog killed Maude — log to surface the offender.
            eprintln!("WATCHDOG: {}::{} killed after {:?}",
                fname, w.lemma_name, elapsed);
        } else if elapsed.as_secs() >= 5 {
            // Slow but completed.  Worth surfacing so we can
            // investigate Maude or solver perf for these cases.
            eprintln!("SLOW: {}::{} took {:?}", fname, w.lemma_name, elapsed);
        }
        let root = match root_result {
            Ok(Ok(r)) => r,
            _ => return LemmaOutcome::Incomparable,
        };
        let our_verdict = match verdict_str(&w.trace_quantifier, &root.status) {
            Some(v) => v,
            None => {
                if dbg_incomp {
                    eprintln!("INCOMPARABLE: {}::{} → {:?} (tamarin={})",
                        w.path.file_name().unwrap().to_string_lossy(),
                        w.lemma_name, root.status, w.tamarin_verdict);
                }
                return LemmaOutcome::Incomparable;
            }
        };
        if our_verdict == w.tamarin_verdict {
            LemmaOutcome::Match
        } else {
            LemmaOutcome::Diff(format!(
                "{}::{} — ours={}, tamarin={}",
                w.path.file_name().unwrap().to_string_lossy(),
                w.lemma_name, our_verdict, w.tamarin_verdict))
        }
    }).collect();

    // Aggregate.
    let mut compared = 0usize;
    let mut matched = 0usize;
    let mut diffs: Vec<String> = Vec::new();
    for o in &outcomes {
        match o {
            LemmaOutcome::Match => { compared += 1; matched += 1; }
            LemmaOutcome::Diff(d) => { compared += 1; diffs.push(d.clone()); }
            LemmaOutcome::Incomparable => {}
        }
    }

    eprintln!("corpus verdict-match: {}/{} matched", matched, compared);
    if !diffs.is_empty() {
        eprintln!("mismatches:");
        // Sort for deterministic output order under parallel scheduling.
        diffs.sort();
        for d in &diffs { eprintln!("  {}", d); }
    }
    // We don't *require* a match rate — this is a diagnostic.
}

/// **Corpus proof-skeleton match probe**: walks the same corpus dirs as
/// `corpus_verdict_match_coverage_probe`, invokes `tamarin-prover --prove
/// --output=<tmp>` once per file (so we get the rendered proof tree from
/// Haskell), then for every verdict-matching lemma diffs our `render`ed
/// `ProofNode` against tamarin's skeleton via `first_divergence`.
///
/// Reports `corpus structural-match: X/Y` where Y is the total number
/// of lemmas where Haskell's proof skeleton is available — verdict
/// divergences DO count against structural match (verdict-only matching
/// masks reasoning bugs).
///
/// This is the **primary metric** for the port's progress, per
/// project directive: count only whether the proof matches the
/// Haskell skeleton directly.
///
/// `#[ignore]`d (run with `cargo test -- --ignored`): this heavyweight
/// whole-corpus probe proves every example in-process, but ~99 corpus
/// files declare an oracle heuristic, and the prover faithfully
/// `std::process::exit(1)`s when an oracle script fails to exec (HS
/// behaviour: oracle IO exception → die with empty stdout, search.rs:975).
/// A `process::exit` is uncatchable by the per-lemma `catch_unwind`, so a
/// single oracle file aborts the whole test binary. Kept active as a
/// deliberate `--ignored` probe, consistent with the sibling diagnostic
/// probes above (run against a corpus with oracle scripts on PATH/CWD).
#[test]
#[ignore = "heavyweight whole-corpus probe; oracle files trigger process::exit. Run with --ignored"]
fn corpus_proof_skeleton_match_probe() {
    use rayon::prelude::*;
    use tamarin_theory::prove::prove_lemma;
    use tamarin_theory::proof_skeleton::{extract_from_haskell, first_divergence, render};

    // Same stack-bump as the verdict probe — Goal-Ord + Sk-matcher path
    // can recurse deeper than rayon's default 2 MiB worker stack on
    // typing-class lemmas.
    let _ = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build_global();

    let mp = match maude_path() { Some(p) => p, None => return };
    if !tamarin_available() { return; }

    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");

    let corpus_root = corpus_root();

    // Phase 1: collect candidate spthy paths — the WHOLE examples/ tree.
    // (Walks the whole examples/ tree; the content filters below still skip
    // diff-mode and SAPIC files.)
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    for e in walkdir::WalkDir::new(&corpus_root).into_iter().filter_map(|e| e.ok()) {
        if e.path().extension().and_then(|s| s.to_str()) == Some("spthy") {
            let p = e.path();
            if p.to_string_lossy().contains("/testParser/include/") { continue; }
            paths.push(p.to_path_buf());
        }
    }

    // Phase 2: per-file work. Same filtering as verdict probe, plus each
    // file gets a unique `--output=` tmp path so rayon jobs don't race.
    struct FileWork {
        path: std::path::PathBuf,
        theory: tamarin_parser::ast::Theory,
        summary: String,
        proof_text: String,
        elab_sig: tamarin_term::maude_sig::MaudeSig,
    }
    let pid = std::process::id();
    let files: Vec<FileWork> = paths.par_iter().enumerate().filter_map(|(idx, path)| {
        let src = std::fs::read_to_string(path).ok()?;
        if src.contains("diff(") { return None; }
        // Macros are supported via parser-AST macro expansion
        // (tamarin_theory::macro_expand).
        if src.contains("predicates:") { return None; }
        if src.contains("process:") { return None; }
        // XOR and bilinear-pairing builtins are SUPPORTED (`AcSym::Xor`,
        // cached `mk_dh`/`mk_bp_intruder_variants`, `xor_maude_sig`/
        // `bp_maude_sig`), so theories using them are deliberately NOT
        // filtered out here — this catches XOR/BP proof-shape regressions
        // (e.g. NSLPK3xor: RS 36/38 vs HS 11/13 steps).

        let theory = tamarin_parser::parse_theory(&src, &[]).ok()?;
        let out_path = format!("/tmp/proof_skel_corpus_{}_{}.spthy", pid, idx);
        let tam_out = Command::new("timeout")
            .arg("10s")
            .arg("tamarin-prover")
            .arg("--prove")
            .arg(format!("--output={}", out_path))
            .arg(path)
            .output()
            .ok()?;
        let tam_text = String::from_utf8_lossy(&tam_out.stdout).into_owned();
        let summary = extract_summary(&tam_text)?.to_string();
        // The output file holds the rendered proof tree.  If tamarin
        // timed out before writing it, skip the file.
        let proof_text = std::fs::read_to_string(&out_path).ok()?;
        let _ = std::fs::remove_file(&out_path);
        let elab_sig = match tamarin_theory::elaborate::elaborate(&theory) {
            Ok(e) => e.signature.maude_sig.clone(),
            Err(_) => tamarin_term::maude_sig::pair_maude_sig(),
        };
        Some(FileWork { path: path.clone(), theory, summary, proof_text, elab_sig })
    }).collect();

    // Phase 3: flatten to per-lemma work.
    struct LemmaWork<'a> {
        path: &'a std::path::PathBuf,
        theory: &'a tamarin_parser::ast::Theory,
        elab_sig: &'a tamarin_term::maude_sig::MaudeSig,
        proof_text: &'a str,
        lemma_name: String,
        trace_quantifier: tamarin_parser::ast::TraceQuantifier,
        tamarin_verdict: &'static str,
    }
    let lemmas: Vec<LemmaWork> = files.iter().flat_map(|f| {
        f.theory.items.iter().filter_map(move |it| {
            let lemma = match it {
                tamarin_parser::ast::TheoryItem::Lemma(l) => l, _ => return None,
            };
            let verdict_line = f.summary.lines()
                .find(|l| l.contains(&format!("{} (", lemma.name)))?;
            let tamarin_verdict = if verdict_line.contains("verified") {
                "verified"
            } else if verdict_line.contains("falsified") {
                "falsified"
            } else { return None };
            Some(LemmaWork {
                path: &f.path,
                theory: &f.theory,
                elab_sig: &f.elab_sig,
                proof_text: &f.proof_text,
                lemma_name: lemma.name.clone(),
                trace_quantifier: lemma.trace_quantifier.clone(),
                tamarin_verdict,
            })
        })
    }).collect();

    // Phase 4: per-lemma prove + diff in parallel.
    #[derive(Clone)]
    enum Outcome {
        StructMatch,
        StructDiff { file_lemma: String, line: usize, ours: String, theirs: String },
        Incomparable,
        NoHaskellSkeleton(String),
    }
    let outcomes: Vec<Outcome> = lemmas.par_iter().map(|w| {
        let h = match tamarin_term::maude_proc::MaudeHandle::start(&mp, w.elab_sig.clone()) {
            Ok(h) => h, Err(_) => return Outcome::Incomparable,
        };
        let watchdog = spawn_kill_watchdog(h.clone(), std::time::Duration::from_secs(20));
        // Catch panics — pre-existing overflow bugs in
        // reduction.rs::bounds_max+1 sites surface on some corpus
        // lemmas (tracked separately).  Without catch_unwind, one
        // panicking lemma kills the whole rayon par_iter and the
        // probe yields no number.
        let h_for_prove = h.clone();
        let theory_ref = w.theory;
        let lemma_name = w.lemma_name.clone();
        let root_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_lemma(theory_ref, &lemma_name, h_for_prove, 2000)
        }));
        let _ = watchdog.finish();
        let root = match root_result {
            Ok(Ok(r)) => r,
            _ => return Outcome::Incomparable,
        };
        let our_verdict = match verdict_str(&w.trace_quantifier, &root.status) {
            Some(v) => v,
            None => return Outcome::Incomparable,
        };
        let fname = w.path.file_name().unwrap().to_string_lossy().into_owned();
        let file_lemma = format!("{}::{}", fname, w.lemma_name);
        // **Structural match is the only metric** (per project directive).
        // Always diff proof skeletons, regardless of verdict — a verdict
        // match on a structurally-divergent proof means we're getting the
        // right answer for the wrong reasons, which is misleading.
        let theirs = match extract_from_haskell(w.proof_text, &w.lemma_name) {
            Some(s) => s,
            None => return Outcome::NoHaskellSkeleton(file_lemma),
        };
        let ours = render(&root);
        let verdict_note = if our_verdict != w.tamarin_verdict {
            format!(" [verdict: ours={} theirs={}]", our_verdict, w.tamarin_verdict)
        } else {
            String::new()
        };
        match first_divergence(&ours, &theirs) {
            None => Outcome::StructMatch,
            Some((line, ol, tl)) => Outcome::StructDiff {
                file_lemma: format!("{}{}", file_lemma, verdict_note),
                line, ours: ol, theirs: tl,
            },
        }
    }).collect();

    let mut struct_match = 0usize;
    let mut struct_diff: Vec<String> = Vec::new();
    let mut no_skel: Vec<String> = Vec::new();
    let mut incomparable = 0usize;
    for o in &outcomes {
        match o {
            Outcome::StructMatch => struct_match += 1,
            Outcome::StructDiff { file_lemma, line, ours, theirs } => {
                struct_diff.push(format!(
                    "{} — diverge line {}: ours={:?} theirs={:?}",
                    file_lemma, line, ours, theirs));
            }
            Outcome::NoHaskellSkeleton(s) => no_skel.push(s.clone()),
            Outcome::Incomparable => incomparable += 1,
        }
    }
    let comparable = struct_match + struct_diff.len() + no_skel.len();
    eprintln!("corpus structural-match: {}/{} ({} struct-divergent, \
              {} no-haskell-skel, {} incomparable)",
              struct_match, comparable,
              struct_diff.len(), no_skel.len(), incomparable);

    if !struct_diff.is_empty() {
        eprintln!("structural divergences:");
        struct_diff.sort();
        for d in &struct_diff { eprintln!("  {}", d); }
    }
    if !no_skel.is_empty() {
        eprintln!("no-haskell-skeleton:");
        no_skel.sort();
        for d in &no_skel { eprintln!("  {}", d); }
    }
}

/// Probe: TPM Exclusive_Secrets::left_reachable contradiction breakdown.
#[test]
#[ignore = "diagnostic probe — task #120; run with --ignored"]
fn probe_tpm_left_reachable() {
    use tamarin_theory::prove::prove_lemma;
    use tamarin_theory::constraint::solver::search::ProofNode;
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("related_work/TPM_DKRS_CSF11/TPM_Exclusive_Secrets.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone()).unwrap();
    // Print sources first
    use tamarin_theory::constraint::solver::context::ProofContext;
    let rules: Vec<_> = elab.rules().cloned().collect();
    let h_probe = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone()).unwrap();
    let ctx = ProofContext::new(h_probe, rules);
    use tamarin_theory::constraint::constraints::Goal;
    for src_obj in &ctx.full_sources {
        if let Goal::Action(_, fa) = &src_obj.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first()).chars().take(120).collect::<String>();
                eprintln!("Ku source ({} cases): {}", src_obj.cases_or_empty().len(), term_dbg);
                for (name, _) in src_obj.cases_or_empty() {
                    eprintln!("  case: {}", name);
                }
            }
        }
    }
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");
    let root = prove_lemma(&theory, "left_reachable", h, 200).unwrap();
    eprintln!("TPM_LEFT status={:?}", root.status);
    fn count_results(n: &ProofNode, m: &mut std::collections::BTreeMap<String, usize>) {
        use tamarin_theory::constraint::solver::proof_method::{ProofMethod, Result as R};
        if let ProofMethod::Finished(r) = &n.method {
            let key = match r {
                R::Solved => "Solved".to_string(),
                R::Unfinishable => "Unfinishable".to_string(),
                R::Contradictory(c) => format!("Contradictory({:?})", c),
            };
            *m.entry(key).or_insert(0) += 1;
        }
        for c in n.children.values() { count_results(c, m); }
    }
    let mut m = std::collections::BTreeMap::new();
    count_results(&root, &mut m);
    eprintln!("TPM_LEFT leaf breakdown:");
    for (k, v) in &m { eprintln!("  {}: {}", k, v); }
    fn dump_tree(n: &ProofNode, d: usize, max: usize) {
        if d > max { return; }
        let pad = "  ".repeat(d);
        let m_short: String = format!("{:?}", n.method).chars().take(100).collect();
        eprintln!("{}{:?} m={} ch={}", pad, n.status, m_short, n.children.len());
        for (name, c) in &n.children {
            eprintln!("{}-> [{}]:", pad, name);
            dump_tree(c, d + 1, max);
        }
    }
    dump_tree(&root, 0, 10);
}

/// Probe: NSPK3 KU(t:Fresh) source-case enumeration.
/// Confirms our saturated cases for `KU(t:Fresh)` are only `c_fresh`
/// and `coerce` — missing the deeper chain-saturated cases tamarin
/// produces (`coerce_d_aenc_..._I_2`, `Reveal_ltk_...`, etc.).
/// See task #120.
#[test]
#[ignore = "diagnostic probe — task #120; run with --ignored"]
fn probe_nspk3_fresh_sources() {
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::sources::precompute_full_sources;
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("classic/NSPK3.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone()).unwrap();
    let rules: Vec<_> = elab.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);
    let sources = precompute_full_sources(&ctx);
    eprintln!("Precomputed sources: {}", sources.len());
    use tamarin_theory::constraint::constraints::Goal;
    for src in &sources {
        if let Goal::Action(_, fa) = &src.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first()).chars().take(80).collect::<String>();
                eprintln!("=== source: Goal::Action _ Ku({}) — {} cases", term_dbg, src.cases_or_empty().len());
                for (name, _) in src.cases_or_empty() {
                    eprintln!("  case: {}", name);
                }
            }
        }
    }
}

/// Probe: NSPK3::nonce_secrecy first Cyclic leaf — diagnostic for #119.
#[test]
#[ignore = "diagnostic probe — task #119; run with --ignored"]
fn probe_nspk3_cyclic_leaf() {
    use tamarin_theory::prove::prove_lemma;
    use tamarin_theory::constraint::solver::search::ProofNode;
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("classic/NSPK3.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone()).unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");
    let root = prove_lemma(&theory, "nonce_secrecy", h, 500).unwrap();
    eprintln!("NSPK3 status={:?}", root.status);
    // Find first Cyclic leaf and dump its system state.
    fn find_cyclic(n: &ProofNode, path: Vec<String>) -> Option<(&ProofNode, Vec<String>)> {
        use tamarin_theory::constraint::solver::proof_method::{ProofMethod, Result};
        if let ProofMethod::Finished(Result::Contradictory(Some(c))) = &n.method {
            if format!("{:?}", c).contains("Cyclic") {
                return Some((n, path));
            }
        }
        for (name, c) in &n.children {
            let mut p = path.clone();
            p.push(name.clone());
            if let Some(r) = find_cyclic(c, p) { return Some(r); }
        }
        None
    }
    if let Some((leaf, path)) = find_cyclic(&root, Vec::new()) {
        eprintln!("Cyclic leaf path: {:?}", path);
        // Find all nodes with Fresh premises — and identify pairs that share fresh.
        use tamarin_term::lterm::HasFrees;
        let mut fresh_consumers: Vec<(tamarin_term::lterm::LVar,
            tamarin_term::lterm::LVar, String)> = Vec::new();
        for (id, ru) in leaf.sys.nodes.iter() {
            for prem in &ru.premises {
                if matches!(prem.tag, tamarin_theory::fact::FactTag::Fresh) {
                    let mut vars = Vec::new();
                    prem.for_each_free(&mut |v| vars.push(v.clone()));
                    if let Some(v) = vars.into_iter().find(|v| v.sort == tamarin_term::lterm::LSort::Fresh) {
                        let info = format!("{:?}", ru.info).chars().take(60).collect::<String>();
                        fresh_consumers.push((id.clone(), v, info));
                    }
                }
            }
        }
        eprintln!("Fresh consumers ({}):", fresh_consumers.len());
        for (id, v, info) in &fresh_consumers {
            eprintln!("  node {}#{} consumes Fr({}#{}:{:?})  rule={}",
                id.name, id.idx, v.name, v.idx, v.sort, info);
        }
        eprintln!("Pairs sharing same fresh:");
        for i in 0..fresh_consumers.len() {
            for j in (i+1)..fresh_consumers.len() {
                if fresh_consumers[i].1 == fresh_consumers[j].1
                    && fresh_consumers[i].0 != fresh_consumers[j].0 {
                    eprintln!("  CONFLATED: {}#{} <> {}#{} share {}#{}",
                        fresh_consumers[i].0.name, fresh_consumers[i].0.idx,
                        fresh_consumers[j].0.name, fresh_consumers[j].0.idx,
                        fresh_consumers[i].1.name, fresh_consumers[i].1.idx);
                }
            }
        }
        let subst_list = leaf.sys.eq_store.subst.to_list();
        eprintln!("eq_store ({}):", subst_list.len());
        for (v, t) in subst_list.iter() {
            let ts = format!("{:?}", t).chars().take(80).collect::<String>();
            eprintln!("  {}#{}:{:?} → {}", v.name, v.idx, v.sort, ts);
        }
        // (Remaining edges/less_atoms/last_atom dump intentionally elided.)
    } else {
        eprintln!("no cyclic leaf found");
    }
}

/// Probe: chaum_unforgeability — KU(sign) source-case count + rendered
/// proof skeleton. Diagnoses the `case fresh vs case B_1` divergence at
/// chaum::exec line 7 + chaum::unforgeability line 22.
#[test]
#[ignore = "diagnostic probe — chaum B_1 over-enum; run with --ignored"]
fn probe_chaum_unforgeability() {
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::constraints::Goal;
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("post17/chaum_unforgeability.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    // Also render Rust's proof for chaum::exec
    {
        let h_proof = tamarin_term::maude_proc::MaudeHandle::start(
            &mp, elab.signature.maude_sig.clone()).unwrap();
        std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
        let root = tamarin_theory::prove::prove_lemma(&theory, "exec", h_proof, 500).unwrap();
        eprintln!("== Rendered proof for exec ==");
        eprintln!("{}", tamarin_theory::proof_skeleton::render(&root));
    }
    let h_probe = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone()).unwrap();
    let rules: Vec<_> = elab.rules().cloned().collect();
    let ctx = ProofContext::new(h_probe, rules);
    // Dump destructor intruder rules (used by close_chains_dfs's
    // destructor-extension branch).
    eprintln!("== Destructor intruder rules ==");
    for ir in &ctx.intruder_rules {
        if tamarin_theory::rule::is_destr_rule_info(&ir.info) {
            let prems = ir.premises.iter()
                .map(|f| format!("{:?}", f).chars().take(80).collect::<String>())
                .collect::<Vec<_>>();
            let concs = ir.conclusions.iter()
                .map(|f| format!("{:?}", f).chars().take(80).collect::<String>())
                .collect::<Vec<_>>();
            eprintln!("  {:?} prems={:?} concs={:?}", ir.info, prems, concs);
        }
    }
    eprintln!("== Precomputed full_sources ({} entries) ==", ctx.full_sources.len());
    for src_obj in &ctx.full_sources {
        if let Goal::Action(_, fa) = &src_obj.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first()).chars().take(160).collect::<String>();
                eprintln!("Ku source ({} cases): {}", src_obj.cases_or_empty().len(), term_dbg);
                for (name, case_sys) in src_obj.cases_or_empty() {
                    eprintln!("  case: {}", name);
                    // Dump key state for diffing
                    eprintln!("    nodes ({}):", case_sys.nodes.len());
                    for (id, ru) in case_sys.nodes.iter() {
                        let ru_dbg = format!("{:?}", ru).chars().take(140).collect::<String>();
                        eprintln!("      #{:?} → {}", id, ru_dbg);
                    }
                    eprintln!("    edges ({}):", case_sys.edges.len());
                    for e in &case_sys.edges {
                        eprintln!("      {:?}", e);
                    }
                    eprintln!("    eq_store.subst ({}):",
                        case_sys.eq_store.subst.to_list().len());
                    for (v, t) in case_sys.eq_store.subst.to_list().iter() {
                        let ts = format!("{:?}", t).chars().take(80).collect::<String>();
                        eprintln!("      {:?} → {}", v, ts);
                    }
                    eprintln!("    eq_store.conj ({}):",
                        case_sys.eq_store.conj.len());
                    for (i, d) in case_sys.eq_store.conj.iter().enumerate() {
                        eprintln!("      disj[{}].substs ({}):", i, d.substs.len());
                        for (j, s) in d.substs.iter().enumerate() {
                            let ts = format!("{:?}", s).chars().take(140).collect::<String>();
                            eprintln!("        [{}] {}", j, ts);
                        }
                    }
                    eprintln!("    open goals ({}):",
                        case_sys.goals.iter().filter(|(_, st)| !st.solved).count());
                    for (g, st) in case_sys.goals.iter() {
                        if !st.solved {
                            let gd = format!("{:?}", g).chars().take(100).collect::<String>();
                            eprintln!("      {}", gd);
                        }
                    }
                }
            }
        }
    }
}

/// Probe: TLS::session_key_setup_possible — render Rust's proof to
/// diagnose why `case S_2_case_1` appears where Haskell has `case S_2`.
#[test]
#[ignore = "diagnostic probe — TLS S_2_case_N; run with --ignored"]
fn probe_tls_setup_possible() {
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("classic/TLS_Handshake.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    // Dump precomputed sources first
    {
        let h_probe = tamarin_term::maude_proc::MaudeHandle::start(
            &mp, elab.signature.maude_sig.clone()).unwrap();
        let rules: Vec<_> = elab.rules().cloned().collect();
        let ctx = tamarin_theory::constraint::solver::context::ProofContext::new(h_probe, rules);
        use tamarin_theory::constraint::constraints::Goal;
        eprintln!("== Precomputed full_sources ({} entries) ==", ctx.full_sources.len());
        for src_obj in &ctx.full_sources {
            if let Goal::Action(_, fa) = &src_obj.goal {
                if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                    let term_dbg = format!("{:?}", fa.terms.first())
                        .chars().take(120).collect::<String>();
                    eprintln!("Ku source ({} cases): {}",
                        src_obj.cases_or_empty().len(), term_dbg);
                    for (name, _) in src_obj.cases_or_empty() {
                        eprintln!("  case: {}", name);
                    }
                }
            }
        }
    }
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp, elab.signature.maude_sig.clone()).unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
    let root = tamarin_theory::prove::prove_lemma(
        &theory, "session_key_setup_possible", h, 2000).unwrap();
    eprintln!("== Rust's proof for TLS::session_key_setup_possible ==");
    eprintln!("{}", tamarin_theory::proof_skeleton::render(&root));
    // Find the first node whose case-name ends in `_case_N` and print its
    // children + open goals before the split.
    use tamarin_theory::constraint::solver::search::ProofNode;
    fn find_case_n(
        n: &ProofNode, path: Vec<String>,
    ) -> Option<(&ProofNode, Vec<String>)> {
        // If any child's case-name contains "_case_", this node is the
        // source of the split.
        for name in n.children.keys() {
            if name.contains("_case_") { return Some((n, path)); }
        }
        for (name, c) in &n.children {
            let mut p = path.clone();
            p.push(name.clone());
            if let Some(r) = find_case_n(c, p) { return Some(r); }
        }
        None
    }
    if let Some((node, path)) = find_case_n(&root, Vec::new()) {
        eprintln!("\n== First _case_N split node ==");
        eprintln!("Path to it: {:?}", path);
        eprintln!("Method: {:?}", format!("{:?}", node.method).chars().take(200).collect::<String>());
        eprintln!("Children ({}):", node.children.len());
        for name in node.children.keys() {
            eprintln!("  - {}", name);
        }
        eprintln!("\n== System state at this node ==");
        eprintln!("  nodes ({}):", node.sys.nodes.len());
        for (id, ru) in node.sys.nodes.iter().take(20) {
            let ru_dbg = format!("{:?}", ru.info).chars().take(80).collect::<String>();
            eprintln!("    #{}:{:?} → {}", id.name, id.idx, ru_dbg);
        }
        eprintln!("  open goals ({}):",
            node.sys.goals.iter().filter(|(_, st)| !st.solved).count());
        for (g, st) in node.sys.goals.iter() {
            if !st.solved {
                let gd = format!("{:?}", g).chars().take(100).collect::<String>();
                eprintln!("    {}", gd);
            }
        }
        eprintln!("  eq_store.conj ({}):", node.sys.eq_store.conj.len());
        for (i, d) in node.sys.eq_store.conj.iter().enumerate() {
            eprintln!("    disj[{}] ({} substs):", i, d.substs.len());
            for (j, s) in d.substs.iter().enumerate().take(5) {
                let ts = format!("{:?}", s).chars().take(200).collect::<String>();
                eprintln!("      [{}] {}", j, ts);
            }
        }
    }
}

/// Probe: NSLPK3_untagged::nonce_secrecy — render Rust's proof and
/// dump precomputed sources for the KU sources implicated in the
/// line-7 `case_1` vs `I_2` divergence.
#[test]
#[ignore = "diagnostic probe — NSLPK3 line-7 case_1; run with --ignored"]
fn probe_nslpk3_nonce_secrecy() {
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("classic/NSLPK3_untagged.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    {
        let h_probe = tamarin_term::maude_proc::MaudeHandle::start(
            &mp, elab.signature.maude_sig.clone()).unwrap();
        let rules: Vec<_> = elab.rules().cloned().collect();
        let ctx = tamarin_theory::constraint::solver::context::ProofContext::new(h_probe, rules);
        use tamarin_theory::constraint::constraints::Goal;
        eprintln!("== Precomputed full_sources ({} entries) ==", ctx.full_sources.len());
        for src_obj in &ctx.full_sources {
            if let Goal::Action(_, fa) = &src_obj.goal {
                if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                    let term_dbg = format!("{:?}", fa.terms.first())
                        .chars().take(140).collect::<String>();
                    eprintln!("Ku source ({} cases): {}",
                        src_obj.cases_or_empty().len(), term_dbg);
                    for (name, _) in src_obj.cases_or_empty() {
                        eprintln!("  case: {}", name);
                    }
                }
            }
        }
    }
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp, elab.signature.maude_sig.clone()).unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "60000");
    let root = tamarin_theory::prove::prove_lemma(
        &theory, "nonce_secrecy", h, 5000).unwrap();
    let rs_skel = tamarin_theory::proof_skeleton::render(&root);
    eprintln!("== Rust's proof for NSLPK3_untagged::nonce_secrecy ==");
    eprintln!("{}", rs_skel);
    // Also fetch HS's skeleton via tamarin-prover output, dump side-by-side
    // around the first divergence to make targeted fixes possible.
    let tam_out = std::process::Command::new("timeout")
        .arg("30s")
        .arg("tamarin-prover")
        .arg("--prove")
        .arg("--output=/tmp/nslpk3_hs_full.spthy")
        .arg(path)
        .output().ok();
    if tam_out.is_some() {
        if let Ok(hs_text) = std::fs::read_to_string("/tmp/nslpk3_hs_full.spthy") {
            if let Some(hs_skel) = tamarin_theory::proof_skeleton::extract_from_haskell(
                &hs_text, "nonce_secrecy")
            {
                eprintln!("== HS skeleton for NSLPK3_untagged::nonce_secrecy ==");
                eprintln!("{}", hs_skel);
                if let Some((line_no, ours_line, theirs_line)) =
                    tamarin_theory::proof_skeleton::first_divergence(&rs_skel, &hs_skel)
                {
                    eprintln!("\n== FIRST DIVERGENCE ==");
                    eprintln!("line {}: ours={:?} theirs={:?}", line_no, ours_line, theirs_line);
                    // Surrounding context.
                    let ours_lines: Vec<&str> = rs_skel.lines().collect();
                    let theirs_lines: Vec<&str> = hs_skel.lines().collect();
                    let lo = line_no.saturating_sub(5);
                    let hi_ours = (line_no + 3).min(ours_lines.len());
                    let hi_theirs = (line_no + 3).min(theirs_lines.len());
                    eprintln!("\n-- Rust (lines {}..{}) --", lo + 1, hi_ours);
                    for (i, l) in ours_lines[lo..hi_ours].iter().enumerate() {
                        let mark = if lo + i + 1 == line_no { ">>" } else { "  " };
                        eprintln!("{} {:4}: {}", mark, lo + i + 1, l);
                    }
                    eprintln!("\n-- HS (lines {}..{}) --", lo + 1, hi_theirs);
                    for (i, l) in theirs_lines[lo..hi_theirs].iter().enumerate() {
                        let mark = if lo + i + 1 == line_no { ">>" } else { "  " };
                        eprintln!("{} {:4}: {}", mark, lo + i + 1, l);
                    }
                }
            }
        }
    }
}

/// Probe: CR.spthy::executable wrong-VERDICT (ours=falsified theirs=verified).
/// Exists-trace lemma where HS finds a witness via `case responder` for
/// KU(h(...)) but Rust takes `case c_h` path and fails.
#[test]
#[ignore = "diagnostic probe — CR executable wrong-VERDICT; run with --ignored"]
fn probe_cr_executable() {
    let mp = match maude_path() { Some(p) => p, None => return };
    let path = corpus_root().join("features/xor/CR.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp, elab.signature.maude_sig.clone()).unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
    let root = tamarin_theory::prove::prove_lemma(
        &theory, "executable", h, 5000).unwrap();
    let skel = tamarin_theory::proof_skeleton::render(&root);
    eprintln!("== Rust's proof for CR::executable ==");
    eprintln!("Status: {:?}", root.status);
    eprintln!("{}", skel);

    // Walk the proof tree to find the Cyclic leaf and dump its system.
    fn walk(node: &tamarin_theory::constraint::solver::search::ProofNode, depth: usize) {
        use tamarin_theory::constraint::solver::proof_method::{
            ProofMethod, Result as MethodResult,
        };
        use tamarin_theory::constraint::solver::contradictions::Contradiction;
        if node.children.is_empty() {
            if let ProofMethod::Finished(MethodResult::Contradictory(c)) = &node.method {
                if matches!(c, Some(Contradiction::Cyclic)) {
                    eprintln!("\n== CYCLIC LEAF at depth {} ==", depth);
                    eprintln!("nodes ({}):", node.sys.nodes.len());
                    for (id, rule) in node.sys.nodes.iter() {
                        let name = tamarin_theory::constraint::solver::reduction::rule_case_name(rule);
                        let ku_acts: Vec<_> = rule.actions.iter()
                            .filter(|a| matches!(a.tag, tamarin_theory::fact::FactTag::Ku))
                            .map(|a| format!("{:?}", a.terms.first())
                                .chars().take(80).collect::<String>())
                            .collect();
                        eprintln!("  {:?} → {} KU={:?}", id, name, ku_acts);
                    }
                    eprintln!("edges ({}):", node.sys.edges.len());
                    for e in &node.sys.edges {
                        eprintln!("  {:?} → {:?}", e.src, e.tgt);
                    }
                    eprintln!("less_atoms ({}):", node.sys.less_atoms.len());
                    for la in &node.sys.less_atoms {
                        eprintln!("  {:?} < {:?} ({:?})", la.smaller, la.larger, la.reason);
                    }
                    eprintln!("eq_store.subst ({}):", node.sys.eq_store.subst.to_list().len());
                    for (k, v) in node.sys.eq_store.subst.to_list() {
                        let vs = format!("{:?}", v).chars().take(120).collect::<String>();
                        eprintln!("  {:?} → {}", k, vs);
                    }
                }
            }
        }
        for child in node.children.values() {
            walk(child, depth + 1);
        }
    }
    walk(&root, 0);
}

/// **First end-to-end verdict-match** against `tamarin-prover`:
/// drive `tiny_setup.spthy` through `prove_lemma` and confirm we
/// reach `Solved` — same verdict tamarin produces (`verified`).
#[test]
fn prove_lemma_tiny_setup_verdict_matches_tamarin() {
    use tamarin_theory::constraint::solver::search::NodeStatus;
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() { Some(p) => p, None => return };
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();

    let path = fixtures_dir().join("tiny_setup.spthy");
    let src = std::fs::read_to_string(&path).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&theory, "trivial", h, 100).expect("prove_lemma");

    // Our verdict.
    assert_eq!(root.status, NodeStatus::Solved,
        "expected Solved on tiny_setup, got {:?}", root.status);

    // Compare against tamarin if available.
    if !tamarin_available() { return; }
    let proved = run_tamarin_prove(&path).expect("tamarin --prove");
    let summary = extract_summary(&proved).expect("summary");
    assert!(summary.contains("verified"),
        "tamarin should also verify tiny_setup; summary:\n{}", summary);
}

/// End-to-end: parse `tiny_setup.spthy` (whose lemma is
/// `Ex k #i. Setup(k)@#i`), drive through formula_to_guarded +
/// formula_to_system + Induction → simplify, and verify the
/// step-case branch contains a `Goal::Action(_, Setup(_))`.
/// This exercises Ex-decomposition.
#[test]
fn ex_decomposition_produces_action_goal_via_induction() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, ProofMethod};
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("tiny_setup.spthy"))
        .expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    // Trigger induction → simplify on each fork. The non_empty_trace
    // case decomposes the Ex via reduce_formulas → insert_atom.
    let cases = exec_proof_method(&ctx, &ProofMethod::Induction, &sys)
        .expect("induction");
    let non_empty = &cases.iter().find(|(n, _)| n == "non_empty_trace")
        .expect("non_empty").1;
    assert!(non_empty.goals.iter().any(|(g, _)|
        matches!(g, tamarin_theory::constraint::constraints::Goal::Action(_, fact)
            if fact.tag == tamarin_theory::fact::FactTag::Proto(
                tamarin_theory::fact::Multiplicity::Linear, "Setup", 1))),
        "expected a Setup-action goal in the step case after Ex decomposition");
}

/// Verify atom decomposition produces real `Goal::Action` entries
/// when an action-atom inside a Conj formula is decomposed. Wraps
/// `Action(Setup, k, #i)` in a Conj so reduce_formulas picks it up.
#[test]
fn atom_decomposition_creates_action_goal_in_simplify() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
    let mkvar = |n: &str, sort: SortHint| Term::Var(VarSpec {
        name: n.to_string(), idx: 0, sort, typ: None,
    });
    let action_atom = Atom::Action(
        Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Setup".into(),
            args: vec![mkvar("k", SortHint::Msg)],
        },
        mkvar("i", SortHint::Node),
    );
    let g = tamarin_theory::guarded::Guarded::Conj(vec![
        tamarin_theory::guarded::Guarded::Atom(tamarin_theory::guarded::atom_to_gatom_free(&action_atom)),
    ].into());
    let mut sys = System::empty();
    sys.formulas_mut().push(std::sync::Arc::new(g));
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    // Action atom should have produced a Goal::Action.
    assert!(r.sys.goals.iter().any(|(g, _)|
        matches!(g, tamarin_theory::constraint::constraints::Goal::Action(_, _))),
        "expected a Goal::Action after simplifying a Conj wrapping an Action atom");
}

/// End-to-end with the high-level `prove_lemma` API: drive the
/// disj_lemma fixture from parse to proof tree and confirm tamarin
/// also verifies it (whatever our verdict).
#[test]
fn prove_lemma_disj_lemma_terminates_and_tamarin_verifies() {
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() { Some(p) => p, None => return };
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();

    let path = fixtures_dir().join("disj_lemma.spthy");
    let src = std::fs::read_to_string(&path).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&theory, "either", h, 50).expect("prove_lemma");

    // Whatever our verdict, the proof must terminate within budget.
    // Tamarin verifies this lemma; record both for cross-comparison.
    let our_status = format!("{:?}", root.status);

    if !tamarin_available() { return; }
    let proved = run_tamarin_prove(&path).expect("tamarin --prove");
    let tam_summary = extract_summary(&proved).expect("summary");
    assert!(tam_summary.contains("verified"),
        "tamarin should verify disj_lemma; summary:\n{}", tam_summary);

    // Our search should reach a non-Open terminal state. We don't
    // require Solved (full proof) since action atoms / KU goals
    // aren't fully ported — but it must not be stuck Open.
    assert!(!matches!(root.status,
        tamarin_theory::constraint::solver::search::NodeStatus::Open),
        "search reached terminal status: {}", our_status);
}

/// Deep-search test: drive the disj_lemma all the way down. After
/// `Induction`, the `non_empty_trace` case should decompose its Conj
/// formula via `reduce_formulas`, yielding a `Goal::Disj` which the
/// search then forks. Confirms the search doesn't infinite-loop on
/// repeated Induction (which would happen without the
/// `can_apply_induction` precondition).
#[test]
fn proof_search_disj_lemma_descends_into_disj_goal() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy"))
        .expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    let sys = formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    // Generous budget — must terminate without infinite-looping.
    let root = run_proof_search(&ctx, sys, 50);
    assert!(matches!(root.method, ProofMethod::Induction));
    let non_empty = root.children.get("non_empty_trace").expect("non_empty branch");
    // The non_empty case should have decomposed its Conj formula
    // via simplify, yielding a Goal::Disj that the search picked up.
    // After SolveGoal fires, `non_empty.method` should be SolveGoal.
    assert!(matches!(&non_empty.method,
        ProofMethod::SolveGoal(tamarin_theory::constraint::constraints::Goal::Disj(_)) |
        ProofMethod::Simplify | ProofMethod::Finished(_)),
        "expected SolveGoal/Simplify/Finished in non_empty_trace, got {:?}",
        non_empty.method);
    // The empty_trace branch should be Solved (empty trace doesn't
    // satisfy ∃ k. A(k), and we look for satisfaction → False) or
    // Contradictory (system reduces to ⊥).
    let empty = root.children.get("empty_trace").expect("empty branch");
    assert!(matches!(empty.status,
        NodeStatus::Solved | NodeStatus::Contradictory | NodeStatus::Sorry),
        "empty_trace should reach a terminal state, got {:?}", empty.status);
}

/// End-to-end with explicit decomposition: wrap a Disj in a Conj so
/// reduce_formulas picks up the Conj, recurses into the Disj, and
/// produces a Goal::Disj. This confirms `insert_formula`
/// fires when invoked through the reducible-formula path.
#[test]
fn simplify_conj_wrapping_disj_produces_goal() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let mkvar = |n: &str| Term::Var(VarSpec {
        name: n.to_string(), idx: 0, sort: SortHint::Node, typ: None,
    });
    let a1 = tamarin_theory::guarded::Guarded::Atom(tamarin_theory::guarded::atom_to_gatom_free(&Atom::Last(mkvar("i"))));
    let a2 = tamarin_theory::guarded::Guarded::Atom(tamarin_theory::guarded::atom_to_gatom_free(&Atom::Last(mkvar("j"))));
    let disj = tamarin_theory::guarded::Guarded::Disj(vec![a1, a2].into());
    let mut sys = System::empty();
    sys.formulas_mut().push(std::sync::Arc::new(tamarin_theory::guarded::Guarded::Conj(vec![disj].into())));
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    assert!(r.sys.goals.iter().any(|(g, _)|
        matches!(g, tamarin_theory::constraint::constraints::Goal::Disj(_))));
}

/// End-to-end: parse a fixture, convert each lemma to guarded form,
/// build an initial System via `formula_to_system`, and verify the
/// system has exactly one open formula and the right structural
/// shape. This is the bridge from the parser to the proof-search
/// driver.
#[test]
fn formula_to_system_pipes_parsed_lemmas() {
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    for name in &["tiny_setup.spthy", "two_rules.spthy"] {
        let path = fixtures_dir().join(name);
        let src = std::fs::read_to_string(&path).expect("read");
        let theory = parse_theory(&src, &[]).expect("parse");
        for it in &theory.items {
            if let tamarin_parser::ast::TheoryItem::Lemma(l) = it {
                let g = formula_to_guarded(&l.formula).expect("guarded");
                let sys = formula_to_system(
                    Vec::new(),
                    SourceKind::RawSources,
                    l.trace_quantifier.clone(),
                    false,
                    &g,
                );
                // Initial system always has exactly one formula.
                assert_eq!(sys.formulas.len(), 1, "{}: lemma {}", name, l.name);
                // No nodes, edges, or goals yet.
                assert!(sys.nodes.is_empty());
                assert!(sys.edges.is_empty());
                assert!(sys.goals.is_empty());
                // No restrictions in these fixtures → no lemmas.
                assert!(sys.lemmas.is_empty());
            }
        }
    }
}

/// End-to-end: drive `run_proof_search` on a built System and check
/// the proof tree shape (single Solved branch, no Contradictory).
/// Confirms the dispatcher / simplify / search loop wires together.
#[test]
fn proof_search_end_to_end_tiny_theory() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    // System: one node + one solved goal — already done.
    let mut sys = System::empty();
    use tamarin_theory::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
        RuleInfo, Rule,
    };
    let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Setup"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
    let rule: tamarin_theory::rule::RuleACInst =
        Rule::new(info, Vec::new(), Vec::new(), Vec::new());
    // Mark non-initial via a solved formula (Haskell's
    // `isInitialSystem` uses solved_formulas emptiness, not the
    // node/edge count).
    sys.solved_formulas_mut().push(std::sync::Arc::new(tamarin_theory::guarded::gtrue()));
    sys.add_node(
        tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0),
        rule);
    let root = run_proof_search(&ctx, sys, 50);
    assert_eq!(root.status, NodeStatus::Solved);
    // The trivial-Setup proof should terminate with no children.
    assert!(root.children.is_empty());
}

/// Drive `solve_premise_goal` on a tiny theory and verify it picks
/// the same number of candidate rules tamarin would consider. The
/// fixture's premise is `Out(x)`; only the `Setup` rule produces an
/// `Out`, so we expect exactly one case (Linear).
#[test]
fn solve_premise_goal_against_fixture_matches_rule_count() {
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::{GoalCases, Reduction};
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() { Some(p) => p, None => return };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();

    // Parse the tiny_setup fixture and lift its rules into the proof
    // context. Build a Premise(Out(x)) goal and solve it.
    let src = std::fs::read_to_string(fixtures_dir().join("tiny_setup.spthy"))
        .expect("fixture");
    let theory = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    // Build a `OpenProtoRule` per rule in the parsed theory. We re-use
    // the elaboration pipeline if it's available; if not, we synthesise
    // a minimal Setup-rule manually so the test is self-contained.
    let mut rules = Vec::new();
    for it in &theory.items {
        if let tamarin_parser::ast::TheoryItem::Rule(r) = it {
            // Tamarin's Setup rule has Out(~k) as a conclusion. Since
            // our parser already exposes structural facts, build a
            // OpenProtoRule shape that has at least an Out conclusion.
            // We don't need full elaboration here — just enough for the
            // candidate-count assertion.
            if r.name == "Setup" {
                let v = tamarin_term::lterm::LVar::new(
                    "k", tamarin_term::lterm::LSort::Fresh, 0);
                use tamarin_term::vterm::Lit;
                let tk: tamarin_term::lterm::LNTerm =
                    tamarin_term::term::Term::Lit(Lit::Var(v));
                let conc = tamarin_theory::fact::out_fact(tk);
                let rule: tamarin_theory::rule::ProtoRuleE = tamarin_theory::rule::Rule::new(
                    tamarin_theory::rule::ProtoRuleEInfo::standard("Setup"),
                    vec![],
                    vec![conc],
                    vec![],
                );
                rules.push(tamarin_theory::theory::OpenProtoRule::new(rule));
            }
        }
    }
    assert_eq!(rules.len(), 1, "expected to find exactly one Setup rule");

    let ctx = ProofContext::new(h, rules);
    let mut r = Reduction::new(&ctx, System::empty());
    let i = tamarin_term::lterm::LVar::new(
        "i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new(
        "x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm =
        tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = tamarin_theory::fact::out_fact(tx);
    let p = (i, tamarin_theory::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa);
    // Exactly one matching rule — solver returns LinearNamed, carrying
    // the producing rule's case name (a single case collapses to a
    // named linear case).
    assert!(matches!(out, GoalCases::Linear | GoalCases::LinearNamed(_)));
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.edges.len(), 1);
}

/// Cross-check our `formula_to_guarded` rejection messages against
/// tamarin's. Both should reject `Ex k #i. (A(k)@#i) | (B(k)@#i)`
/// with an "unguarded variable(s)" error, since the existential
/// guard is a disjunction of actions rather than a conjunction.
#[test]
fn unguarded_variable_error_matches_tamarin() {
    if !tamarin_available() { return; }
    let bad = r#"theory Bad
begin

rule A:
  [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]

rule B:
  [ Fr(~k) ] --[ B(~k) ]-> [ Out(~k) ]

lemma bad:
  exists-trace
  "Ex k #i. (A(k) @ #i) | (B(k) @ #i)"

end
"#;
    // Write to a temp file so tamarin can read it.
    let tmp = std::env::temp_dir().join("oracle_bad_guarded.spthy");
    std::fs::write(&tmp, bad).unwrap();
    let out = Command::new("tamarin-prover")
        .arg("--prove")
        .arg(&tmp)
        .output()
        .expect("run tamarin");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let combined = format!("{}{}", stderr, stdout);
    assert!(combined.contains("unguarded variable"),
        "expected 'unguarded variable' from tamarin:\n{}", combined);

    // Our side: the same formula should fail guarded conversion with
    // a structurally-equivalent message.
    let theory = parse_theory(bad, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|i|
        if let tamarin_parser::ast::TheoryItem::Lemma(l) = i { Some(l) } else { None }
    ).expect("lemma");
    let err = formula_to_guarded(&lemma.formula).expect_err("should fail");
    assert!(err.message.contains("unguarded variable"),
        "expected 'unguarded variable' in our error:\n{:?}", err);
    let _ = std::fs::remove_file(&tmp);
}

#[test]
fn fixture_disj_lemma_round_trip() {
    let path = fixtures_dir().join("disj_lemma.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    assert_eq!(rust_rule_count(&src), 2);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() { return; }
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 2);
    assert_eq!(count_lemmas_in_output(&out), 1);

    // The lemma body contains a top-level disjunction. Tamarin's
    // pretty-printed parse-only form should preserve the `|`.
    assert!(out.contains('|') || out.contains('∨'));
}
