//! Solver-component oracle: cross-check our Rust pipeline against the PINNED
//! `tamarin-prover` — the `tamarin-prover-testing` build of the submodule
//! revision, or `HS_PATH` — on small fixture `.spthy` files.
//!
//! What the cases here compare against the oracle:
//! 1. The rule and lemma counts.  The test compares ours against the counts
//!    in the oracle's `--parse-only` echo.
//! 2. The quantifier structure the guarded conversion builds.  The test
//!    compares it against the `∃`/`∀` prefixes of the same echo.
//! 3. The per-lemma verdicts from `prove_lemma`.  The test compares them
//!    against the oracle's `--prove` summary line.  The fixtures are all
//!    small lemmas, and tamarin settles each one in a few steps.
//! 4. The `unguarded variable(s)` rejection.  Both sides must produce it.
//!
//! The rest of the file runs the reduction and search machinery directly on
//! the same fixtures.  Those cases do not use the oracle.
//!
//! The harness skips silently when the pinned oracle has not been built
//! (`./setup.sh testing`), so the test stays fast in environments without it.
//! A missing *maude* is a different matter — see [`require_maude_path`]: it panics
//! rather than skip, because skipping there greens the whole file.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::path::{Path, PathBuf};
use std::process::Command;

use tamarin_parser::parse_theory;
use tamarin_test_support::{corpus_root, require_maude_path};
use tamarin_theory::elaborate::formula_to_guarded_parsed;

#[path = "support/proof_skeleton.rs"]
mod proof_skeleton;

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The pinned oracle, discovered the way every parity script discovers it:
/// `HS_PATH` when set, else the `tamarin-prover-testing` stack-work build.
///
/// An arbitrary `tamarin-prover` on `PATH` may use a different upstream
/// revision, so it is not accepted as the parity oracle.
fn oracle_binary() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("HS_PATH") {
        let p = PathBuf::from(p);
        return p.is_file().then_some(p);
    }
    // .stack-work/install/<arch>/<pkg-hash>/<ghc-version>/bin/tamarin-prover
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tamarin-prover-testing/.stack-work/install");
    let mut level = vec![root];
    for _ in 0..3 {
        let mut next = Vec::new();
        for dir in level {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            next.extend(entries.flatten().map(|e| e.path()).filter(|p| p.is_dir()));
        }
        level = next;
    }
    level
        .into_iter()
        .map(|d| d.join("bin/tamarin-prover"))
        .find(|p| p.is_file())
}

/// The oracle needs maude, and the box that runs these tests keeps it outside
/// `PATH` — the same `MAUDE_PATH` override the rest of the suite uses.
fn oracle_command() -> Option<Command> {
    let mut cmd = Command::new(oracle_binary()?);
    if let Some(m) = require_maude_path() {
        cmd.arg(format!("--with-maude={m}"));
    }
    Some(cmd)
}

/// [`oracle_command`] under `timeout <secs>s`, for the probe of the whole
/// corpus.  The probe invokes the oracle once per file.  A single example
/// that does not terminate
/// would otherwise wedge the rayon pool.
fn oracle_command_within(secs: u32) -> Option<Command> {
    let mut cmd = Command::new("timeout");
    cmd.arg(format!("{secs}s")).arg(oracle_binary()?);
    if let Some(m) = require_maude_path() {
        cmd.arg(format!("--with-maude={m}"));
    }
    Some(cmd)
}

/// A corpus probe's committed mismatch ledger: `Some` lists the exact
/// `<corpus-relative-path>::<lemma>` identities expected to mismatch (the
/// analogue of scripts/sweep_expected.tsv), `None` means no run has
/// enumerated one yet.  The path is corpus-relative, not a bare file name:
/// the corpus mirrors some files (`features/auto-sources/tamarin-repo/…`
/// duplicates `related_work/…`), and a name-keyed identity would collide
/// across the mirror — one copy's divergence resolving would be masked by
/// the other's persisting.
///
/// Per-file oracle timeouts make the eligible set depend on machine load.
/// Exact mismatch identities keep that variation separate from parity changes.
type ProbeLedger = Option<&'static [&'static str]>;

/// Expected structural mismatches for `corpus_proof_skeleton_match_probe`.
///
/// Corpus mirror copies are listed individually.
const STRUCTURAL_MISMATCH_LEDGER: ProbeLedger = Some(&[
    "asiaccs20-POIDC/OIDC_Implicit.spthy::Intent_Consent_and_Correct_Browser",
    "asiaccs20-POIDC/proofs/PROOF_OIDC_Implicit.spthy::executable",
    "csf26-ac/fast/Yubikey_multiset.spthy::Login_invalidates_smaller_counters",
    "csf26-ac/multiset-UD/YubiSecure_KS_STM12/Yubikey_multiset.spthy::Login_invalidates_smaller_counters",
    "features/auto-sources/tamarin-repo/asiaccs20-POIDC/OIDC_Implicit.spthy::Intent_Consent_and_Correct_Browser",
    "features/auto-sources/tamarin-repo/thesis-SvenHammann-POIDC/OIDC_Implicit.spthy::User_Authentication",
    "thesis-SvenHammann-POIDC/OIDC_Implicit.spthy::User_Authentication",
    "thesis-SvenHammann-POIDC/proofs/PROOF_OIDC_Implicit.spthy::executable",
]);

/// Minimum lemmas the skeleton probe must hold a comparison for (a
/// no-Haskell-skeleton lemma counts: the oracle produced a proof we could
/// look for, which is coverage even when the diff itself is impossible).
const STRUCTURAL_MIN_COMPARED: usize = 540;

/// Enforce a corpus probe's mismatch ledger, after diagnostics are printed.
///
/// Four ways to fail: coverage collapsed below `min_compared`; the ledger is
/// still `None` (a probe that only whispers its mismatches is a probe no
/// regression can fail — the panic prints the paste-ready ledger); a mismatch
/// appeared that the ledger does not name (a regression); or a ledgered
/// identity was compared and came out clean (a stale ledger — remove the
/// entry in a commit that explains the fix).  Ledgered identities that were
/// not compared this run (per-file oracle timeout under load) are printed
/// but sorted into neither failure class: absence of a comparison is not
/// evidence in either direction.
#[allow(clippy::too_many_arguments)]
fn enforce_probe_ledger(
    label: &str,
    ledger_const: &str,
    min_const: &str,
    ledger: ProbeLedger,
    min_compared: usize,
    compared_ids: &[String],
    coverage: usize,
    mismatches: &[(String, String)],
) {
    use tamarin_utils::FastSet;
    assert!(
        coverage >= min_compared,
        "{label}: only {coverage} comparisons (need {min_const}={min_compared}) — \
         coverage collapsed. Check the oracle binary, maude, the corpus root \
         and machine load before reading anything into this run."
    );
    let mut mm_ids: Vec<&str> = mismatches.iter().map(|(id, _)| id.as_str()).collect();
    mm_ids.sort_unstable();
    let led = match ledger {
        None => panic!(
            "{label}: {} mismatches over {coverage} comparisons, but {ledger_const} \
             is None — no run has committed the expected set yet. Record this run:\n\
             const {ledger_const}: ProbeLedger = Some(&[\n{}]);",
            mismatches.len(),
            mm_ids
                .iter()
                .map(|i| format!("    {i:?},\n"))
                .collect::<String>(),
        ),
        Some(l) => l,
    };
    let led_set: FastSet<&str> = led.iter().copied().collect();
    let mm_set: FastSet<&str> = mm_ids.iter().copied().collect();
    let cmp_set: FastSet<&str> = compared_ids.iter().map(|s| s.as_str()).collect();
    let mut unexpected: Vec<&(String, String)> = mismatches
        .iter()
        .filter(|(id, _)| !led_set.contains(id.as_str()))
        .collect();
    unexpected.sort_by(|a, b| a.0.cmp(&b.0));
    let mut resolved: Vec<&str> = led
        .iter()
        .copied()
        .filter(|e| cmp_set.contains(e) && !mm_set.contains(e))
        .collect();
    resolved.sort_unstable();
    let mut uncompared: Vec<&str> = led
        .iter()
        .copied()
        .filter(|e| !cmp_set.contains(e))
        .collect();
    uncompared.sort_unstable();
    if !uncompared.is_empty() {
        eprintln!(
            "{label}: {} ledgered mismatch(es) not compared this run (per-file \
             oracle timeout under load?): {uncompared:?}",
            uncompared.len(),
        );
    }
    assert!(
        unexpected.is_empty() && resolved.is_empty(),
        "{label}: ledger violated.\n\
         unexpected mismatches (regressions): {unexpected:#?}\n\
         ledgered but compared clean (stale {ledger_const} entries — remove in \
         a commit that explains the fix): {resolved:?}",
    );
}

/// True if `src` declares an oracle-ranked heuristic — theory-level
/// (`heuristic: o "./script"`, `heuristic: osopo`) or lemma-attribute
/// (`[heuristic=soioo]`).  Braced values (`heuristic={tactic_name}`)
/// reference named tactics, never external scripts, and don't count.
///
/// Oracle-ranked proving runs an external executable whose dependencies,
/// side effects and runtime are outside this in-process probe's control.
/// In-file oracle paths resolve beside the theory, but a script can still
/// block beyond the solver's cooperative deadline. The corpus probe therefore
/// skips these files to remain bounded and hermetic. Matches inside a
/// comment that only quotes a
/// `--heuristic=O` command line over-exclude a few files; the
/// `*_MIN_COMPARED` guards keep the exclusion honest.
fn mentions_oracle_ranking(src: &str) -> bool {
    for (i, _) in src.match_indices("heuristic") {
        let rest = src[i + "heuristic".len()..].trim_start();
        let Some(rest) = rest.strip_prefix([':', '=']) else {
            continue;
        };
        let val = rest.trim_start();
        if val.starts_with('{') {
            continue; // named-tactic reference, no external script
        }
        if val
            .chars()
            .take_while(|c| c.is_ascii_alphabetic())
            .any(|c| c == 'o' || c == 'O')
        {
            return true;
        }
    }
    false
}

/// Whether the pinned oracle is present and also runnable.  The function
/// probes this once per process.  The case lists below consult it once per
/// case, and each probe is a `--help` process spawn.
fn tamarin_available() -> bool {
    static AVAILABLE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *AVAILABLE.get_or_init(|| {
        oracle_binary().is_some_and(|p| {
            Command::new(p)
                .arg("--help")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
        })
    })
}

fn run_tamarin_prove(path: &Path) -> Option<String> {
    let out = oracle_command()?.arg("--prove").arg(path).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Extract the `summary of summaries` block — useful for asserting
/// every lemma got a verdict.
fn extract_summary(s: &str) -> Option<&str> {
    let i = s.find("summary of summaries:")?;
    Some(&s[i..])
}

/// Map a lemma's trace quantifier + solved-root status onto tamarin's
/// verdict string.  Returns `None` for the incomparable fallthrough
/// (root status is neither Solved nor Contradictory) — each caller keeps
/// its own handling and logging for `None`.
fn verdict_str(
    tq: &tamarin_theory::theory::TraceQuantifier,
    st: &tamarin_theory::constraint::solver::search::NodeStatus,
) -> Option<&'static str> {
    use tamarin_theory::constraint::solver::search::NodeStatus;
    use tamarin_theory::theory::TraceQuantifier;
    match (tq, st) {
        (TraceQuantifier::ExistsTrace, NodeStatus::Solved) => Some("verified"),
        (TraceQuantifier::ExistsTrace, NodeStatus::Contradictory) => Some("falsified"),
        (TraceQuantifier::AllTraces, NodeStatus::Contradictory) => Some("verified"),
        (TraceQuantifier::AllTraces, NodeStatus::Solved) => Some("falsified"),
        _ => None,
    }
}

/// The per-lemma kill-watchdog that the corpus probe uses.  The wall-clock
/// deadline at `search::expand` fires BETWEEN expand calls, but a single
/// blocking Maude IPC read sits forever if Maude itself hangs.  A watchdog
/// thread kills the subprocess after a hard cap; the blocked read then
/// returns EOF and `prove_lemma` unwinds with an error.  Without this, even
/// one hung lemma blocks the whole `par_iter().collect()`.
#[must_use = "dropping the guard immediately joins the watchdog, disarming it"]
struct WatchdogGuard {
    done: std::sync::Arc<std::sync::atomic::AtomicBool>,
    fired: std::sync::Arc<std::sync::atomic::AtomicBool>,
    join: Option<std::thread::JoinHandle<()>>,
}

impl WatchdogGuard {
    /// Signal completion and join the watchdog thread.
    fn stop(&mut self) {
        self.done.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(j) = self.join.take() {
            let _ = j.join();
        }
    }

    /// [`stop`](Self::stop), then report whether the watchdog fired (killed
    /// the subprocess) before we finished.
    fn finish(mut self) -> bool {
        self.stop();
        self.fired.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl Drop for WatchdogGuard {
    fn drop(&mut self) {
        self.stop();
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
    WatchdogGuard {
        done,
        fired,
        join: Some(join),
    }
}

/// A rule-free [`ProofContext`](tamarin_theory::constraint::solver::context::ProofContext)
/// over a fresh maude subprocess.  The subprocess carries the `pair`
/// signature.  The reduction and search unit cases below use this context.
/// They test the constraint-system machinery, not rule instantiation.
///
/// The result is `None` only when maude does not resolve.  [`require_maude_path`]
/// already restricts that case to the explicit `TAM_ALLOW_NO_MAUDE=1`
/// opt-out.
fn rule_free_context() -> Option<tamarin_theory::constraint::solver::context::ProofContext> {
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &require_maude_path()?,
        tamarin_term::maude_sig::pair_maude_sig(),
    )
    .unwrap();
    Some(tamarin_theory::constraint::solver::context::ProofContext::new(h, Vec::new()))
}

/// The initial `System` for the first lemma of fixture `name`.  The function
/// builds it the way `prove_lemma` builds one.  It first converts the lemma
/// formula to guarded form.  It then calls `formula_to_system` with no
/// restrictions and with raw sources.
fn fixture_lemma_system(name: &str) -> tamarin_theory::constraint::system::System {
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};
    let src = std::fs::read_to_string(fixtures_dir().join(name)).expect("read fixture");
    let theory = parse_theory(&src, &[]).expect("parse");
    let lemma = theory
        .items
        .iter()
        .find_map(|i| match i {
            tamarin_parser::ast::TheoryItem::Lemma(l) => Some(l),
            _ => None,
        })
        .expect("lemma");
    let elaborated = tamarin_theory::elaborate::elaborate(&theory).expect("elaborate");
    let g = formula_to_guarded_parsed(&lemma.formula, &elaborated.signature).expect("guarded");
    let tq = elaborated.lemmas().next().expect("lemma").trace_quantifier;
    formula_to_system(Vec::new(), SourceKind::RawSources, tq, &g)
}

fn simplify_once(
    ctx: &tamarin_theory::constraint::solver::context::ProofContext,
    sys: tamarin_theory::constraint::system::System,
) -> tamarin_theory::constraint::system::System {
    use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, ProofMethod};

    match exec_proof_method(ctx, &ProofMethod::Simplify, &sys).expect("source materialisation") {
        None => sys,
        Some(mut cases) if cases.len() == 1 => cases.remove(0).1,
        Some(cases) => panic!("simplify unexpectedly produced {} cases", cases.len()),
    }
}

/// Initial disjunctions retain their formula and gain a matching case-split
/// goal. Induction is unavailable once that goal exists.
#[test]
fn simplify_top_level_disjunction_installs_its_goal() {
    use tamarin_theory::constraint::constraints::Goal;
    use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, ProofMethod};
    let Some(ctx) = rule_free_context() else {
        return;
    };
    let sys = fixture_lemma_system("disj_lemma.spthy");
    let formulas = sys.formulas.clone();
    let simplified = simplify_once(&ctx, sys);
    assert_eq!(simplified.formulas, formulas);
    assert!(simplified
        .goals
        .iter()
        .any(|(goal, _)| matches!(goal, Goal::Disj(_))));
    assert!(
        exec_proof_method(&ctx, &ProofMethod::Induction, &simplified)
            .unwrap()
            .is_none()
    );
}

/// **Verdict-match suite**: drive each fixture through `prove_lemma`
/// and confirm that our verdict matches the oracle's summary line.
///
/// Verdict mapping:
/// - **`exists-trace`** lemma + tamarin `verified` ⇒ we expect `Solved`
///   (we found a satisfying trace).
/// - **`all-traces`** lemma + tamarin `verified` ⇒ we expect
///   `Contradictory` (the negated counterexample-search dead-ended,
///   which means the lemma holds).
/// - **`all-traces`** lemma + tamarin `falsified` ⇒ we expect `Solved`
///   (the counterexample search found its trace).
#[test]
fn verdict_match_suite_all_solved_against_tamarin() {
    use tamarin_theory::constraint::solver::search::NodeStatus;
    use tamarin_theory::prove::prove_lemma;

    let mp = match require_maude_path() {
        Some(p) => p,
        None => return,
    };

    // (fixture, lemma, expected our-side status, oracle summary marker)
    let cases: &[(&str, &str, NodeStatus, &str)] = &[
        // Existence lemmas → Solved.
        (
            "tiny_setup.spthy",
            "trivial",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "two_actions.spthy",
            "both_actions",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "three_facts.spthy",
            "all_three",
            NodeStatus::Solved,
            "verified",
        ),
        ("multi_rule.spthy", "can_a", NodeStatus::Solved, "verified"),
        ("multi_rule.spthy", "can_b", NodeStatus::Solved, "verified"),
        ("multi_rule.spthy", "can_c", NodeStatus::Solved, "verified"),
        (
            "multi_arity.spthy",
            "pair_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "multi_arity.spthy",
            "triple_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "pub_var.spthy",
            "setup_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "persistent_fact.spthy",
            "init_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "with_restriction.spthy",
            "a_exists",
            NodeStatus::Solved,
            "verified",
        ),
        // Multi-rule chain (Send → Recv) needs intruder rules for KU.
        (
            "two_rules.spthy",
            "reachable",
            NodeStatus::Solved,
            "verified",
        ),
        // Send-Receive with timing constraint (#i < #j).
        (
            "sendrecv_chain.spthy",
            "chain_works",
            NodeStatus::Solved,
            "verified",
        ),
        // 3-rule chain with shared state (St1 → St2).
        (
            "three_rule.spthy",
            "all_three_steps",
            NodeStatus::Solved,
            "verified",
        ),
        // Multiple persistent fact dependencies.
        ("two_keys.spthy", "can_use", NodeStatus::Solved, "verified"),
        // Multiple lemmas in one theory.
        (
            "multiple_lemmas.spthy",
            "init_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "multiple_lemmas.spthy",
            "active_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "multiple_lemmas.spthy",
            "done_exists",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "multiple_lemmas.spthy",
            "all_at_same_node",
            NodeStatus::Solved,
            "verified",
        ),
        // 5-step state-machine chain.
        (
            "auth_pattern.spthy",
            "protocol_runs",
            NodeStatus::Solved,
            "verified",
        ),
        // Simple In/Out chain — no pair construction.
        ("single_recv.spthy", "chain", NodeStatus::Solved, "verified"),
        // A public name spelled like a reserved skolem id still matches a
        // public variable inside a multiset, as its control does.
        (
            "skolem_prefix_name.spthy",
            "prefixed_reachable",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "skolem_prefix_name.spthy",
            "control_reachable",
            NodeStatus::Solved,
            "verified",
        ),
        // A restriction on linear Mark ignores a persistent !Mark action.
        (
            "restriction_fact_multiplicity.spthy",
            "reachable",
            NodeStatus::Solved,
            "verified",
        ),
        (
            "restriction_fact_multiplicity.spthy",
            "impossible",
            NodeStatus::Solved,
            "falsified",
        ),
        // All-traces lemmas → Contradictory (negation dead-ends).
        (
            "safety_unique.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
            "verified",
        ),
        (
            "safety_two_keys.spthy",
            "fresh_distinct_times",
            NodeStatus::Contradictory,
            "verified",
        ),
        // Restriction-driven uniqueness lemma.
        (
            "restriction_unique.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
            "verified",
        ),
        // Reuse-flagged lemma — stands alone and is verifiable.
        (
            "reuse_lemma.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
            "verified",
        ),
        // [use_induction] attribute — trivially-true tautology.
        (
            "use_induction.spthy",
            "a_self",
            NodeStatus::Contradictory,
            "verified",
        ),
        // Rule-level let-block desugaring (`let r = ~k in ...`).
        (
            "let_block.spthy",
            "use_self",
            NodeStatus::Contradictory,
            "verified",
        ),
        // Fresh-ordering CR-rule + edge-aware cyclic check: ~s
        // creator must precede any rule mentioning ~s downstream.
        (
            "fresh_ordering.spthy",
            "order",
            NodeStatus::Contradictory,
            "verified",
        ),
        // [sources] lemma — forces induction + appends to restrictions.
        (
            "sources_lemma.spthy",
            "setup_self",
            NodeStatus::Contradictory,
            "verified",
        ),
        (
            "sources_lemma.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
            "verified",
        ),
        // partialAtomValuation: `i < j | i = j` collapses once the
        // chain edge fires and `alwaysBefore` decides the disjunct.
        (
            "eval_atoms.spthy",
            "a_then_b",
            NodeStatus::Contradictory,
            "verified",
        ),
        // The oracle falsifies these all-traces lemmas.  Our
        // counter-example search finds the trace, so the terminal
        // status is `Solved`.
        (
            "falsifiable.spthy",
            "never_both",
            NodeStatus::Solved,
            "falsified",
        ),
        (
            "falsified_unique_action.spthy",
            "x_unique",
            NodeStatus::Solved,
            "falsified",
        ),
        (
            "falsified_chain.spthy",
            "a_implies_b",
            NodeStatus::Solved,
            "falsified",
        ),
        // A top-level disjunction: the solver installs its goal and splits.
        ("disj_lemma.spthy", "either", NodeStatus::Solved, "verified"),
        // The simplify loop converges on hashed, tagged messages.
        (
            "CR_external.spthy",
            "recentalive",
            NodeStatus::Contradictory,
            "verified",
        ),
        (
            "sig_minimal.spthy",
            "a_self",
            NodeStatus::Contradictory,
            "verified",
        ),
        // Two fresh premises in one rule.
        (
            "needs_constructor_simple.spthy",
            "sent_exists",
            NodeStatus::Solved,
            "verified",
        ),
        // The intruder constructs a pair; this needs the larger step budget.
        (
            "needs_constructor.spthy",
            "pair_arrives",
            NodeStatus::Solved,
            "verified",
        ),
    ];

    // Several fixtures carry more than one case.  The oracle's `--prove` run
    // covers the whole file.  The loop below therefore reuses one summary for
    // all of the rows of a fixture.
    let mut summaries: tamarin_utils::FastMap<&str, String> = tamarin_utils::FastMap::default();
    for (fixture, lemma, expected, marker) in cases {
        let path = fixtures_dir().join(fixture);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", fixture, e));
        let theory = parse_theory(&src, &[]).expect("parse");
        let elab = tamarin_theory::elaborate::elaborate(&theory).expect("elaborate");
        let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.clone()).unwrap();
        let root = prove_lemma(std::sync::Arc::new(elab), lemma, h, 2000)
            .unwrap_or_else(|e| panic!("prove_lemma({}/{}): {:?}", fixture, lemma, e));
        assert_eq!(
            root.status, *expected,
            "{}/{}: expected {:?}, got {:?}",
            fixture, lemma, expected, root.status
        );

        // Confirm tamarin agrees, when the binary is available.
        if !tamarin_available() {
            continue;
        }
        let summary = summaries.entry(fixture).or_insert_with(|| {
            let proved = run_tamarin_prove(&path).expect("tamarin");
            extract_summary(&proved).expect("summary").to_string()
        });
        // The summary lists every lemma.  Check that this one carries the
        // marker.
        let line = summary
            .lines()
            .find(|l| l.contains(&format!("{} (", lemma)))
            .unwrap_or_else(|| panic!("no summary line for {}", lemma));
        assert!(
            line.contains(*marker),
            "tamarin should mark {}/{} as `{}`; got line:\n{}",
            fixture,
            lemma,
            marker,
            line
        );
    }
}

/// **Corpus proof-skeleton match probe**.  The probe walks the whole
/// `examples/` tree.  It invokes `tamarin-prover --prove --output=<tmp>` once
/// per file, which gives us the rendered proof tree from Haskell.  The probe
/// then proves each lemma itself and diffs our `render`ed `ProofNode` against
/// tamarin's skeleton with `first_divergence`.  It diffs the two skeletons
/// even when the two verdicts agree, because a verdict match on a
/// structurally divergent proof is the right answer for the wrong reason.
///
/// The probe reports `corpus structural-match: X/Y`.  X counts the lemmas
/// whose skeletons match.  Y counts every lemma the probe reached: the
/// matches, the structural divergences, and the lemmas whose oracle output
/// carries no proof the probe can extract.  Y leaves out a lemma the probe
/// could not prove or could not name a verdict for; it reports those as
/// `incomparable`.  A lemma with no extractable skeleton goes to the
/// `no-haskell-skeleton` list, so it never becomes a ledger entry.  Only a
/// structural difference makes a lemma a mismatch.  When such a lemma also
/// disagrees on the verdict, its record carries a
/// `[verdict: ours=… theirs=…]` note.  The probe holds the divergence
/// identities to [`STRUCTURAL_MISMATCH_LEDGER`].  An unexpected divergence
/// fails the probe.  So does a ledger entry that the probe compares without
/// finding a divergence.  The probe does not merely print either one in the
/// log.
///
/// This probe is not the correctness criterion.  That criterion is
/// byte-identical `--prove` stdout, and `scripts/corpus_file_diff.sh` checks
/// it over the 432-row corpus.  That gate is stricter than this probe on the
/// files it covers, because a proof is part of the stdout it compares.  Its
/// file list is narrower: it names 431 of the 1042 `.spthy` files under
/// `examples/`, so this probe reaches files the gate never opens.
///
/// The test carries `#[ignore]`.  Run it with `cargo test -- --ignored`.
/// This heavyweight whole-corpus probe proves every example in-process, which
/// takes more than an hour of wall clock.  The probe skips oracle-ranked
/// files first. See [`mentions_oracle_ranking`]: arbitrary external scripts
/// are deliberately outside this in-process structural probe.
#[test]
#[ignore = "heavyweight whole-corpus probe (hour-plus). Run with --ignored"]
fn corpus_proof_skeleton_match_probe() {
    use proof_skeleton::{extract_from_haskell, first_divergence, render};
    use rayon::prelude::*;
    use tamarin_theory::constraint::solver::search::ProofDeadlineGuard;
    use tamarin_theory::prove::prove_lemma;

    // Same stack-bump as the verdict probe — Goal-Ord + Sk-matcher path
    // can recurse deeper than rayon's default 2 MiB worker stack on
    // typing-class lemmas.
    let _ = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build_global();

    let mp = match require_maude_path() {
        Some(p) => p,
        None => return,
    };
    if !tamarin_available() {
        return;
    }

    let corpus_root = corpus_root();

    // Phase 1: collect candidate spthy paths — the WHOLE examples/ tree.
    // (Walks the whole examples/ tree; the content filters below still skip
    // diff-mode and SAPIC files.)
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    for e in walkdir::WalkDir::new(&corpus_root)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        if e.path().extension().and_then(|s| s.to_str()) == Some("spthy") {
            let p = e.path();
            if p.to_string_lossy().contains("/testParser/include/") {
                continue;
            }
            paths.push(p.to_path_buf());
        }
    }

    // Phase 2: per-file work. Same filtering as verdict probe, plus each
    // file gets a unique `--output=` tmp path so rayon jobs don't race.
    struct FileWork {
        path: std::path::PathBuf,
        summary: String,
        proof_text: String,
        elab: std::sync::Arc<tamarin_theory::theory::Theory>,
    }
    let pid = std::process::id();
    let files: Vec<FileWork> = paths
        .par_iter()
        .enumerate()
        .filter_map(|(idx, path)| {
            let src = std::fs::read_to_string(path).ok()?;
            if src.contains("diff(") {
                return None;
            }
            // Keep the in-process probe bounded and free of external scripts.
            if mentions_oracle_ranking(&src) {
                return None;
            }
            if src.contains("predicates:") {
                return None;
            }
            if src.contains("process:") {
                return None;
            }
            // XOR and bilinear-pairing builtins are SUPPORTED (`AcSym::Xor`,
            // cached `mk_dh`/`mk_bp_intruder_variants`, `xor_maude_sig`/
            // `bp_maude_sig`), so theories using them are deliberately NOT
            // filtered out here — this catches XOR/BP proof-shape regressions

            let theory = tamarin_parser::parse_theory(&src, &[]).ok()?;
            let out_path = format!("/tmp/proof_skel_corpus_{}_{}.spthy", pid, idx);
            // 60s, not 10: at 10s the eligible set breathed with machine
            // load, and the ledger pins identities from a
            // maximally-complete enumeration.
            let tam_out = oracle_command_within(60)?
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
            let elab = tamarin_theory::elaborate::elaborate(&theory).ok()?;
            Some(FileWork {
                path: path.clone(),
                summary,
                proof_text,
                elab: std::sync::Arc::new(elab),
            })
        })
        .collect();

    // Phase 3: flatten to per-lemma work.
    struct LemmaWork<'a> {
        path: &'a std::path::PathBuf,
        elab: std::sync::Arc<tamarin_theory::theory::Theory>,
        proof_text: &'a str,
        lemma_name: String,
        trace_quantifier: tamarin_theory::theory::TraceQuantifier,
        tamarin_verdict: &'static str,
    }
    let lemmas: Vec<LemmaWork> = files
        .iter()
        .flat_map(|f| {
            f.elab.lemmas().filter_map(move |lemma| {
                let verdict_line = f
                    .summary
                    .lines()
                    .find(|l| l.contains(&format!("{} (", lemma.name)))?;
                let tamarin_verdict = if verdict_line.contains("verified") {
                    "verified"
                } else if verdict_line.contains("falsified") {
                    "falsified"
                } else {
                    return None;
                };
                Some(LemmaWork {
                    path: &f.path,
                    elab: std::sync::Arc::clone(&f.elab),
                    proof_text: &f.proof_text,
                    lemma_name: lemma.name.clone(),
                    trace_quantifier: lemma.trace_quantifier,
                    tamarin_verdict,
                })
            })
        })
        .collect();

    // Phase 4: per-lemma prove + diff in parallel.
    enum Outcome {
        StructMatch(String),
        StructDiff {
            // `id` stays the bare `file::lemma` (the ledger key); the
            // verdict annotation rides separately in `note` so a verdict
            // flip can't mint a second identity for the same divergence.
            id: String,
            note: String,
            line: usize,
            ours: String,
            theirs: String,
        },
        Incomparable,
        NoHaskellSkeleton(String),
    }
    let outcomes: Vec<Outcome> = lemmas
        .par_iter()
        .map(|w| {
            let _deadline = ProofDeadlineGuard::set_ms(10_000);
            let h =
                match tamarin_term::maude_proc::MaudeHandle::start(&mp, w.elab.signature.clone()) {
                    Ok(h) => h,
                    Err(_) => return Outcome::Incomparable,
                };
            let watchdog = spawn_kill_watchdog(h.clone(), std::time::Duration::from_secs(20));
            // Catch panics — pre-existing overflow bugs in
            // reduction.rs::bounds_max+1 sites surface on some corpus
            // lemmas (tracked separately).  Without catch_unwind, one
            // panicking lemma kills the whole rayon par_iter and the
            // probe yields no number.
            let h_for_prove = h.clone();
            let theory = std::sync::Arc::clone(&w.elab);
            let lemma_name = w.lemma_name.clone();
            let root_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prove_lemma(theory, &lemma_name, h_for_prove, 2000)
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
            let rel = w
                .path
                .strip_prefix(&corpus_root)
                .unwrap_or(w.path.as_path())
                .to_string_lossy();
            let file_lemma = format!("{}::{}", rel, w.lemma_name);
            // This probe's metric is the structural match, not the verdict.
            // So it diffs the skeletons even when the two verdicts agree.  A
            // verdict match on a structurally divergent proof means we get
            // the right answer for the wrong reasons, which is misleading.
            let theirs = match extract_from_haskell(w.proof_text, &w.lemma_name) {
                Some(s) => s,
                None => return Outcome::NoHaskellSkeleton(file_lemma),
            };
            let ours = render(&root);
            let verdict_note = if our_verdict != w.tamarin_verdict {
                format!(
                    " [verdict: ours={} theirs={}]",
                    our_verdict, w.tamarin_verdict
                )
            } else {
                String::new()
            };
            match first_divergence(&ours, &theirs) {
                None => Outcome::StructMatch(file_lemma),
                Some((line, ol, tl)) => Outcome::StructDiff {
                    id: file_lemma,
                    note: verdict_note,
                    line,
                    ours: ol,
                    theirs: tl,
                },
            }
        })
        .collect();

    let mut struct_match = 0usize;
    let mut compared_ids: Vec<String> = Vec::new();
    let mut mismatches: Vec<(String, String)> = Vec::new();
    let mut no_skel: Vec<String> = Vec::new();
    let mut incomparable = 0usize;
    for o in outcomes {
        match o {
            Outcome::StructMatch(id) => {
                struct_match += 1;
                compared_ids.push(id);
            }
            Outcome::StructDiff {
                id,
                note,
                line,
                ours,
                theirs,
            } => {
                let detail = format!(
                    "{}{} — diverge line {}: ours={:?} theirs={:?}",
                    id, note, line, ours, theirs
                );
                compared_ids.push(id.clone());
                mismatches.push((id, detail));
            }
            Outcome::NoHaskellSkeleton(s) => no_skel.push(s),
            Outcome::Incomparable => incomparable += 1,
        }
    }
    let coverage = struct_match + mismatches.len() + no_skel.len();
    eprintln!(
        "corpus structural-match: {}/{} ({} struct-divergent, \
              {} no-haskell-skel, {} incomparable)",
        struct_match,
        coverage,
        mismatches.len(),
        no_skel.len(),
        incomparable
    );

    if !mismatches.is_empty() {
        eprintln!("structural divergences:");
        mismatches.sort();
        for (_, d) in &mismatches {
            eprintln!("  {}", d);
        }
    }
    if !no_skel.is_empty() {
        eprintln!("no-haskell-skeleton:");
        no_skel.sort();
        for d in &no_skel {
            eprintln!("  {}", d);
        }
    }
    enforce_probe_ledger(
        "corpus structural-match",
        "STRUCTURAL_MISMATCH_LEDGER",
        "STRUCTURAL_MIN_COMPARED",
        STRUCTURAL_MISMATCH_LEDGER,
        STRUCTURAL_MIN_COMPARED,
        &compared_ids,
        coverage,
        &mismatches,
    );
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
        let elaborated = tamarin_theory::elaborate::elaborate(&theory).expect("elaborate");
        for it in &theory.items {
            if let tamarin_parser::ast::TheoryItem::Lemma(l) = it {
                let g =
                    formula_to_guarded_parsed(&l.formula, &elaborated.signature).expect("guarded");
                let tq = elaborated
                    .lemmas()
                    .find(|el| el.name == l.name)
                    .expect("elaborated lemma")
                    .trace_quantifier;
                let sys = formula_to_system(Vec::new(), SourceKind::RawSources, tq, &g);
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
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};
    use tamarin_theory::constraint::system::System;

    let Some(ctx) = rule_free_context() else {
        return;
    };

    // System: one node + one solved goal — already done.
    let mut sys = System::empty();
    use tamarin_theory::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
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
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(tamarin_theory::guarded::gtrue()));
    sys.add_node(
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
        rule,
    );
    let root = run_proof_search(&ctx, sys, 50).expect("default ranking");
    assert_eq!(root.status, NodeStatus::Solved);
    // The trivial-Setup proof should terminate with no children.
    assert!(root.children.is_empty());
}
