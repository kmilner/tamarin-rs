//! Solver-component oracle: cross-check our Rust pipeline against the PINNED
//! `tamarin-prover` — the `tamarin-prover-testing` build of the submodule
//! revision, or `HS_PATH` — on small fixture `.spthy` files.
//!
//! What the cases here compare against the oracle:
//! 1. The rule and lemma counts.  The test compares ours against the counts
//!    in the oracle's `--parse-only` echo.
//! 2. The quantifier structure of `formula_to_guarded`.  The test compares it
//!    against the `∃`/`∀` prefixes of the same echo.
//! 3. The per-lemma verdicts from `prove_lemma`.  The test compares them
//!    against the oracle's `--prove` summary line.  The fixtures are all
//!    small lemmas, and tamarin settles each one in a few steps.
//! 4. The `unguarded variable(s)` rejection.  Both sides must produce it.
//!
//! The rest of the file drives the reduction and search machinery directly on
//! the same fixtures.  Those cases do not use the oracle.
//!
//! The harness skips silently when the pinned oracle has not been built
//! (`./setup.sh testing`), so the test stays fast in environments without it.
//! A missing *maude* is a different matter — see [`maude_path`]: it panics
//! rather than skip, because skipping there greens the whole file.

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
    std::env::var("CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tamarin-prover/examples")
        })
}

/// Absolute maude locations probed before `PATH` is walked.
///
/// This probe mirrors the crate-shared `src/test_maude.rs` one (an
/// integration test cannot see a `#[cfg(test)]` module of the library it
/// links) — keep the two in sync.
const MAUDE_CANDIDATES: [&str; 2] = ["/usr/local/bin/maude", "/usr/bin/maude"];

/// Last resort, after `PATH`: the linuxbrew prefix this project's maude lives
/// under on the development box, which is deliberately not on `PATH`.
const MAUDE_LINUXBREW: &str = "/home/linuxbrew/.linuxbrew/bin/maude";

/// The maude every maude-gated case below runs against: `$MAUDE_PATH`, else
/// the first existing [`MAUDE_CANDIDATES`] entry, else a `PATH` walk, else
/// [`MAUDE_LINUXBREW`].
///
/// Resolving NOTHING is a misconfiguration, not a reason to skip: every
/// maude-gated test in this file opens with `let mp = match maude_path() {
/// Some(p) => p, None => return }`, so a `None` here reports the same green
/// run with and without maude installed.  Panic instead — unless
/// `TAM_ALLOW_NO_MAUDE=1` explicitly asks for the old silent skip (a box that
/// genuinely has no maude and only wants the maude-free cases).  A
/// `MAUDE_PATH` naming a file that does not exist is the same
/// misconfiguration and panics too.
fn maude_path() -> Option<String> {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        assert!(
            std::path::Path::new(&p).exists(),
            "MAUDE_PATH={p} does not exist; unset it to fall back to \
             {MAUDE_CANDIDATES:?} / PATH / {MAUDE_LINUXBREW}, or point it at a \
             real maude — skipping every maude-gated case here would report \
             green vacuously"
        );
        return Some(p);
    }
    if let Some(c) = MAUDE_CANDIDATES
        .iter()
        .find(|c| std::path::Path::new(c).exists())
    {
        return Some((*c).to_string());
    }
    // `PATH` walk, kept dependency-free like every other copy of this probe.
    if let Some(p) = std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|d| d.join("maude"))
            .find(|p| p.is_file())
    }) {
        return Some(p.to_string_lossy().into_owned());
    }
    if std::path::Path::new(MAUDE_LINUXBREW).exists() {
        return Some(MAUDE_LINUXBREW.to_string());
    }
    if std::env::var("TAM_ALLOW_NO_MAUDE").as_deref() == Ok("1") {
        return None;
    }
    panic!(
        "no maude found: MAUDE_PATH unset, none of {MAUDE_CANDIDATES:?} exist, \
         nothing named `maude` on PATH, and no {MAUDE_LINUXBREW}. Every \
         maude-gated case in this file would skip and the run would be green \
         having proved nothing. Install maude, set MAUDE_PATH, or set \
         TAM_ALLOW_NO_MAUDE=1 to accept the silent skip."
    );
}

/// The pinned oracle, discovered the way every parity script discovers it:
/// `HS_PATH` when set, else the `tamarin-prover-testing` stack-work build.
///
/// A bare `tamarin-prover` on `PATH` is deliberately NOT accepted.  It is
/// whatever the machine happens to have installed — on this box a packaged
/// release 1.12.0, a different upstream release from the submodule pin — and
/// a differential test that compares against the wrong release is comparing
/// against the wrong specification.
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
    if let Some(m) = maude_path() {
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
    if let Some(m) = maude_path() {
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
/// Counts proved untrustworthy here: the eligible set breathes with the
/// per-file oracle timeout under machine load — a quiet run admits marginal
/// files that carry disproportionate mismatches — so a count floor flakes in
/// both directions while the mismatch *identities* stay put.
type ProbeLedger = Option<&'static [&'static str]>;

/// Expected structural mismatches for `corpus_proof_skeleton_match_probe`.
///
/// Enumerated 2026-08-10 (60s oracle timeout, release; identity-stable across
/// two enumerations — 815/837 and 819/841 matched, same 22-identity multiset
/// both times, corpus mirror copies listed individually).
const STRUCTURAL_MISMATCH_LEDGER: ProbeLedger = Some(&[
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::EligVerif",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::TimelyP",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::Uniqueness",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::VoterC",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::ballotsFromVoters",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::indivVerif",
    "accountability/csf21-acc-unbounded/mixvote/mixvote_SmHh-multi-session.spthy::secretSskD",
    "asiaccs20-POIDC/OIDC_Implicit.spthy::Intent_Consent_and_Correct_Browser",
    "asiaccs20-POIDC/proofs/PROOF_OIDC_Implicit.spthy::executable",
    "csf26-ac/fast/Yubikey_multiset.spthy::Login_invalidates_smaller_counters",
    "csf26-ac/multiset-UD/YubiSecure_KS_STM12/Yubikey_multiset.spthy::Login_invalidates_smaller_counters",
    "features/auto-sources/tamarin-repo/asiaccs20-POIDC/OIDC_Implicit.spthy::Intent_Consent_and_Correct_Browser",
    "features/auto-sources/tamarin-repo/loops/JCS12_Typing_Example.spthy::Client_session_key_secrecy_raw",
    "features/auto-sources/tamarin-repo/loops/JCS12_Typing_Example.spthy::typing_assertion",
    "features/auto-sources/tamarin-repo/thesis-SvenHammann-POIDC/OIDC_Implicit.spthy::User_Authentication",
    "loops/JCS12_Typing_Example.spthy::Client_session_key_secrecy_raw",
    "loops/JCS12_Typing_Example.spthy::typing_assertion",
    "post17/foo_eligibility.spthy::eligibility",
    "post17/foo_eligibility.spthy::exec",
    "post17/foo_eligibility.spthy::types",
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
/// Oracle-ranked proving execs the oracle script relative to the invoker's
/// CWD and `std::process::exit(1)`s when it is missing (HS: IO exception →
/// dies with empty stdout; RS: `search::rank_goals_or_abort`) — one such
/// file aborts the whole probe binary.  The abort cannot be caught.  The
/// corpus probe therefore skips these files first.  Matches inside a
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

fn run_tamarin_parse_only(path: &Path) -> Option<String> {
    let out = oracle_command()?
        .arg("--parse-only")
        .arg(path)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn run_tamarin_prove(path: &Path) -> Option<String> {
    let out = oracle_command()?.arg("--prove").arg(path).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Count `lemma <name>` occurrences in tamarin's parse output.
fn count_lemmas_in_output(s: &str) -> usize {
    s.lines()
        .filter(|l| l.trim_start().starts_with("lemma "))
        .count()
}

/// Count `rule <name>:` occurrences in tamarin's parse output.
fn count_rules_in_output(s: &str) -> usize {
    s.lines()
        .filter(|l| {
            let t = l.trim_start();
            t.starts_with("rule ") && t.contains(':')
        })
        .count()
}

/// Extract the `summary of summaries` block — useful for asserting
/// every lemma got a verdict.
fn extract_summary(s: &str) -> Option<&str> {
    let i = s.find("summary of summaries:")?;
    Some(&s[i..])
}

fn rust_lemma_count(src: &str) -> usize {
    let theory = parse_theory(src, &[]).expect("parse_theory");
    theory
        .items
        .iter()
        .filter(|i| matches!(i, tamarin_parser::ast::TheoryItem::Lemma(_)))
        .count()
}

fn rust_rule_count(src: &str) -> usize {
    let theory = parse_theory(src, &[]).expect("parse_theory");
    theory
        .items
        .iter()
        .filter(|i| matches!(i, tamarin_parser::ast::TheoryItem::Rule(_)))
        .count()
}

/// Map a lemma's trace quantifier + solved-root status onto tamarin's
/// verdict string.  Returns `None` for the incomparable fallthrough
/// (root status is neither Solved nor Contradictory) — each caller keeps
/// its own handling and logging for `None`.
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
/// signature.  The reduction and search unit cases below drive this context.
/// They test the constraint-system machinery, not rule instantiation.
///
/// The result is `None` only when maude does not resolve.  [`maude_path`]
/// already restricts that case to the explicit `TAM_ALLOW_NO_MAUDE=1`
/// opt-out.
fn rule_free_context() -> Option<tamarin_theory::constraint::solver::context::ProofContext> {
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &maude_path()?,
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
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    formula_to_system(
        Vec::new(),
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    )
}

/// Our parser and the oracle's `--parse-only` echo must find the same number
/// of rules and lemmas in each fixture.  If our parser drops a rule, or if it
/// swallows a lemma, the count changes on one side only.
#[test]
fn fixture_rule_and_lemma_counts_match_the_oracle() {
    // (fixture, rules, lemmas)
    let cases: &[(&str, usize, usize)] = &[
        ("tiny_setup.spthy", 1, 1),
        ("two_rules.spthy", 2, 1),
        ("disj_lemma.spthy", 2, 1),
    ];
    for (name, rules, lemmas) in cases {
        let path = fixtures_dir().join(name);
        let src = std::fs::read_to_string(&path).expect("read fixture");
        assert_eq!(rust_rule_count(&src), *rules, "{name} rules");
        assert_eq!(rust_lemma_count(&src), *lemmas, "{name} lemmas");

        if !tamarin_available() {
            continue;
        }
        let out = run_tamarin_parse_only(&path).expect("tamarin parse");
        assert_eq!(count_rules_in_output(&out), *rules, "{name} oracle rules");
        assert_eq!(
            count_lemmas_in_output(&out),
            *lemmas,
            "{name} oracle lemmas"
        );
    }
}

/// Sample a small set of real-corpus examples and check that lemma
/// and rule counts match between the Rust parser and tamarin's
/// `--parse-only` output. Covers larger / more realistic theories.
#[test]
fn corpus_sample_lemma_and_rule_counts_match() {
    if !tamarin_available() {
        return;
    }
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
        let path = match found {
            Some(p) => p,
            None => continue,
        };

        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let our_rules = match std::panic::catch_unwind(|| rust_rule_count(&src)) {
            Ok(n) => n,
            Err(_) => continue,
        };
        let our_lemmas = match std::panic::catch_unwind(|| rust_lemma_count(&src)) {
            Ok(n) => n,
            Err(_) => continue,
        };
        let out = match run_tamarin_parse_only(&path) {
            Some(o) => o,
            None => continue,
        };
        let tam_rules = count_rules_in_output(&out);
        let tam_lemmas = count_lemmas_in_output(&out);

        compared += 1;
        // Tamarin's pretty-print may expand let-defs / restrictions
        // so allow tamarin to have ≥ ours on rules. Lemmas should be
        // exact — tamarin doesn't synthesise lemmas.
        if our_lemmas != tam_lemmas {
            mismatches.push(format!(
                "{}: lemmas ours={} theirs={}",
                path.display(),
                our_lemmas,
                tam_lemmas
            ));
        }
        if our_rules > tam_rules {
            mismatches.push(format!(
                "{}: rules ours={} > theirs={}",
                path.display(),
                our_rules,
                tam_rules
            ));
        }
    }
    if !mismatches.is_empty() {
        panic!(
            "rule/lemma count mismatches ({} compared):\n  {}",
            compared,
            mismatches.join("\n  ")
        );
    }
    // A run that located none of the candidates compared nothing, and a green
    // "0 mismatches out of 0 files" is exactly the vacuous pass this suite
    // exists to avoid.
    assert!(
        compared > 0,
        "none of {:?} were found under {} — the test compared nothing",
        candidates,
        corpus.display()
    );
}

/// A guarded formula's quantifier census: `(ex_blocks, ex_vars, all_blocks,
/// all_vars)`.  Blocks are `GGuarded` nodes.  There is one block per
/// quantifier prefix.  A prefix is the unit that HS's `prettyGuarded` prints
/// a single `∃`/`∀` glyph for.  Vars are the binders that those prefixes
/// open.
fn count_quantifiers(g: &Guarded) -> (usize, usize, usize, usize) {
    fn rec(g: &Guarded, c: &mut (usize, usize, usize, usize)) {
        match g {
            Guarded::Atom(_) => {}
            Guarded::Conj(xs) | Guarded::Disj(xs) => {
                for x in xs.iter() {
                    rec(x, c);
                }
            }
            Guarded::GGuarded {
                qua, vars, body, ..
            } => {
                match qua {
                    Quant::Ex => {
                        c.0 += 1;
                        c.1 += vars.len();
                    }
                    Quant::All => {
                        c.2 += 1;
                        c.3 += vars.len();
                    }
                }
                rec(body, c);
            }
        }
    }
    let mut c = (0, 0, 0, 0);
    rec(g, &mut c);
    c
}

/// The oracle's echo of the source formula of lemma `lemma` in `parse_only`.
/// This is the first quoted line at or after the `lemma <name>:` header.  The
/// echo below that line is the guarded form, negated for `all-traces`.  The
/// guarded form is a different formula, so this function must not return it.
fn oracle_lemma_echo<'a>(parse_only: &'a str, lemma: &str) -> &'a str {
    let header = format!("lemma {lemma}:");
    parse_only
        .lines()
        .skip_while(|l| l.trim_start() != header)
        .find(|l| l.contains('"'))
        .unwrap_or_else(|| panic!("no source echo for lemma `{lemma}`:\n{parse_only}"))
}

/// The test checks `formula_to_guarded`'s quantifier structure against the
/// oracle in three ways per fixture.  It pins our `(ex_blocks, ex_vars,
/// all_blocks, all_vars)` census.  It pins the oracle's echo of the same
/// lemma to its bytes.  It then checks our block counts against the glyph
/// counts in that echo.  `prettyLFormula` emits exactly one `∃`/`∀` glyph
/// per quantifier prefix.  So a prefix that our conversion splits or merges
/// disagrees with the glyph count of the formula that the oracle reads from
/// the same source.
///
/// The case list covers both trace quantifiers on purpose.  A list of only
/// `exists-trace` lemmas leaves every `all_*` count at zero on both sides.
/// No mutation of the `All` arm can disturb a count that stays at zero.
///
/// The echo bytes come from the pinned oracle (Git revision ef3f0468), run
/// with `--parse-only`.
#[test]
fn guarded_quantifier_structure_matches_tamarin() {
    // (fixture, lemma, ex_blocks, ex_vars, all_blocks, all_vars, oracle echo)
    #[allow(clippy::type_complexity)]
    let cases: &[(&str, &str, usize, usize, usize, usize, &str)] = &[
        // One prefix, two binders.
        (
            "tiny_setup.spthy",
            "trivial",
            1,
            2,
            0,
            0,
            "  exists-trace \"∃ k #i. Setup( k ) @ #i\"",
        ),
        // One prefix, three binders.
        (
            "two_rules.spthy",
            "reachable",
            1,
            3,
            0,
            0,
            "  exists-trace \"∃ k #i #j. (Sent( k ) @ #i) ∧ (Recv( k ) @ #j)\"",
        ),
        // A top-level disjunction of two `Ex k #i` prefixes.
        (
            "disj_lemma.spthy",
            "either",
            2,
            4,
            0,
            0,
            "  exists-trace \"(∃ k #i. A( k ) @ #i) ∨ (∃ k #i. B( k ) @ #i)\"",
        ),
        // One universal prefix, three binders.
        (
            "safety_unique.spthy",
            "setup_unique",
            0,
            0,
            1,
            3,
            "  \"∀ k #i #j. ((Setup( k ) @ #i) ∧ (Setup( k ) @ #j)) ⇒ (#i = #j)\"",
        ),
        // Same prefix shape, disjunctive conclusion.
        (
            "eval_atoms.spthy",
            "a_then_b",
            0,
            0,
            1,
            3,
            "  \"∀ x #i #j. ((A( x ) @ #i) ∧ (B( x ) @ #j)) ⇒ ((#i < #j) ∨ (#i = #j))\"",
        ),
    ];
    for (name, lemma, ex_blocks, ex_vars, all_blocks, all_vars, expected_echo) in cases {
        let path = fixtures_dir().join(name);
        let src = std::fs::read_to_string(&path).expect("read fixture");
        let theory = parse_theory(&src, &[]).expect("parse_theory");
        let l = theory
            .items
            .iter()
            .find_map(|i| match i {
                tamarin_parser::ast::TheoryItem::Lemma(l) if l.name == *lemma => Some(l),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{name}: lemma `{lemma}` present"));
        let g = formula_to_guarded(&l.formula).expect("guarded conv");
        assert_eq!(
            count_quantifiers(&g),
            (*ex_blocks, *ex_vars, *all_blocks, *all_vars),
            "{name}::{lemma} quantifier census"
        );

        if !tamarin_available() {
            continue;
        }
        let parse_only = run_tamarin_parse_only(&path).expect("tamarin parse");
        let echo = oracle_lemma_echo(&parse_only, lemma);
        assert_eq!(echo, *expected_echo, "{name}::{lemma} oracle echo");
        assert_eq!(
            (echo.matches('∃').count(), echo.matches('∀').count()),
            (*ex_blocks, *all_blocks),
            "{name}::{lemma}: oracle echo disagrees on prefix count"
        );
    }
}

/// End-to-end: parse the disj_lemma fixture, build the initial
/// system, simplify, and verify the formula structure stays intact.
/// `reducible_formula(Disj) = false` matches Haskell — top-level Disj
/// does NOT get decomposed by `reduce_formulas`. Decomposition happens
/// later via `Induction` or via being nested inside a reducible parent.
#[test]
fn simplify_top_level_disj_lemma_left_intact() {
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;

    let Some(ctx) = rule_free_context() else {
        return;
    };
    let sys = fixture_lemma_system("disj_lemma.spthy");
    let n_formulas_before = sys.formulas.len();
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    // The top-level Disj is non-reducible, so the formula count
    // doesn't change.
    assert_eq!(r.sys.formulas.len(), n_formulas_before);
    // No Goal::Disj created during simplify alone (induction or
    // SolveGoal would trigger that).
    assert!(!r
        .sys
        .goals
        .iter()
        .any(|(g, _)| matches!(g, tamarin_theory::constraint::constraints::Goal::Disj(_))));
}

/// End-to-end: drive `run_proof_search` on the disj_lemma fixture
/// from start. The search should pick `Induction` first (matching
/// tamarin), creating two cases: `empty_trace` and `non_empty_trace`.
/// Tamarin's actual proof for this fixture: induction → case_1 → SOLVED.
#[test]
fn proof_search_disj_lemma_picks_induction_first() {
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::run_proof_search;

    let Some(ctx) = rule_free_context() else {
        return;
    };
    let root = run_proof_search(&ctx, fixture_lemma_system("disj_lemma.spthy"), 5);
    // First method should be Induction — matches tamarin's
    // `induction` step at the start of the proof.
    assert!(
        matches!(root.method, ProofMethod::Induction),
        "expected Induction, got {:?}",
        root.method
    );
    // Two children: empty_trace and non_empty_trace.
    assert_eq!(root.children.len(), 2);
    assert!(root.children.contains_key("empty_trace"));
    assert!(root.children.contains_key("non_empty_trace"));
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

    let mp = match maude_path() {
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
    ];

    // Several fixtures carry more than one case.  The oracle's `--prove` run
    // covers the whole file.  The loop below therefore reuses one summary for
    // all of the rows of a fixture.
    let mut summaries: tamarin_utils::FastMap<&str, String> = tamarin_utils::FastMap::default();
    for (fixture, lemma, expected, marker) in cases {
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &mp,
            tamarin_term::maude_sig::pair_maude_sig(),
        )
        .unwrap();
        let path = fixtures_dir().join(fixture);
        let src =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", fixture, e));
        let theory = parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&theory, lemma, h, 200)
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
/// per file, which gives us the rendered proof tree from Haskell.  For every
/// lemma whose verdict matches, it then diffs our `render`ed `ProofNode`
/// against tamarin's skeleton with `first_divergence`.
///
/// The probe reports `corpus structural-match: X/Y`.  Y is the total number
/// of lemmas where Haskell's proof skeleton is available.  A verdict
/// divergence does count against the structural match, because a match on
/// the verdict alone hides reasoning bugs.  There is one exception: a lemma
/// whose oracle output carries no proof the probe can extract.  The probe
/// reports such a lemma in the `no-haskell-skeleton` list and keeps it out of
/// the ledger.  The probe then holds the divergence identities to
/// [`STRUCTURAL_MISMATCH_LEDGER`].  An unexpected divergence fails the probe.
/// So does a ledger entry that the probe compares without finding a
/// divergence.  The probe does not merely print either one in the log.
///
/// This is the **primary metric** for the port's progress, per the project
/// directive: count only whether the proof matches the Haskell skeleton
/// directly.
///
/// The test carries `#[ignore]`.  Run it with `cargo test -- --ignored`.
/// This heavyweight whole-corpus probe proves every example in-process, which
/// takes more than an hour of wall clock.  The probe skips oracle-ranked
/// files first.  See [`mentions_oracle_ranking`]: a missing oracle script
/// causes a `process::exit(1)` that nothing can catch, and that would abort
/// the whole test binary.
#[test]
#[ignore = "heavyweight whole-corpus probe (hour-plus). Run with --ignored"]
fn corpus_proof_skeleton_match_probe() {
    use rayon::prelude::*;
    use tamarin_theory::proof_skeleton::{extract_from_haskell, first_divergence, render};
    use tamarin_theory::prove::prove_lemma;

    // Same stack-bump as the verdict probe — Goal-Ord + Sk-matcher path
    // can recurse deeper than rayon's default 2 MiB worker stack on
    // typing-class lemmas.
    let _ = rayon::ThreadPoolBuilder::new()
        .stack_size(64 * 1024 * 1024)
        .build_global();

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    if !tamarin_available() {
        return;
    }

    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");

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
        theory: tamarin_parser::ast::Theory,
        summary: String,
        proof_text: String,
        elab_sig: tamarin_term::maude_sig::MaudeSig,
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
            // Oracle-ranked files would process::exit the probe binary.
            if mentions_oracle_ranking(&src) {
                return None;
            }
            // Macros are supported via parser-AST macro expansion
            // (tamarin_theory::macro_expand).
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
            // (e.g. NSLPK3xor: RS 36/38 vs HS 11/13 steps).

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
            let elab_sig = match tamarin_theory::elaborate::elaborate(&theory) {
                Ok(e) => e.signature.maude_sig.clone(),
                Err(_) => tamarin_term::maude_sig::pair_maude_sig(),
            };
            Some(FileWork {
                path: path.clone(),
                theory,
                summary,
                proof_text,
                elab_sig,
            })
        })
        .collect();

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
    let lemmas: Vec<LemmaWork> = files
        .iter()
        .flat_map(|f| {
            f.theory.items.iter().filter_map(move |it| {
                let lemma = match it {
                    tamarin_parser::ast::TheoryItem::Lemma(l) => l,
                    _ => return None,
                };
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
                    theory: &f.theory,
                    elab_sig: &f.elab_sig,
                    proof_text: &f.proof_text,
                    lemma_name: lemma.name.clone(),
                    trace_quantifier: lemma.trace_quantifier.clone(),
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
            let h = match tamarin_term::maude_proc::MaudeHandle::start(&mp, w.elab_sig.clone()) {
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
            let rel = w
                .path
                .strip_prefix(&corpus_root)
                .unwrap_or(w.path.as_path())
                .to_string_lossy();
            let file_lemma = format!("{}::{}", rel, w.lemma_name);
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

/// **First end-to-end verdict-match** against `tamarin-prover`:
/// drive `tiny_setup.spthy` through `prove_lemma` and confirm we
/// reach `Solved` — same verdict tamarin produces (`verified`).
#[test]
fn prove_lemma_tiny_setup_verdict_matches_tamarin() {
    use tamarin_theory::constraint::solver::search::NodeStatus;
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp,
        tamarin_term::maude_sig::pair_maude_sig(),
    )
    .unwrap();

    let path = fixtures_dir().join("tiny_setup.spthy");
    let src = std::fs::read_to_string(&path).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&theory, "trivial", h, 100).expect("prove_lemma");

    // Our verdict.
    assert_eq!(
        root.status,
        NodeStatus::Solved,
        "expected Solved on tiny_setup, got {:?}",
        root.status
    );

    // Compare against tamarin if available.
    if !tamarin_available() {
        return;
    }
    let proved = run_tamarin_prove(&path).expect("tamarin --prove");
    let summary = extract_summary(&proved).expect("summary");
    assert!(
        summary.contains("verified"),
        "tamarin should also verify tiny_setup; summary:\n{}",
        summary
    );
}

/// End-to-end: parse `tiny_setup.spthy` (whose lemma is
/// `Ex k #i. Setup(k)@#i`), drive through formula_to_guarded +
/// formula_to_system + Induction → simplify, and verify the
/// step-case branch contains a `Goal::Action(_, Setup(_))`.
/// This exercises Ex-decomposition.
#[test]
fn ex_decomposition_produces_action_goal_via_induction() {
    use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, ProofMethod};

    let Some(ctx) = rule_free_context() else {
        return;
    };
    let sys = fixture_lemma_system("tiny_setup.spthy");
    // Trigger induction → simplify on each fork. The non_empty_trace
    // case decomposes the Ex via reduce_formulas → insert_atom.
    let cases = exec_proof_method(&ctx, &ProofMethod::Induction, &sys).expect("induction");
    let non_empty = &cases
        .iter()
        .find(|(n, _)| n == "non_empty_trace")
        .expect("non_empty")
        .1;
    assert!(
        non_empty.goals.iter().any(
            |(g, _)| matches!(g, tamarin_theory::constraint::constraints::Goal::Action(_, fact)
            if fact.tag == tamarin_theory::fact::FactTag::Proto(
                tamarin_theory::fact::Multiplicity::Linear, "Setup", 1))
        ),
        "expected a Setup-action goal in the step case after Ex decomposition"
    );
}

/// Verify atom decomposition produces real `Goal::Action` entries
/// when an action-atom inside a Conj formula is decomposed. Wraps
/// `Action(Setup, k, #i)` in a Conj so reduce_formulas picks it up.
#[test]
fn atom_decomposition_creates_action_goal_in_simplify() {
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::System;

    let Some(ctx) = rule_free_context() else {
        return;
    };

    use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
    let mkvar = |n: &str, sort: SortHint| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort,
            typ: None,
        })
    };
    let action_atom = Atom::Action(
        Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Setup".into(),
            args: vec![mkvar("k", SortHint::Msg)],
        },
        mkvar("i", SortHint::Node),
    );
    let g = tamarin_theory::guarded::Guarded::Conj(
        vec![tamarin_theory::guarded::Guarded::Atom(
            tamarin_theory::guarded::atom_to_gatom_free(&action_atom),
        )]
        .into(),
    );
    let mut sys = System::empty();
    sys.formulas_mut().push(std::sync::Arc::new(g));
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    // Action atom should have produced a Goal::Action.
    assert!(
        r.sys.goals.iter().any(|(g, _)| matches!(
            g,
            tamarin_theory::constraint::constraints::Goal::Action(_, _)
        )),
        "expected a Goal::Action after simplifying a Conj wrapping an Action atom"
    );
}

/// End-to-end with the high-level `prove_lemma` API: drive the
/// disj_lemma fixture from parse to proof tree and confirm tamarin
/// also verifies it (whatever our verdict).
#[test]
fn prove_lemma_disj_lemma_terminates_and_tamarin_verifies() {
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp,
        tamarin_term::maude_sig::pair_maude_sig(),
    )
    .unwrap();

    let path = fixtures_dir().join("disj_lemma.spthy");
    let src = std::fs::read_to_string(&path).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&theory, "either", h, 50).expect("prove_lemma");

    // `either` is `exists-trace`.  A witness trace is therefore `Solved` on
    // our side and `verified` on the oracle's.  Every other status is a
    // verdict divergence: `Open` (the budget is too small, or the search
    // stalled), `Sorry` (the search gave up) and `Contradictory` (we decided
    // that no witness exists).  So the assertion below pins the status.  It
    // does not merely require the status to be terminal.
    assert_eq!(
        root.status,
        tamarin_theory::constraint::solver::search::NodeStatus::Solved,
        "expected Solved on disj_lemma"
    );

    if !tamarin_available() {
        return;
    }
    let proved = run_tamarin_prove(&path).expect("tamarin --prove");
    let tam_summary = extract_summary(&proved).expect("summary");
    assert!(
        tam_summary.contains("verified"),
        "tamarin should verify disj_lemma; summary:\n{}",
        tam_summary
    );
}

/// Deep-search test: drive the disj_lemma all the way down. After
/// `Induction`, the `non_empty_trace` case should decompose its Conj
/// formula via `reduce_formulas`, yielding a `Goal::Disj` which the
/// search then forks. Confirms the search doesn't infinite-loop on
/// repeated Induction (which would happen without the
/// `can_apply_induction` precondition).
#[test]
fn proof_search_disj_lemma_descends_into_disj_goal() {
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};

    let Some(ctx) = rule_free_context() else {
        return;
    };
    // Generous budget — must terminate without infinite-looping.
    let root = run_proof_search(&ctx, fixture_lemma_system("disj_lemma.spthy"), 50);
    assert!(matches!(root.method, ProofMethod::Induction));
    let non_empty = root
        .children
        .get("non_empty_trace")
        .expect("non_empty branch");
    // The non_empty case decomposes its Conj formula with simplify.  That
    // yields the `Goal::Disj` that the search then picks.  If this assertion
    // also accepted `Simplify` or `Finished`, it would pass for a run that
    // never reached the disjunction.  Reaching the disjunction is what this
    // case checks.
    assert!(
        matches!(
            &non_empty.method,
            ProofMethod::SolveGoal(tamarin_theory::constraint::constraints::Goal::Disj(_))
        ),
        "expected SolveGoal(Disj) in non_empty_trace, got {:?}",
        non_empty.method
    );
    // The context holds no rules.  Nothing can produce the `A` action or the
    // `B` action that the disjuncts need, so both branches end at ⊥.
    assert_eq!(non_empty.status, NodeStatus::Contradictory);
    let empty = root.children.get("empty_trace").expect("empty branch");
    assert_eq!(empty.status, NodeStatus::Contradictory);
}

/// End-to-end with explicit decomposition: wrap a Disj in a Conj so
/// reduce_formulas picks up the Conj, recurses into the Disj, and
/// produces a Goal::Disj. This confirms `insert_formula`
/// fires when invoked through the reducible-formula path.
#[test]
fn simplify_conj_wrapping_disj_produces_goal() {
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::System;

    let Some(ctx) = rule_free_context() else {
        return;
    };

    use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
    let mkvar = |n: &str| {
        Term::Var(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort: SortHint::Node,
            typ: None,
        })
    };
    let a1 = tamarin_theory::guarded::Guarded::Atom(tamarin_theory::guarded::atom_to_gatom_free(
        &Atom::Last(mkvar("i")),
    ));
    let a2 = tamarin_theory::guarded::Guarded::Atom(tamarin_theory::guarded::atom_to_gatom_free(
        &Atom::Last(mkvar("j")),
    ));
    let disj = tamarin_theory::guarded::Guarded::Disj(vec![a1, a2].into());
    let mut sys = System::empty();
    sys.formulas_mut()
        .push(std::sync::Arc::new(tamarin_theory::guarded::Guarded::Conj(
            vec![disj].into(),
        )));
    let mut r = Reduction::new(&ctx, sys);
    simplify_system(&mut r);
    assert!(r
        .sys
        .goals
        .iter()
        .any(|(g, _)| matches!(g, tamarin_theory::constraint::constraints::Goal::Disj(_))));
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

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();

    // Parse the tiny_setup fixture and lift its rules into the proof
    // context. Build a Premise(Out(x)) goal and solve it.
    let src = std::fs::read_to_string(fixtures_dir().join("tiny_setup.spthy")).expect("fixture");
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
                let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Fresh, 0);
                use tamarin_term::vterm::Lit;
                let tk: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
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
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let fa = tamarin_theory::fact::out_fact(tx);
    let p = (i, tamarin_theory::rule::PremIdx(0));
    let out = r.solve_premise_goal(&p, &fa);
    // Exactly one rule matches.  The solver returns `LinearNamed`, which
    // carries the name of the rule that produces the fact.  HS's
    // `prettyProof` prints that name as the single `case Setup`.  A `Linear`
    // without a name prints no case heading.
    assert!(
        matches!(&out, GoalCases::LinearNamed(n) if n == "Setup"),
        "expected LinearNamed(\"Setup\"), got {out:?}"
    );
    assert_eq!(r.sys.nodes.len(), 1);
    assert_eq!(r.sys.edges.len(), 1);
}

/// Cross-check our `formula_to_guarded` rejection messages against
/// tamarin's. Both should reject `Ex k #i. (A(k)@#i) | (B(k)@#i)`
/// with an "unguarded variable(s)" error, since the existential
/// guard is a disjunction of actions rather than a conjunction.
#[test]
fn unguarded_variable_error_matches_tamarin() {
    if !tamarin_available() {
        return;
    }
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
    let out = oracle_command()
        .expect("tamarin_available")
        .arg("--prove")
        .arg(&tmp)
        .output()
        .expect("run tamarin");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let combined = format!("{}{}", stderr, stdout);
    assert!(
        combined.contains("unguarded variable"),
        "expected 'unguarded variable' from tamarin:\n{}",
        combined
    );

    // Our side: the same formula should fail guarded conversion with
    // a structurally-equivalent message.
    let theory = parse_theory(bad, &[]).expect("parse");
    let lemma = theory
        .items
        .iter()
        .find_map(|i| {
            if let tamarin_parser::ast::TheoryItem::Lemma(l) = i {
                Some(l)
            } else {
                None
            }
        })
        .expect("lemma");
    let err = formula_to_guarded(&lemma.formula).expect_err("should fail");
    assert!(
        err.message.contains("unguarded variable"),
        "expected 'unguarded variable' in our error:\n{:?}",
        err
    );
    let _ = std::fs::remove_file(&tmp);
}

/// Regression: `insert_implied_formulas_pass` must derive a `[reuse]`
/// lemma's implied consequence even when the triggering action's
/// argument is a Nat-sorted `App` term (e.g. `tone()`, the internal
/// form of `%1`) rather than a `Lit`. A prior bug in `structural_match`
/// classified every `App` as sort `Msg`, so a Nat-sorted pattern
/// variable never matched — silently dropping the reuse lemma's
/// `HonestSignatureKey` consequence whenever no sibling action offered
/// a free-variable fallback. The verdict alone doesn't catch this: the
/// buggy port still finds `Solved` via a shorter path that skips
/// `HonestSignatureKey` entirely. So this checks the proof tree
/// explicitly contains a `HonestSignatureKey` step.
#[test]
fn fixture_nat_sort_reuse_lemma_derives_implied_fact() {
    use tamarin_theory::constraint::constraints::Goal;
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::{NodeStatus, ProofNode};
    use tamarin_theory::prove::prove_lemma;

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = fixtures_dir().join("nat_sort_regression.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    let theory = parse_theory(&src, &[]).expect("parse");
    let elab = tamarin_theory::elaborate::elaborate(&theory).expect("elaborate");
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    let root = prove_lemma(&theory, "CanForgeAndPost", h, 500).expect("prove_lemma");
    assert_eq!(root.status, NodeStatus::Solved, "expected a witness trace");

    fn contains_honest_signature_key(n: &ProofNode) -> bool {
        if let ProofMethod::SolveGoal(Goal::Action(_, fa)) = &n.method {
            if tamarin_theory::fact::fact_tag_name(&fa.tag) == "HonestSignatureKey" {
                return true;
            }
        }
        n.children.values().any(contains_honest_signature_key)
    }
    assert!(
        contains_honest_signature_key(&root),
        "proof must solve HonestSignatureKey as an explicit step; \
         the reuse lemma's implied fact was silently dropped"
    );

    // Confirm tamarin agrees, when the binary is available.
    if !tamarin_available() {
        return;
    }
    let proved = run_tamarin_prove(&path).expect("tamarin");
    let summary = extract_summary(&proved).expect("summary");
    let line = summary
        .lines()
        .find(|l| l.contains("CanForgeAndPost ("))
        .expect("summary line for CanForgeAndPost");
    assert!(
        line.contains("verified"),
        "tamarin should verify CanForgeAndPost; got line:\n{}",
        line
    );
    // `solve(` only wraps explicit proof-tree steps, so this doesn't
    // depend on argument pretty-printing or timepoint variable naming.
    assert!(
        proved.contains("solve( HonestSignatureKey("),
        "tamarin's own proof must solve HonestSignatureKey explicitly"
    );
}
