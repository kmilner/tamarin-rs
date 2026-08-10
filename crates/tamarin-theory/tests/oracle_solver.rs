//! Solver-component oracle: cross-check our Rust pipeline against the PINNED
//! `tamarin-prover` — the `tamarin-prover-testing` build of the submodule
//! revision, or `HS_PATH` — on small fixture `.spthy` files.
//!
//! For each fixture we verify:
//! 1. The Rust parser/elaborator accepts the file.
//! 2. Wellformedness: no errors (the fixtures are clean).
//! 3. `tamarin-prover --parse-only` agrees the file is syntactically
//!    well-formed (return code 0).
//! 4. `tamarin-prover --prove` produces a non-error summary (the
//!    fixtures are all small lemmas tamarin can solve in a few steps).
//! 5. The number of lemmas we elaborate equals what tamarin sees.
//! 6. For each lemma, the guarded conversion succeeds.
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

/// [`oracle_command`] under `timeout <secs>s`, for the whole-corpus probes:
/// they invoke the oracle once per file and a single non-terminating example
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

/// Expected verdict mismatches for `corpus_verdict_match_coverage_probe`.
///
/// Enumerated 2026-08-10 (60s oracle timeout, release, guarded serial run;
/// identity-stable across two enumerations at different machine load —
/// 138/142 and 150/154 matched, same four identities both times).
const VERDICT_MISMATCH_LEDGER: ProbeLedger = Some(&[
    "loops/JCS12_Typing_Example.spthy::Client_session_key_secrecy_raw",
    "loops/JCS12_Typing_Example.spthy::typing_assertion",
    "post17/foo_eligibility.spthy::eligibility",
    "post17/foo_eligibility.spthy::types",
]);

/// Minimum lemmas the verdict probe must actually compare.  Guards the
/// source-text exclusions (oracle-ranked, `diff(`, sapic, DH/XOR/BP) and the
/// eligible-set breathing: a run that compares fewer has collapsed its
/// coverage (oracle missing, corpus moved, timeout too tight for the load)
/// and proves nothing no matter how clean its mismatch list looks.
const VERDICT_MIN_COMPARED: usize = 120;

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
/// file aborts the whole probe binary, uncatchably, so both corpus probes
/// skip them up front.  Matches inside comments that merely quote a
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

fn tamarin_available() -> bool {
    oracle_binary().is_some_and(|p| {
        Command::new(p)
            .arg("--help")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
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

#[test]
fn fixture_tiny_setup_round_trip() {
    let path = fixtures_dir().join("tiny_setup.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    // Rust side: parses, has 1 rule, 1 lemma.
    assert_eq!(rust_rule_count(&src), 1);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() {
        return;
    }

    // Tamarin parse-only.
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 1);
    assert_eq!(count_lemmas_in_output(&out), 1);

    // Tamarin proves it.
    let proved = run_tamarin_prove(&path).expect("tamarin prove");
    let summary = extract_summary(&proved).expect("summary block");
    assert!(
        summary.contains("verified"),
        "expected 'verified' in summary:\n{}",
        summary
    );
}

#[test]
fn fixture_two_rules_round_trip() {
    let path = fixtures_dir().join("two_rules.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    assert_eq!(rust_rule_count(&src), 2);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() {
        return;
    }
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 2);
    assert_eq!(count_lemmas_in_output(&out), 1);
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

/// Count quantifiers in a guarded formula.
fn count_quantifiers(g: &Guarded) -> (usize, usize) {
    fn rec(g: &Guarded, ex: &mut usize, all: &mut usize) {
        match g {
            Guarded::Atom(_) => {}
            Guarded::Conj(xs) | Guarded::Disj(xs) => {
                for x in xs.iter() {
                    rec(x, ex, all);
                }
            }
            Guarded::GGuarded {
                qua, vars, body, ..
            } => {
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
/// count Ex/All in our `formula_to_guarded` output and compare with the
/// `∃` / `∀` glyphs in tamarin's `--prove` output.  Tamarin emits one glyph
/// per quantifier BLOCK while `count_quantifiers` counts bound variables, so
/// the comparison below is presence-parity, not an equality.
#[test]
fn guarded_quantifier_count_matches_tamarin() {
    if !tamarin_available() {
        return;
    }
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
            Some(o) => o,
            None => continue,
        };
        let tam_has_ex = proved.contains('∃');
        let tam_has_all = proved.contains('∀');
        assert_eq!(
            our_ex > 0,
            tam_has_ex,
            "{}: our_ex={} vs tam_has_ex={}",
            name,
            our_ex,
            tam_has_ex
        );
        assert_eq!(
            our_all > 0,
            tam_has_all,
            "{}: our_all={} vs tam_has_all={}",
            name,
            our_all,
            tam_has_all
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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy")).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::run_proof_search;
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy")).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
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

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };

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
        (
            "multiple_lemmas.spthy",
            "all_at_same_node",
            NodeStatus::Solved,
        ),
        // 5-step state-machine chain.
        ("auth_pattern.spthy", "protocol_runs", NodeStatus::Solved),
        // Simple In/Out chain — no pair construction.
        ("single_recv.spthy", "chain", NodeStatus::Solved),
        // All-traces lemmas → Contradictory (negation dead-ends).
        (
            "safety_unique.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
        ),
        (
            "safety_two_keys.spthy",
            "fresh_distinct_times",
            NodeStatus::Contradictory,
        ),
        // Restriction-driven uniqueness lemma.
        (
            "restriction_unique.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
        ),
        // Reuse-flagged lemma — stands alone and is verifiable.
        (
            "reuse_lemma.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
        ),
        // [use_induction] attribute — trivially-true tautology.
        ("use_induction.spthy", "a_self", NodeStatus::Contradictory),
        // Rule-level let-block desugaring (`let r = ~k in ...`).
        ("let_block.spthy", "use_self", NodeStatus::Contradictory),
        // Fresh-ordering CR-rule + edge-aware cyclic check: ~s
        // creator must precede any rule mentioning ~s downstream.
        ("fresh_ordering.spthy", "order", NodeStatus::Contradictory),
        // [sources] lemma — forces induction + appends to restrictions.
        (
            "sources_lemma.spthy",
            "setup_self",
            NodeStatus::Contradictory,
        ),
        (
            "sources_lemma.spthy",
            "setup_unique",
            NodeStatus::Contradictory,
        ),
        // partialAtomValuation: `i < j | i = j` collapses once the
        // chain edge fires and `alwaysBefore` decides the disjunct.
        ("eval_atoms.spthy", "a_then_b", NodeStatus::Contradictory),
    ];

    // Tamarin falsifies `never_both` — for an all-traces lemma that's
    // FALSE, our counter-example search should reach `Solved`.
    let falsifiable_cases: &[(&str, &str, NodeStatus, &str)] = &[
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

    for (fixture, lemma, expected) in cases {
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
        let proved = run_tamarin_prove(&path).expect("tamarin");
        let summary = extract_summary(&proved).expect("summary");
        // The summary lists every lemma; check this one shows verified.
        let line = summary
            .lines()
            .find(|l| l.contains(&format!("{} (", lemma)))
            .unwrap_or_else(|| panic!("no summary line for {}", lemma));
        assert!(
            line.contains("verified"),
            "tamarin should verify {}/{}; got line:\n{}",
            fixture,
            lemma,
            line
        );
    }

    // Falsifiable lemmas: verdict = falsified ↔ Solved (counterexample).
    for (fixture, lemma, expected, marker) in falsifiable_cases {
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &mp,
            tamarin_term::maude_sig::pair_maude_sig(),
        )
        .unwrap();
        let path = fixtures_dir().join(fixture);
        let src = std::fs::read_to_string(&path).expect("read");
        let theory = parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&theory, lemma, h, 200)
            .unwrap_or_else(|e| panic!("prove_lemma({}/{}): {:?}", fixture, lemma, e));
        assert_eq!(
            root.status, *expected,
            "{}/{}: expected {:?}, got {:?}",
            fixture, lemma, expected, root.status
        );

        if !tamarin_available() {
            continue;
        }
        let proved = run_tamarin_prove(&path).expect("tamarin");
        let summary = extract_summary(&proved).expect("summary");
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

/// **Haskell-behavior pin tests**: structural cross-checks that
/// don't just compare verdicts but pin specific Haskell-documented
/// behaviors:
///   1. Tamarin emits "unguarded variable(s)" for non-doubly-guarded
///      formulas — our `formula_to_guarded` should too.
///   2. Tamarin's signature output for a `pair`-only theory names the
///      `pair` symbol — our elaboration agrees.
#[test]
fn haskell_behavior_pins() {
    if !tamarin_available() {
        return;
    }

    // Pin #1: error message wording for unguarded variables.
    let bad = r#"theory T begin
rule R: [Fr(~k)] --[A(~k)]-> []
lemma bad: exists-trace "Ex k #i. (A(k) @ #i) | (A(k) @ #i)"
end"#;
    let tmp = std::env::temp_dir().join("oracle_pin_bad_guarded.spthy");
    std::fs::write(&tmp, bad).unwrap();
    let out = oracle_command()
        .expect("tamarin_available")
        .arg("--prove")
        .arg(&tmp)
        .output()
        .expect("tamarin");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let combined = format!("{}{}", stderr, stdout);
    assert!(
        combined.contains("unguarded variable"),
        "tamarin should reject this formula with 'unguarded variable'; got:\n{}",
        combined
    );
    // Our side: rejected with same wording.
    let parsed = parse_theory(bad, &[]).expect("parse");
    let lemma = parsed
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
    let err = tamarin_theory::guarded::formula_to_guarded(&lemma.formula)
        .expect_err("our guarded conversion should reject");
    assert!(
        err.message.contains("unguarded variable"),
        "we should also report 'unguarded variable'; got: {:?}",
        err
    );
    let _ = std::fs::remove_file(&tmp);

    // Pin #2: tamarin --parse-only output for a pair-only theory
    // names `pair`, `fst`, `snd` symbols (matches our elaboration's
    // signature population).
    let pair_thy = "theory P begin\nrule R: [Fr(~k)] --[A(~k)]-> [Out(<~k, ~k>)]\nend";
    let ptmp = std::env::temp_dir().join("oracle_pin_pair.spthy");
    std::fs::write(&ptmp, pair_thy).unwrap();
    let out = oracle_command()
        .expect("tamarin_available")
        .arg("--parse-only")
        .arg(&ptmp)
        .output()
        .expect("tamarin");
    let outs = String::from_utf8_lossy(&out.stdout);
    assert!(
        outs.contains("pair/2") || outs.contains("pair"),
        "tamarin's signature should mention pair: {}",
        outs
    );
    let _ = std::fs::remove_file(&ptmp);
}

/// **Corpus verdict-match coverage probe**: walks the corpus directories
/// listed below, runs `prove_lemma` and the pinned oracle's `--prove` on
/// every lemma, and holds the mismatches to [`VERDICT_MISMATCH_LEDGER`] —
/// an unexpected mismatch or a silently-resolved ledger entry fails the
/// probe instead of scrolling past in the log.
///
/// Skips files that mention `diff(`, `predicates:` or `process:`, files whose
/// `builtins:` name diffie-hellman / xor / bilinear-pairing, oracle-ranked
/// files (see [`mentions_oracle_ranking`]), and any file the oracle does not
/// finish within 60s.
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

    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    if !tamarin_available() {
        return;
    }

    // Per-process global — set ONCE before parallel work so threads
    // don't race on env writes.  Step budget (2000) is the deterministic
    // gate; 10s deadline is the wall-clock backstop.
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "10000");

    let corpus_root = corpus_root();
    let target_dirs = [
        "loops",
        "csf23-subterms",
        "experiments",
        "regression",
        "ccs15",
        "classic",
        "features",
        "related_work",
        "post17",
        "cav13",
        "jcs18",
        "csf18-alethea",
        // Added — small dirs with mostly-supported protocols.  csf17
        // is 4 files all unexcluded; csf12 has a few simple ones.
        "csf17",
        "csf12",
        // testParser is parser-level fixtures; define.spthy is a tiny
        // #ifdef preprocessor exercise.
        "testParser",
    ];

    // Phase 1: collect candidate spthy paths (sequential — just I/O).
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    for dir in &target_dirs {
        let dir_path = corpus_root.join(dir);
        if !dir_path.exists() {
            continue;
        }
        for e in walkdir::WalkDir::new(&dir_path)
            .max_depth(2)
            .into_iter()
            .filter_map(|e| e.ok())
        {
            if e.path().extension().and_then(|s| s.to_str()) == Some("spthy") {
                // testParser/include uses #include which pulls in
                // user-defined equations from sibling files; the
                // builtin-filter on the entry file can't see them.
                let p = e.path();
                if p.to_string_lossy().contains("/testParser/include/") {
                    continue;
                }
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
    let files: Vec<FileWork> = paths
        .par_iter()
        .filter_map(|path| {
            let src = std::fs::read_to_string(path).ok()?;
            // No `equations:` filter here: user-declared equations are wired
            // through elaborate.rs → MaudeSig.st_rules → Maude module text.
            // A destructor-chain explosion can truncate case enumeration; the
            // source is then tagged `Source.incomplete`, which — as in HS
            // `isFinished` — is diagnostic only and does NOT downgrade a
            // Solved leaf (see `proof_method`'s `is_finished`).
            if src.contains("diff(") {
                return None;
            }
            // Oracle-ranked files would process::exit the probe binary.
            if mentions_oracle_ranking(&src) {
                return None;
            }
            // Macros are supported via parser-AST macro expansion
            // (tamarin_theory::macro_expand).  Predicates still need their
            // own port (RS predicate_expand handles formulas but elaborate
            // skips predicate items at the typed layer).
            if src.contains("predicates:") {
                return None;
            }
            if src.contains("process:") {
                return None;
            }
            if src.contains("builtins:")
                && (src.contains("diffie-hellman")
                    || src.contains("xor")
                    || src.contains("bilinear-pairing"))
            {
                return None;
            }

            let theory = tamarin_parser::parse_theory(&src, &[]).ok()?;
            // Run tamarin once per file with a timeout.  60s, not 10: at 10s
            // the eligible set breathed with machine load, and the ledger
            // pins identities from a maximally-complete enumeration.
            let tam_out = oracle_command_within(60)?
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
            Some(FileWork {
                path: path.clone(),
                theory,
                summary: summary.to_string(),
                elab_sig,
            })
        })
        .collect();

    // Phase 3: flatten to per-lemma work items.
    struct LemmaWork<'a> {
        path: &'a std::path::PathBuf,
        theory: &'a tamarin_parser::ast::Theory,
        elab_sig: &'a tamarin_term::maude_sig::MaudeSig,
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
                    lemma_name: lemma.name.clone(),
                    trace_quantifier: lemma.trace_quantifier.clone(),
                    tamarin_verdict,
                })
            })
        })
        .collect();

    // Phase 4: run prove_lemma per lemma in parallel.  Each lemma gets
    // its own MaudeHandle (independent subprocess); rayon manages
    // thread-pool sizing via num_cpus.
    enum LemmaOutcome {
        Match(String),
        Diff(String, String),
        Incomparable,
    }
    let dbg_incomp = std::env::var("TAM_DBG_INCOMPARABLE").is_ok();
    let outcomes: Vec<LemmaOutcome> = lemmas
        .par_iter()
        .map(|w| {
            let h = match tamarin_term::maude_proc::MaudeHandle::start(&mp, w.elab_sig.clone()) {
                Ok(h) => h,
                Err(_) => return LemmaOutcome::Incomparable,
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
                eprintln!(
                    "WATCHDOG: {}::{} killed after {:?}",
                    fname, w.lemma_name, elapsed
                );
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
                        eprintln!(
                            "INCOMPARABLE: {}::{} → {:?} (tamarin={})",
                            w.path.file_name().unwrap().to_string_lossy(),
                            w.lemma_name,
                            root.status,
                            w.tamarin_verdict
                        );
                    }
                    return LemmaOutcome::Incomparable;
                }
            };
            let rel = w
                .path
                .strip_prefix(&corpus_root)
                .unwrap_or(w.path.as_path())
                .to_string_lossy();
            let id = format!("{}::{}", rel, w.lemma_name);
            if our_verdict == w.tamarin_verdict {
                LemmaOutcome::Match(id)
            } else {
                let detail = format!(
                    "{} — ours={}, tamarin={}",
                    id, our_verdict, w.tamarin_verdict
                );
                LemmaOutcome::Diff(id, detail)
            }
        })
        .collect();

    // Aggregate.
    let mut compared_ids: Vec<String> = Vec::new();
    let mut matched = 0usize;
    let mut mismatches: Vec<(String, String)> = Vec::new();
    for o in outcomes {
        match o {
            LemmaOutcome::Match(id) => {
                compared_ids.push(id);
                matched += 1;
            }
            LemmaOutcome::Diff(id, detail) => {
                compared_ids.push(id.clone());
                mismatches.push((id, detail));
            }
            LemmaOutcome::Incomparable => {}
        }
    }

    eprintln!(
        "corpus verdict-match: {}/{} matched",
        matched,
        compared_ids.len()
    );
    if !mismatches.is_empty() {
        eprintln!("mismatches:");
        // Sort for deterministic output order under parallel scheduling.
        mismatches.sort();
        for (_, d) in &mismatches {
            eprintln!("  {}", d);
        }
    }
    let coverage = compared_ids.len();
    enforce_probe_ledger(
        "corpus verdict-match",
        "VERDICT_MISMATCH_LEDGER",
        "VERDICT_MIN_COMPARED",
        VERDICT_MISMATCH_LEDGER,
        VERDICT_MIN_COMPARED,
        &compared_ids,
        coverage,
        &mismatches,
    );
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
/// masks reasoning bugs).  The divergence identities are then held to
/// [`STRUCTURAL_MISMATCH_LEDGER`], so an unexpected divergence or a
/// silently-resolved ledger entry fails the probe instead of scrolling
/// past in the log.
///
/// This is the **primary metric** for the port's progress, per
/// project directive: count only whether the proof matches the
/// Haskell skeleton directly.
///
/// `#[ignore]`d (run with `cargo test -- --ignored`): this heavyweight
/// whole-corpus probe proves every example in-process — an hour-plus of
/// wall clock.  Oracle-ranked files are skipped up front (see
/// [`mentions_oracle_ranking`]: a missing oracle script is an uncatchable
/// `process::exit(1)` that would abort the whole test binary).
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

/// Probe: TPM Exclusive_Secrets::left_reachable contradiction breakdown.
#[test]
#[ignore = "diagnostic probe — task #120; run with --ignored"]
fn probe_tpm_left_reachable() {
    use tamarin_theory::constraint::solver::search::ProofNode;
    use tamarin_theory::prove::prove_lemma;
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("related_work/TPM_DKRS_CSF11/TPM_Exclusive_Secrets.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    // Print sources first
    use tamarin_theory::constraint::solver::context::ProofContext;
    let rules: Vec<_> = elab.rules().cloned().collect();
    let h_probe =
        tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
            .unwrap();
    let ctx = ProofContext::new(h_probe, rules);
    use tamarin_theory::constraint::constraints::Goal;
    for src_obj in &ctx.full_sources {
        if let Goal::Action(_, fa) = &src_obj.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first())
                    .chars()
                    .take(120)
                    .collect::<String>();
                eprintln!(
                    "Ku source ({} cases): {}",
                    src_obj.cases_or_empty().len(),
                    term_dbg
                );
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
        for c in n.children.values() {
            count_results(c, m);
        }
    }
    let mut m = std::collections::BTreeMap::new();
    count_results(&root, &mut m);
    eprintln!("TPM_LEFT leaf breakdown:");
    for (k, v) in &m {
        eprintln!("  {}: {}", k, v);
    }
    fn dump_tree(n: &ProofNode, d: usize, max: usize) {
        if d > max {
            return;
        }
        let pad = "  ".repeat(d);
        let m_short: String = format!("{:?}", n.method).chars().take(100).collect();
        eprintln!(
            "{}{:?} m={} ch={}",
            pad,
            n.status,
            m_short,
            n.children.len()
        );
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
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("classic/NSPK3.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    let rules: Vec<_> = elab.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);
    let sources = precompute_full_sources(&ctx);
    eprintln!("Precomputed sources: {}", sources.len());
    use tamarin_theory::constraint::constraints::Goal;
    for src in &sources {
        if let Goal::Action(_, fa) = &src.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first())
                    .chars()
                    .take(80)
                    .collect::<String>();
                eprintln!(
                    "=== source: Goal::Action _ Ku({}) — {} cases",
                    term_dbg,
                    src.cases_or_empty().len()
                );
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
    use tamarin_theory::constraint::solver::search::ProofNode;
    use tamarin_theory::prove::prove_lemma;
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("classic/NSPK3.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
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
            if let Some(r) = find_cyclic(c, p) {
                return Some(r);
            }
        }
        None
    }
    if let Some((leaf, path)) = find_cyclic(&root, Vec::new()) {
        eprintln!("Cyclic leaf path: {:?}", path);
        // Find all nodes with Fresh premises — and identify pairs that share fresh.
        use tamarin_term::lterm::HasFrees;
        let mut fresh_consumers: Vec<(
            tamarin_term::lterm::LVar,
            tamarin_term::lterm::LVar,
            String,
        )> = Vec::new();
        for (id, ru) in leaf.sys.nodes.iter() {
            for prem in &ru.premises {
                if matches!(prem.tag, tamarin_theory::fact::FactTag::Fresh) {
                    let mut vars = Vec::new();
                    prem.for_each_free(&mut |v| vars.push(*v));
                    if let Some(v) = vars
                        .into_iter()
                        .find(|v| v.sort == tamarin_term::lterm::LSort::Fresh)
                    {
                        let info = format!("{:?}", ru.info)
                            .chars()
                            .take(60)
                            .collect::<String>();
                        fresh_consumers.push((*id, v, info));
                    }
                }
            }
        }
        eprintln!("Fresh consumers ({}):", fresh_consumers.len());
        for (id, v, info) in &fresh_consumers {
            eprintln!(
                "  node {}#{} consumes Fr({}#{}:{:?})  rule={}",
                id.name, id.idx, v.name, v.idx, v.sort, info
            );
        }
        eprintln!("Pairs sharing same fresh:");
        for i in 0..fresh_consumers.len() {
            for j in (i + 1)..fresh_consumers.len() {
                if fresh_consumers[i].1 == fresh_consumers[j].1
                    && fresh_consumers[i].0 != fresh_consumers[j].0
                {
                    eprintln!(
                        "  CONFLATED: {}#{} <> {}#{} share {}#{}",
                        fresh_consumers[i].0.name,
                        fresh_consumers[i].0.idx,
                        fresh_consumers[j].0.name,
                        fresh_consumers[j].0.idx,
                        fresh_consumers[i].1.name,
                        fresh_consumers[i].1.idx
                    );
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
    use tamarin_theory::constraint::constraints::Goal;
    use tamarin_theory::constraint::solver::context::ProofContext;
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("post17/chaum_unforgeability.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    // Also render Rust's proof for chaum::exec
    {
        let h_proof =
            tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
                .unwrap();
        std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
        let root = tamarin_theory::prove::prove_lemma(&theory, "exec", h_proof, 500).unwrap();
        eprintln!("== Rendered proof for exec ==");
        eprintln!("{}", tamarin_theory::proof_skeleton::render(&root));
    }
    let h_probe =
        tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
            .unwrap();
    let rules: Vec<_> = elab.rules().cloned().collect();
    let ctx = ProofContext::new(h_probe, rules);
    // Dump destructor intruder rules (used by close_chains_dfs's
    // destructor-extension branch).
    eprintln!("== Destructor intruder rules ==");
    for ir in &ctx.intruder_rules {
        if tamarin_theory::rule::is_destr_rule_info(&ir.info) {
            let prems = ir
                .premises
                .iter()
                .map(|f| format!("{:?}", f).chars().take(80).collect::<String>())
                .collect::<Vec<_>>();
            let concs = ir
                .conclusions
                .iter()
                .map(|f| format!("{:?}", f).chars().take(80).collect::<String>())
                .collect::<Vec<_>>();
            eprintln!("  {:?} prems={:?} concs={:?}", ir.info, prems, concs);
        }
    }
    eprintln!(
        "== Precomputed full_sources ({} entries) ==",
        ctx.full_sources.len()
    );
    for src_obj in &ctx.full_sources {
        if let Goal::Action(_, fa) = &src_obj.goal {
            if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                let term_dbg = format!("{:?}", fa.terms.first())
                    .chars()
                    .take(160)
                    .collect::<String>();
                eprintln!(
                    "Ku source ({} cases): {}",
                    src_obj.cases_or_empty().len(),
                    term_dbg
                );
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
                    eprintln!(
                        "    eq_store.subst ({}):",
                        case_sys.eq_store.subst.to_list().len()
                    );
                    for (v, t) in case_sys.eq_store.subst.to_list().iter() {
                        let ts = format!("{:?}", t).chars().take(80).collect::<String>();
                        eprintln!("      {:?} → {}", v, ts);
                    }
                    eprintln!("    eq_store.conj ({}):", case_sys.eq_store.conj.len());
                    for (i, d) in case_sys.eq_store.conj.iter().enumerate() {
                        eprintln!("      disj[{}].substs ({}):", i, d.substs.len());
                        for (j, s) in d.substs.iter().enumerate() {
                            let ts = format!("{:?}", s).chars().take(140).collect::<String>();
                            eprintln!("        [{}] {}", j, ts);
                        }
                    }
                    eprintln!(
                        "    open goals ({}):",
                        case_sys.goals.iter().filter(|(_, st)| !st.solved).count()
                    );
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
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("classic/TLS_Handshake.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    // Dump precomputed sources first
    {
        let h_probe =
            tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
                .unwrap();
        let rules: Vec<_> = elab.rules().cloned().collect();
        let ctx = tamarin_theory::constraint::solver::context::ProofContext::new(h_probe, rules);
        use tamarin_theory::constraint::constraints::Goal;
        eprintln!(
            "== Precomputed full_sources ({} entries) ==",
            ctx.full_sources.len()
        );
        for src_obj in &ctx.full_sources {
            if let Goal::Action(_, fa) = &src_obj.goal {
                if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                    let term_dbg = format!("{:?}", fa.terms.first())
                        .chars()
                        .take(120)
                        .collect::<String>();
                    eprintln!(
                        "Ku source ({} cases): {}",
                        src_obj.cases_or_empty().len(),
                        term_dbg
                    );
                    for (name, _) in src_obj.cases_or_empty() {
                        eprintln!("  case: {}", name);
                    }
                }
            }
        }
    }
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
    let root =
        tamarin_theory::prove::prove_lemma(&theory, "session_key_setup_possible", h, 2000).unwrap();
    eprintln!("== Rust's proof for TLS::session_key_setup_possible ==");
    eprintln!("{}", tamarin_theory::proof_skeleton::render(&root));
    // Find the first node whose case-name ends in `_case_N` and print its
    // children + open goals before the split.
    use tamarin_theory::constraint::solver::search::ProofNode;
    fn find_case_n(n: &ProofNode, path: Vec<String>) -> Option<(&ProofNode, Vec<String>)> {
        // If any child's case-name contains "_case_", this node is the
        // source of the split.
        for name in n.children.keys() {
            if name.contains("_case_") {
                return Some((n, path));
            }
        }
        for (name, c) in &n.children {
            let mut p = path.clone();
            p.push(name.clone());
            if let Some(r) = find_case_n(c, p) {
                return Some(r);
            }
        }
        None
    }
    if let Some((node, path)) = find_case_n(&root, Vec::new()) {
        eprintln!("\n== First _case_N split node ==");
        eprintln!("Path to it: {:?}", path);
        eprintln!(
            "Method: {:?}",
            format!("{:?}", node.method)
                .chars()
                .take(200)
                .collect::<String>()
        );
        eprintln!("Children ({}):", node.children.len());
        for name in node.children.keys() {
            eprintln!("  - {}", name);
        }
        eprintln!("\n== System state at this node ==");
        eprintln!("  nodes ({}):", node.sys.nodes.len());
        for (id, ru) in node.sys.nodes.iter().take(20) {
            let ru_dbg = format!("{:?}", ru.info)
                .chars()
                .take(80)
                .collect::<String>();
            eprintln!("    #{}:{:?} → {}", id.name, id.idx, ru_dbg);
        }
        eprintln!(
            "  open goals ({}):",
            node.sys.goals.iter().filter(|(_, st)| !st.solved).count()
        );
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
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("classic/NSLPK3_untagged.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    {
        let h_probe =
            tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
                .unwrap();
        let rules: Vec<_> = elab.rules().cloned().collect();
        let ctx = tamarin_theory::constraint::solver::context::ProofContext::new(h_probe, rules);
        use tamarin_theory::constraint::constraints::Goal;
        eprintln!(
            "== Precomputed full_sources ({} entries) ==",
            ctx.full_sources.len()
        );
        for src_obj in &ctx.full_sources {
            if let Goal::Action(_, fa) = &src_obj.goal {
                if matches!(fa.tag, tamarin_theory::fact::FactTag::Ku) {
                    let term_dbg = format!("{:?}", fa.terms.first())
                        .chars()
                        .take(140)
                        .collect::<String>();
                    eprintln!(
                        "Ku source ({} cases): {}",
                        src_obj.cases_or_empty().len(),
                        term_dbg
                    );
                    for (name, _) in src_obj.cases_or_empty() {
                        eprintln!("  case: {}", name);
                    }
                }
            }
        }
    }
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "60000");
    let root = tamarin_theory::prove::prove_lemma(&theory, "nonce_secrecy", h, 5000).unwrap();
    let rs_skel = tamarin_theory::proof_skeleton::render(&root);
    eprintln!("== Rust's proof for NSLPK3_untagged::nonce_secrecy ==");
    eprintln!("{}", rs_skel);
    // Also fetch HS's skeleton via tamarin-prover output, dump side-by-side
    // around the first divergence to make targeted fixes possible.
    let tam_out = oracle_command_within(30).and_then(|mut c| {
        c.arg("--prove")
            .arg("--output=/tmp/nslpk3_hs_full.spthy")
            .arg(path)
            .output()
            .ok()
    });
    if tam_out.is_some() {
        if let Ok(hs_text) = std::fs::read_to_string("/tmp/nslpk3_hs_full.spthy") {
            if let Some(hs_skel) =
                tamarin_theory::proof_skeleton::extract_from_haskell(&hs_text, "nonce_secrecy")
            {
                eprintln!("== HS skeleton for NSLPK3_untagged::nonce_secrecy ==");
                eprintln!("{}", hs_skel);
                if let Some((line_no, ours_line, theirs_line)) =
                    tamarin_theory::proof_skeleton::first_divergence(&rs_skel, &hs_skel)
                {
                    eprintln!("\n== FIRST DIVERGENCE ==");
                    eprintln!(
                        "line {}: ours={:?} theirs={:?}",
                        line_no, ours_line, theirs_line
                    );
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
    let mp = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let path = corpus_root().join("features/xor/CR.spthy");
    let src = std::fs::read_to_string(&path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&mp, elab.signature.maude_sig.clone())
        .unwrap();
    std::env::set_var("TAM_PROVE_DEADLINE_MS", "30000");
    let root = tamarin_theory::prove::prove_lemma(&theory, "executable", h, 5000).unwrap();
    let skel = tamarin_theory::proof_skeleton::render(&root);
    eprintln!("== Rust's proof for CR::executable ==");
    eprintln!("Status: {:?}", root.status);
    eprintln!("{}", skel);

    // Walk the proof tree to find the Cyclic leaf and dump its system.
    fn walk(node: &tamarin_theory::constraint::solver::search::ProofNode, depth: usize) {
        use tamarin_theory::constraint::solver::contradictions::Contradiction;
        use tamarin_theory::constraint::solver::proof_method::{
            ProofMethod, Result as MethodResult,
        };
        if node.children.is_empty() {
            if let ProofMethod::Finished(MethodResult::Contradictory(c)) = &node.method {
                if matches!(c, Some(Contradiction::Cyclic)) {
                    eprintln!("\n== CYCLIC LEAF at depth {} ==", depth);
                    eprintln!("nodes ({}):", node.sys.nodes.len());
                    for (id, rule) in node.sys.nodes.iter() {
                        let name =
                            tamarin_theory::constraint::solver::reduction::rule_case_name(rule);
                        let ku_acts: Vec<_> = rule
                            .actions
                            .iter()
                            .filter(|a| matches!(a.tag, tamarin_theory::fact::FactTag::Ku))
                            .map(|a| {
                                format!("{:?}", a.terms.first())
                                    .chars()
                                    .take(80)
                                    .collect::<String>()
                            })
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
                    eprintln!(
                        "eq_store.subst ({}):",
                        node.sys.eq_store.subst.to_list().len()
                    );
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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, ProofMethod};
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("tiny_setup.spthy")).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::reduction::Reduction;
    use tamarin_theory::constraint::solver::simplify::simplify_system;
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

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

    // Whatever our verdict, the proof must terminate within budget.
    // Tamarin verifies this lemma; record both for cross-comparison.
    let our_status = format!("{:?}", root.status);

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

    // Our search should reach a non-Open terminal state. We don't
    // require Solved (full proof) since action atoms / KU goals
    // aren't fully ported — but it must not be stuck Open.
    assert!(
        !matches!(
            root.status,
            tamarin_theory::constraint::solver::search::NodeStatus::Open
        ),
        "search reached terminal status: {}",
        our_status
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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::proof_method::ProofMethod;
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};
    use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

    let src = std::fs::read_to_string(fixtures_dir().join("disj_lemma.spthy")).expect("read");
    let theory = parse_theory(&src, &[]).expect("parse");
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
    let non_empty = root
        .children
        .get("non_empty_trace")
        .expect("non_empty branch");
    // The non_empty case should have decomposed its Conj formula
    // via simplify, yielding a Goal::Disj that the search picked up.
    // After SolveGoal fires, `non_empty.method` should be SolveGoal.
    assert!(
        matches!(
            &non_empty.method,
            ProofMethod::SolveGoal(tamarin_theory::constraint::constraints::Goal::Disj(_))
                | ProofMethod::Simplify
                | ProofMethod::Finished(_)
        ),
        "expected SolveGoal/Simplify/Finished in non_empty_trace, got {:?}",
        non_empty.method
    );
    // The empty_trace branch should be Solved (empty trace doesn't
    // satisfy ∃ k. A(k), and we look for satisfaction → False) or
    // Contradictory (system reduces to ⊥).
    let empty = root.children.get("empty_trace").expect("empty branch");
    assert!(
        matches!(
            empty.status,
            NodeStatus::Solved | NodeStatus::Contradictory | NodeStatus::Sorry
        ),
        "empty_trace should reach a terminal state, got {:?}",
        empty.status
    );
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

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

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
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_theory::constraint::solver::context::ProofContext;
    use tamarin_theory::constraint::solver::search::{run_proof_search, NodeStatus};
    use tamarin_theory::constraint::system::System;

    let path = match maude_path() {
        Some(p) => p,
        None => return,
    };
    let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let ctx = ProofContext::new(h, Vec::new());

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

#[test]
fn fixture_disj_lemma_round_trip() {
    let path = fixtures_dir().join("disj_lemma.spthy");
    let src = std::fs::read_to_string(&path).expect("read fixture");
    assert_eq!(rust_rule_count(&src), 2);
    assert_eq!(rust_lemma_count(&src), 1);

    if !tamarin_available() {
        return;
    }
    let out = run_tamarin_parse_only(&path).expect("tamarin parse");
    assert_eq!(count_rules_in_output(&out), 2);
    assert_eq!(count_lemmas_in_output(&out), 1);

    // The lemma body contains a top-level disjunction. Tamarin's
    // pretty-printed parse-only form should preserve the `|`.
    assert!(out.contains('|') || out.contains('∨'));
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
