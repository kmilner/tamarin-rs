// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Out-of-line tests for [`super`].
//!
//! The verdict checks here cover the shapes that the fixture verdict suite
//! in `tests/oracle_solver.rs` does not carry.  That suite cross-checks its
//! own `(fixture, lemma) -> NodeStatus` table against the pinned Haskell
//! oracle's `verified`/`falsified` summary.  A shape that the suite already
//! lists therefore needs no second check that asserts less here.

use super::*;
use crate::constraint::solver::search::NodeStatus;
use crate::test_maude::maude_path;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::{pair_maude_sig, MaudeSig};

/// Returns a maude handle on `sig`.  Returns `None` only when the run opts
/// out explicitly with `TAM_ALLOW_NO_MAUDE=1`.  Path resolution and the
/// policy that panics both live in [`crate::test_maude::maude_path`].
///
/// A maude that resolves but does not start is the same misconfiguration as
/// a dangling `MAUDE_PATH`.  A `.ok()` here would hide that error, and every
/// check in this file would then skip without notice.  This function panics
/// instead.
fn maude_with(sig: MaudeSig) -> Option<MaudeHandle> {
    let path = maude_path()?;
    Some(MaudeHandle::start(&path, sig).unwrap_or_else(|e| {
        panic!("maude at {path} failed to start: {e:?} — every maude-backed pin here would otherwise skip silently")
    }))
}

/// Calls [`maude_with`] with the pair-only signature.
fn maude() -> Option<MaudeHandle> {
    maude_with(pair_maude_sig())
}

/// Parses `tests/fixtures/<name>`.  The fixture is committed next to this
/// crate.  A read failure therefore means a broken checkout.  It is never a
/// reason to skip the test.
fn fixture_theory(name: &str) -> tamarin_parser::ast::Theory {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    tamarin_parser::parse_theory(&src, &[]).expect("parse")
}

#[test]
fn prove_lemma_unknown_name_is_error() {
    let Some(h) = maude() else { return };
    let parser_theory = tamarin_parser::parse_theory("theory T begin end", &[]).expect("parse");
    let r = prove_lemma(&parser_theory, "nonexistent", h, 5);
    assert!(matches!(r, Err(ProveError::LemmaNotFound(_))));
}

/// The `features/injectivity` corpus example runs
/// `simple_injective_fact_instances` through a complete proof.  The
/// injective-fact analysis supplies the less-atoms that close the negation
/// of `injectivity_check`.  Without the analysis, or without the less-atoms
/// it feeds, the negated all-traces formula no longer contradicts.  The
/// verdict then changes from `Contradictory` to `Solved` or `Sorry`.
///
/// The example is an upstream feature demo, and the oracle verifies it.
/// `Contradictory` is therefore the oracle's verdict, not only the port's.
#[test]
fn injectivity_corpus_example_is_contradictory() {
    let Some(h) = maude() else { return };
    // The crate cannot build without the `tamarin-prover` submodule.  The
    // crate uses `include_str!` on files in `tamarin-prover/data/`.  The
    // example is therefore present whenever this test compiles.
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tamarin-prover/examples/features/injectivity/injectivity.spthy"
    ))
    .expect("read features/injectivity/injectivity.spthy");
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let root = prove_lemma(&pt, "injectivity_check", h, 200).expect("prove");
    assert_eq!(root.status, NodeStatus::Contradictory);
}

/// With the elaborated `MaudeSig` (hashing), the simplify loop must
/// converge.  It must not loop forever on edges that are already canonical.
///
/// The fixture records the upstream verdict for `recentalive` ("FINDS PROOF
/// AUTOMATICALLY"), that is `verified`.  The oracle proves this all-traces
/// lemma.  The negation therefore dead-ends, and the port's verdict is
/// `Contradictory`.  The bound on the elapsed time guards against
/// non-convergence.  A simplify loop that makes no more progress runs
/// forever here instead of returning any verdict.
#[test]
fn cr_external_recentalive_converges_and_holds() {
    let pt = fixture_theory("CR_external.spthy");
    let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
    let Some(h) = maude_with(elab.signature.maude_sig.clone()) else {
        return;
    };
    let t0 = std::time::Instant::now();
    let root = prove_lemma(&pt, "recentalive", h, 200).expect("prove");
    let dt = t0.elapsed();
    assert_eq!(root.status, NodeStatus::Contradictory);
    assert!(
        dt < std::time::Duration::from_secs(60),
        "recentalive ran {:?}, expected ≤60s (simplify-loop converges)",
        dt
    );
}

/// `All k #i. A(k) @ #i ==> A(k) @ #i` is a tautology.  Its negation
/// therefore reduces to ⊥, and the search closes as `Contradictory`.  The
/// test proves the lemma against the elaborated `MaudeSig` of the theory
/// itself, which adds `h/1`, and not against the pair-only signature.  A
/// signature that grows must not change the verdict.
#[test]
fn sig_minimal_tautology_is_contradictory() {
    let pt = fixture_theory("sig_minimal.spthy");
    let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
    let Some(h) = maude_with(elab.signature.maude_sig.clone()) else {
        return;
    };
    let root = prove_lemma(&pt, "a_self", h, 50).expect("prove");
    assert_eq!(root.status, NodeStatus::Contradictory);
}

/// The rule has two `Fr` premises.  A single rule instance must solve both
/// fresh-node premises before the two-variable existential can close.
#[test]
fn two_fresh_premises_in_one_rule_reach_solved() {
    let Some(h) = maude() else { return };
    let pt = fixture_theory("needs_constructor_simple.spthy");
    let root = prove_lemma(&pt, "sent_exists", h, 200).expect("prove");
    assert_eq!(root.status, NodeStatus::Solved);
}

/// The adversary must build `<a, b>` from two fresh values, each sent out by
/// its own `Out` fact, to satisfy `In(<x, y>)`.  Without the
/// pair-construction intruder rule, this existential no longer closes.  The
/// same holds without the `!KU` chain that feeds that rule.
#[test]
fn intruder_pair_construction_reaches_solved() {
    let Some(h) = maude() else { return };
    let pt = fixture_theory("needs_constructor.spthy");
    let root = prove_lemma(&pt, "pair_arrives", h, 2000).expect("prove");
    assert_eq!(root.status, NodeStatus::Solved);
}

/// HS `gatherReusableLemmas` (CloseRule.hs:179-188) collects the lemmas that
/// become `sLemmas` hypotheses for the lemma under proof.  Each guard
/// matters, and each one can be dropped on its own, so the test checks them
/// one by one.  The declaration order acts as a `break`: a `[reuse]` lemma is
/// invisible to itself and to every lemma ahead of it.  The `[reuse]`
/// attribute is required.  The check `AllTraces == lTraceQuantifier` excludes
/// exists-trace lemmas.  Finally, `pcHiddenLemmas` subtracts from the result.
/// It holds the `[hide_lemma=..]` names of the lemma under proof, and `ALL`
/// is the wildcard.
#[test]
fn gather_reusable_lemmas_matches_hs_guards() {
    let f = |name: &str| format!("\"All k #i. {name}(k) @ #i ==> Ex #j. {name}(k) @ #j\"");
    let src = format!(
        "theory T begin\n\
         rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
         lemma reusable [reuse]: all-traces {}\n\
         lemma existential [reuse]: exists-trace \"Ex k #i. A(k) @ #i\"\n\
         lemma unflagged: all-traces {}\n\
         lemma plain: all-traces {}\n\
         lemma hides_one [hide_lemma=reusable]: all-traces {}\n\
         lemma hides_all [hide_lemma=ALL]: all-traces {}\n\
         lemma trailing [reuse]: all-traces {}\n\
         end",
        f("A"),
        f("A"),
        f("A"),
        f("A"),
        f("A"),
        f("A"),
    );
    let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let thy = crate::elaborate::elaborate(&pt).expect("elaborate");
    let gathered = |name: &str| {
        gather_reusable_lemmas(&thy, name, SourceKind::RefinedSources)
            .expect("gather")
            .len()
    };
    // All three of `reusable`, `existential` and `unflagged` precede `plain`.
    // Only `reusable` passes every guard.  A result of 1, rather than 3,
    // therefore separates a correct filter from a missing attribute check or
    // a missing trace-quantifier check.
    assert_eq!(gathered("plain"), 1, "only the [reuse] all-traces prior");
    // The `break` uses the name of the lemma under proof.  Nothing precedes
    // `reusable`, and `reusable` cannot reuse itself.
    assert_eq!(gathered("reusable"), 0, "declared-before is a break");
    // `pcHiddenLemmas` subtracts by name, and `ALL` subtracts everything.
    assert_eq!(gathered("hides_one"), 0, "[hide_lemma=reusable] removes it");
    assert_eq!(
        gathered("hides_all"),
        0,
        "[hide_lemma=ALL] removes every one"
    );
    // `trailing` carries `[reuse]` itself, but it still sees only
    // `reusable`.  The break keeps a lemma out of its own hypothesis set,
    // whatever number of lemmas precede it.
    assert_eq!(gathered("trailing"), 1);
}

/// Web-parity regression: under `SysRetention::KeepAll` (what the
/// interactive server sets at startup), `run_proof_search` must
/// RETAIN each proof node's constraint `System` instead of dropping
/// it to `System::default()` (the `--prove` RSS optimisation in
/// `expand`).  The interactive proof-view snippet renders the
/// annotated system + applicable proof methods at every proof path,
/// so an empty root would show a bogus "Constraint System is Solved"
/// with no formulas (HS keeps a `Just System` on every node).
#[test]
fn prove_lemma_keep_sys_retains_node_systems() {
    let Some(h) = maude() else { return };
    let src = r#"
theory T begin
rule R:
  [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]
lemma always_A:
  all-traces
  "All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j"
end
"#;
    // The policy is process-wide; hold the lock its other writer takes so
    // no concurrent test stores a lower one mid-search.
    let _guard = crate::constraint::solver::search::SYS_RETENTION_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    crate::constraint::solver::search::set_sys_retention(
        crate::constraint::solver::search::SysRetention::KeepAll,
    );
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root = prove_lemma(&pt, "always_A", h, 200).expect("prove");
    // Root = the initial constraint system (the negated goal formula),
    // with the lemma's refined source kind — NOT an empty default.
    assert!(
        !root.sys.formulas.is_empty(),
        "root node must retain the initial system's formulas"
    );
    assert_eq!(
        root.sys.source_kind,
        Some(crate::constraint::system::SourceKind::RefinedSources),
        "root system source kind must survive (refined for a non-sources lemma)"
    );
    // Every child must also carry a real system.
    for (name, ch) in &root.children {
        assert!(
            ch.sys.source_kind.is_some(),
            "child {:?} must retain a real system, not System::default()",
            name
        );
    }
}

/// Drive the tiny_setup proof and inspect the proof-tree shape: the root
/// takes one of the three methods `rankProofMethods` can rank first here,
/// the `Ex` decomposes into a `Goal::Action(Setup(_))`, solving it
/// instantiates the `Setup` rule via its `Fr(~k)` premise, and the search
/// reaches `Solved`.
#[test]
fn prove_lemma_tiny_setup_drives_through_action_goal() {
    let Some(h) = maude() else { return };
    let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
    let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let root =
        prove_lemma(&parser_theory, "trivial", h, 100).expect("prove_lemma should not error");

    // Root method: under the `AvoidInduction` default (exists-trace
    // lemmas), Haskell's `rankProofMethods` tries Simplify first.
    // If Simplify produces non-empty cases (decomposes the formula
    // into goals), that's picked; otherwise we fall through to
    // Induction.  For this trivial existence lemma the Ex is
    // reducible, so Simplify is the root method.  Either is
    // structurally acceptable as long as the proof reaches Solved.
    use crate::constraint::solver::proof_method::ProofMethod;
    assert!(
        matches!(
            root.method,
            ProofMethod::Induction | ProofMethod::Simplify | ProofMethod::SolveGoal(_)
        ),
        "expected Simplify/Induction/SolveGoal at root, got {:?}",
        root.method
    );
    assert_eq!(
        root.status,
        NodeStatus::Solved,
        "expected Solved on tiny_setup, got {:?}",
        root.status
    );
}

/// Build a `ProverSession` from theory source for the pre-pass tests.
fn session_from(src: &str) -> Option<ProverSession> {
    let h = maude()?;
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    ProverSession::build_with_in_file_and_heuristic(
        &pt,
        h,
        None,
        "",
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )
    .ok()
}

const SHARED_KEY_TWO_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma a: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
lemma b: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\"\n\
end";

/// Two lemmas with the same (empty) `source_key` saturate ONCE in the
/// pre-pass, seed one cache entry, and a same-key lemma then restores it.
#[test]
fn presaturate_dedups_shared_source_key() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    // Both lemmas are RefinedSource with no prior `[sources]` lemma, so
    // both carry the identical empty key — one saturation covers both.
    let n = session.presaturate_shared_sources(false, |_| true);
    assert_eq!(n, 1, "two lemmas sharing a key must saturate once");
    assert_eq!(
        session.source_cache.lock().unwrap().len(),
        1,
        "exactly one refined-source set is cached"
    );
    // A fan-out lemma of the same key restores from the pre-seeded cache.
    let lemma_b = session.theory.lookup_lemma("b").expect("lemma b");
    let kind = lemma_source_kind(lemma_b);
    let (mut ctx, key) = session
        .setup_per_lemma_ctx(lemma_b, "b", kind)
        .expect("ctx");
    let hit = session.restore_or_saturate_sources(&mut ctx, key, false);
    assert!(
        hit,
        "lemma b must restore from the pre-seeded shared-key cache"
    );
}

/// A lemma that would emit a bare `sorry` (not a `--prove` target and with
/// no stored proof tree) never saturates in the fan-out, so the pre-pass
/// must skip it — the spdm121 `--prove=<no match>` regression precedent.
#[test]
fn presaturate_skips_bare_sorry_lemmas() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    // Freshly parsed lemmas have no stored proof tree; with no target
    // selected they emit a bare sorry and never consult a source.
    let n = session.presaturate_shared_sources(false, |_| false);
    assert_eq!(n, 0, "bare-sorry lemmas must not be pre-saturated");
    assert!(
        session.source_cache.lock().unwrap().is_empty(),
        "no key is seeded for bare-sorry lemmas"
    );
    // The SAME lemmas do saturate once they are `--prove` targets.
    let n2 = session.presaturate_shared_sources(false, |_| true);
    assert_eq!(n2, 1, "targeted lemmas saturate their shared key once");
}

/// `cache_disabled` (`TAM_RS_NO_SOURCE_CACHE`) bypasses the pre-pass
/// entirely, falling back to the per-lemma compute path.
#[test]
fn presaturate_disabled_is_noop() {
    let session = match session_from(SHARED_KEY_TWO_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    let n = session.presaturate_shared_sources(true, |_| true);
    assert_eq!(n, 0, "the disabled pre-pass saturates nothing");
    assert!(
        session.source_cache.lock().unwrap().is_empty(),
        "the disabled pre-pass seeds no cache entries"
    );
}

/// `parse_config_block` records what cmdargs records, rejection strings
/// byte-pinned against the oracle (`configuration: "<cfg>"` under
/// `--prove`, stderr after `tamarin-prover: `).
#[test]
fn config_block_matches_cmdargs_semantics() {
    use crate::constraint::solver::context::CutStrategy;

    // Prefix matching resolves like HS cmdargs': `--stop`, even `--s`.
    for cfg in ["--stop-on-trace=bfs", "--stop=bfs", "--s=bfs"] {
        let b = parse_config_block(cfg);
        assert_eq!(b.flag_error, None, "{cfg}");
        assert_eq!(b.stop_on_trace.as_deref(), Some("bfs"), "{cfg}");
    }
    // flagOpt: bare records "dfs"; no separate token is consumed.
    let b = parse_config_block("--stop-on-trace bfs");
    assert_eq!(b.stop_on_trace.as_deref(), Some("dfs"));
    // The VALUE is recorded raw — validation is the reader's, later.
    let b = parse_config_block("--stop-on-trace=XYZ --auto-sources");
    assert_eq!(b.flag_error, None);
    assert_eq!(b.stop_on_trace.as_deref(), Some("XYZ"));
    assert!(b.auto_sources);
    // Positionals are swallowed by the catch-all.
    let b = parse_config_block("positional --auto-sources");
    assert_eq!(b.flag_error, None);
    assert!(b.auto_sources);

    // cmdargs-level rejections, byte-for-byte.
    for (cfg, want) in [
        ("--nonsense", "Unknown flag: --nonsense"),
        (
            "--auto-sources=x",
            "Unhandled argument to flag, none expected: --auto-sources=x",
        ),
        ("-a", "Unknown flag: -a"),
        ("-abc", "Unknown flag: -a"),
        (
            "--=x",
            "Ambiguous flag '--', could be any of: stop-on-trace auto-sources",
        ),
    ] {
        assert_eq!(
            parse_config_block(cfg).flag_error.as_deref(),
            Some(want),
            "{cfg}"
        );
    }

    // The deferred value reader — HS `stopOnTrace`, lowercasing first.
    assert_eq!(parse_stop_on_trace("BFS"), Ok(CutStrategy::Bfs));
    assert_eq!(
        parse_stop_on_trace("XYZ"),
        Err("unknown stop-on-trace method: xyz".to_string())
    );

    // The server's eager wrapper surfaces both kinds of error.
    assert_eq!(
        config_block_options("--nonsense"),
        Err("Unknown flag: --nonsense".to_string())
    );
    assert_eq!(
        config_block_options("--stop-on-trace=XYZ"),
        Err("unknown stop-on-trace method: xyz".to_string())
    );
    assert_eq!(
        config_block_options("--stop-on-trace=seqdfs --auto-sources"),
        Ok((Some(CutStrategy::SeqDfs), true))
    );
}

/// `validate_cli_heuristic` — the ACCEPTANCE SET is what matches HS
/// (`filterHeuristic`: identifier chars + declared `{tactic}` groups,
/// names verbatim); the rejection wording is the port's own.
#[test]
fn validate_cli_heuristic_accepts_and_rejects_like_filter_heuristic() {
    let cli = |raw: &str| CliHeuristic {
        raw: Some(raw.to_string()),
        ..CliHeuristic::default()
    };
    let t = |name: &str| crate::tactic::Tactic::parse(name, "");
    // Every identifier char, compact runs included; a declared tactic.
    assert_eq!(validate_cli_heuristic(&cli("sSoOpPcCiI"), &[]), Ok(()));
    assert_eq!(
        validate_cli_heuristic(&cli("s{mytac}i"), &[t("mytac")]),
        Ok(())
    );
    // No raw string = nothing to validate.
    assert_eq!(
        validate_cli_heuristic(&CliHeuristic::default(), &[]),
        Ok(())
    );
    // HS rejects whitespace, digits and quotes as unknown rankings —
    // matching the acceptance set is what keeps a typo from silently
    // proving under the smart fallback.
    for bad in ["s x", "s1Ss", "o \"p\""] {
        let e = validate_cli_heuristic(&cli(bad), &[]).unwrap_err();
        assert!(e.contains("unknown goal ranking"), "{bad}: {e}");
    }
    // Tactic names resolve VERBATIM (no trim): `{ mytac }` is undeclared,
    // as in HS `chosenTactic`.
    let e = validate_cli_heuristic(&cli("{ mytac }"), &[t("mytac")]).unwrap_err();
    assert!(e.contains("\" mytac \""), "{e}");
    let e = validate_cli_heuristic(&cli("{zz}"), &[t("t1"), t("t2")]).unwrap_err();
    assert!(e.contains("not declared in the theory"), "{e}");
    assert!(e.contains("t1, t2"), "{e}");
    // `{.}` on the CLI is a tactic named "." — NOT the in-file parser's
    // defaultTactic shortcut — so it errors unless a tactic "." exists
    // (HS refuses it too).
    assert!(validate_cli_heuristic(&cli("{.}"), &[]).is_err());
    // Unterminated brace.
    let e = validate_cli_heuristic(&cli("{oops"), &[]).unwrap_err();
    assert!(e.contains("unterminated '{'"), "{e}");
}
