// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Out-of-line tests for [`super`].
//!
//! The verdict checks here cover the shapes that the fixture verdict suite
//! in `tests/oracle_solver.rs` does not carry.  That suite cross-checks its
//! own `(fixture, lemma) -> NodeStatus` table against the pinned Haskell
//! oracle's `verified`/`falsified` summary.  A shape that the suite already
//! lists therefore needs no second check that asserts less here.

use super::*;
use crate::constraint::solver::search::{NodeStatus, ProofStatus};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::maude_sig::{pair_maude_sig, MaudeSig};
use tamarin_test_support::require_maude_path;

/// Returns a maude handle on `sig`.  Returns `None` only when the run opts
/// out explicitly with `TAM_ALLOW_NO_MAUDE=1`.  Path resolution and the
/// policy that panics both live in [`tamarin_test_support::require_maude_path`].
///
/// A maude that resolves but does not start is the same misconfiguration as
/// a dangling `MAUDE_PATH`.  A `.ok()` here would hide that error, and every
/// check in this file would then skip without notice.  This function panics
/// instead.
fn maude_with(sig: MaudeSig) -> Option<MaudeHandle> {
    let path = require_maude_path()?;
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

/// Elaborates a parsed theory into the internal theory the prover entry
/// points take.
fn elaborated(pt: &tamarin_parser::ast::Theory) -> crate::theory::Theory {
    crate::elaborate::elaborate(pt).expect("elaborate")
}

/// Closes `theory` as the loader does before a prover session is built.
fn closed(
    theory: crate::theory::Theory,
    maude: &MaudeHandle,
) -> crate::closed_theory::ClosedTheory {
    crate::closed_theory::close_theory(theory, maude, None)
        .expect("close theory")
        .0
}

#[test]
fn prove_lemma_unknown_name_is_error() {
    let Some(h) = maude() else { return };
    let parser_theory = tamarin_parser::parse_theory("theory T begin end", &[]).expect("parse");
    let r = prove_lemma(
        std::sync::Arc::new(elaborated(&parser_theory)),
        "nonexistent",
        h,
        5,
    );
    assert!(matches!(r, Err(ProveError::LemmaNotFound(_))));
}

#[test]
fn public_proving_rejects_invalid_manual_variants() {
    let Some(h) = maude() else { return };
    let parsed = tamarin_parser::parse_theory(
        r#"theory InvalidVariant begin
        rule Emit: [In(x)] --[A(x)]-> []
        variants
        rule (modulo AC) Emit___VARIANT_1: [In('a')] --[A('a')]-> []
        lemma fixed: "All x #i. A(x) @ i ==> x = 'a'"
        end"#,
        &[],
    )
    .unwrap();
    // The public API can receive a compiled body that differs from its E
    // rule. Neither representation may make the incomplete family valid.
    for narrow_compiled in [false, true] {
        let mut theory = elaborated(&parsed);
        if narrow_compiled {
            for item in &mut theory.items {
                if let crate::theory::TheoryItem::Rule(rule) = item {
                    rule.rule_e = Some(Box::new(rule.rule.clone()));
                    rule.rule = rule.rule_ac[0].clone();
                    rule.rule.info.name = rule.rule_e().info.name;
                }
            }
        }
        let theory = std::sync::Arc::new(theory);
        let counter = h.fresh_counter_peek();
        let error = prove_lemma(theory.clone(), "fixed", h.clone(), 30).unwrap_err();
        assert!(matches!(error, ProveError::UnsupportedInput(ref s) if s.contains("Variants")));
        assert_eq!(h.fresh_counter_peek(), counter);
    }
}

#[test]
fn public_proving_accepts_valid_manual_variants_and_ordinary_warnings() {
    let Some(h) = maude() else { return };
    // Reuse on an exists-trace lemma is an ordinary warning, not a reason to
    // reject this complete family or turn the false all-traces lemma true.
    let parsed = tamarin_parser::parse_theory(
        r#"theory ValidVariant begin
        rule Emit: [In(x)] --[A(x)]-> []
        variants
        rule (modulo AC) Emit___VARIANT_1: [In(y)] --[A(y)]-> []
        lemma fixed: "All x #i. A(x) @ i ==> x = 'a'"
        lemma witness [reuse]: exists-trace "Ex x #i. A(x) @ i"
        end"#,
        &[],
    )
    .unwrap();
    let (theory, report) =
        crate::closed_theory::close_theory(elaborated(&parsed), &h, None).unwrap();
    assert!(!report.is_empty());
    assert!(crate::wellformedness::variants::fatal_wf_errors(&report).is_empty());
    let counter = h.fresh_counter_peek();
    let session = ProverSession::build(&theory, h.clone(), Default::default()).unwrap();
    assert_eq!(h.fresh_counter_peek(), counter);
    let proof = prove_lemma_in_session(&session, "fixed", 30).unwrap();
    assert_eq!(
        crate::constraint::solver::search::proof_status(&proof),
        ProofStatus::TraceFound
    );
}

#[test]
fn public_proving_rejects_unsupported_source_products() {
    for term in ["'a' * 'b'", "product('a','b')"] {
        let source = format!(
            r#"theory UnsupportedProduct begin
        builtins: diffie-hellman
        macros: product(x,y) = x*y
        rule Emit: [] --[A({term})]-> []
        lemma witness: exists-trace "Ex x #i. A(x) @ i"
        end"#
        );
        let parsed = tamarin_parser::parse_theory(&source, &[]).unwrap();
        let theory = elaborated(&parsed);
        let Some(h) = maude_with(theory.signature.clone()) else {
            return;
        };
        let error = prove_lemma(std::sync::Arc::new(theory), "witness", h, 5).unwrap_err();
        assert!(matches!(error, ProveError::UnsupportedInput(ref s)
        if s.contains("Unsupported multiplication outside exponents")));
    }
}

#[test]
fn public_proving_computes_reducible_manual_families_before_validating() {
    let parsed = tamarin_parser::parse_theory(
        r#"theory PublicManualVariant begin
        builtins: symmetric-encryption
        macros: decrypt(x,k) = sdec(x,k)
        rule Key: [Fr(~k)] --> [!Key(~k)]
        rule Dec: [In(x), !Key(k)] --[A(decrypt(x,k))]-> []
        variants
        rule (modulo AC) Dec___VARIANT_1:
          [In(x.2), !Key(k.1)] --[A(sdec(x.2,k.1))]-> [],
        rule (modulo AC) Dec___VARIANT_2:
          [In(senc(z.2,k.1)), !Key(k.1)] --[A(z.2)]-> []
        lemma witness: exists-trace "Ex m #i. A(m)@i"
        end"#,
        &[],
    )
    .unwrap();
    let theory = elaborated(&parsed);
    let Some(h) = maude_with(theory.signature.clone()) else {
        return;
    };
    let proof = prove_lemma(std::sync::Arc::new(theory), "witness", h, 10).unwrap();
    assert_eq!(
        crate::constraint::solver::search::proof_status(&proof),
        ProofStatus::TraceFound
    );
}

#[test]
fn guarded_conversion_errors_use_haskell_default_width() {
    let vars = (1..=25)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let src = format!(
        "theory T begin \
         lemma many: \"All {vars} #i. AA(x1) @ i ==> F\" \
         end"
    );
    let parsed = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let theory = elaborated(&parsed);
    let formula = &theory.lemmas().next().expect("lemma").formula;
    let error = formula_to_guarded(formula).expect_err("formula is unguarded");
    let doc = error.full_doc(formula);
    let expected = doc.clone().render_with(
        crate::pretty_hpj::DEFAULT_LINE_LENGTH,
        crate::pretty_hpj::DEFAULT_RIBBON,
    );
    assert_ne!(
        expected,
        doc.render(),
        "fixture must distinguish 100 from 110 columns"
    );
    assert_eq!(
        guarded_or_error(formula),
        Err(ProveError::Guarded(expected))
    );
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
    let root = prove_lemma(
        std::sync::Arc::new(elaborated(&pt)),
        "injectivity_check",
        h,
        200,
    )
    .expect("prove");
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
    let Some(h) = maude_with(elab.signature.clone()) else {
        return;
    };
    let t0 = std::time::Instant::now();
    let root = prove_lemma(std::sync::Arc::new(elab), "recentalive", h, 200).expect("prove");
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
    let Some(h) = maude_with(elab.signature.clone()) else {
        return;
    };
    let root = prove_lemma(std::sync::Arc::new(elab), "a_self", h, 50).expect("prove");
    assert_eq!(root.status, NodeStatus::Contradictory);
}

/// The rule has two `Fr` premises.  A single rule instance must solve both
/// fresh-node premises before the two-variable existential can close.
#[test]
fn two_fresh_premises_in_one_rule_reach_solved() {
    let Some(h) = maude() else { return };
    let pt = fixture_theory("needs_constructor_simple.spthy");
    let root =
        prove_lemma(std::sync::Arc::new(elaborated(&pt)), "sent_exists", h, 200).expect("prove");
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
    let root = prove_lemma(
        std::sync::Arc::new(elaborated(&pt)),
        "pair_arrives",
        h,
        2000,
    )
    .expect("prove");
    assert_eq!(root.status, NodeStatus::Solved);
}

/// HS `gatherReusableLemmas` (CloseRule.hs) collects the lemmas that
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
    let prepared: Vec<_> = thy
        .lemmas()
        .map(|lemma| PreparedLemma {
            guarded: guarded_or_error(&lemma.formula).map(std::sync::Arc::new),
            heuristic: None,
        })
        .collect();
    let gathered = |name: &str| {
        gather_reusable_lemmas(&thy, &prepared, thy.lookup_lemma(name).unwrap())
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
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    let session = ProverSession::build(
        &closed(elaborated(&pt), &h),
        h,
        ProverSessionOptions {
            sys_retention: crate::constraint::solver::search::SysRetention::KeepAll,
            ..Default::default()
        },
    )
    .expect("session");
    let root = prove_lemma_in_session(&session, "always_A", 200).expect("prove");
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

/// Build a `ProverSession` from theory source for the pre-pass tests.
fn session_from(src: &str) -> Option<ProverSession> {
    let h = maude()?;
    let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
    Some(
        ProverSession::build(
            &closed(elaborated(&pt), &h),
            h,
            ProverSessionOptions::default(),
        )
        .expect("build test session"),
    )
}

fn session_with_malformed_sources(goal: &str) -> Option<ProverSession> {
    session_from(&format!(
        "theory T begin\n\
         rule R: [] --[ A() ]-> []\n\
         lemma typing [sources]: \"All x #i. A() @ #i ==> x = x\"\n\
         {goal}\n\
         end"
    ))
}

fn assert_guarded_error<T>(result: Result<T, ProveError>) {
    assert!(matches!(result, Err(ProveError::Guarded(_))));
}

#[test]
fn session_context_factory_installs_lemma_state_without_mutating_template() {
    let Some(session) = session_from(
        "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ ]\n\
lemma inductive [use_induction]: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
end",
    ) else {
        return;
    };

    assert_eq!(
        session.template_context().use_induction,
        crate::constraint::solver::context::UseInduction::AvoidInduction
    );
    let ctx = session.context_for_lemma("inductive").expect("context");
    assert!(std::sync::Arc::ptr_eq(
        &session.template_context().shared,
        &ctx.shared
    ));
    assert_eq!(
        ctx.use_induction,
        crate::constraint::solver::context::UseInduction::UseInduction
    );
    assert_eq!(ctx.lemma_name, "inductive");
    assert_eq!(
        session.template_context().use_induction,
        crate::constraint::solver::context::UseInduction::AvoidInduction
    );
    assert!(matches!(
        session.context_for_lemma("missing"),
        Err(ProveError::LemmaNotFound(name)) if name == "missing"
    ));
}

#[test]
fn only_an_oracle_ranking_may_fail() {
    let Some(session) = session_from(
        "theory T begin\n\
         lemma safe: \"T\"\n\
         lemma external [heuristic=o \"oracle\"]: \"T\"\n\
         end",
    ) else {
        return;
    };

    let ranking_may_fail = |name| {
        let (_, prepared) = session.lemma_and_prepared(name).unwrap();
        prepared
            .heuristic
            .as_deref()
            .is_some_and(crate::constraint::solver::goals::rankings_may_fail)
    };
    assert!(!session.guarded_lemmas_may_fail());
    assert!(!ranking_may_fail("safe"));
    assert!(ranking_may_fail("external"));
}

#[test]
fn ordinary_dfs_in_a_mixed_batch_can_fork_under_a_deadline() {
    use crate::constraint::solver::cancellation_tests::{Work, WorkerGate};
    use crate::constraint::solver::search::ProofDeadlineGuard;
    let Some(mut session) = session_from(
        r#"theory T begin
        rule GenL: [ Fr(~x) ] --> [ L(~x) ]
        rule GenR: [ Fr(~x) ] --> [ R(~x) ]
        rule Left: [ L(x) ] --[ End(x) ]-> []
        rule Right: [ R(x) ] --[ End(x) ]-> []
        lemma builtin: "All x #i. End(x) @ i ==> F"
        lemma external [heuristic=o "unused-oracle"]: "T"
        end"#,
    ) else {
        return;
    };
    let ctx = Arc::get_mut(&mut session.template_ctx).unwrap();
    ctx.maude_pool = Some(Arc::new(
        tamarin_term::maude_proc::MaudePool::new(
            &require_maude_path().unwrap(),
            pair_maude_sig(),
            1,
            Default::default(),
        )
        .unwrap(),
    ));
    let (gate, entered) = WorkerGate::new(Work::Search, 2);
    *ctx.worker_gate.lock().unwrap() = Some(gate.clone());
    let workers = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    std::thread::scope(|scope| {
        let proof = scope.spawn(|| {
            workers.install(|| {
                let _deadline = ProofDeadlineGuard::set_ms(30_000);
                session.map_lemma_proofs(|_| Some(12), |_, _| ())
            })
        });
        let next = || entered.recv_timeout(std::time::Duration::from_secs(5));
        let first = next();
        let second = next();
        gate.release();
        proof.join().unwrap().unwrap();
        assert_ne!(first.unwrap(), second.unwrap());
    });
}

#[test]
fn ordinary_lemmas_use_the_session_process_when_only_cold_slots_remain() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let pool = std::sync::Arc::new(
        tamarin_term::maude_proc::MaudePool::new(&path, pair_maude_sig(), 4, Default::default())
            .unwrap(),
    );
    let theory = tamarin_parser::parse_theory(
        "theory T begin\nlemma a: \"T\" by sorry\nlemma b: \"T\"\nend",
        &[],
    )
    .unwrap();
    let maude = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
    let session = ProverSession::build(
        &closed(elaborated(&theory), &maude),
        maude,
        ProverSessionOptions {
            maude_pool: Some(pool.clone()),
            ..Default::default()
        },
    )
    .unwrap();
    let held = pool.try_take_idle_owned().unwrap();
    let names = session
        .map_lemma_proofs(
            |lemma| (lemma.name == "b").then_some(1),
            |lemma, _| lemma.name.clone(),
        )
        .unwrap();
    assert_eq!(names, ["a", "b"]);
    assert_eq!(
        pool.spawned(),
        1,
        "proof admission started a cold Maude process"
    );
    drop(held);
}

#[test]
fn batched_lemmas_keep_the_callers_deadline_on_workers() {
    use crate::constraint::solver::search::{proof_status, ProofDeadlineGuard, ProofStatus};
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(session) = session_from(
        r#"theory T begin
        rule Send: [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]
        lemma a: exists-trace "Ex k #i. S(k) @ i"
        lemma b: exists-trace "Ex k #i. S(k) @ i"
        end"#,
    ) else {
        return;
    };
    for cancellable in [false, true] {
        let _request = CancellationGuard::new(cancellable.then(CancellationToken::default));
        for expected in [ProofStatus::Incomplete, ProofStatus::TraceFound] {
            let _deadline = if expected == ProofStatus::Incomplete {
                ProofDeadlineGuard::set_ms(0)
            } else {
                ProofDeadlineGuard::unbounded()
            };
            let results = session
                .map_lemma_proofs(|_| Some(10), |_, p| proof_status(&p))
                .unwrap();
            assert_eq!(results, [expected; 2]);
        }
    }
}

#[test]
fn malformed_batch_reports_the_first_error_in_declaration_order() {
    let Some(session) = session_from(
        r#"theory T begin
           rule R: [] --[ A() ]-> []
           lemma selected [heuristic=o "missing-test-oracle"]: exists-trace "Ex #i. A() @ i"
           lemma invalid: "All x #i. A() @ i ==> x = x"
           end"#,
    ) else {
        return;
    };
    let proof = session.map_lemma_proofs(
        |lemma| (lemma.name == "selected").then_some(usize::MAX),
        |_, _| (),
    );
    assert!(
        matches!(&proof, Err(ProveError::Ranking(err)) if err.0.contains("missing-test-oracle")),
        "{proof:?}"
    );
    // With replay alone, the first lemma succeeds and the second reports
    // its guard error even though it was never selected for auto-proving.
    assert_guarded_error(session.map_lemma_proofs(|_| None, |_, _| ()));
}

const RAW_AND_REFINED_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma typing [sources]: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
lemma goal: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
end";

fn source_cache_disabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE")
}

#[test]
fn source_cache_is_lazy() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    assert!(session.source_cache.is_empty());

    let (lemma, prepared) = session.lemma_and_prepared("goal").expect("goal lemma");
    let ctx = session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude);
    let second_ctx = session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude);
    assert!(std::sync::Arc::ptr_eq(
        &ctx.full_sources,
        &second_ctx.full_sources
    ));
    assert!(session.source_cache.is_empty());
}

#[test]
fn batch_source_phase_follows_worker_count_and_lemma_selection() {
    let Some(session) = session_from(
        r#"theory T begin
           lemma a [sources]: "T"
           lemma b [sources]: "T"
           lemma c: "T"
           end"#,
    ) else {
        return;
    };
    // These proofs need no source cases. Any populated slot must come from
    // the batch phase, and every renderer must see it already populated.
    for (workers, selected, slots) in [(1, "abc", 0), (2, "c", 0), (2, "ab", 1), (2, "abc", 2)] {
        let cache = session.source_cache.clone();
        let expected = if source_cache_disabled() { 0 } else { slots };
        rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap()
            .install(|| {
                session.map_lemma_proofs(
                    |lemma| selected.contains(lemma.name.as_str()).then_some(1),
                    move |_, _| assert_eq!(cache.len(), expected),
                )
            })
            .unwrap();
    }
}

#[test]
fn a_malformed_source_lemma_is_reported_in_declaration_order() {
    let Some(mut session) = session_from(
        r#"theory T begin
           rule R: [] --[ A() ]-> []
           lemma a: "T"
           lemma b: "T"
           lemma invalid [sources]: "All x #i. A() @ #i ==> x = x"
           end"#,
    ) else {
        return;
    };
    let workers = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .unwrap();
    for bypass in [false, true] {
        session.source_cache_disabled = bypass;
        let rendered = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let count = rendered.clone();
        let result = workers.install(|| {
            session.map_lemma_proofs(
                |lemma| (lemma.name != "invalid").then_some(1),
                move |_, _| {
                    count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                },
            )
        });
        assert_guarded_error(result);
        // Both trivial proofs finish before replay reaches the invalid lemma.
        assert_eq!(rendered.load(std::sync::atomic::Ordering::Relaxed), 2);
    }
}

#[test]
fn standalone_workers_can_choose_assumptions_before_forcing_sources() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    let raw = session.template_context();
    let mut refined = raw.with_swapped_maude(raw.maude.clone());
    refined.typing_assumptions = session
        .source_assumptions
        .as_ref()
        .as_ref()
        .unwrap()
        .clone();
    // HS `refineWithSourceAsms` marks the cases refined even when there
    // are no assumptions.
    for ctx in [&refined, raw] {
        let expected = SourceKind::RefinedSources;
        let cases = ctx.source_cases().unwrap();
        let kinds: Vec<_> = cases
            .iter()
            .flat_map(|(_, cases)| cases.iter().map(|(_, sys)| sys.source_kind))
            .collect();
        assert!(!kinds.is_empty());
        assert!(kinds.iter().all(|kind| *kind == Some(expected)));
        let worker = ctx.with_swapped_maude(ctx.maude.clone());
        assert!(Arc::ptr_eq(
            &ctx.ensure_saturated().unwrap(),
            &worker.ensure_saturated().unwrap()
        ));
    }
}

#[test]
fn source_materialization_preserves_maude_failures() {
    let source = "theory T begin\n\
        builtins: multiset\n\
        rule R: [In(<x,y,z,w>)] --[A(x,y,z,w)]-> [F(x)]\n\
        restriction Eq: \"All x y z w #i. A(x,y,z,w) @i ==> x ++ y = z ++ w\"\n\
        lemma goal: \"Ex x y z w #i. A(x,y,z,w) @i\"\n\
        end";
    let theory = elaborated(&tamarin_parser::parse_theory(source, &[]).unwrap());
    let build = || {
        let maude = maude_with(theory.signature.clone())?;
        let closed = closed(theory.clone(), &maude);
        Some(ProverSession::build(&closed, maude, ProverSessionOptions::default()).unwrap())
    };
    let Some(healthy) = build() else {
        return;
    };
    assert!(healthy.context_for_sources(SourceKind::RawSources).is_ok());
    let mut session = build().unwrap();
    // Preparation also queries Maude. Replace its warmed handle so source
    // materialization must consult the failed backend rather than that cache.
    let failed = maude_with(theory.signature.clone()).unwrap();
    failed.kill_subprocess();
    std::sync::Arc::get_mut(&mut session.template_ctx)
        .unwrap()
        .maude = failed;
    for kind in [SourceKind::RawSources, SourceKind::RefinedSources] {
        for _ in 0..2 {
            assert!(matches!(
                session.context_for_sources(kind),
                Err(ProveError::Maude(_))
            ));
        }
    }
    let stats = session.source_stats();
    assert!(matches!(stats.raw, Err(ProveError::Maude(_))));
    assert!(matches!(stats.refined, Err(ProveError::Maude(_))));
    // A lemma assigned a different process must be able to force sources even
    // with the template's process offline and the same empty cache.
    assert!(session.source_cache.is_empty());
    let assigned = maude_with(theory.signature.clone()).unwrap();
    let (ctx, _) = lemma_context_and_system(
        &session,
        session.lemma_and_prepared("goal").unwrap(),
        &assigned,
    )
    .unwrap();
    ctx.ensure_saturated()
        .expect("assigned lemma process must also serve lazy source queries");
}

#[test]
fn terminal_system_does_not_force_sources() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    let mut terminal = crate::constraint::system::System::default();
    terminal
        .formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gfalse()));

    prove_system_in_session_with_options(
        &session,
        "goal",
        terminal,
        SearchOptions {
            proof_bound: usize::MAX,
            ranking_depth_offset: 0,
            cut: session.cut,
            oracle_only: false,
        },
    )
    .expect("terminal system bypasses sources");
    assert!(session.source_cache.is_empty());
}

#[test]
fn interactive_source_views_use_the_session_provider() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };

    session
        .context_for_sources(SourceKind::RawSources)
        .expect("raw source view");
    if !source_cache_disabled() {
        assert!(session.source_cache.raw.ready.get().is_some());
        assert!(session.source_cache.refined.ready.get().is_none());
    }

    session
        .context_for_sources(SourceKind::RefinedSources)
        .expect("refined source view");
    assert!(session.source_stats().refined.is_ok());
    assert_eq!(
        session.source_cache.len(),
        if source_cache_disabled() { 0 } else { 2 }
    );
}

#[test]
fn interactive_refined_source_errors_cross_the_provider_boundary() {
    let Some(session) = session_with_malformed_sources("lemma goal: \"Ex #i. A() @ #i\"") else {
        return;
    };

    assert_guarded_error(session.context_for_sources(SourceKind::RefinedSources));
}

#[test]
fn lazy_source_consumers_report_deferred_source_errors() {
    let Some(session) = session_with_malformed_sources("lemma goal: \"Ex #i. A() @ #i\"") else {
        return;
    };
    let (lemma, prepared) = session.lemma_and_prepared("goal").expect("goal lemma");
    let mut ctx = session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude);
    ctx.heuristic = Some(
        crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            "{missing}",
            "test.spthy",
            &[],
        ),
    );
    assert_guarded_error(ctx.ensure_saturated());
    assert_guarded_error(ctx.source_cases());
}

#[test]
fn simplify_only_proof_does_not_force_malformed_source_assumption() {
    let Some(session) =
        session_with_malformed_sources("lemma done: \"All #i. A() @ #i ==> A() @ #i\"")
    else {
        return;
    };
    let typing = session.theory.lookup_lemma("typing").expect("typing lemma");
    assert!(guarded_or_error(&typing.formula).is_err());

    let proof = prove_lemma_in_session(&session, "done", usize::MAX)
        .expect("simplification must not force unrelated sources");
    assert_eq!(proof.status, NodeStatus::Contradictory);
    assert!(session.source_cache.is_empty());
}

#[test]
fn refined_slot_derives_from_the_single_raw_slot() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    let (lemma, prepared) = session.lemma_and_prepared("goal").expect("goal lemma");
    let ctx = session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude);
    ctx.ensure_saturated().expect("valid source assumptions");

    if source_cache_disabled() {
        assert!(session.source_cache.is_empty());
        return;
    }
    assert!(session.source_cache.raw.ready.get().is_some());
    assert!(session.source_cache.refined.ready.get().is_some());
    assert_eq!(session.source_cache.len(), 2);

    let resolved = ctx.ensure_saturated().unwrap();
    assert!(Arc::ptr_eq(
        session.source_cache.refined.ready.get().unwrap(),
        &resolved
    ));
    assert!(Arc::ptr_eq(
        &ctx.clone().ensure_saturated().unwrap(),
        &resolved
    ));
}

#[test]
fn empty_refinement_still_labels_source_systems_refined() {
    let Some(session) = session_from(
        "theory T begin\n\
         rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
         lemma goal: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
         end",
    ) else {
        return;
    };
    let refined = session
        .context_for_sources(SourceKind::RefinedSources)
        .expect("refined sources");
    let mut systems = 0;
    for source in refined.ensure_saturated().unwrap().iter() {
        for (_, system) in source.cases().unwrap().iter() {
            systems += 1;
            assert_eq!(system.source_kind, Some(SourceKind::RefinedSources));
        }
    }
    assert!(systems > 0, "fixture must produce source cases");
}

#[test]
fn concurrent_raw_and_refined_consumers_share_each_materialisation() {
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    let barrier = std::sync::Barrier::new(4);
    let shared = std::thread::scope(|scope| {
        let workers: Vec<_> = [
            SourceKind::RawSources,
            SourceKind::RefinedSources,
            SourceKind::RawSources,
            SourceKind::RefinedSources,
        ]
        .into_iter()
        .map(|kind| {
            let session = &session;
            let barrier = &barrier;
            scope.spawn(move || {
                barrier.wait();
                let ctx = session.context_for_sources(kind).expect("source context");
                (kind, ctx.ensure_saturated().unwrap())
            })
        })
        .collect();
        workers
            .into_iter()
            .map(|worker| worker.join().expect("source worker"))
            .collect::<Vec<_>>()
    });

    for kind in [SourceKind::RawSources, SourceKind::RefinedSources] {
        let mut matching = shared
            .iter()
            .filter(|(candidate, _)| *candidate == kind)
            .map(|(_, cases)| cases);
        let first = matching.next().expect("first consumer");
        assert_eq!(
            matching.all(|cases| std::sync::Arc::ptr_eq(first, cases)),
            !source_cache_disabled()
        );
    }
    assert_eq!(
        session.source_cache.len(),
        if source_cache_disabled() { 0 } else { 2 }
    );
}

const STORED_TERMINAL_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma open: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by sorry\n\
lemma terminal: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by contradiction\n\
end";

#[test]
fn parallel_replay_of_terminal_roots_leaves_sources_lazy() {
    use rayon::prelude::*;

    let Some(session) = session_from(STORED_TERMINAL_LEMMAS) else {
        return;
    };
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .expect("lemma pool");
    pool.install(|| {
        ["open", "terminal"].par_iter().try_for_each(|name| {
            check_and_extend_lemma_in_session(&session, name, usize::MAX).map(drop)
        })
    })
    .expect("parallel replay");

    for selected in [None, Some("terminal")] {
        pool.install(|| {
            session.map_lemma_proofs(
                |lemma| (Some(lemma.name.as_str()) == selected).then_some(1),
                |_, _| (),
            )
        })
        .unwrap();
    }
    assert!(session.source_cache.is_empty());
}

#[test]
fn replacing_stored_sorry_reports_unresolved_ranking() {
    let Some(session) = session_from(
        "theory T begin\n\
heuristic: {missing}\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma open: exists-trace \"Ex k #i. A(k) @ #i\" by sorry\n\
end",
    ) else {
        return;
    };

    let error = prove_lemma_in_session(&session, "open", usize::MAX)
        .expect_err("auto-proving the stored sorry must resolve its ranking");
    assert!(
        matches!(
            &error,
        ProveError::Ranking(
            crate::constraint::solver::goals::RankingError(message)
        ) if message == "No tactic has been written in the theory file"
        ),
        "unexpected error: {error:?}"
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
    let t = |name: &str| crate::tactic::Tactic {
        name: name.to_string(),
        presort: 's',
        prios: Vec::new(),
        deprios: Vec::new(),
    };
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
    assert!(validate_cli_heuristic(&cli(""), &[])
        .unwrap_err()
        .contains("at least one ranking"));
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

#[test]
fn prover_session_rejects_an_unvalidated_cli_heuristic() {
    let Some(h) = maude() else { return };
    let parsed = tamarin_parser::parse_theory("theory T begin end", &[]).expect("parse");
    let theory = closed(elaborated(&parsed), &h);
    let result = ProverSession::build(
        &theory,
        h.clone(),
        ProverSessionOptions {
            cli_heuristic: CliHeuristic {
                raw: Some("unknown".to_string()),
                ..CliHeuristic::default()
            },
            ..Default::default()
        },
    );
    assert!(matches!(result, Err(ProveError::InvalidHeuristic(_))));
}

#[test]
fn default_cli_oracles_are_resolved_beside_the_theory() {
    use crate::constraint::solver::goals::GoalRanking;

    let root = std::env::temp_dir().join(format!(
        "tamarin_rs_cli_default_oracle_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    let theory = root.join("protocol.spthy");
    std::fs::write(&theory, "theory T begin end").unwrap();
    std::fs::write(root.join("protocol.oracle"), "#!/bin/sh\n").unwrap();
    let default_oracle = root.join("protocol.oracle").to_string_lossy().into_owned();

    let cli = CliHeuristic {
        raw: Some("o".to_string()),
        ..CliHeuristic::default()
    };
    let rankings = resolve_cli_heuristic(&cli, theory.to_str().unwrap(), &[]).unwrap();
    assert!(matches!(
        &rankings[0],
        GoalRanking::Oracle { oracle_path, .. }
            if oracle_path == &default_oracle
    ));

    let explicit = CliHeuristic {
        raw: Some("o".to_string()),
        oracle_name: Some("chosen.oracle".to_string()),
        ..CliHeuristic::default()
    };
    let rankings = resolve_cli_heuristic(&explicit, theory.to_str().unwrap(), &[]).unwrap();
    assert!(matches!(
        &rankings[0],
        GoalRanking::Oracle { oracle_path, .. } if oracle_path == "./chosen.oracle"
    ));

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn all_in_file_oracles_are_resolved_beside_the_theory() {
    use crate::constraint::solver::goals::GoalRanking;

    let mut rankings = vec![
        GoalRanking::Oracle {
            quit_on_empty: false,
            oracle_path: "oracle".to_string(),
        },
        GoalRanking::Oracle {
            quit_on_empty: false,
            oracle_path: "oracle".to_string(),
        },
    ];
    resolve_oracle_rankings(&mut rankings, "dir/theory.spthy", None);

    assert!(matches!(
        &rankings[0],
        GoalRanking::Oracle { oracle_path, .. } if oracle_path == "dir/oracle"
    ));
    assert!(matches!(
        &rankings[1],
        GoalRanking::Oracle { oracle_path, .. } if oracle_path == "dir/oracle"
    ));
    assert_eq!(
        resolve_oracle_path("/tmp/./nested//rank", Some("ignored")),
        "/tmp/nested/rank"
    );
}

#[test]
fn included_oracle_locations_are_preserved_and_frozen() {
    use crate::constraint::solver::goals::GoalRanking;

    let root =
        std::env::temp_dir().join(format!("tamarin_rs_included_oracle_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("sub")).unwrap();
    let theory_file = root.join("root.spthy");
    let include_file = root.join("sub/inc.spthy");
    std::fs::write(
        &theory_file,
        "theory T begin\n#include \"sub/inc.spthy\"\nend\n",
    )
    .unwrap();
    std::fs::write(
        &include_file,
        "heuristic: o\n\
         lemma header: \"T\"\n\
         lemma local [heuristic=o \"rank\"]: \"T\"\n\
         lemma local_default [heuristic=o, heuristic=o]: \"T\"\n",
    )
    .unwrap();
    std::fs::write(root.join("sub/inc.oracle"), "").unwrap();
    std::fs::write(root.join("sub/rank"), "").unwrap();

    let source = std::fs::read_to_string(&theory_file).unwrap();
    let parsed = tamarin_parser::parse_theory_with_base(&source, &[], Some(root.clone())).unwrap();
    let theory =
        crate::elaborate::elaborate_with_in_file(&parsed, theory_file.to_str().unwrap()).unwrap();
    assert!(matches!(
        &theory.heuristic[0],
        GoalRanking::Oracle { oracle_path, .. } if oracle_path == "inc.oracle"
    ));
    let local_default = theory.lookup_lemma("local_default").unwrap();
    assert_eq!(
        local_default
            .attributes
            .iter()
            .filter_map(|attribute| match attribute {
                crate::theory::LemmaAttr::Heuristic(raw) => Some(raw.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>(),
        ["o \"inc.oracle\"", "o \"inc.oracle\""]
    );

    // Changing the filesystem after elaboration must not switch either the
    // header or lemma-local default to the fallback `oracle` executable.
    std::fs::remove_file(root.join("sub/inc.oracle")).unwrap();
    std::fs::write(root.join("sub/oracle"), "").unwrap();
    let Some(maude) = maude_with(theory.signature.clone()) else {
        std::fs::remove_dir_all(root).unwrap();
        return;
    };
    let session = ProverSession::build(
        &closed(theory, &maude),
        maude,
        ProverSessionOptions::default(),
    )
    .unwrap();
    let oracle_path = |lemma: &str| {
        let ctx = session.context_for_lemma(lemma).unwrap();
        match &ctx.heuristic.as_ref().unwrap()[0] {
            GoalRanking::Oracle { oracle_path, .. } => oracle_path.clone(),
            other => panic!("expected oracle ranking, got {other:?}"),
        }
    };
    assert_eq!(
        oracle_path("header"),
        root.join("sub/inc.oracle").to_string_lossy()
    );
    assert_eq!(
        oracle_path("local"),
        root.join("sub/rank").to_string_lossy()
    );
    assert_eq!(
        oracle_path("local_default"),
        root.join("sub/inc.oracle").to_string_lossy()
    );

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn scratch_proof_checks_return_backend_errors() {
    use crate::constraint::solver::sources::IntegerParameters;
    let theory = elaborated(
        // A premise `fst` makes the rule's and its probe's variants query
        // Maude.
        &tamarin_parser::parse_theory(
            "theory T begin rule R: [In(x), In(fst(x))] --> [F(x)] end",
            &[],
        )
        .unwrap(),
    );
    for failed in [false, true] {
        for derivation in [false, true] {
            let Some(h) = maude_with(theory.signature.clone()) else {
                return;
            };
            if failed {
                h.kill_subprocess();
            }
            let result = if derivation {
                crate::deriv_check::check_message_derivation(
                    &theory,
                    &h,
                    None,
                    crate::deriv_check::DerivCheckTimeout::Secs(
                        std::num::NonZeroU32::new(1).expect("nonzero"),
                    ),
                    None,
                    IntegerParameters::default(),
                )
                .map(|warnings| assert!(warnings.is_empty()))
            } else {
                crate::auto_sources::apply_auto_sources(
                    &mut theory.clone(),
                    h,
                    None,
                    None,
                    IntegerParameters::default(),
                )
                .map(|changed| assert!(!changed))
            };
            if failed {
                assert!(matches!(result, Err(ProveError::Maude(_))));
            } else {
                result.unwrap();
            }
        }
    }
}

#[test]
fn cold_sources_get_both_workers_when_dfs_siblings_need_them() {
    use crate::constraint::solver::cancellation_tests::{Work, WorkerGate};
    use std::time::Duration;

    let Some(session) = session_from(
        r#"theory T begin
        rule Left: [] --> [ F('left') ]
        rule Right: [] --> [ F('right') ]
        rule UseA: [ F(x) ] --[ Seen(x), A(x) ]-> []
        rule UseB: [ F(x) ] --[ Seen(x), B(x) ]-> []
        lemma goal: "not (Ex x #i. Seen(x) @ i)"
        end"#,
    ) else {
        return;
    };
    let (gate, entered) = WorkerGate::new(Work::Sources, 2);
    *session.template_ctx.worker_gate.lock().unwrap() = Some(gate.clone());
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .unwrap();
    std::thread::scope(|scope| {
        let proof = scope.spawn(|| pool.install(|| prove_lemma_in_session(&session, "goal", 24)));
        let first = entered.recv_timeout(Duration::from_secs(5));
        let second = entered.recv_timeout(Duration::from_secs(5));
        gate.release();
        assert_eq!(proof.join().unwrap().unwrap().status, NodeStatus::Solved);
        assert_ne!(first.unwrap(), second.unwrap());
    });
}

#[test]
fn cancel_active_parallel_sources_then_retry_the_same_context() {
    use crate::constraint::solver::cancellation_tests::{Work, WorkerGate};
    use std::time::Duration;
    use tamarin_utils::cancellation::{CancellationGuard, CancellationToken};
    let Some(session) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .unwrap();
    let (gate, entered) = WorkerGate::new(Work::Sources, 2);
    *session.template_ctx.worker_gate.lock().unwrap() = Some(gate.clone());
    let token = CancellationToken::default();
    let ctx = session.context_for_lemma("goal").unwrap();
    let next = ctx.maude.fresh_counter_peek() + 43;
    std::thread::scope(|scope| {
        let worker_token = token.clone();
        let worker = scope.spawn(|| {
            pool.install(|| {
                let _guard = CancellationGuard::new(Some(worker_token));
                ctx.ensure_saturated()
            })
        });
        let first = entered.recv_timeout(Duration::from_secs(5)).unwrap();
        assert_ne!(first, std::thread::current().id());
        let second = entered.recv_timeout(Duration::from_secs(5)).unwrap();
        assert_ne!(first, second, "source fan-out must reach distinct workers");
        // A second request can snapshot the same in-progress view. Its own
        // cancellation must return while the original builder is still parked.
        let waiter_token = CancellationToken::default();
        let (started, waiting) = std::sync::mpsc::channel();
        let (done, result) = std::sync::mpsc::channel();
        let wait_token = waiter_token.clone();
        let ctx_ref = &ctx;
        scope.spawn(move || {
            let _guard = CancellationGuard::new(Some(wait_token));
            let worker = ctx_ref.with_swapped_maude(ctx_ref.maude.clone());
            started.send(()).unwrap();
            done.send(worker.source_cases()).unwrap();
        });
        waiting.recv_timeout(Duration::from_secs(2)).unwrap();
        assert!(result.recv_timeout(Duration::from_millis(30)).is_err());
        ctx.maude.reset_counter_to(next);
        waiter_token.cancel();
        assert!(matches!(
            result.recv_timeout(Duration::from_secs(3)),
            Ok(Err(ProveError::Cancelled))
        ));
        token.cancel();
        gate.release();
        assert!(matches!(worker.join().unwrap(), Err(ProveError::Cancelled)));
    });
    *session.template_ctx.worker_gate.lock().unwrap() = None;
    assert!(
        session.source_cache.raw.ready.get().is_none(),
        "no partial sources may be published"
    );
    assert!(pool
        .broadcast(|_| tamarin_utils::cancellation::current().is_none())
        .into_iter()
        .all(|clear| clear));
    assert_eq!(ctx.maude.fresh_counter_peek(), next);
    let cases = ctx.source_cases().unwrap();
    assert_eq!(ctx.maude.fresh_counter_peek(), next);
    assert!(!cases.is_empty());
    {
        let _guard = CancellationGuard::new(Some(token));
        assert!(matches!(ctx.source_cases(), Err(ProveError::Cancelled)));
    }
    let retry = prove_lemma_in_session(&session, "goal", 12).unwrap();
    let Some(clean) = session_from(RAW_AND_REFINED_LEMMAS) else {
        return;
    };
    clean
        .context_for_lemma("goal")
        .unwrap()
        .ensure_saturated()
        .unwrap();
    let baseline = prove_lemma_in_session(&clean, "goal", 12).unwrap();
    assert_eq!(format!("{retry:?}"), format!("{baseline:?}"));
    assert_eq!(session.source_stats().raw, clean.source_stats().raw);
    assert_eq!(session.source_stats().refined, clean.source_stats().refined);
}

#[test]
fn a_cancelled_maude_call_stays_a_cancellation() {
    use tamarin_term::maude_proc::MaudeError;
    assert!(matches!(
        ProveError::maude("last-node unification", MaudeError::Cancelled),
        ProveError::Cancelled
    ));
    match ProveError::maude(
        "source matching failed",
        MaudeError::Spawn("no maude".into()),
    ) {
        ProveError::Maude(message) => assert!(message.starts_with("source matching failed: ")),
        other => panic!("expected a Maude error, got {other:?}"),
    }
}
