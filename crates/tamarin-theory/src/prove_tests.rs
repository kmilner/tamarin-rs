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
    let root =
        prove_lemma(std::sync::Arc::new(elaborated(&pt)), "always_A", h, 200).expect("prove");
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
    let root = prove_lemma(
        std::sync::Arc::new(elaborated(&parser_theory)),
        "trivial",
        h,
        100,
    )
    .expect("prove_lemma should not error");

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
    ProverSession::build_with_heuristic(
        std::sync::Arc::new(elaborated(&pt)),
        h,
        None,
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )
    .ok()
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
    assert!(!session.guarded_lemmas_may_fail());
    assert!(!session.lemma_ranking_may_fail("inductive"));
    let ctx = session.context_for_lemma("inductive").expect("context");
    assert!(!ctx.proving_may_fail());
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
fn ranking_fallibility_stays_local_to_its_lemma() {
    let Some(session) = session_from(
        "theory T begin\n\
         lemma safe: \"T\"\n\
         lemma external [heuristic=o \"oracle\"]: \"T\"\n\
         end",
    ) else {
        return;
    };

    assert!(!session.guarded_lemmas_may_fail());
    assert!(!session.lemma_ranking_may_fail("safe"));
    assert!(session.lemma_ranking_may_fail("external"));
    assert!(!session
        .context_for_lemma("safe")
        .expect("safe context")
        .proving_may_fail());
    assert!(session
        .context_for_lemma("external")
        .expect("oracle context")
        .proving_may_fail());
}

/// HS `closeProtoRule` (lib/theory/src/Rule.hs:82-86, see line 84) builds
/// `ClosedProtoRule ruE <$> maybeToList (variantsProtoRule hnd ruE)`, so a
/// rule with no variants yields NO closed rule: it is in neither the closed
/// theory nor the proof search.  The canonical case is a rule carrying both
/// `Fr(~x)` and `In(~x)`, where `~x` cannot be sent before it is generated.
/// `run.rs` drops such a rule from the internal theory before the session is
/// built, and the session's rules are that theory's, so the drop reaches the
/// proof context.
#[test]
fn a_no_variant_rule_is_absent_from_the_session() {
    let Some(h) = maude() else { return };
    let pt = tamarin_parser::parse_theory(
        "theory T begin\n\
rule Contradictory: [ Fr(~x), In(~x) ] --[ C(~x) ]-> [ Out(~x) ]\n\
rule Setup: [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]\n\
lemma trivial: exists-trace \"Ex k #i. Setup(k) @ #i\"\n\
end",
        &[],
    )
    .expect("parse");
    let mut theory = elaborated(&pt);
    let no_variant: Vec<String> = theory
        .rules()
        .filter(|r| {
            crate::tools::rule_variants::rule_has_no_variants_for_wf_with(&h, &r.rule, None)
        })
        .map(|r| r.name().to_string())
        .collect();
    assert_eq!(no_variant, vec!["Contradictory".to_string()]);
    theory.items.retain(|i| match i {
        crate::theory::TheoryItem::Rule(r) => !no_variant.iter().any(|n| n == r.name()),
        _ => true,
    });

    let session = ProverSession::build_with_heuristic(
        std::sync::Arc::new(theory),
        h,
        None,
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    )
    .expect("session");
    let names: Vec<&str> = session.theory.rules().map(|r| r.name()).collect();
    assert_eq!(names, vec!["Setup"]);
    assert!(
        !session
            .template_ctx
            .rules
            .iter()
            .any(|r| r.name() == "Contradictory"),
        "the dropped rule must not reach the template proof context"
    );
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
    let session = match session_from(RAW_AND_REFINED_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    assert!(session.source_cache.is_empty());

    let lemma = session.theory.lookup_lemma("goal").expect("goal lemma");
    let ctx = session.setup_per_lemma_ctx(lemma, "goal");
    let second_ctx = session.setup_per_lemma_ctx(lemma, "goal");
    assert!(!std::sync::Arc::ptr_eq(
        &ctx.full_sources,
        &second_ctx.full_sources
    ));
    assert!(session.source_cache.is_empty());
}

#[test]
fn terminal_system_does_not_force_sources() {
    let session = match session_from(RAW_AND_REFINED_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    let mut terminal = crate::constraint::system::System::default();
    terminal
        .formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gfalse()));

    prove_system_in_session(&session, "goal", terminal, usize::MAX)
        .expect("terminal system bypasses sources");
    assert!(session.source_cache.is_empty());
}

#[test]
fn interactive_source_views_use_the_session_provider() {
    let session = match session_from(RAW_AND_REFINED_LEMMAS) {
        Some(s) => s,
        None => return,
    };

    session
        .context_for_sources(SourceKind::RawSources)
        .expect("raw source view");
    if !source_cache_disabled() {
        assert!(session.source_cache.raw.get().is_some());
        assert!(session.source_cache.refined.get().is_none());
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
    let session = match session_from(
        "theory T begin\n\
         rule R: [] --[ A() ]-> []\n\
         lemma typing [sources]: \"All x #i. A() @ #i ==> x = x\"\n\
         lemma goal: \"Ex #i. A() @ #i\"\n\
         end",
    ) {
        Some(s) => s,
        None => return,
    };

    assert!(matches!(
        session.context_for_sources(SourceKind::RefinedSources),
        Err(ProveError::Guarded(_))
    ));
}

#[test]
fn low_level_search_apis_report_deferred_source_errors() {
    let session = match session_from(
        "theory T begin\n\
         rule R: [] --[ A() ]-> []\n\
         lemma typing [sources]: \"All x #i. A() @ #i ==> x = x\"\n\
         lemma goal: \"Ex #i. A() @ #i\"\n\
         end",
    ) {
        Some(s) => s,
        None => return,
    };
    let lemma = session.theory.lookup_lemma("goal").expect("goal lemma");
    let mut ctx = session.setup_per_lemma_ctx(lemma, "goal");
    assert!(session.guarded_lemmas_may_fail());
    assert!(ctx.proving_may_fail());
    ctx.heuristic = Some(
        crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            "{missing}",
            "test.spthy",
            &[],
        ),
    );
    ctx.ensure_saturated();
    assert!(matches!(ctx.source_error(), Some(ProveError::Guarded(_))));
    assert!(matches!(ctx.source_cases(), Err(ProveError::Guarded(_))));

    let sys = crate::constraint::system::System::empty();
    assert!(matches!(
        crate::constraint::solver::search::candidate_methods(&sys, &ctx, 0),
        Err(ProveError::Guarded(_))
    ));
    assert!(matches!(
        crate::constraint::solver::search::run_proof_search(&ctx, sys, 0),
        Err(ProveError::Guarded(_))
    ));
    let sys = crate::constraint::system::System::empty();
    assert!(matches!(
        crate::constraint::solver::proof_method::exec_proof_method(
            &ctx,
            &crate::constraint::solver::proof_method::ProofMethod::Sorry(None),
            &sys,
        ),
        Err(ProveError::Guarded(_))
    ));
    assert!(matches!(
        crate::constraint::solver::proof_method::is_finished(&ctx, &sys),
        Err(ProveError::Guarded(_))
    ));
}

#[test]
fn simplify_only_proof_does_not_force_malformed_source_assumption() {
    let src = "theory T begin\n\
rule R: [] --[ A() ]-> []\n\
lemma typing [sources]: \"All x #i. A() @ #i ==> x = x\"\n\
lemma done: \"All #i. A() @ #i ==> A() @ #i\"\n\
end";
    let session = match session_from(src) {
        Some(s) => s,
        None => return,
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
    let session = match session_from(RAW_AND_REFINED_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    let lemma = session.theory.lookup_lemma("goal").expect("goal lemma");
    let ctx = session.setup_per_lemma_ctx(lemma, "goal");
    ctx.ensure_saturated();
    assert!(ctx.source_error().is_none());

    if source_cache_disabled() {
        assert!(session.source_cache.is_empty());
        return;
    }
    assert!(session.source_cache.raw.get().is_some());
    assert!(session.source_cache.refined.get().is_some());
    assert_eq!(session.source_cache.len(), 2);

    let cached = session
        .source_cache
        .refined
        .get()
        .and_then(|result| result.as_ref().ok())
        .and_then(|sources| sources.first())
        .expect("cached refined source");
    let restored = ctx.full_sources.iter().next().expect("restored source");
    assert!(std::sync::Arc::ptr_eq(
        cached,
        &restored.cases_shared_or_empty()
    ));
}

#[test]
fn empty_refinement_still_labels_source_systems_refined() {
    let session = match session_from(
        "theory T begin\n\
         rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
         lemma goal: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
         end",
    ) {
        Some(s) => s,
        None => return,
    };
    let refined = session
        .context_for_sources(SourceKind::RefinedSources)
        .expect("refined sources");
    let mut systems = 0;
    for source in refined.full_sources.iter() {
        let cases = source.cases_shared_or_empty();
        for (_, system) in cases
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .iter()
        {
            systems += 1;
            assert_eq!(system.source_kind, Some(SourceKind::RefinedSources));
        }
    }
    assert!(systems > 0, "fixture must produce source cases");
}

#[test]
fn concurrent_refined_consumers_share_one_materialisation() {
    let session = match session_from(RAW_AND_REFINED_LEMMAS) {
        Some(s) => s,
        None => return,
    };
    let shared = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..4)
            .map(|_| {
                scope.spawn(|| {
                    let lemma = session.theory.lookup_lemma("goal").expect("goal lemma");
                    let ctx = session.setup_per_lemma_ctx(lemma, "goal");
                    ctx.ensure_saturated();
                    assert!(ctx.source_error().is_none());
                    ctx.full_sources
                        .iter()
                        .next()
                        .expect("source")
                        .cases_shared_or_empty()
                })
            })
            .collect();
        workers
            .into_iter()
            .map(|worker| worker.join().expect("source worker"))
            .collect::<Vec<_>>()
    });

    assert_eq!(
        shared
            .iter()
            .skip(1)
            .all(|cases| std::sync::Arc::ptr_eq(&shared[0], cases)),
        !source_cache_disabled()
    );
    assert_eq!(
        session.source_cache.len(),
        if source_cache_disabled() { 0 } else { 2 }
    );
}

#[test]
fn restoring_cached_sources_does_not_publish_completion() {
    #[derive(Debug)]
    struct CountingProvider(std::sync::Arc<std::sync::atomic::AtomicUsize>);

    impl crate::constraint::solver::context::SourceProvider for CountingProvider {
        fn materialize(&self, _ctx: &ProofContext) -> Result<(), ProveError> {
            self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Ok(())
        }
    }

    let h = match maude() {
        Some(h) => h,
        None => return,
    };
    let mut ctx = ProofContext::new(h, Vec::new());
    let calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    ctx.set_source_provider(std::sync::Arc::new(CountingProvider(
        std::sync::Arc::clone(&calls),
    )));
    let cached = ctx
        .full_sources
        .iter()
        .map(|_| std::sync::Arc::new(std::sync::Mutex::new(Vec::new())))
        .collect();

    restore_sources(&ctx, &cached);
    ctx.ensure_saturated();
    assert_eq!(calls.load(std::sync::atomic::Ordering::Relaxed), 1);
}

const STORED_TERMINAL_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma open: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by sorry\n\
lemma terminal: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by contradiction\n\
end";

#[test]
fn replay_of_terminal_roots_leaves_sources_lazy() {
    let session = match session_from(STORED_TERMINAL_LEMMAS) {
        Some(s) => s,
        None => return,
    };

    for name in ["open", "terminal"] {
        check_and_extend_lemma_in_session(&session, name, usize::MAX).expect("replay");
    }
    assert!(session.source_cache.is_empty());
}

#[test]
fn replacing_stored_sorry_reports_unresolved_ranking() {
    let session = match session_from(
        "theory T begin\n\
heuristic: {missing}\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma open: exists-trace \"Ex k #i. A(k) @ #i\" by sorry\n\
end",
    ) {
        Some(session) => session,
        None => return,
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
    let theory = std::sync::Arc::new(elaborated(&parsed));
    let result = ProverSession::build_with_heuristic(
        theory.clone(),
        h.clone(),
        None,
        CliHeuristic {
            raw: Some("unknown".to_string()),
            ..CliHeuristic::default()
        },
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
    );
    assert!(matches!(result, Err(ProveError::InvalidHeuristic(_))));

    let result = ProverSession::build_with_heuristic(
        theory,
        h,
        None,
        CliHeuristic {
            raw: Some(String::new()),
            ..CliHeuristic::default()
        },
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
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

    let compact_default = CliHeuristic {
        raw: Some("so".to_string()),
        ..CliHeuristic::default()
    };
    let rankings = resolve_cli_heuristic(&compact_default, theory.to_str().unwrap(), &[]).unwrap();
    assert!(matches!(
        &rankings[1],
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

    let compact = CliHeuristic {
        raw: Some("so".to_string()),
        oracle_name: Some("chosen.oracle".to_string()),
        ..CliHeuristic::default()
    };
    let rankings = resolve_cli_heuristic(&compact, theory.to_str().unwrap(), &[]).unwrap();
    assert!(matches!(
        &rankings[1],
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
    prepend_theory_dir_to_oracle_paths(&mut rankings, "dir/theory.spthy");

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
    let session = ProverSession::build_with_heuristic(
        std::sync::Arc::new(theory),
        maude,
        None,
        CliHeuristic::default(),
        crate::constraint::solver::context::CutStrategy::Dfs,
        None,
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
