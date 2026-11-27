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

/// How a public-prove-input row reaches the prover.
enum Entry {
    /// `prove_lemma` on the elaborated theory.  With `narrow`, each rule's
    /// compiled body is replaced by its first AC variant: the public API can
    /// receive a compiled body that differs from its E rule.
    Raw { narrow: bool },
    /// `close_theory` (which must report only non-fatal warnings), then a
    /// session.
    Closed,
}

/// The public proving API validates its input itself, whatever the caller
/// did before.  Rows `(label, theory, entry, expected)`: `Ok` is the proof
/// status of the lemma `l`, `Err` a substring of the `UnsupportedInput`
/// error.  Neither a rejection nor building a session draws a fresh name.
#[test]
fn public_proving_validates_its_input() {
    const INVALID_VARIANT: &str = r#"theory InvalidVariant begin
        rule Emit: [In(x)] --[A(x)]-> []
        variants
        rule (modulo AC) Emit___VARIANT_1: [In('a')] --[A('a')]-> []
        lemma l: "All x #i. A(x) @ i ==> x = 'a'"
        end"#;
    // Reuse on an exists-trace lemma is an ordinary warning: it neither
    // rejects this complete family nor turns the false lemma true.
    const VALID_VARIANT: &str = r#"theory ValidVariant begin
        rule Emit: [In(x)] --[A(x)]-> []
        variants
        rule (modulo AC) Emit___VARIANT_1: [In(y)] --[A(y)]-> []
        lemma l: "All x #i. A(x) @ i ==> x = 'a'"
        lemma witness [reuse]: exists-trace "Ex x #i. A(x) @ i"
        end"#;
    // The reducible family is computed before the variants are validated.
    const REDUCIBLE_VARIANT: &str = r#"theory PublicManualVariant begin
        builtins: symmetric-encryption
        macros: decrypt(x,k) = sdec(x,k)
        rule Key: [Fr(~k)] --> [!Key(~k)]
        rule Dec: [In(x), !Key(k)] --[A(decrypt(x,k))]-> []
        variants
        rule (modulo AC) Dec___VARIANT_1:
          [In(x.2), !Key(k.1)] --[A(sdec(x.2,k.1))]-> [],
        rule (modulo AC) Dec___VARIANT_2:
          [In(senc(z.2,k.1)), !Key(k.1)] --[A(z.2)]-> []
        lemma l: exists-trace "Ex m #i. A(m)@i"
        end"#;
    let product = |term: &str| {
        format!(
            r#"theory UnsupportedProduct begin
            builtins: diffie-hellman
            macros: product(x,y) = x*y
            rule Emit: [] --[A({term})]-> []
            lemma l: exists-trace "Ex x #i. A(x) @ i"
            end"#
        )
    };
    let product_error = "Unsupported multiplication outside exponents";
    let rows: Vec<(&str, String, Entry, Result<ProofStatus, &str>)> = vec![
        (
            "invalid variants",
            INVALID_VARIANT.into(),
            Entry::Raw { narrow: false },
            Err("Variants"),
        ),
        (
            "invalid variants at close",
            INVALID_VARIANT.into(),
            Entry::Closed,
            Err("Variants"),
        ),
        (
            "invalid variants, narrowed body",
            INVALID_VARIANT.into(),
            Entry::Raw { narrow: true },
            Err("Variants"),
        ),
        (
            "valid variants and a warning",
            VALID_VARIANT.into(),
            Entry::Closed,
            Ok(ProofStatus::TraceFound),
        ),
        (
            "reducible variant family",
            REDUCIBLE_VARIANT.into(),
            Entry::Raw { narrow: false },
            Ok(ProofStatus::TraceFound),
        ),
        (
            "product of names",
            product("'a' * 'b'"),
            Entry::Raw { narrow: false },
            Err(product_error),
        ),
        (
            "product through a macro",
            product("product('a','b')"),
            Entry::Raw { narrow: false },
            Err(product_error),
        ),
    ];
    for (label, source, entry, expected) in rows {
        let mut theory = elaborated(&tamarin_parser::parse_theory(&source, &[]).unwrap());
        let Some(h) = maude_with(theory.signature.clone()) else {
            return;
        };
        let result = match entry {
            Entry::Raw { narrow } => {
                for item in theory.items.iter_mut().filter(|_| narrow) {
                    if let crate::theory::TheoryItem::Rule(rule) = item {
                        rule.rule_e = Some(Box::new(rule.rule.clone()));
                        rule.rule = rule.rule_ac[0].clone();
                        rule.rule.info.name = rule.rule_e().info.name;
                    }
                }
                prove_lemma(std::sync::Arc::new(theory), "l", h.clone(), 30)
            }
            Entry::Closed => crate::closed_theory::close_theory(theory, &h, None)
                .map_err(ProveError::from)
                .and_then(|(theory, report)| {
                    assert!(!report.is_empty(), "{label}");
                    assert!(crate::wellformedness::variants::fatal_wf_errors(&report).is_empty());
                    let session = ProverSession::build(&theory, h.clone(), Default::default())?;
                    prove_lemma_in_session(&session, "l", 30)
                }),
        };
        match (result, expected) {
            (Ok(proof), Ok(status)) => assert_eq!(
                crate::constraint::solver::search::proof_status(&proof),
                status,
                "{label}"
            ),
            (Err(ProveError::UnsupportedInput(message)), Err(needle)) => {
                assert!(message.contains(needle), "{label}: {message}");
            }
            (other, _) => panic!("{label}: {:?}", other.map(|_| ())),
        }
    }
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

/// What a parallel-scheduling row must observe.
enum Admission {
    /// Two distinct rayon workers reach this kind of gated solver work.
    Distinct(crate::constraint::solver::cancellation_tests::Work),
    /// Proving started no Maude process beyond this many.
    Spawned(usize),
}

/// Which workers and Maude processes a batch may use.  Rows `(label,
/// theory, threads, Maude pool size, hold one idle process, admission,
/// run)`; `run` proves on a pool of `threads` workers and checks its own
/// result.  No gate observes fork admission or Maude-process admission.
#[test]
fn proof_work_is_admitted_to_free_workers() {
    use crate::constraint::solver::cancellation_tests::{Work, WorkerGate};
    use crate::constraint::solver::search::ProofDeadlineGuard;

    type Run = fn(&ProverSession);
    let rows: &[(&str, &str, usize, Option<usize>, bool, Admission, Run)] = &[
        (
            // An oracle lemma in the batch makes its own search serial; the
            // built-in DFS beside it may still fork under a deadline.
            "ordinary DFS in a mixed batch under a deadline",
            r#"theory T begin
            rule GenL: [ Fr(~x) ] --> [ L(~x) ]
            rule GenR: [ Fr(~x) ] --> [ R(~x) ]
            rule Left: [ L(x) ] --[ End(x) ]-> []
            rule Right: [ R(x) ] --[ End(x) ]-> []
            lemma builtin: "All x #i. End(x) @ i ==> F"
            lemma external [heuristic=o "unused-oracle"]: "T"
            end"#,
            4,
            Some(1),
            false,
            Admission::Distinct(Work::Search),
            |session| {
                let _deadline = ProofDeadlineGuard::set_ms(30_000);
                session.map_lemma_proofs(|_| Some(12), |_, _| ()).unwrap();
            },
        ),
        (
            // Cold sources fan out over both workers that DFS siblings need.
            "cold sources beside DFS siblings",
            r#"theory T begin
            rule Left: [] --> [ F('left') ]
            rule Right: [] --> [ F('right') ]
            rule UseA: [ F(x) ] --[ Seen(x), A(x) ]-> []
            rule UseB: [ F(x) ] --[ Seen(x), B(x) ]-> []
            lemma goal: "not (Ex x #i. Seen(x) @ i)"
            end"#,
            2,
            None,
            false,
            Admission::Distinct(Work::Sources),
            |session| {
                let proof = prove_lemma_in_session(session, "goal", 24).unwrap();
                assert_eq!(proof.status, NodeStatus::Solved);
            },
        ),
        (
            // With the only warm process taken, lemmas run on the session's
            // own process instead of starting a cold one.
            "ordinary lemmas when only cold slots remain",
            "theory T begin\nlemma a: \"T\" by sorry\nlemma b: \"T\"\nend",
            1,
            Some(4),
            true,
            Admission::Spawned(1),
            |session| {
                let names = session
                    .map_lemma_proofs(
                        |lemma| (lemma.name == "b").then_some(1),
                        |lemma, _| lemma.name.clone(),
                    )
                    .unwrap();
                assert_eq!(names, ["a", "b"]);
            },
        ),
    ];
    let Some(path) = require_maude_path() else {
        return;
    };
    for (label, source, threads, pool_size, hold_idle, admission, run) in rows {
        let maude = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let theory = closed(
            elaborated(&tamarin_parser::parse_theory(source, &[]).unwrap()),
            &maude,
        );
        let pool = pool_size.map(|size| {
            let pool = tamarin_term::maude_proc::MaudePool::new(
                &path,
                pair_maude_sig(),
                size,
                Default::default(),
            );
            Arc::new(pool.unwrap())
        });
        let options = ProverSessionOptions {
            maude_pool: pool.clone(),
            ..Default::default()
        };
        let session = ProverSession::build(&theory, maude, options).unwrap();
        let _held = hold_idle.then(|| pool.as_ref().unwrap().try_take_idle_owned().unwrap());
        let workers = rayon::ThreadPoolBuilder::new()
            .num_threads(*threads)
            .build()
            .unwrap();
        match admission {
            Admission::Distinct(work) => {
                let (gate, entered) = WorkerGate::new(*work, 2);
                *session.template_ctx.worker_gate.lock().unwrap() = Some(gate.clone());
                std::thread::scope(|scope| {
                    let proof = scope.spawn(|| workers.install(|| run(&session)));
                    let wait = std::time::Duration::from_secs(5);
                    let first = entered.recv_timeout(wait);
                    let second = entered.recv_timeout(wait);
                    gate.release();
                    proof.join().unwrap();
                    assert_ne!(first.unwrap(), second.unwrap(), "{label}");
                });
            }
            Admission::Spawned(count) => {
                workers.install(|| run(&session));
                assert_eq!(pool.unwrap().spawned(), *count, "{label}");
            }
        }
    }
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

const RAW_AND_REFINED_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma typing [sources]: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
lemma goal: \"All k #i. A(k) @ #i ==> A(k) @ #i\"\n\
end";

fn source_cache_disabled() -> bool {
    tamarin_utils::env_gate!("TAM_RS_NO_SOURCE_CACHE")
}

/// A consumer of a session's source cache in a source-cache row.
type SourceConsumer = Box<dyn Fn(&ProverSession)>;

/// The source cache is materialised lazily, once per slot, and shared.
/// Rows `(label, theory, consumer, filled slots)`: after the consumer runs
/// (making its own sharing checks), the cache holds that many of its raw
/// and refined slots; none when `TAM_RS_NO_SOURCE_CACHE` bypasses it.
#[test]
fn source_cache_fills_only_what_consumers_force() {
    use crate::constraint::solver::context::ProofContext;

    const TRIVIAL_SOURCES: &str = r#"theory T begin
        lemma a [sources]: "T"
        lemma b [sources]: "T"
        lemma c: "T"
        end"#;
    let disabled = source_cache_disabled();
    let goal_ctx = |session: &ProverSession| {
        let (lemma, prepared) = session.lemma_and_prepared("goal").expect("goal lemma");
        session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude)
    };
    // A batch whose proofs need no source cases: any filled slot comes from
    // the batch phase, and every renderer already sees it filled.
    let batch = |workers: usize, selected: &'static str, slots: usize| -> SourceConsumer {
        Box::new(move |session| {
            let cache = session.source_cache.clone();
            let expected = if disabled { 0 } else { slots };
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
        })
    };
    let rows: Vec<(&str, &str, SourceConsumer, usize)> = vec![
        (
            "per-lemma contexts share one lazy handle",
            RAW_AND_REFINED_LEMMAS,
            Box::new(move |session| {
                let (first, second) = (goal_ctx(session), goal_ctx(session));
                assert!(Arc::ptr_eq(&first.full_sources, &second.full_sources));
            }),
            0,
        ),
        (
            "one worker, every lemma",
            TRIVIAL_SOURCES,
            batch(1, "abc", 0),
            0,
        ),
        (
            "two workers, no sources lemma",
            TRIVIAL_SOURCES,
            batch(2, "c", 0),
            0,
        ),
        (
            "two workers, sources lemmas",
            TRIVIAL_SOURCES,
            batch(2, "ab", 1),
            1,
        ),
        (
            "two workers, every lemma",
            TRIVIAL_SOURCES,
            batch(2, "abc", 2),
            2,
        ),
        (
            // HS `refineWithSourceAsms` marks the cases refined even with no
            // assumptions; a worker on another process shares the build.
            "standalone workers choose assumptions first",
            RAW_AND_REFINED_LEMMAS,
            Box::new(|session| {
                let raw = session.template_context();
                let mut refined = raw.with_swapped_maude(raw.maude.clone());
                refined.typing_assumptions = session
                    .source_assumptions
                    .as_ref()
                    .as_ref()
                    .unwrap()
                    .clone();
                for ctx in [&refined, raw] {
                    let cases = ctx.source_cases().unwrap();
                    let kinds: Vec<_> = cases
                        .iter()
                        .flat_map(|(_, cases)| cases.iter().map(|(_, sys)| sys.source_kind))
                        .collect();
                    assert!(!kinds.is_empty());
                    assert!(kinds
                        .iter()
                        .all(|kind| *kind == Some(SourceKind::RefinedSources)));
                    let worker: ProofContext = ctx.with_swapped_maude(ctx.maude.clone());
                    assert!(Arc::ptr_eq(
                        &ctx.ensure_saturated().unwrap(),
                        &worker.ensure_saturated().unwrap()
                    ));
                }
            }),
            0,
        ),
        (
            "a terminal system",
            RAW_AND_REFINED_LEMMAS,
            Box::new(|session| {
                let mut terminal = crate::constraint::system::System::default();
                terminal
                    .formulas_mut()
                    .push(Arc::new(crate::guarded::gfalse()));
                let options = SearchOptions {
                    proof_bound: usize::MAX,
                    ranking_depth_offset: 0,
                    cut: session.cut,
                    oracle_only: false,
                };
                prove_system_in_session_with_options(session, "goal", terminal, options)
                    .expect("terminal system bypasses sources");
            }),
            0,
        ),
        (
            // Interactive views go through the session's provider: the raw
            // view fills the raw slot alone.
            "interactive raw then refined views",
            RAW_AND_REFINED_LEMMAS,
            Box::new(move |session| {
                session.context_for_sources(SourceKind::RawSources).unwrap();
                if !disabled {
                    assert!(session.source_cache.raw.ready.get().is_some());
                    assert!(session.source_cache.refined.ready.get().is_none());
                }
                session
                    .context_for_sources(SourceKind::RefinedSources)
                    .unwrap();
                assert!(session.source_stats().refined.is_ok());
            }),
            2,
        ),
        (
            // The refined slot derives from the single raw slot, and every
            // later request returns the published refined cases.
            "a lemma's saturation",
            RAW_AND_REFINED_LEMMAS,
            Box::new(move |session| {
                let ctx = goal_ctx(session);
                let resolved = ctx.ensure_saturated().unwrap();
                if !disabled {
                    let published = session.source_cache.refined.ready.get().unwrap();
                    assert!(Arc::ptr_eq(published, &resolved));
                    assert!(Arc::ptr_eq(&ctx.ensure_saturated().unwrap(), &resolved));
                    assert!(Arc::ptr_eq(
                        &ctx.clone().ensure_saturated().unwrap(),
                        &resolved
                    ));
                }
            }),
            2,
        ),
        (
            "concurrent raw and refined consumers",
            RAW_AND_REFINED_LEMMAS,
            Box::new(move |session| {
                use SourceKind::{RawSources, RefinedSources};
                let barrier = std::sync::Barrier::new(4);
                let shared: Vec<_> = std::thread::scope(|scope| {
                    let workers: Vec<_> = [RawSources, RefinedSources, RawSources, RefinedSources]
                        .into_iter()
                        .map(|kind| {
                            let barrier = &barrier;
                            scope.spawn(move || {
                                barrier.wait();
                                let ctx = session.context_for_sources(kind).unwrap();
                                (kind, ctx.ensure_saturated().unwrap())
                            })
                        })
                        .collect();
                    workers.into_iter().map(|w| w.join().unwrap()).collect()
                });
                for kind in [RawSources, RefinedSources] {
                    let mut matching = shared.iter().filter(|(k, _)| *k == kind).map(|(_, c)| c);
                    let first = matching.next().unwrap();
                    assert_eq!(matching.all(|c| Arc::ptr_eq(first, c)), !disabled);
                }
            }),
            2,
        ),
        (
            // Replaying stored `by sorry` / `by contradiction` roots in
            // parallel, then proving none or the terminal one.
            "parallel replay of terminal roots",
            STORED_TERMINAL_LEMMAS,
            Box::new(|session| {
                use rayon::prelude::*;
                let pool = rayon::ThreadPoolBuilder::new()
                    .num_threads(2)
                    .build()
                    .unwrap();
                pool.install(|| {
                    ["open", "terminal"].par_iter().try_for_each(|name| {
                        check_and_extend_lemma_in_session(session, name, usize::MAX).map(drop)
                    })
                })
                .unwrap();
                for selected in [None, Some("terminal")] {
                    let selection = |lemma: &crate::theory::Lemma| {
                        (Some(lemma.name.as_str()) == selected).then_some(1)
                    };
                    pool.install(|| session.map_lemma_proofs(selection, |_, _| ()))
                        .unwrap();
                }
            }),
            0,
        ),
    ];
    for (label, source, consume, slots) in rows {
        let Some(session) = session_from(source) else {
            return;
        };
        consume(&session);
        let expected = if disabled { 0 } else { slots };
        assert_eq!(session.source_cache.len(), expected, "{label}");
    }
}

/// What a deferred-error row's consumer must fail with.
enum Deferred {
    /// `ProveError::Guarded`: the malformed `[sources]` lemma.
    Guarded,
    /// `ProveError::Ranking` naming this missing oracle.
    Ranking(&'static str),
}

/// A malformed lemma is reported where it is consumed, deterministically:
/// in declaration order under two workers, with or without the source
/// cache, and across the provider boundary of every lazy source consumer.
/// Rows `(label, theory, consumer, error, proofs rendered first)`; the
/// consumer returns its result and how many proofs it rendered.
#[test]
fn deferred_errors_surface_in_declaration_order() {
    type Consumer = Box<dyn Fn(&mut ProverSession) -> (Result<(), ProveError>, usize)>;
    const SELECTED_ORACLE: &str = r#"theory T begin
        rule R: [] --[ A() ]-> []
        lemma selected [heuristic=o "missing-test-oracle"]: exists-trace "Ex #i. A() @ i"
        lemma invalid: "All x #i. A() @ i ==> x = x"
        end"#;
    const LATE_SOURCES: &str = r#"theory T begin
        rule R: [] --[ A() ]-> []
        lemma a: "T"
        lemma b: "T"
        lemma invalid [sources]: "All x #i. A() @ #i ==> x = x"
        end"#;
    const EARLY_SOURCES: &str = "theory T begin\n\
        rule R: [] --[ A() ]-> []\n\
        lemma typing [sources]: \"All x #i. A() @ #i ==> x = x\"\n\
        lemma goal: \"Ex #i. A() @ #i\"\n\
        end";
    let batch = |selected: Option<&'static str>, bypass: bool| -> Consumer {
        Box::new(move |session| {
            session.source_cache_disabled = bypass;
            let rendered = Arc::new(std::sync::atomic::AtomicUsize::new(0));
            let count = rendered.clone();
            let workers = rayon::ThreadPoolBuilder::new()
                .num_threads(2)
                .build()
                .unwrap();
            let result = workers.install(|| {
                session.map_lemma_proofs(
                    |lemma| match selected {
                        Some(name) => (lemma.name == name).then_some(usize::MAX),
                        None => (lemma.name != "invalid").then_some(1),
                    },
                    move |_, _| {
                        count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    },
                )
            });
            (
                result.map(drop),
                rendered.load(std::sync::atomic::Ordering::Relaxed),
            )
        })
    };
    // A lemma context whose ranking cannot fail before sources are forced.
    let lemma_ctx = |session: &ProverSession| {
        let (lemma, prepared) = session.lemma_and_prepared("goal").expect("goal lemma");
        let mut ctx = session.setup_per_lemma_ctx(lemma, prepared, &session.template_ctx.maude);
        ctx.heuristic = Some(
            crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
                "{missing}",
                "test.spthy",
                &[],
            ),
        );
        ctx
    };
    let replay_only: Consumer = Box::new(|session| {
        let result = session.map_lemma_proofs(|_| None, |_, _| ());
        (result.map(drop), 0)
    });
    let rows: Vec<(&str, &str, Consumer, Deferred, usize)> = vec![
        // The selected lemma fails first, though the invalid one follows.
        (
            "batch, auto-proving the first lemma",
            SELECTED_ORACLE,
            Box::new(|session| {
                let result = session.map_lemma_proofs(
                    |lemma| (lemma.name == "selected").then_some(usize::MAX),
                    |_, _| (),
                );
                (result.map(drop), 0)
            }),
            Deferred::Ranking("missing-test-oracle"),
            0,
        ),
        // Replay alone passes the first lemma and reports the second's guard
        // error though it was never selected.
        (
            "batch, replay only",
            SELECTED_ORACLE,
            replay_only,
            Deferred::Guarded,
            0,
        ),
        // Both trivial proofs finish before replay reaches the invalid lemma.
        (
            "two workers, cached sources",
            LATE_SOURCES,
            batch(None, false),
            Deferred::Guarded,
            2,
        ),
        (
            "two workers, bypassed cache",
            LATE_SOURCES,
            batch(None, true),
            Deferred::Guarded,
            2,
        ),
        (
            "interactive refined view",
            EARLY_SOURCES,
            Box::new(|session| {
                let result = session.context_for_sources(SourceKind::RefinedSources);
                (result.map(drop), 0)
            }),
            Deferred::Guarded,
            0,
        ),
        (
            "lazy saturation",
            EARLY_SOURCES,
            Box::new(move |session| (lemma_ctx(session).ensure_saturated().map(drop), 0)),
            Deferred::Guarded,
            0,
        ),
        (
            "lazy source cases",
            EARLY_SOURCES,
            Box::new(move |session| (lemma_ctx(session).source_cases().map(drop), 0)),
            Deferred::Guarded,
            0,
        ),
    ];
    for (label, source, consume, expected, rendered_first) in rows {
        let Some(mut session) = session_from(source) else {
            return;
        };
        let (result, rendered) = consume(&mut session);
        match (result, expected) {
            (Err(ProveError::Guarded(_)), Deferred::Guarded) => {}
            (Err(ProveError::Ranking(err)), Deferred::Ranking(oracle)) => {
                assert!(err.0.contains(oracle), "{label}: {err:?}")
            }
            (other, _) => panic!("{label}: {other:?}"),
        }
        assert_eq!(rendered, rendered_first, "{label}");
    }
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

const STORED_TERMINAL_LEMMAS: &str = "theory T begin\n\
rule R: [ Fr(~k) ] --[ A(~k) ]-> [ Out(~k) ]\n\
lemma open: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by sorry\n\
lemma terminal: all-traces \"All k #i. A(k) @ #i ==> Ex #j. A(k) @ #j\" by contradiction\n\
end";

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

/// Where each way of naming an oracle resolves, as rows `(label, resolved,
/// expected)` over one scratch tree:
///
/// ```text
/// protocol.spthy  protocol.oracle
/// root.spthy      (#include "sub/inc.spthy")
/// sub/inc.spthy   sub/inc.oracle  sub/rank
/// ```
///
/// A default oracle sits beside the theory (`<theory>.oracle` from the
/// CLI, `oracle` in the file); `--oraclename` is relative to the working
/// directory; an included file's oracles resolve beside the include, and
/// are frozen at elaboration: removing `sub/inc.oracle` and adding
/// `sub/oracle` afterwards switches nothing to the fallback name.
#[test]
fn oracle_paths_resolve_like_haskell() {
    use crate::constraint::solver::goals::GoalRanking;

    let path_of = |ranking: &GoalRanking| match ranking {
        GoalRanking::Oracle { oracle_path, .. } => oracle_path.clone(),
        other => panic!("expected an oracle ranking, got {other:?}"),
    };
    let root = std::env::temp_dir().join(format!("tamarin_rs_oracle_paths_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("sub")).unwrap();
    let at = |rel: &str| root.join(rel).to_string_lossy().into_owned();
    for (file, text) in [
        ("protocol.spthy", "theory T begin end"),
        ("protocol.oracle", "#!/bin/sh\n"),
        (
            "root.spthy",
            "theory T begin\n#include \"sub/inc.spthy\"\nend\n",
        ),
        (
            "sub/inc.spthy",
            "heuristic: o\n\
             lemma header: \"T\"\n\
             lemma local [heuristic=o \"rank\"]: \"T\"\n\
             lemma local_default [heuristic=o, heuristic=o]: \"T\"\n",
        ),
        ("sub/inc.oracle", ""),
        ("sub/rank", ""),
    ] {
        std::fs::write(root.join(file), text).unwrap();
    }
    let mut rows: Vec<(&str, String, String)> = Vec::new();

    let cli = |oracle_name: Option<&str>| {
        let cli = CliHeuristic {
            raw: Some("o".to_string()),
            oracle_name: oracle_name.map(str::to_string),
            ..CliHeuristic::default()
        };
        path_of(&resolve_cli_heuristic(&cli, &at("protocol.spthy"), &[]).unwrap()[0])
    };
    rows.push(("CLI default", cli(None), at("protocol.oracle")));
    rows.push((
        "CLI --oraclename",
        cli(Some("chosen.oracle")),
        "./chosen.oracle".into(),
    ));

    let mut in_file = vec![
        GoalRanking::Oracle {
            quit_on_empty: false,
            oracle_path: "oracle".to_string(),
        };
        2
    ];
    resolve_oracle_rankings(&mut in_file, "dir/theory.spthy", None);
    for ranking in &in_file {
        rows.push(("in-file default", path_of(ranking), "dir/oracle".into()));
    }
    rows.push((
        "absolute path is normalised",
        resolve_oracle_path("/tmp/./nested//rank", Some("ignored")),
        "/tmp/nested/rank".into(),
    ));

    let source = std::fs::read_to_string(root.join("root.spthy")).unwrap();
    let parsed = tamarin_parser::parse_theory_with_base(&source, &[], Some(root.clone())).unwrap();
    let theory = crate::elaborate::elaborate_with_in_file(&parsed, &at("root.spthy")).unwrap();
    rows.push((
        "included header",
        path_of(&theory.heuristic[0]),
        "inc.oracle".into(),
    ));
    let attributes: Vec<_> = theory
        .lookup_lemma("local_default")
        .unwrap()
        .attributes
        .iter()
        .filter_map(|attribute| match attribute {
            crate::theory::LemmaAttr::Heuristic(raw) => Some(raw.as_str()),
            _ => None,
        })
        .collect();
    rows.push((
        "included lemma defaults",
        attributes.join(", "),
        "o \"inc.oracle\", o \"inc.oracle\"".into(),
    ));

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
    let in_session = |lemma: &str| {
        let ctx = session.context_for_lemma(lemma).unwrap();
        path_of(&ctx.heuristic.as_ref().unwrap()[0])
    };
    rows.push(("session header", in_session("header"), at("sub/inc.oracle")));
    rows.push(("session lemma-local", in_session("local"), at("sub/rank")));
    rows.push((
        "session lemma default",
        in_session("local_default"),
        at("sub/inc.oracle"),
    ));

    let _ = std::fs::remove_dir_all(&root);
    for (label, resolved, expected) in rows {
        assert_eq!(resolved, expected, "{label}");
    }
}

/// A cancellation scenario.  `run` is the cancellable operation, rendered
/// with `Debug`; `gate` parks that many workers at this kind of solver work
/// on `ctx` before the token is cancelled (`None`: the token is cancelled
/// before `run` starts); `parked` runs while they are parked, and `after`
/// once the cancelled run returned.  `retry` must then equal `baseline`.
struct CancelRow<'a> {
    label: String,
    threads: usize,
    gate: Option<(
        &'a ProofContext,
        crate::constraint::solver::cancellation_tests::Work,
        usize,
    )>,
    run: Box<dyn Fn() -> Result<String, ProveError> + Sync + 'a>,
    parked: Box<dyn Fn() + 'a>,
    after: Box<dyn Fn(&tamarin_utils::cancellation::CancellationToken) + 'a>,
    retry: Box<dyn Fn() -> String + Sync + 'a>,
    baseline: String,
}

/// Cancellation fails the run with `Cancelled` wherever it lands (before
/// the search, inside a parallel search or source fan-out, or during
/// terminal classification), leaves no worker holding the token, publishes
/// nothing partial, and a retry on the same workers and context equals a
/// clean run.  No gate cancels a proof.
#[test]
fn cancellation_fails_cleanly_and_a_retry_matches_a_clean_run() {
    use crate::constraint::solver::cancellation_tests::Work;
    use crate::constraint::solver::context::CutStrategy;
    use crate::constraint::solver::proof_method::{ProofMethod, Result as MethodResult};
    use crate::constraint::solver::search::run_proof_search;
    use crate::constraint::system::System;
    use crate::theory::ProofTree;
    use tamarin_utils::cancellation::{check, CancellationGuard, CancellationToken};

    let Some(path) = require_maude_path() else {
        return;
    };
    let debug = |proof: ProofNode| format!("{proof:?}");
    let cut_ctxs: Vec<_> = [
        CutStrategy::Dfs,
        CutStrategy::Bfs,
        CutStrategy::SeqDfs,
        CutStrategy::Nothing,
        CutStrategy::AfterSorry,
    ]
    .into_iter()
    .map(|cut| {
        let mut ctx = ProofContext::new(maude().unwrap(), Vec::new());
        ctx.cut = cut;
        ctx
    })
    .collect();
    let branching = |pool: bool| {
        let mut ctx = ProofContext::new(maude().unwrap(), Vec::new());
        if pool {
            let pool = tamarin_term::maude_proc::MaudePool::new(
                &path,
                pair_maude_sig(),
                1,
                Default::default(),
            );
            ctx.maude_pool = Some(Arc::new(pool.unwrap()));
        }
        ctx.cut = CutStrategy::Dfs;
        ctx.is_exists_trace = false;
        ctx
    };
    fn disj_sys() -> System {
        let mut sys = System::empty();
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(vec![
                crate::guarded::gtrue(),
                crate::guarded::gfalse(),
            ]),
        ));
        sys
    }
    let search_ctx = branching(true);
    let clean_ctx = branching(false);
    let session = session_from(RAW_AND_REFINED_LEMMAS).unwrap();
    let clean = session_from(RAW_AND_REFINED_LEMMAS).unwrap();
    clean
        .context_for_lemma("goal")
        .unwrap()
        .ensure_saturated()
        .unwrap();
    let sources_ctx = session.context_for_lemma("goal").unwrap();
    let xorr_ctx = xorr_contradiction_ctx(&path);
    // One system (one set of stamps) for the baseline and every run.
    let xorr_sys = std::sync::Mutex::new(xorr_contradiction_system());
    let skeletons: Vec<_> = [
        Some(MethodResult::Contradictory(None)),
        Some(MethodResult::Solved),
        None,
    ]
    .into_iter()
    .map(|stored| {
        stored.map(|method| ProofTree {
            method: ProofMethod::Finished(method),
            cases: Default::default(),
        })
    })
    .collect();
    let mut rows: Vec<CancelRow> = Vec::new();

    // Cancelled before the search starts, under every cut strategy.
    for ctx in &cut_ctxs {
        let run = move || run_proof_search(ctx, System::empty(), usize::MAX).map(debug);
        rows.push(CancelRow {
            label: format!("{:?} search, cancelled up front", ctx.cut),
            threads: 1,
            gate: None,
            baseline: run().unwrap(),
            run: Box::new(run),
            parked: Box::new(|| ()),
            after: Box::new(|_| ()),
            retry: Box::new(move || run().unwrap()),
        });
    }

    // A DFS over a two-armed disjunction, cancelled while both rayon workers
    // are inside the search.
    let search = || run_proof_search(&search_ctx, disj_sys(), 10).map(debug);
    rows.push(CancelRow {
        label: "parallel search".into(),
        threads: 2,
        gate: Some((&search_ctx, Work::Search, 2)),
        baseline: run_proof_search(&clean_ctx, disj_sys(), 10)
            .map(debug)
            .unwrap(),
        run: Box::new(search),
        parked: Box::new(|| ()),
        after: Box::new(|_| ()),
        retry: Box::new(move || search().unwrap()),
    });

    // Source fan-out, cancelled while both workers build sources.  A second
    // request snapshotting the same in-progress build must return on its
    // own cancellation while the builder is still parked.  Nothing partial
    // is published.
    rows.push(CancelRow {
        label: "parallel sources".into(),
        threads: 2,
        gate: Some((&session.template_ctx, Work::Sources, 2)),
        baseline: debug(prove_lemma_in_session(&clean, "goal", 12).unwrap()),
        run: Box::new(|| {
            sources_ctx
                .ensure_saturated()
                .map(|cases| format!("{cases:?}"))
        }),
        parked: Box::new(|| {
            let token = CancellationToken::default();
            std::thread::scope(|scope| {
                let (started, waiting) = std::sync::mpsc::channel();
                let (done, result) = std::sync::mpsc::channel();
                let waiter_token = token.clone();
                let ctx = &sources_ctx;
                scope.spawn(move || {
                    let _guard = CancellationGuard::new(Some(waiter_token));
                    let worker = ctx.with_swapped_maude(ctx.maude.clone());
                    started.send(()).unwrap();
                    done.send(worker.source_cases().map(drop)).unwrap();
                });
                waiting
                    .recv_timeout(std::time::Duration::from_secs(2))
                    .unwrap();
                let short = std::time::Duration::from_millis(30);
                assert!(result.recv_timeout(short).is_err(), "the waiter waits");
                token.cancel();
                let wait = std::time::Duration::from_secs(3);
                assert!(matches!(
                    result.recv_timeout(wait),
                    Ok(Err(ProveError::Cancelled))
                ));
            });
        }),
        after: Box::new(|token| {
            assert!(
                session.source_cache.raw.ready.get().is_none(),
                "partial sources"
            );
            assert!(!sources_ctx.source_cases().unwrap().is_empty());
            let _guard = CancellationGuard::new(Some(token.clone()));
            assert!(matches!(
                sources_ctx.source_cases(),
                Err(ProveError::Cancelled)
            ));
        }),
        retry: Box::new(|| {
            let retry = debug(prove_lemma_in_session(&session, "goal", 12).unwrap());
            assert_eq!(session.source_stats().raw, clean.source_stats().raw);
            assert_eq!(session.source_stats().refined, clean.source_stats().refined);
            retry
        }),
    });

    // A node concluding the non-normal `xorr(k,k)` makes the system
    // contradictory.  Cancelling its AC match during terminal
    // classification must not reject the valid contradiction or accept an
    // invalid stored SOLVED claim.
    for skeleton in &skeletons {
        let run = || {
            let sys = xorr_sys.lock().unwrap().clone();
            match skeleton {
                Some(skeleton) => {
                    crate::replay::check_and_extend(&xorr_ctx, sys, skeleton, usize::MAX)
                }
                None => run_proof_search(&xorr_ctx, sys, usize::MAX),
            }
        };
        let baseline = run().unwrap();
        match skeleton.as_ref().map(|tree| &tree.method) {
            Some(ProofMethod::Finished(MethodResult::Solved)) => {
                assert!(matches!(baseline.method, ProofMethod::Sorry(_)))
            }
            _ => assert_eq!(baseline.status, NodeStatus::Contradictory),
        }
        rows.push(CancelRow {
            label: format!(
                "terminal classification under {:?}",
                skeleton.as_ref().map(|t| &t.method)
            ),
            threads: 1,
            gate: Some((&xorr_ctx, Work::Terminal, 1)),
            baseline: debug(baseline),
            run: Box::new(move || run().map(debug)),
            parked: Box::new(|| ()),
            after: Box::new(|_| ()),
            retry: Box::new(move || debug(run().unwrap())),
        });
    }

    for row in rows {
        let label = &row.label;
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(row.threads)
            .build()
            .unwrap();
        let token = CancellationToken::default();
        match row.gate {
            None => {
                token.cancel();
                pool.install(|| {
                    let _guard = CancellationGuard::new(Some(token.clone()));
                    assert!(matches!((row.run)(), Err(ProveError::Cancelled)), "{label}");
                    // A nested worker scope restores its parent's cancellation.
                    {
                        let _nested = CancellationGuard::new(Some(CancellationToken::default()));
                        assert!(check().is_ok());
                    }
                    assert!(check().is_err(), "{label}");
                });
            }
            Some((ctx, work, participants)) => {
                let (gate, entered) =
                    crate::constraint::solver::cancellation_tests::WorkerGate::new(
                        work,
                        participants,
                    );
                *ctx.worker_gate.lock().unwrap() = Some(gate.clone());
                std::thread::scope(|scope| {
                    let worker = scope.spawn(|| {
                        pool.install(|| {
                            let _guard = CancellationGuard::new(Some(token.clone()));
                            (row.run)()
                        })
                    });
                    let wait = std::time::Duration::from_secs(5);
                    let ids: Vec<_> = (0..participants)
                        .map(|_| entered.recv_timeout(wait).unwrap())
                        .collect();
                    assert!(!ids.contains(&std::thread::current().id()), "{label}");
                    let distinct: std::collections::BTreeSet<_> =
                        ids.iter().map(|id| format!("{id:?}")).collect();
                    assert_eq!(distinct.len(), participants, "{label}: distinct workers");
                    (row.parked)();
                    token.cancel();
                    gate.release();
                    assert!(
                        matches!(worker.join().unwrap(), Err(ProveError::Cancelled)),
                        "{label}"
                    );
                });
                *ctx.worker_gate.lock().unwrap() = None;
            }
        }
        let clear = pool.broadcast(|_| tamarin_utils::cancellation::current().is_none());
        assert!(
            clear.into_iter().all(|clear| clear),
            "{label}: a worker kept the token"
        );
        (row.after)(&token);
        assert_eq!(pool.install(|| (row.retry)()), row.baseline, "{label}");
    }
}

/// A context whose signature has a user AC symbol `xorr` with the
/// non-subterm rule `xorr(x, x) = zeroo`.
fn xorr_contradiction_ctx(path: &str) -> ProofContext {
    ProofContext::new(MaudeHandle::start(path, xorr_maude_sig()).unwrap(), vec![])
}

/// The pair signature extended by a user AC symbol `xorr` with the
/// non-subterm rule `xorr(x, x) = zeroo`.
fn xorr_maude_sig() -> MaudeSig {
    use tamarin_term::builtin::msg_var;
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::rewriting::RRule;
    use tamarin_term::term::{f_app_acfct, f_app_no_eq};

    let mut sig = pair_maude_sig();
    sig.st_ac_fun_syms.insert(xorr_sym());
    let zeroo = NoEqSym::new(
        b"zeroo".to_vec(),
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    sig.st_fun_syms.insert(zeroo);
    let x = msg_var("x", 0);
    let rule = RRule::new(
        f_app_acfct(xorr_sym(), vec![x.clone(), x]),
        f_app_no_eq(zeroo, vec![]),
    );
    sig.st_rules
        .insert(tamarin_term::subterm_rule::rrule_to_ctxt_st_rule(&rule).unwrap());
    sig.refresh()
}

fn xorr_sym() -> tamarin_term::function_symbols::AcFctSym {
    use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
    AcFctSym::new(
        b"xorr".to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::IsNdc,
    )
}

/// A system past its initial state with one node concluding `F(xorr(~k, ~k))`.
fn xorr_contradiction_system() -> crate::constraint::system::System {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    use tamarin_term::builtin::fresh_var;
    use tamarin_term::lterm::{LSort, LVar};

    let mut sys = crate::constraint::system::System::empty();
    sys.solved_formulas_mut()
        .push(Arc::new(crate::guarded::gtrue()));
    let k = fresh_var("k", 0);
    let conclusion = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "F", 1),
        vec![tamarin_term::term::f_app_acfct(
            xorr_sym(),
            vec![k.clone(), k],
        )],
    );
    let info = RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
        name: ProtoRuleName::Stand("R"),
        attributes: RuleAttributes::empty(),
        loop_breakers: vec![],
    });
    sys.add_node(
        LVar::new("i", LSort::Node, 0),
        Rule::new(info, vec![], vec![conclusion], vec![]),
    );
    sys
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

/// What a backend-failure row's operation returns once its backend fails.
enum Failure {
    /// `ProveError::Maude`: the Maude process died under the operation.
    Maude,
    /// `ProveError::Guarded` with this message: the source provider failed.
    Guarded(&'static str),
}

/// The backend of one backend-failure row run.  In failure mode every
/// process the row starts through [`Backend::maude`] is killed before use,
/// and [`Backend::sources`] installs a provider that always fails.
struct Backend {
    path: String,
    failed: bool,
}

impl Backend {
    /// A fresh process on `sig`, dead in failure mode.  A fresh handle per
    /// run keeps a healthy run's memoised answers out of the failed one.
    fn maude(&self, sig: MaudeSig) -> MaudeHandle {
        let h = self.healthy(sig);
        if self.failed {
            h.kill_subprocess();
        }
        h
    }

    /// A context whose solver process is [`Backend::maude`].  It is built
    /// on a live process, since building assembles the intruder rules
    /// through Maude.
    fn context(
        &self,
        sig: MaudeSig,
        options: crate::constraint::solver::context::ProofContextOptions,
    ) -> ProofContext {
        let mut ctx = ProofContext::with_options(self.healthy(sig.clone()), Vec::new(), options);
        ctx.maude = self.maude(sig);
        ctx
    }

    /// A process that stays healthy in both modes.
    fn healthy(&self, sig: MaudeSig) -> MaudeHandle {
        MaudeHandle::start(&self.path, sig).expect("start maude")
    }

    /// In failure mode, makes every source materialisation of `ctx` fail.
    fn sources(&self, ctx: &mut crate::constraint::solver::context::ProofContext) {
        if self.failed {
            ctx.set_source_provider(std::sync::Arc::new(
                crate::constraint::solver::context::FailingSourceProvider,
            ));
        }
    }
}

type BackendOperation = fn(&Backend) -> Result<(), ProveError>;

/// A backend failure surfaces as an error.  It never becomes a closed or
/// contradictory branch, a weaker constraint system, a missing warning or
/// a cached result.  Each row runs
/// once healthy, where the operation must succeed (and meet its own
/// postconditions), and once with the failure injected.  No corpus run ever
/// kills Maude, so this is the only check of these paths.
#[test]
fn backend_failures_surface_as_errors() {
    let rows: &[(&str, Failure, BackendOperation)] = &[
        ("solve an AC action goal", Failure::Maude, |b| {
            backend_proof_method(b, true)
        }),
        ("simplify an AC equality formula", Failure::Maude, |b| {
            backend_proof_method(b, false)
        }),
        ("match an action guard", Failure::Maude, |b| {
            backend_guard_match(b, true)
        }),
        ("match an equality guard", Failure::Maude, |b| {
            backend_guard_match(b, false)
        }),
        (
            "order nodes after a fresh supplier",
            Failure::Maude,
            backend_fresh_ordering,
        ),
        (
            "order injective-fact instances",
            Failure::Maude,
            backend_injective_facts,
        ),
        (
            "evaluate formula atoms",
            Failure::Maude,
            backend_formula_atoms,
        ),
        (
            "annotate loop breakers",
            Failure::Maude,
            backend_loop_breakers,
        ),
        ("check terms are in normal form", Failure::Maude, |b| {
            backend_normal_forms(b, false)
        }),
        ("filter non-normal substitutions", Failure::Maude, |b| {
            backend_normal_forms(b, true)
        }),
        (
            "assemble intruder rules",
            Failure::Maude,
            backend_intruder_rules,
        ),
        (
            "materialise sources for a smart oracle",
            Failure::Guarded("bad source"),
            backend_oracle_sources,
        ),
        (
            "materialise a session's sources",
            Failure::Maude,
            backend_session_sources,
        ),
        ("check message derivations", Failure::Maude, |b| {
            backend_scratch_check(b, true)
        }),
        ("compute auto-sources", Failure::Maude, |b| {
            backend_scratch_check(b, false)
        }),
        ("check NDC destructors", Failure::Maude, backend_ndc_check),
    ];
    let Some(path) = require_maude_path() else {
        return;
    };
    for (label, failure, operation) in rows {
        for failed in [false, true] {
            let backend = Backend {
                path: path.clone(),
                failed,
            };
            let result = operation(&backend);
            match (failed, failure, result) {
                (false, _, result) => result.unwrap_or_else(|e| panic!("{label}: {e:?}")),
                (true, Failure::Maude, Err(ProveError::Maude(_))) => {}
                (true, Failure::Guarded(want), Err(ProveError::Guarded(got))) if got == *want => {}
                (true, _, other) => panic!("{label}: the failed backend gave {other:?}"),
            }
        }
    }
}

/// Solves `A(x ∪ y)` against a node concluding `A(a ∪ b)`, or simplifies
/// the formula `a ∪ b = x ∪ y`: both need an AC unifier.  Healthy, the
/// method yields branches.
fn backend_proof_method(backend: &Backend, action: bool) -> Result<(), ProveError> {
    use crate::atom::ProtoAtom;
    use crate::constraint::solver::proof_method::{exec_proof_method, ProofMethod};
    use crate::constraint::system::System;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::var_term;

    let ctx = backend.context(
        tamarin_term::maude_sig::mset_maude_sig(),
        Default::default(),
    );
    let union = |a, b| {
        Term::App(
            FunSym::Ac(AcSym::Union),
            vec![
                var_term(LVar::new(a, LSort::Msg, 0)),
                var_term(LVar::new(b, LSort::Msg, 0)),
            ]
            .into(),
        )
    };
    let (left, right) = (union("a", "b"), union("x", "y"));
    let fact = |term| proto_fact(Multiplicity::Linear, "A", vec![term]);
    let mut sys = System::empty();
    let method = if action {
        let node = LVar::new("i", LSort::Node, 0);
        let info = RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("R"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
        sys.add_node(
            node,
            Rule::new(info, Vec::new(), Vec::new(), vec![fact(left)]),
        );
        let goal = crate::constraint::constraints::Goal::Action(node, fact(right));
        sys.add_goal(goal.clone());
        ProofMethod::SolveGoal(goal)
    } else {
        sys.insert_formula(crate::guarded::Guarded::Atom(
            crate::guarded::lift_free_atom(&ProtoAtom::EqE(left, right)),
        ));
        ProofMethod::Simplify
    };
    let cases = exec_proof_method(&ctx, &method, &sys)?.expect("method applies");
    assert!(!cases.is_empty(), "the healthy method has branches");
    Ok(())
}

/// Matches a restriction guard (`A(x ∪ y) @ t`, or `x ∪ y = a ∪ b`) against
/// the action `A(a ∪ b)`.  Healthy, the body is instantiated once.
fn backend_guard_match(backend: &Backend, action: bool) -> Result<(), ProveError> {
    use crate::atom::ProtoAtom;
    use crate::constraint::system::System;
    use crate::fact::{proto_fact, Multiplicity};
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::var_term;

    let h = backend.maude(tamarin_term::maude_sig::mset_maude_sig());
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let t = LVar::new("t", LSort::Node, 0);
    let union = |a, b| {
        Term::App(
            FunSym::Ac(AcSym::Union),
            vec![var_term(a), var_term(b)].into(),
        )
    };
    let pattern = union(x, y);
    let subject = union(LVar::new("a", LSort::Msg, 0), LVar::new("b", LSort::Msg, 0));
    let fact = |term| proto_fact(Multiplicity::Linear, "A", vec![term]);
    let guard = if action {
        ProtoAtom::Action(var_term(t), fact(pattern))
    } else {
        ProtoAtom::EqE(pattern, subject.clone())
    };
    let subject_fact = fact(subject);
    let actions = vec![(LVar::new("i", LSort::Node, 0), &subject_fact)];
    let mut by_tag = tamarin_utils::FastMap::default();
    by_tag.insert(subject_fact.tag, vec![0]);
    let mut out = Vec::new();
    crate::constraint::solver::simplify::try_match_all_guards(
        &h,
        &[x, y, t],
        &[&guard],
        &actions,
        &by_tag,
        &crate::guarded::gfalse(),
        &System::empty(),
        &[],
        &mut out,
    )?;
    assert_eq!(out, vec![crate::guarded::gfalse()]);
    Ok(())
}

/// S_fresh-order asks whether the node consuming `~x` unifies with the
/// supplier's successor.  HS runs that unifier purely, so a failed backend
/// aborts the pass; reading the failure as "unifiable" would silently
/// weaken the system instead.
fn backend_fresh_ordering(backend: &Backend) -> Result<(), ProveError> {
    use crate::constraint::constraints::Edge;
    use crate::constraint::solver::reduction::{Reduction, SystemOutcome};
    use crate::constraint::system::System;
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{
        ConcIdx, PremIdx, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
    };
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    let ctx = backend.context(tamarin_term::maude_sig::dh_maude_sig(), Default::default());
    let term = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let fresh = term("x", LSort::Fresh);
    let message = tamarin_term::builtin::mult(term("m", LSort::Msg), term("n", LSort::Msg));
    let containing_fresh = tamarin_term::builtin::mult(fresh.clone(), term("z", LSort::Msg));
    let fact = |term| Fact::new(FactTag::Proto(Multiplicity::Linear, "P", 1), vec![term]);
    let rule = |name, prems, concs| {
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(name),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            prems,
            concs,
            Vec::new(),
        )
    };
    let supplier = LVar::new("supplier", LSort::Node, 0);
    let successor = LVar::new("successor", LSort::Node, 0);
    let consumer = LVar::new("consumer", LSort::Node, 0);
    let mut sys = System::empty();
    sys.add_node(
        supplier,
        rule(
            "Init",
            vec![Fact::new(FactTag::Fresh, vec![fresh.clone()])],
            vec![fact(fresh.clone())],
        ),
    );
    let mut consumer_rule = rule(
        "Step",
        vec![fact(containing_fresh.clone())],
        vec![fact(containing_fresh)],
    );
    consumer_rule.actions.push(fact(fresh));
    sys.add_node(
        successor,
        rule("Step", vec![fact(message.clone())], vec![fact(message)]),
    );
    sys.add_node(consumer, consumer_rule);
    sys.add_edge(Edge {
        src: (supplier, ConcIdx(0)),
        tgt: (successor, PremIdx(0)),
    });
    let mut red = Reduction::new(&ctx, sys);
    let outcome = crate::constraint::solver::simplify::enforce_fresh_ordering_pass(&mut red)?;
    assert!(matches!(outcome, SystemOutcome::Linear));
    Ok(())
}

/// `x ∪ y` over two message variables, an AC term only Maude unifies.
fn msg_union(x: &'static str, y: &'static str) -> tamarin_term::lterm::LNTerm {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    tamarin_term::term::Term::App(
        FunSym::Ac(AcSym::Union),
        vec![
            var_term(LVar::new(x, LSort::Msg, 0)),
            var_term(LVar::new(y, LSort::Msg, 0)),
        ]
        .into(),
    )
}

/// A protocol-rule instance named `name` with no actions.
fn backend_rule(
    name: &'static str,
    premises: Vec<crate::fact::LNFact>,
    conclusions: Vec<crate::fact::LNFact>,
) -> crate::rule::RuleACInst {
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
    Rule::new(
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand(name),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        }),
        premises,
        conclusions,
        Vec::new(),
    )
}

/// The injective-fact ordering asks whether the supplier of an injective
/// `St` fact and an earlier node holding the same fact are instances of one
/// rule that unify.  Healthy, they do, so no ordering is added.
fn backend_injective_facts(backend: &Backend) -> Result<(), ProveError> {
    use crate::constraint::constraints::{Edge, LessAtom, Reason};
    use crate::constraint::solver::reduction::Reduction;
    use crate::constraint::system::System;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ConcIdx, PremIdx};
    use tamarin_term::lterm::{LSort, LVar};

    let state = proto_fact(
        Multiplicity::Linear,
        "St",
        vec![tamarin_term::builtin::msg_var("t", 0)],
    );
    let ctx = backend.context(
        tamarin_term::maude_sig::mset_maude_sig(),
        crate::constraint::solver::context::ProofContextOptions {
            forced_injective_facts: [state.tag].into(),
            ..Default::default()
        },
    );
    let input = |term| proto_fact(Multiplicity::Linear, "A", vec![term]);
    let supplier = LVar::new("supplier", LSort::Node, 0);
    let earlier = LVar::new("earlier", LSort::Node, 0);
    let consumer = LVar::new("consumer", LSort::Node, 0);
    let mut sys = System::empty();
    sys.add_node(
        supplier,
        backend_rule("R", vec![input(msg_union("a", "b"))], vec![state.clone()]),
    );
    sys.add_node(
        earlier,
        backend_rule("R", vec![input(msg_union("x", "y"))], vec![state.clone()]),
    );
    sys.add_node(consumer, backend_rule("Use", vec![state], Vec::new()));
    sys.add_edge(Edge {
        src: (supplier, ConcIdx(0)),
        tgt: (consumer, PremIdx(0)),
    });
    sys.add_less(LessAtom::new(earlier, consumer, Reason::Formula));
    let mut red = Reduction::new(&ctx, sys);
    let before = red.sys.clone();
    crate::constraint::solver::simplify::add_non_injective_fact_instances(&mut red)?;
    assert!(red.sys == before, "unifiable instances are not ordered");
    Ok(())
}

/// Formula-atom evaluation asks whether the two sides of each equality
/// unify.  Healthy, both AC equalities do, so the disjunction is unknown
/// and stays.
fn backend_formula_atoms(backend: &Backend) -> Result<(), ProveError> {
    use crate::atom::ProtoAtom;
    use crate::constraint::solver::reduction::{Reduction, SystemOutcome};
    use crate::constraint::system::System;
    use crate::guarded::{gdisj, lift_free_atom, Guarded};

    let ctx = backend.context(
        tamarin_term::maude_sig::mset_maude_sig(),
        Default::default(),
    );
    let eq = |l, r| Guarded::Atom(lift_free_atom(&ProtoAtom::EqE(l, r)));
    let mut sys = System::empty();
    sys.insert_formula(gdisj(vec![
        eq(msg_union("a", "b"), msg_union("x", "y")),
        eq(msg_union("a", "x"), msg_union("b", "y")),
    ]));
    let mut red = Reduction::new(&ctx, sys);
    let outcome = crate::constraint::solver::simplify::eval_formula_atoms_pass(&mut red)?;
    assert!(matches!(outcome, SystemOutcome::Linear));
    Ok(())
}

/// Loop-breaker annotation draws an edge from a conclusion to a premise
/// only when the two facts unify.  Healthy, `A(a ∪ b)` feeds `A(x ∪ y)`
/// and the acyclic pair gets no breaker.
fn backend_loop_breakers(backend: &Backend) -> Result<(), ProveError> {
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use crate::theory::OpenProtoRule;

    let h = backend.maude(tamarin_term::maude_sig::mset_maude_sig());
    let fact = |term| proto_fact(Multiplicity::Linear, "A", vec![term]);
    let rule = |name, premises, conclusions| {
        OpenProtoRule::new(Rule::new(
            ProtoRuleEInfo::standard(name),
            premises,
            conclusions,
            Vec::new(),
        ))
    };
    let mut rules = [
        rule("Send", Vec::new(), vec![fact(msg_union("a", "b"))]),
        rule("Recv", vec![fact(msg_union("x", "y"))], Vec::new()),
    ];
    crate::constraint::solver::context::annotate_loop_breakers(
        &mut rules.iter_mut().collect::<Vec<_>>(),
        &h,
    )
    .map_err(|error| ProveError::maude("loop breakers", error))?;
    assert!(rules.iter().all(|r| r.loop_breakers.is_empty()));
    Ok(())
}

/// Under `xorr(x, x) = zeroo`, whether `xorr(~k, ~k)` is in normal form
/// (in the system, or once a substitution renames `~k`) takes a Maude AC
/// match.  Healthy, the term is found reducible.
fn backend_normal_forms(backend: &Backend, subst: bool) -> Result<(), ProveError> {
    use crate::tools::equation_store::{LNSubst, LNSubstVFresh};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;

    let ctx = backend.context(xorr_maude_sig(), Default::default());
    let sys = xorr_contradiction_system();
    let non_normal = if subst {
        let renaming = LNSubstVFresh::from_list([(
            LVar::new("k", LSort::Fresh, 0),
            var_term(LVar::new("m", LSort::Fresh, 0)),
        )]);
        crate::constraint::solver::contradictions::SubstNfChecker::new(&ctx.maude, &sys)
            .check(&LNSubst::empty(), &renaming)
            .map_err(|error| ProveError::maude("normal forms", error))?
    } else {
        crate::constraint::solver::contradictions::contradictions(&ctx, &sys)?
            .contains(&crate::constraint::solver::contradictions::Contradiction::NonNormalTerms)
    };
    assert!(non_normal);
    Ok(())
}

/// Assembling the intruder rules computes the variants of the destructor
/// of `g(f(x)) = x`.  Healthy, the cache is built.
fn backend_intruder_rules(backend: &Backend) -> Result<(), ProveError> {
    let theory = elaborated(
        &tamarin_parser::parse_theory(
            "theory T begin\n\
             functions: f/1, g/1\n\
             equations: g(f(x)) = x\n\
             end",
            &[],
        )
        .unwrap(),
    );
    let h = backend.maude(theory.signature);
    let checked =
        crate::close_rule::check_close_intr_rule(&h, None, false, &[], Default::default())?;
    assert!(!checked.cache.is_empty());
    Ok(())
}

/// A smart oracle ranks goals over lazily materialised sources.  When the
/// materialisation fails, that error is reported before the (missing)
/// oracle is launched.  Healthy, ranking reaches the oracle launch.
fn backend_oracle_sources(backend: &Backend) -> Result<(), ProveError> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::goals::{rank_goals_with, GoalRanking};
    use crate::constraint::solver::sources::Source;
    use crate::constraint::system::System;
    use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
    use tamarin_term::lterm::{pub_term, LSort, LVar};
    use tamarin_term::term::Term;

    let mut ctx = ProofContext::new(backend.healthy(pair_maude_sig()), Vec::new());
    let f = FunSym::NoEq(NoEqSym::new(
        b"f".to_vec(),
        1,
        Privacy::Public,
        Constructability::Constructor,
    ));
    let term = Term::App(f, vec![pub_term("x")].into());
    let goal = Goal::Action(LVar::new("i", LSort::Node, 0), crate::fact::ku_fact(term));
    ctx.full_sources = std::sync::Arc::new(vec![Source::lazy(goal.clone())]);
    backend.sources(&mut ctx);
    ctx.heuristic = Some(vec![GoalRanking::OracleSmart {
        quit_on_empty: false,
        oracle_path: "/definitely/missing/oracle".into(),
    }]);
    let mut sys = System::empty();
    sys.add_goal(goal);
    match rank_goals_with(&sys, &ctx, 0) {
        Err(ProveError::Guarded(message)) if message == "bad source" => {
            Err(ProveError::Guarded(message))
        }
        other => {
            assert!(!backend.failed, "{other:?}");
            Ok(())
        }
    }
}

/// A session materialises its raw and refined sources on its template
/// process.  With that process dead, both kinds fail on every request
/// (nothing is cached) and the statistics report the failure.  A lemma
/// assigned another, live process can still force the sources.
fn backend_session_sources(backend: &Backend) -> Result<(), ProveError> {
    let source = "theory T begin\n\
        builtins: multiset\n\
        rule R: [In(<x,y,z,w>)] --[A(x,y,z,w)]-> [F(x)]\n\
        restriction Eq: \"All x y z w #i. A(x,y,z,w) @i ==> x ++ y = z ++ w\"\n\
        lemma goal: \"Ex x y z w #i. A(x,y,z,w) @i\"\n\
        end";
    let theory = elaborated(&tamarin_parser::parse_theory(source, &[]).unwrap());
    let maude = backend.healthy(theory.signature.clone());
    let closed = closed(theory.clone(), &maude);
    let mut session = ProverSession::build(&closed, maude, ProverSessionOptions::default())?;
    // Preparation also queries Maude: replace its warmed handle so that
    // materialisation must consult the row's backend rather than that cache.
    std::sync::Arc::get_mut(&mut session.template_ctx)
        .unwrap()
        .maude = backend.maude(theory.signature.clone());
    let mut results = Vec::new();
    for kind in [SourceKind::RawSources, SourceKind::RefinedSources] {
        for _ in 0..2 {
            results.push(session.context_for_sources(kind).map(drop));
        }
    }
    if !backend.failed {
        return results.into_iter().collect();
    }
    assert!(
        results
            .iter()
            .all(|r| matches!(r, Err(ProveError::Maude(_)))),
        "every request fails: a failure is never cached"
    );
    let stats = session.source_stats();
    assert!(matches!(stats.raw, Err(ProveError::Maude(_))));
    assert!(matches!(stats.refined, Err(ProveError::Maude(_))));
    assert!(session.source_cache.is_empty());
    let assigned = backend.healthy(theory.signature.clone());
    let (ctx, _) = lemma_context_and_system(
        &session,
        session.lemma_and_prepared("goal").unwrap(),
        &assigned,
    )?;
    ctx.ensure_saturated()?;
    results.swap_remove(0)
}

/// The derivation check and auto-sources each run scratch proofs that query
/// Maude for the variants of a rule with a `fst` premise.  Healthy, the
/// rule raises no warning and gains no sources.
fn backend_scratch_check(backend: &Backend, derivation: bool) -> Result<(), ProveError> {
    use crate::constraint::solver::sources::IntegerParameters;
    let theory = elaborated(
        &tamarin_parser::parse_theory(
            "theory T begin rule R: [In(x), In(fst(x))] --> [F(x)] end",
            &[],
        )
        .unwrap(),
    );
    let h = backend.maude(theory.signature.clone());
    if derivation {
        let timeout = crate::deriv_check::DerivCheckTimeout::Secs(
            std::num::NonZeroU32::new(1).expect("nonzero"),
        );
        let warnings = crate::deriv_check::check_message_derivation(
            &theory,
            &h,
            None,
            timeout,
            None,
            IntegerParameters::default(),
        )?;
        assert!(warnings.is_empty());
    } else {
        let changed = crate::auto_sources::apply_auto_sources(
            &mut theory.clone(),
            h,
            None,
            None,
            IntegerParameters::default(),
        )?;
        assert!(!changed);
    }
    Ok(())
}

/// The NDC check unifies the destructor variants of a user AC symbol with
/// a non-subterm equation (`xorr(x, x) = zeroo`).  A failed check draws no
/// fresh name.  The healthy check of this signature saturates for half a
/// minute in a debug build (csf26-ac/fast/KCL07 runs it under rs_ref), so
/// only the failure is run here.
fn backend_ndc_check(backend: &Backend) -> Result<(), ProveError> {
    if !backend.failed {
        return Ok(());
    }
    let theory = elaborated(
        &tamarin_parser::parse_theory(
            "theory T begin\n\
             functions: xorr/2 [AC], zeroo/0\n\
             equations: xorr(xorr(x, y), x) = y, xorr(x, x) = zeroo, xorr(x, zeroo) = x\n\
             end",
            &[],
        )
        .unwrap(),
    );
    let sig = theory.signature;
    let rules = crate::constraint::solver::context::ProofContext::assemble_intruder_rules(
        &sig,
        &backend.healthy(sig.clone()),
        &[],
    )
    .unwrap();
    let h = backend.maude(sig);
    crate::close_rule::pretty_ndc_check(&h, None, rules, Default::default()).map(drop)
}
