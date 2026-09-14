use super::*;
use tamarin_term::maude_sig::pair_maude_sig;

use tamarin_test_support::require_maude_path;

/// This function returns `None` only when [`maude_path`] resolves nothing.
/// That case is the documented `TAM_ALLOW_NO_MAUDE` skip.  A maude that
/// resolves but does not start is the same misconfiguration as a dangling
/// `MAUDE_PATH`, so this function panics for it.  A `.ok()?` here would
/// hide that error and skip every maude-backed test in this file.
fn ctx() -> Option<ProofContext> {
    let path = require_maude_path()?;
    let h =
        tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 test here would otherwise skip silently"
            )
        });
    Some(ProofContext::new(h, Vec::new()))
}

#[test]
fn deep_terms_survive_search_stack_growth() {
    check_deep_terms_in_search(false, false);
}

#[test]
fn deep_dh_terms_survive_search_stack_growth() {
    check_deep_terms_in_search(true, false);
}

#[test]
fn deep_binding_images_survive_search_stack_growth() {
    check_deep_terms_in_search(false, true);
}

fn check_deep_terms_in_search(dh: bool, whole_image: bool) {
    let Some(path) = require_maude_path() else {
        return;
    };
    tamarin_test_support::on_stack(256 * 1024, move || {
        use crate::fact::{Fact, FactTag};
        use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo};
        use tamarin_term::lterm::{BVar, LSort, LVar};
        let sig = tamarin_term::maude_sig::hash_maude_sig();
        let sig = if dh {
            sig.merge(tamarin_term::maude_sig::dh_maude_sig())
        } else {
            sig
        };
        let maude = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).unwrap();
        let mut ctx = ProofContext::new(maude, vec![]);
        ctx.cut = CutStrategy::SeqDfs;
        let mut left = tamarin_term::builtin::msg_var("x", 0);
        let mut right = tamarin_term::builtin::msg_var("y", 1);
        for _ in 0..8192 {
            left = tamarin_term::term::f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![left]);
            right = tamarin_term::term::f_app_no_eq(tamarin_term::builtin::hash_sym(), vec![right]);
        }
        if dh {
            left = tamarin_term::builtin::exp(left, tamarin_term::builtin::msg_var("z", 2));
            right = tamarin_term::builtin::exp(right, tamarin_term::builtin::msg_var("z", 2));
        }
        if whole_image {
            // Bind a variable to the entire deep image, rather than
            // descending matching shells and binding shallow leaves.
            left = tamarin_term::builtin::msg_var("x", 0);
        }
        for preceding in [0, 128] {
            let mut sys = System::empty();
            sys.add_node(
                LVar::new("i", LSort::Node, 0),
                Rule::new(
                    RuleInfo::Proto(ProtoRuleACInstInfo {
                        name: ProtoRuleName::Stand("Test"),
                        attributes: RuleAttributes::empty(),
                        loop_breakers: vec![],
                    }),
                    vec![],
                    vec![Fact::new(FactTag::Kd, vec![left.clone()])],
                    vec![],
                ),
            );
            sys.solved_formulas_mut()
                .push(std::sync::Arc::new(crate::guarded::gtrue()));
            for i in 0..preceding {
                let term = tamarin_term::lterm::pub_term(format!("prefix_{i:04}"));
                sys.add_goal(crate::constraint::constraints::Goal::Disj(
                    crate::constraint::constraints::Disj::new(vec![crate::guarded::Guarded::Atom(
                        crate::atom::ProtoAtom::EqE(term.clone(), term),
                    )]),
                ));
            }
            let lift = |term: &tamarin_term::lterm::LNTerm| {
                tamarin_term::term::map_lits(term, &mut |lit| match lit {
                    tamarin_term::vterm::Lit::Con(c) => tamarin_term::vterm::Lit::Con(*c),
                    tamarin_term::vterm::Lit::Var(v) => {
                        tamarin_term::vterm::Lit::Var(BVar::Free(*v))
                    }
                })
            };
            sys.add_goal(crate::constraint::constraints::Goal::Disj(
                crate::constraint::constraints::Disj::new(vec![crate::guarded::Guarded::Atom(
                    crate::atom::ProtoAtom::EqE(lift(&left), lift(&right)),
                )]),
            ));
            let result = run_proof_search(&ctx, sys, usize::MAX).unwrap();
            assert_eq!(result.status, NodeStatus::Solved);
            let mut depth = 0;
            let mut node = &result;
            while let Some(child) = node.children.values().next() {
                depth += 1;
                node = child;
            }
            assert!(depth >= preceding);
        }
    });
}

#[test]
fn deep_search_uses_guarded_stack() {
    let Some(mut ctx) = ctx() else { return };
    tamarin_test_support::on_stack(256 * 1024, move || {
        let depth: usize = std::env::var("TAM_TEST_SEARCH_DEPTH")
            .ok()
            .map(|s| s.parse().unwrap())
            .unwrap_or(256);
        let mut sys = System::empty();
        sys.solved_formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        for i in 0..depth {
            let term = tamarin_term::lterm::pub_term(format!("goal_{i:05}"));
            sys.add_goal(crate::constraint::constraints::Goal::Disj(
                crate::constraint::constraints::Disj::new(vec![crate::guarded::Guarded::Atom(
                    crate::atom::ProtoAtom::EqE(term.clone(), term),
                )]),
            ));
        }
        let cuts = if std::env::var_os("TAM_TEST_SEARCH_SERIAL_ONLY").is_some() {
            vec![CutStrategy::SeqDfs]
        } else {
            vec![
                CutStrategy::SeqDfs,
                CutStrategy::Dfs,
                CutStrategy::Bfs,
                CutStrategy::Nothing,
                CutStrategy::AfterSorry,
            ]
        };
        for cut in cuts {
            ctx.cut = cut;
            let result = run_proof_search(&ctx, sys.clone(), usize::MAX).unwrap();
            assert_eq!(result.status, NodeStatus::Solved);
            let mut count = 0;
            let mut current = &result;
            while !current.children.is_empty() {
                assert_eq!(current.children.len(), 1);
                assert!(current.annotated);
                if matches!(current.method, ProofMethod::SolveGoal(_)) {
                    count += 1;
                }
                current = current.children.values().next().unwrap();
            }
            assert_eq!(count, depth);
            assert_eq!(current.method, ProofMethod::Finished(MethodResult::Solved));
        }
        ctx.cut = CutStrategy::Dfs;
        let bound = depth / 2;
        let bounded = run_proof_search(&ctx, sys, bound).unwrap();
        assert_eq!(bounded.status, NodeStatus::Sorry);
        let mut leaf = &bounded;
        for _ in 0..bound {
            assert_eq!(leaf.children.len(), 1);
            leaf = leaf.children.values().next().unwrap();
        }
        assert_eq!(
            leaf.method,
            ProofMethod::Sorry(Some(format!("bound {bound} hit")))
        );
        assert!(leaf.children.is_empty());
    });
}

#[test]
fn deep_frontier_and_cut_walks_use_guarded_stack() {
    let Some(ctx) = ctx() else { return };
    tamarin_test_support::on_stack(256 * 1024, move || {
        let depth = 8192;
        let mut sys = System::empty();
        sys.solved_formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        let mut root = open_node(sys);
        root.method = ProofMethod::Sorry(Some("depth limit".into()));
        root.status = NodeStatus::Sorry;
        for _ in 0..depth {
            let mut parent = open_node(System::default());
            parent.method = ProofMethod::Simplify;
            parent.status = NodeStatus::Sorry;
            parent.children.insert("next".into(), root);
            root = parent;
        }
        let mut budget = usize::MAX;
        let deadline = proof_deadline();
        re_expand_depth_limited(&ctx, &mut root, &mut budget, &deadline, 0).unwrap();
        assert_eq!(root.status, NodeStatus::Solved);
        let (mut found, mut incomplete) = (false, false);
        assert!(bfs_check_level(&root, depth, &mut found, &mut incomplete, false).is_none());
        assert!(found && !incomplete);
        let mut cut = bfs_check_level(&root, depth, &mut false, &mut false, true).unwrap();
        extract_solved_path(&mut cut);
        let mut node = &cut;
        for _ in 0..depth {
            assert_eq!(node.children.len(), 1);
            assert_eq!(node.status, NodeStatus::Solved);
            node = &node.children["next"];
        }
        assert_eq!(node.method, ProofMethod::Finished(MethodResult::Solved));
    });
}

#[test]
fn bfs_cut_preserves_case_order_and_status_threading() {
    let stub = || {
        let mut node = open_node(System::default());
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.status = NodeStatus::Sorry;
        node
    };
    let mut solved = open_node(System::default());
    solved.method = ProofMethod::Finished(MethodResult::Solved);
    solved.status = NodeStatus::Solved;
    let mut root = open_node(System::default());
    let mut pending = stub();
    // BFS recognizes the method marker independently of cached status.
    pending.status = NodeStatus::Open;
    root.children = BTreeMap::from([
        ("a".into(), stub()),
        ("b".into(), solved),
        ("c".into(), pending),
    ]);
    let (mut found, mut incomplete) = (false, false);
    let cut = bfs_check_level(&root, 1, &mut found, &mut incomplete, true).unwrap();
    assert!(found && incomplete);
    assert_eq!(cut.status, NodeStatus::Solved);
    assert_eq!(
        cut.children["a"].method,
        ProofMethod::Sorry(Some("bound reached".into()))
    );
    assert_eq!(
        cut.children["b"].method,
        ProofMethod::Finished(MethodResult::Solved)
    );
    assert_eq!(
        cut.children["c"].method,
        ProofMethod::Sorry(Some("ignored (attack exists)".into()))
    );
}

#[test]
fn expansion_restores_partial_root_after_child_error() {
    let Some(mut ctx) = ctx() else { return };
    ctx.cut = CutStrategy::SeqDfs;
    ctx.heuristic = Some(vec![
        crate::constraint::solver::goals::GoalRanking::Smart(false),
        crate::constraint::solver::goals::GoalRanking::Tactic {
            quit_on_empty: false,
            tactic: std::sync::Arc::new(crate::tactic::Tactic {
                name: "missing".into(),
                presort: 's',
                prios: Vec::new(),
                deprios: Vec::new(),
            }),
            resolution_error: Some(std::sync::Arc::from("child ranking failure")),
        },
    ]);
    let mut sys = System::empty();
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    for name in ["a", "b"] {
        let term = tamarin_term::lterm::pub_term(name);
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(vec![crate::guarded::Guarded::Atom(
                crate::atom::ProtoAtom::EqE(term.clone(), term),
            )]),
        ));
    }
    let mut root = open_node(sys);
    let path = crate::constraint::solver::trace::case_path_snapshot();
    let mut budget = usize::MAX;
    let error = expand(&ctx, &mut root, &mut budget, &proof_deadline(), 0).unwrap_err();
    assert!(format!("{error:?}").contains("child ranking failure"));
    assert!(matches!(root.method, ProofMethod::SolveGoal(_)));
    assert_eq!(root.sys.goals.len(), 2);
    assert!(
        root.children.is_empty(),
        "the failed child was never inserted"
    );
    assert_eq!(crate::constraint::solver::trace::case_path_snapshot(), path);
}

/// The per-child fan-out (`expand_children`) converts terms on rayon
/// worker threads.  The converter answers from the signature it is
/// handed, which the workers share with the caller, so a declared 0-arity
/// symbol is the same application on every thread.
#[test]
fn a_worker_thread_converts_a_nullary_symbol_the_same_way() {
    use rayon::prelude::*;

    let thy = tamarin_parser::parse_theory(
        "theory T begin\n\
         functions: true/0\n\
         rule R: [ ] --> [ Out(true) ]\n\
         end",
        &[],
    )
    .expect("parses");
    let msig = crate::elaborate::elaborate(&thy)
        .expect("elaborates")
        .signature;
    let term = thy
        .items
        .iter()
        .find_map(|i| match i {
            tamarin_parser::ast::TheoryItem::Rule(r) => Some(r.conclusions[0].args[0].clone()),
            _ => None,
        })
        .expect("rule present");

    let on_caller = crate::elaborate::term_to_lnterm(&term, &msig).expect("converts");
    assert!(
        matches!(&on_caller, tamarin_term::term::Term::App(_, args) if args.is_empty()),
        "`true` is a 0-arity application, not a variable: {on_caller:?}"
    );
    let on_workers: Vec<_> = (0..64)
        .into_par_iter()
        .map(|_| crate::elaborate::term_to_lnterm(&term, &msig).expect("converts"))
        .collect();
    assert!(on_workers.iter().all(|t| *t == on_caller));
}

#[test]
fn fallible_searches_do_not_fan_out_siblings() {
    #[derive(Debug)]
    struct FallibleProvider;

    impl crate::constraint::solver::context::SourceProvider for FallibleProvider {
        fn may_fail(&self) -> bool {
            true
        }

        fn materialize(&self, _ctx: &ProofContext) -> Result<(), crate::prove::ProveError> {
            Ok(())
        }
    }

    let Some(mut parallel_ctx) = ctx() else {
        return;
    };
    parallel_ctx.cut = CutStrategy::Dfs;
    parallel_ctx.is_exists_trace = false;
    assert!(should_parallel_expand(&parallel_ctx, 2, 0, false));

    parallel_ctx.set_source_provider(std::sync::Arc::new(FallibleProvider));
    assert!(!should_parallel_expand(&parallel_ctx, 2, 0, false));

    let Some(mut ctx) = ctx() else { return };
    ctx.cut = CutStrategy::Dfs;
    ctx.is_exists_trace = false;
    ctx.heuristic = Some(vec![
        crate::constraint::solver::goals::GoalRanking::Smart(false),
        crate::constraint::solver::goals::GoalRanking::Oracle {
            quit_on_empty: false,
            oracle_path: "oracle".into(),
        },
    ]);
    assert!(!should_parallel_expand(&ctx, 2, 0, false));
}

#[test]
fn search_empty_system_with_a_node_solves_immediately() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    // Force out of initial state by adding a node, then no goals
    // / subterms remain.
    use crate::rule::{
        IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst, RuleAttributes,
        RuleInfo,
    };
    let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
        RuleInfo::Proto(ProtoRuleACInstInfo {
            name: ProtoRuleName::Stand("Test"),
            attributes: RuleAttributes::empty(),
            loop_breakers: Vec::new(),
        });
    let rule: RuleACInst = Rule::new(info, Vec::new(), Vec::new(), Vec::new());
    let mut sys = System::empty();
    // Mark non-initial via a solved formula (Haskell's
    // `isInitialSystem` uses solved_formulas emptiness, not the
    // node/edge count).
    sys.solved_formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    sys.add_node(
        tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0),
        rule,
    );
    let root = run_proof_search(&ctx, sys, 10).expect("default ranking");
    assert_eq!(root.status, NodeStatus::Solved);
    // `expand_inner` consults `is_finished` before it tries `simplify`.
    // A system that is already finished therefore becomes the terminal
    // node itself.  It does not become a `Simplify` with a Solved child.
    assert_eq!(root.method, ProofMethod::Finished(MethodResult::Solved));
    assert!(root.children.is_empty());
}

#[test]
fn search_empty_disj_goal_closes_contradictory() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    // Force out of initial state.
    sys.add_less(crate::constraint::constraints::LessAtom::new(
        tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
        tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
        crate::constraint::constraints::Reason::Fresh,
    ));
    // An empty disjunction comes hand-in-hand with `gfalse` in the
    // formula set (insert_formula pushes both).  That's
    // also how Haskell signals contradictoryness — `openGoals`
    // filters `DisjG (Disj [])` and `FormulasFalse` fires from
    // `contradictions`.  We mirror exactly that here.
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gfalse()));
    sys.add_goal(crate::constraint::constraints::Goal::Disj(
        crate::constraint::constraints::Disj::new(Vec::new()),
    ));
    let root = run_proof_search(&ctx, sys, 5).expect("default ranking");
    assert_eq!(root.status, NodeStatus::Contradictory);
    // The root is the contradiction itself.  It is not a `SolveGoal` on
    // the empty disjunction.  `is_open_in_sys` drops `DisjG (Disj [])`, so
    // the search has no goal to pick.  It closes on `FormulasFalse` with
    // no children.
    assert_eq!(
        root.method,
        ProofMethod::Finished(MethodResult::Contradictory(Some(
            crate::constraint::solver::contradictions::Contradiction::FormulasFalse
        )))
    );
    assert!(root.children.is_empty());
}

#[test]
fn search_disj_goal_with_two_branches_lazy_early_break_on_solved() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    // Force out of initial state.
    sys.add_less(crate::constraint::constraints::LessAtom::new(
        tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
        tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
        crate::constraint::constraints::Reason::Fresh,
    ));
    // Add a 2-branch disjunction goal — true | false.
    // Haskell's lazy Disj-monad early-breaks once any branch
    // returns TraceFound (Solved).  The gtrue branch Solves
    // immediately, so the gfalse branch is never forced.
    // Our search mirrors this: only 1 child rendered.
    let f1 = crate::guarded::gtrue();
    let f2 = crate::guarded::gfalse();
    sys.add_goal(crate::constraint::constraints::Goal::Disj(
        crate::constraint::constraints::Disj::new(vec![f1, f2]),
    ));
    let root = run_proof_search(&ctx, sys, 10).expect("default ranking");
    assert!(matches!(
        root.method,
        ProofMethod::SolveGoal(crate::constraint::constraints::Goal::Disj(_))
    ));
    // Lazy early-break: only the first-Solved branch is rendered.
    assert_eq!(root.children.len(), 1);
    assert_eq!(root.status, NodeStatus::Solved);
}

/// This system holds only trivially-true formulas.  `simplify` clears them
/// with `dedupe_formulas_pass` and then
/// `drop_trivially_true_formulas_pass`, and the child then closes as
/// Solved.  A `simplify` that leaves the formulas in place never finishes
/// the search, and the search returns `Sorry`.
#[test]
fn search_simplify_drops_trivially_true_formulas_then_solves() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    // Force out of initial state.
    sys.add_less(crate::constraint::constraints::LessAtom::new(
        tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
        tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
        crate::constraint::constraints::Reason::Fresh,
    ));
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    sys.formulas_mut()
        .push(std::sync::Arc::new(crate::guarded::gtrue()));
    let root = run_proof_search(&ctx, sys, 5).expect("default ranking");
    assert_eq!(root.status, NodeStatus::Solved);
    // There is one `simplify` step, and its single child is the Solved
    // leaf.  The simplified system no longer holds the trivially-true
    // formulas.  That removal turns a system that cannot otherwise finish
    // into a Solved one.
    assert_eq!(root.method, ProofMethod::Simplify);
    assert_eq!(root.children.len(), 1);
    let (name, leaf) = root.children.iter().next().unwrap();
    assert_eq!(name, "");
    assert_eq!(leaf.method, ProofMethod::Finished(MethodResult::Solved));
    assert!(leaf.sys.formulas.is_empty());
}

/// `--bound=N` is HS `boundProofDepth`.  Every node at depth `N` becomes
/// `sorry (Just "bound N hit")`.  This stub is final.  It is not a
/// `depth limit` thunk, so `is_depth_limited` rejects it.  Otherwise the
/// ID-DFS loop keeps doubling `MAX_DEPTH` against a frontier that can
/// never move.
#[test]
fn search_runs_out_of_budget_returns_sorry() {
    let ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    let mut sys = System::empty();
    let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
    let v2 = tamarin_term::lterm::LVar::new("y", tamarin_term::lterm::LSort::Msg, 0);
    use tamarin_term::vterm::Lit;
    let tx: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v));
    let ty: tamarin_term::lterm::LNTerm = tamarin_term::term::Term::Lit(Lit::Var(v2));
    // The context has no rules, so it can never solve this Action goal.
    // The search continues without end if the bound does not cut it.
    let i = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
    let f = crate::fact::out_fact(tx);
    sys.add_goal(crate::constraint::constraints::Goal::Action(i, f));
    // Add a non-empty piece so isInitialSystem returns false.
    sys.subterm_store_mut().add(ty.clone(), ty);
    let root = run_proof_search(&ctx, sys, 1).expect("default ranking");
    // Depth 0 is the root's own `simplify`.  Depth 1 is the cut.
    assert_eq!(root.method, ProofMethod::Simplify);
    assert_eq!(root.status, NodeStatus::Sorry);
    assert_eq!(root.children.len(), 1);
    let (name, cut) = root.children.iter().next().unwrap();
    assert_eq!(name, "");
    assert_eq!(cut.method, ProofMethod::Sorry(Some("bound 1 hit".into())));
    assert_eq!(cut.status, NodeStatus::Sorry);
    assert!(cut.children.is_empty());
    assert!(
        !is_depth_limited(cut),
        "a bound-sorry must not be re-expandable as a depth-limit thunk"
    );
}

#[test]
fn proof_bound_does_not_rank_the_cut_node() {
    let mut ctx = match ctx() {
        Some(c) => c,
        None => return,
    };
    ctx.heuristic = Some(vec![
        crate::constraint::solver::goals::GoalRanking::Tactic {
            quit_on_empty: false,
            tactic: std::sync::Arc::new(crate::tactic::Tactic {
                name: "missing".into(),
                presort: 's',
                prios: Vec::new(),
                deprios: Vec::new(),
            }),
            resolution_error: Some(std::sync::Arc::from("must not be evaluated")),
        },
    ]);
    let root = run_proof_search_at_depth(&ctx, System::empty(), 0, 0)
        .expect("a bound-cut node never invokes its ranking");
    assert_eq!(root.method, ProofMethod::Sorry(Some("bound 0 hit".into())));
}

// --- `solved_systems` (HS `proofSystems`) + solved-sys retention ----
//
// Maude-free: these drive hand-built proof trees and the pure
// `drop_sys_after_expand` predicate, so they run unconditionally.

/// A `System` tagged with `id` recoverable by [`sys_tag`], so a walk
/// result can be matched to the node it came from.
fn tagged_sys(id: usize) -> System {
    let mut sys = System::empty();
    for _ in 0..id {
        sys.solved_formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
    }
    sys
}

fn sys_tag(sys: &System) -> usize {
    sys.solved_formulas.len()
}

fn node(
    method: ProofMethod,
    id: usize,
    children: Vec<(&str, ProofNode)>,
    annotated: bool,
) -> ProofNode {
    ProofNode {
        method,
        sys: tagged_sys(id),
        children: children
            .into_iter()
            .map(|(n, c)| (n.to_string(), c))
            .collect(),
        status: NodeStatus::Solved,
        annotated,
    }
}

fn solved(id: usize) -> ProofNode {
    node(
        ProofMethod::Finished(MethodResult::Solved),
        id,
        Vec::new(),
        true,
    )
}

fn walk(root: ProofNode) -> Vec<(Vec<String>, usize)> {
    into_solved_systems(root)
        .into_iter()
        .map(|(p, s)| (p, sys_tag(&s)))
        .collect()
}

#[test]
fn solved_systems_root_leaf_yields_empty_path() {
    assert_eq!(walk(solved(3)), vec![(Vec::<String>::new(), 3)]);
}

#[test]
fn solved_systems_walks_children_in_btreemap_order() {
    // Insertion order deliberately reversed w.r.t. the expected
    // output: `M.toList` / `BTreeMap` iterate ascending by key.
    let root = node(
        ProofMethod::Simplify,
        9,
        vec![
            (
                "case_2",
                node(ProofMethod::Induction, 8, vec![("z", solved(2))], true),
            ),
            (
                "case_1",
                node(
                    ProofMethod::Induction,
                    7,
                    vec![("b", solved(4)), ("a", solved(1))],
                    true,
                ),
            ),
            (
                "",
                node(ProofMethod::Simplify, 6, vec![("k", solved(5))], true),
            ),
        ],
        true,
    );
    assert_eq!(
        walk(root),
        vec![
            (vec![String::new(), "k".to_string()], 5),
            (vec!["case_1".to_string(), "a".to_string()], 1),
            (vec!["case_1".to_string(), "b".to_string()], 4),
            (vec!["case_2".to_string(), "z".to_string()], 2),
        ]
    );
}

#[test]
fn solved_systems_skips_unannotated_solved_node() {
    // HS's first equation needs `Just sys`; an unannotated
    // (`Nothing`) solved step falls through to the recursive
    // equation, so its own system is dropped but its children are
    // still walked.
    let unannotated = node(
        ProofMethod::Finished(MethodResult::Solved),
        5,
        vec![("c", solved(6))],
        false,
    );
    let root = node(ProofMethod::Simplify, 9, vec![("a", unannotated)], true);
    assert_eq!(
        walk(root),
        vec![(vec!["a".to_string(), "c".to_string()], 6)]
    );
    // A childless unannotated solved node contributes nothing.
    let bare = node(
        ProofMethod::Finished(MethodResult::Solved),
        5,
        Vec::new(),
        false,
    );
    assert!(walk(bare).is_empty());
}

#[test]
fn solved_systems_does_not_recurse_into_solved_node() {
    // Batch.hs:285 matches `_` children and returns immediately: the
    // solved node's own system is the only result, its solved
    // descendants are invisible.
    let root = node(
        ProofMethod::Finished(MethodResult::Solved),
        1,
        vec![("a", solved(2)), ("b", solved(3))],
        true,
    );
    assert_eq!(walk(root), vec![(Vec::<String>::new(), 1)]);
}

#[test]
fn solved_systems_other_finished_kinds_are_not_collected() {
    let root = node(
        ProofMethod::Simplify,
        9,
        vec![
            (
                "a",
                node(
                    ProofMethod::Finished(MethodResult::Unfinishable),
                    1,
                    Vec::new(),
                    true,
                ),
            ),
            ("b", node(ProofMethod::Sorry(None), 2, Vec::new(), true)),
            ("c", node(ProofMethod::Invalidated, 3, Vec::new(), true)),
        ],
        true,
    );
    assert!(walk(root).is_empty());
}

#[test]
fn drop_sys_after_expand_retains_only_solved_when_switch_on() {
    let solved_leaf = solved(1);
    let simplify = node(ProofMethod::Simplify, 1, Vec::new(), true);
    let contradictory = node(
        ProofMethod::Finished(MethodResult::Contradictory(None)),
        1,
        Vec::new(),
        true,
    );
    // `DropAll`: everything but a depth-limit stub is dropped.
    for n in [&solved_leaf, &simplify, &contradictory] {
        assert!(drop_sys_after_expand(n, SysRetention::DropAll));
    }
    // `KeepSolved`: the solved node keeps its system, ONLY it.
    assert!(!drop_sys_after_expand(
        &solved_leaf,
        SysRetention::KeepSolved
    ));
    assert!(drop_sys_after_expand(&simplify, SysRetention::KeepSolved));
    assert!(drop_sys_after_expand(
        &contradictory,
        SysRetention::KeepSolved
    ));
    // An unannotated solved node still counts here — `expand` never
    // produces one, and `into_solved_systems` filters it out anyway.
    let unannotated = node(
        ProofMethod::Finished(MethodResult::Solved),
        1,
        Vec::new(),
        false,
    );
    assert!(!drop_sys_after_expand(
        &unannotated,
        SysRetention::KeepSolved
    ));
    // `KeepAll` (interactive server) retains everything.
    assert!(!drop_sys_after_expand(&simplify, SysRetention::KeepAll));
}

#[test]
fn drop_sys_after_expand_keeps_depth_limited_frontier() {
    let mut stub = node(
        ProofMethod::Sorry(Some("depth limit".into())),
        1,
        Vec::new(),
        true,
    );
    stub.status = NodeStatus::Sorry;
    assert!(!drop_sys_after_expand(&stub, SysRetention::DropAll));
    // A terminal (non-frontier) sorry is still dropped.
    let terminal = node(
        ProofMethod::Sorry(Some("budget exhausted".into())),
        1,
        Vec::new(),
        true,
    );
    assert!(drop_sys_after_expand(&terminal, SysRetention::DropAll));
}

// The standalone skolem-walk tests cover 8,192 levels; this bounded backend
// workload covers the AC fallback through real proof search and Maude.
#[cfg(test)]
mod skolem_depth_tests {
    use crate::{
        atom::ProtoAtom,
        constraint::{
            solver::{context::ProofContext, search::run_proof_search},
            system::System,
        },
        fact::{Fact, FactTag},
        guarded::{gall, gfalse},
        rule::*,
    };
    use tamarin_term::{
        builtin::{hash, msg_var},
        function_symbols::AcSym,
        lterm::{BVar, LSort, LVar},
        maude_proc::MaudeHandle,
        maude_sig::{dh_maude_sig, hash_maude_sig},
        term::{f_app_ac, map_lits},
        vterm::{var_term, Lit},
    };
    #[test]
    fn ac_guard_matching_survives_a_small_caller_stack() {
        let n = 1024;
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let h = MaudeHandle::start(&path, hash_maude_sig().merge(dh_maude_sig())).unwrap();
        tamarin_test_support::on_stack(256 * 1024, move || {
            let mut t = msg_var("z", 0);
            for _ in 0..n {
                t = hash(t)
            }
            let ctx = ProofContext::new(h, vec![]);
            let mut sys = System::empty();
            sys.add_node(
                LVar::new("i", LSort::Node, 0),
                Rule::new(
                    RuleInfo::Proto(ProtoRuleACInstInfo {
                        name: ProtoRuleName::Stand("Test"),
                        attributes: RuleAttributes::empty(),
                        loop_breakers: vec![],
                    }),
                    vec![],
                    vec![Fact::new(FactTag::Kd, vec![t.clone()])],
                    vec![Fact::new(FactTag::Ku, vec![msg_var("a", 2)])],
                ),
            );
            let lift = |t: &tamarin_term::lterm::LNTerm| {
                map_lits(t, &mut |l| match l {
                    Lit::Var(v) => Lit::Var(BVar::Free(*v)),
                    Lit::Con(c) => Lit::Con(*c),
                })
            };
            let lhs = f_app_ac(AcSym::Mult, vec![var_term(BVar::Bound(0)), lift(&t)]);
            let rhs = f_app_ac(AcSym::Mult, vec![lift(&msg_var("y", 1)), lift(&t)]);
            sys.insert_lemma(gall(
                vec![("p".into(), LSort::Msg)],
                vec![ProtoAtom::EqE(lhs, rhs)],
                gfalse(),
            ));
            assert_eq!(
                run_proof_search(&ctx, sys, 10).unwrap().status,
                super::NodeStatus::Contradictory
            );
        });
    }
}

#[cfg(test)]
mod subterm_depth_tests {
    use super::*;
    use crate::{
        fact::{Fact, FactTag},
        rule::*,
    };
    use std::sync::Arc;
    use tamarin_term::{
        builtin::{hash, msg_var},
        lterm::{LSort, LVar},
        maude_proc::MaudeHandle,
        maude_sig::hash_maude_sig,
        vterm::var_term,
    };

    #[test]
    fn freshness_and_subterm_constraints_survive_small_search_stack() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let maude = MaudeHandle::start(&path, hash_maude_sig()).unwrap();
        tamarin_test_support::on_stack(256 * 1024, move || {
            let ctx = ProofContext::new(maude, vec![]);
            // Fresh ordering and positive membership need only linear scans.
            // Negative splitting emits a leaf per level, so use a smaller case.
            for (fresh_rule, negative, depth) in [
                (true, false, 8192),
                (false, false, 8192),
                (false, true, 512),
            ] {
                let mut term = msg_var("z", 0);
                for _ in 0..depth {
                    term = hash(term);
                }
                let mut sys = System::empty();
                if fresh_rule {
                    sys.add_node(
                        LVar::new("i", LSort::Node, 0),
                        Rule::new(
                            RuleInfo::Proto(ProtoRuleACInstInfo {
                                name: ProtoRuleName::Stand("Test"),
                                attributes: RuleAttributes::empty(),
                                loop_breakers: vec![],
                            }),
                            vec![Fact::new(
                                FactTag::Fresh,
                                vec![var_term(LVar::new("f", LSort::Fresh, 4))],
                            )],
                            vec![],
                            vec![Fact::new(FactTag::Ku, vec![term])],
                        ),
                    );
                } else {
                    let store = Arc::make_mut(&mut sys.content_mut().subterm_store);
                    if negative {
                        store.add_neg(msg_var("x", 1), term);
                    } else {
                        store.add(msg_var("z", 0), term);
                    }
                }
                assert_eq!(
                    run_proof_search(&ctx, sys, 10).unwrap().status,
                    NodeStatus::Sorry
                );
            }
        });
    }
}
