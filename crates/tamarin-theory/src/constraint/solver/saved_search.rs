// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Whole-proof solution extraction for checked saved proofs (Theory/Proof.hs,
//! including the patched oracle's upstream #955 changes).
//! Unfinished replacements share the outer extractor's depth frontier. Their
//! own proof bounds and heuristic depths still start at zero, independently.

use super::*;
use std::collections::BTreeSet;

struct SavedSearch<'a> {
    ctx: &'a ProofContext,
    deadline: std::time::Instant,
    proof_bound: usize,
    replacements: BTreeSet<Vec<String>>,
}

fn prepare_replacements(
    node: &mut ProofNode,
    path: &mut Vec<String>,
    roots: &mut BTreeSet<Vec<String>>,
) {
    if node.annotated && matches!(node.method, ProofMethod::Sorry(_)) {
        roots.insert(path.clone());
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.children.clear();
        node.status = NodeStatus::Sorry;
        return;
    }
    for (name, child) in &mut node.children {
        path.push(name.clone());
        prepare_replacements(child, path, roots);
        path.pop();
    }
}

impl SavedSearch<'_> {
    /// Force just the portion needed by this whole-tree extraction round.
    /// Return the selected path explicitly: aggregated statuses can include
    /// saved solutions *below* this round's frontier and cannot select it.
    fn visit(
        &self,
        node: &mut ProofNode,
        path: &mut Vec<String>,
        limit: usize,
        incomplete: &mut bool,
    ) -> Result<Option<Vec<String>>, ProveError> {
        if path.len() >= limit {
            *incomplete = true;
            return Ok(None);
        }
        if !node.annotated {
            // A stale stored-only branch has no checked system. In particular
            // a parsed SOLVED marker is not evidence of a solution.
            return Ok(None);
        }
        if self.replacements.contains(path) {
            let _tls = SearchTlsGuard::install(SearchTlsState {
                deadline: Some(self.deadline),
                max_depth: limit.saturating_sub(path.len()),
                depth_limit_hit: false,
                proof_bound: self.proof_bound,
                ranking_depth_offset: 0,
            });
            let mut budget = usize::MAX;
            re_expand_depth_limited(self.ctx, node, &mut budget, &self.deadline, 0)?;
            *incomplete |= DEPTH_LIMIT_HIT.with(|flag| flag.get());
            let mut suffix = Vec::new();
            return Ok(find_solved_path(node, &mut suffix).then(|| {
                let mut selected = path.clone();
                selected.extend(suffix);
                selected
            }));
        }
        if matches!(node.method, ProofMethod::Finished(MethodResult::Solved)) {
            return Ok(Some(path.clone()));
        }
        let mut selected = None;
        for (name, child) in &mut node.children {
            if std::time::Instant::now() >= self.deadline {
                break;
            }
            path.push(name.clone());
            let _case = crate::constraint::solver::trace::CasePathGuard::push(name);
            let found = self.visit(child, path, limit, incomplete)?;
            path.pop();
            if selected.is_none() {
                selected = found;
            }
            if selected.is_some() && matches!(self.ctx.cut, CutStrategy::Dfs | CutStrategy::SeqDfs)
            {
                break;
            }
        }
        if !node.children.is_empty() {
            node.status = rollup_status(&node.children);
        }
        Ok(selected)
    }
}

pub(crate) fn extend_saved_proof(
    ctx: &ProofContext,
    mut root: ProofNode,
    proof_bound: usize,
) -> Result<ProofNode, ProveError> {
    let mut search = SavedSearch {
        ctx,
        deadline: proof_deadline(),
        proof_bound,
        replacements: BTreeSet::new(),
    };
    prepare_replacements(&mut root, &mut Vec::new(), &mut search.replacements);
    let mut depth = match ctx.cut {
        CutStrategy::Dfs => 4,
        CutStrategy::Bfs => 1,
        _ => usize::MAX,
    };
    loop {
        let mut incomplete = false;
        let limit = if ctx.cut == CutStrategy::Bfs {
            depth + 1
        } else {
            depth
        };
        let selected = search.visit(&mut root, &mut Vec::new(), limit, &mut incomplete)?;
        match ctx.cut {
            CutStrategy::Dfs | CutStrategy::SeqDfs => {
                if let Some(path) = selected {
                    prune_to_path(&mut root, &path);
                    break;
                }
            }
            CutStrategy::Bfs => {
                eprintln!("searching for attacks at depth: {depth}");
                let mut found = false;
                incomplete = false;
                bfs_check_level(&root, depth, &mut found, &mut incomplete, false);
                if found {
                    eprintln!("attack found at depth: {depth}");
                    root = bfs_check_level(&root, depth, &mut false, &mut false, true)
                        .expect("BFS build returns a tree");
                    break;
                }
            }
            CutStrategy::Nothing => break,
            CutStrategy::AfterSorry => unreachable!("sorry cut stays local to each replacement"),
        }
        if !incomplete || std::time::Instant::now() >= search.deadline || depth >= usize::MAX / 4 {
            break;
        }
        depth = if ctx.cut == CutStrategy::Bfs {
            depth + 1
        } else {
            depth * 2
        };
    }
    Ok(root)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Option<ProofContext> {
        let path = tamarin_test_support::require_maude_path()?;
        let maude = tamarin_term::maude_proc::MaudeHandle::start(
            &path,
            tamarin_term::maude_sig::pair_maude_sig(),
        )
        .unwrap();
        Some(ProofContext::new(maude, Vec::new()))
    }

    fn leaf(method: ProofMethod) -> ProofNode {
        let status = match &method {
            ProofMethod::Finished(result) => node_status_of(result),
            _ => NodeStatus::Sorry,
        };
        ProofNode {
            method,
            sys: System::empty(),
            children: BTreeMap::new(),
            status,
            annotated: true,
        }
    }

    fn solved() -> ProofNode {
        // This tests extraction from an already CHECKED tree. Replay's tests
        // separately ensure parsed terminal claims are re-executed.
        leaf(ProofMethod::Finished(MethodResult::Solved))
    }

    fn branch(children: Vec<(&str, ProofNode)>) -> ProofNode {
        let children = children.into_iter().map(|(k, v)| (k.into(), v)).collect();
        ProofNode {
            method: ProofMethod::Simplify,
            sys: System::empty(),
            status: rollup_status(&children),
            children,
            annotated: true,
        }
    }

    fn deep_solution() -> ProofNode {
        let mut node = solved();
        for _ in 0..5 {
            node = branch(vec![("", node)]);
        }
        node
    }

    #[test]
    fn bfs_replay_preserves_nested_stale_saved_branches() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let parsed = tamarin_parser::parse_theory(
            r#"theory StaleBfs begin
            rule Emit1: [Fr(~x)] --[A(~x)]-> []
            rule Emit2: [Fr(~x)] --[A(~x)]-> []
            lemma witness [stop-on-trace=BFS]: exists-trace
              "Ex x #i. A(x) @ i"
            simplify
            case stale
              simplify
              simplify
              by sorry
            qed
            end"#,
            &[],
        )
        .unwrap();
        let theory = crate::elaborate::elaborate(&parsed).unwrap();
        let maude =
            tamarin_term::maude_proc::MaudeHandle::start(&path, theory.signature.clone()).unwrap();
        let proof =
            crate::prove::prove_lemma(std::sync::Arc::new(theory), "witness", maude, 30).unwrap();
        assert_eq!(proof_status(&proof), ProofStatus::TraceFound);
        let mut stale = &proof.children["stale"];
        for _ in 0..2 {
            assert!(!stale.annotated);
            assert!(matches!(stale.method, ProofMethod::Simplify));
            assert_eq!(stale.children.len(), 1);
            stale = stale.children.values().next().unwrap();
        }
        assert!(!stale.annotated);
        assert!(matches!(stale.method, ProofMethod::Sorry(None)));
        assert!(stale.children.is_empty());
        fn steps(node: &ProofNode) -> usize {
            1 + node.children.values().map(steps).sum::<usize>()
        }
        assert_eq!(steps(&proof), 7);
    }

    #[test]
    fn whole_proof_depth_selects_the_reached_path_not_an_earlier_deeper_trace() {
        let Some(ctx) = context() else {
            return;
        };
        let tree = branch(vec![("a", deep_solution()), ("b", solved())]);
        let result = extend_saved_proof(&ctx, tree, usize::MAX).unwrap();
        assert_eq!(
            result.children.keys().cloned().collect::<Vec<_>>(),
            vec!["b"]
        );
    }

    #[test]
    fn replacement_bound_does_not_bound_the_saved_tree() {
        let Some(ctx) = context() else {
            return;
        };
        let tree = branch(vec![
            ("a", leaf(ProofMethod::Sorry(None))),
            ("b", deep_solution()),
        ]);
        let result = extend_saved_proof(&ctx, tree, 0).unwrap();
        assert_eq!(
            result.children.keys().cloned().collect::<Vec<_>>(),
            vec!["b"]
        );
        assert_eq!(proof_status(&result), ProofStatus::TraceFound);
    }

    #[test]
    fn stored_only_solved_markers_cannot_cut_a_checked_proof() {
        let Some(mut ctx) = context() else {
            return;
        };
        for cut in [CutStrategy::Dfs, CutStrategy::Bfs, CutStrategy::SeqDfs] {
            ctx.cut = cut;
            let mut stale = solved();
            stale.annotated = false;
            stale.status = NodeStatus::Sorry;
            let tree = branch(vec![("a", stale), ("b", leaf(ProofMethod::Sorry(None)))]);
            let result = extend_saved_proof(&ctx, tree, 0).unwrap();
            assert_ne!(proof_status(&result), ProofStatus::TraceFound);
            assert!(result.children.contains_key("b"));
        }
    }
}
