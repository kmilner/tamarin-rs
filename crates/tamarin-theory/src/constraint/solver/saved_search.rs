// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Whole-proof solution extraction for checked saved proofs (Theory/Proof.hs).
//! Unfinished replacements share the outer extractor's depth frontier. Their
//! own proof bounds and heuristic depths start at zero, independently. Each
//! replacement has its own time budget, charged only while that search runs.

use super::*;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

struct SavedSearch<'a> {
    ctx: &'a ProofContext,
    proof_bound: usize,
    replacements: BTreeMap<Vec<String>, Option<Duration>>,
}

fn prepare_replacements(
    node: &mut ProofNode,
    path: &mut Vec<String>,
    roots: &mut BTreeMap<Vec<String>, Option<Duration>>,
    time_limit: Option<Duration>,
) {
    if node.annotation.is_checked() && matches!(node.method, ProofMethod::Sorry(_)) {
        roots.insert(path.clone(), time_limit);
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.children.clear();
        node.status = NodeStatus::Sorry;
        return;
    }
    for (name, child) in &mut node.children {
        path.push(name.clone());
        prepare_replacements(child, path, roots, time_limit);
        path.pop();
    }
}

impl SavedSearch<'_> {
    /// Force just the portion needed by this whole-tree extraction round.
    /// Return the selected path explicitly: aggregated statuses can include
    /// saved solutions *below* this round's frontier and cannot select it.
    fn visit(
        &mut self,
        node: &mut ProofNode,
        path: &mut Vec<String>,
        limit: usize,
        incomplete: &mut bool,
    ) -> Result<Option<Vec<String>>, ProveError> {
        check_cancelled()?;
        if path.len() >= limit {
            *incomplete = true;
            return Ok(None);
        }
        if !node.annotation.is_checked() {
            // A stale stored-only branch has no checked system. In particular
            // a parsed SOLVED marker is not evidence of a solution.
            return Ok(None);
        }
        if let Some(remaining) = self.replacements.get_mut(path) {
            let started = Instant::now();
            let _deadline =
                DeadlineGuard::install(remaining.and_then(|budget| started.checked_add(budget)));
            let mut search = Search {
                max_depth: limit.saturating_sub(path.len()),
                ..Search::new(self.proof_bound, 0)
            };
            let result = re_expand_depth_limited(self.ctx, &mut search, node, 0);
            if let Some(budget) = remaining {
                *budget = budget.saturating_sub(started.elapsed());
            }
            result?;
            *incomplete |= search.depth_limit_hit;
            let mut suffix = Vec::new();
            return Ok(find_solved_path(node, &mut suffix).then(|| {
                let mut selected = path.clone();
                selected.extend(suffix);
                selected
            }));
        }
        let mut selected = None;
        for (name, child) in &mut node.children {
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
    if matches!(
        ctx.cut,
        CutStrategy::Dfs | CutStrategy::Bfs | CutStrategy::SeqDfs
    ) && keep_saved_witness(&mut root)
    {
        return Ok(root);
    }
    let mut search = SavedSearch {
        ctx,
        proof_bound,
        replacements: BTreeMap::new(),
    };
    prepare_replacements(
        &mut root,
        &mut Vec::new(),
        &mut search.replacements,
        ProofTimeLimit::current().duration(),
    );
    let mut frontier = SearchFrontier::new(ctx.cut, None);
    loop {
        let mut incomplete = false;
        let selected = search.visit(
            &mut root,
            &mut Vec::new(),
            frontier.limit(),
            &mut incomplete,
        )?;
        if !frontier.advance(&mut root, selected, incomplete) {
            break;
        }
    }
    Ok(root)
}

/// Prefer an already checked witness in case order before searching any
/// unfinished branch. A stored-only SOLVED claim cannot establish a witness.
fn keep_saved_witness(node: &mut ProofNode) -> bool {
    if !node.annotation.is_checked() {
        return false;
    }
    if matches!(node.method, ProofMethod::Finished(MethodResult::Solved)) {
        node.children.clear();
        node.status = NodeStatus::Solved;
        return true;
    }
    let selected = node
        .children
        .iter_mut()
        .find_map(|(name, child)| keep_saved_witness(child).then(|| name.clone()));
    if let Some(selected) = selected {
        node.children.retain(|name, _| *name == selected);
        node.status = rollup_status(&node.children);
        true
    } else {
        false
    }
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
            annotation: ProofAnnotation::checked(System::empty()),
            children: BTreeMap::new(),
            status,
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
            annotation: ProofAnnotation::checked(System::empty()),
            status: rollup_status(&children),
            children,
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
    fn an_expired_replacement_does_not_consume_its_siblings_budget() {
        let Some(mut ctx) = context() else { return };
        ctx.cut = CutStrategy::Nothing;
        let mut tree = branch(vec![
            ("a", leaf(ProofMethod::Sorry(None))),
            ("b", leaf(ProofMethod::Sorry(None))),
        ]);
        let mut search = SavedSearch {
            ctx: &ctx,
            proof_bound: usize::MAX,
            replacements: BTreeMap::new(),
        };
        prepare_replacements(&mut tree, &mut Vec::new(), &mut search.replacements, None);
        search
            .replacements
            .insert(vec!["a".into()], Some(Duration::ZERO));
        search
            .visit(&mut tree, &mut Vec::new(), usize::MAX, &mut false)
            .unwrap();
        assert!(matches!(
            &tree.children["a"].method,
            ProofMethod::Sorry(Some(reason)) if reason == "deadline reached"
        ));
        let expected = run_proof_search(&ctx, System::empty(), usize::MAX).unwrap();
        assert_eq!(tree.children["b"].method, expected.method);
        assert_eq!(search.replacements[&vec!["a".into()]], Some(Duration::ZERO));
        assert_eq!(search.replacements[&vec!["b".into()]], None);
    }

    #[test]
    fn checked_saved_witness_uses_case_order_before_search_depth() {
        let Some(mut ctx) = context() else {
            return;
        };
        for cut in [CutStrategy::Dfs, CutStrategy::Bfs, CutStrategy::SeqDfs] {
            ctx.cut = cut;
            let tree = branch(vec![("a", deep_solution()), ("b", solved())]);
            let result = extend_saved_proof(&ctx, tree, usize::MAX).unwrap();
            assert_eq!(
                result.children.keys().cloned().collect::<Vec<_>>(),
                vec!["a"]
            );
        }
    }

    #[test]
    fn stored_only_solved_markers_cannot_cut_a_checked_proof() {
        let Some(mut ctx) = context() else {
            return;
        };
        for cut in [CutStrategy::Dfs, CutStrategy::Bfs, CutStrategy::SeqDfs] {
            ctx.cut = cut;
            let mut stale = solved();
            stale.annotation = ProofAnnotation::Unchecked;
            stale.status = NodeStatus::Sorry;
            let tree = branch(vec![("a", stale), ("b", leaf(ProofMethod::Sorry(None)))]);
            let result = extend_saved_proof(&ctx, tree, 0).unwrap();
            assert_ne!(proof_status(&result), ProofStatus::TraceFound);
            assert!(result.children.contains_key("b"));
        }
    }
}
