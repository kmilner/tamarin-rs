// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, addap, sans-sucre, felixlinker, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Graph/Simplification.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/utils/src/Data/DAG/Simple.hs

//! Port of `Theory.Constraint.System.Graph.Simplification` —
//! drops transitive `Less`-atoms and hides "transfer" nodes
//! (irecv/isend/coerce/fresh chains, or rule nodes with no actions
//! and at most one premise/conclusion).
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/Simplification.hs`.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_theory::constraint::constraints::{
    Edge, Goal, LessAtom, NodeId, Reason,
};
use tamarin_theory::constraint::system::System;
use super::render_system::RenderSystem;
use tamarin_theory::fact::FactTag;
use tamarin_theory::rule::{
    is_coerce_rule_info, is_irecv_rule_info, is_isend_rule_info,
    RuleACInst, RuleInfo,
};
use tamarin_term::lterm::{sort_of_lnterm, LSort, LNTerm};

// ---------------------------------------------------------------------
// Compression (compressSystem)
// ---------------------------------------------------------------------

/// Mirror of Haskell `compressSystem` (Simplification.hs:42-46).
/// Drops entailed less-atoms, then tries to hide each node in turn.
pub fn compress_system(mut sys: RenderSystem) -> RenderSystem {
    sys = drop_entailed_ord_constraints(sys);
    // Haskell: `foldl' (flip tryHideNodeId) se (frees (sLessAtoms, sNodes))`
    // where `frees = sortednub . freesList` — a SINGLE sorted, deduplicated
    // pass over the free vars of the (less-atoms, nodes) tuple.  The only
    // Node-sort frees come from the node-id keys and the less-atom
    // endpoints (rule instances carry term vars, not node vars), so we
    // gather both into one sorted+deduplicated set and fold once.  We do
    // NOT include `last_atom` (it is not part of Haskell's tuple) and we
    // never double-visit a node id.  `BTreeSet<NodeId>` reproduces
    // `sortednub`, since `LVar`'s `Ord` is Haskell-faithful (idx, sort,
    // name).
    let mut frees: BTreeSet<NodeId> = BTreeSet::new();
    for la in &sys.less_atoms {
        frees.insert(la.smaller.clone());
        frees.insert(la.larger.clone());
    }
    for (id, _) in sys.nodes.iter() {
        frees.insert(id.clone());
    }
    for v in frees {
        sys = try_hide_node_id(&v, sys);
    }
    sys
}

/// Drop `LessAtom`s that are implied by the edge relation.
fn drop_entailed_ord_constraints(mut sys: RenderSystem) -> RenderSystem {
    // Build adjacency from `rawEdgeRel` = edges ++ unsolvedChains
    // (Simplification.hs:33-38, see line 37 / System.hs:1613-1616).
    let adj = build_raw_edge_adjacency(&sys);
    let mut new_atoms: Vec<LessAtom> = Vec::with_capacity(sys.less_atoms.len());
    for la in &sys.less_atoms {
        // HS `entailed (LessAtom from to _) = to `S.member` reachableSet [from] edges`
        // (Simplification.hs:33-38, see line 38).  `Dag.reachableSet [from]` ALWAYS contains the
        // start node `from` itself (DAG/Simple.hs:72-78: `visit` inserts `x`
        // before recursing), so a REFLEXIVE atom (`from == to`) is unconditionally
        // entailed — hence dropped from the display graph.  `reachable` below is
        // strict-path (returns false for `from == to`), so the reflexive case must
        // be added explicitly to match HS; otherwise a `#t1 < #t1` born from a
        // `#t1 < #t2` less-atom collapsed under a `t2 = t1` subst survives here and
        // renders as a spurious dashed self-loop that HS never draws.
        let entailed = la.smaller == la.larger
            || reachable(&adj, &la.smaller, &la.larger);
        if !entailed {
            new_atoms.push(la.clone());
        }
    }
    sys.content_mut().less_atoms = new_atoms;
    sys
}

/// `(from, to)` node pairs of unsolved chain goals — mirror of
/// `unsolvedChains` (System.hs:1601-1605) projected to node ids via
/// `nodeConcNode *** nodePremNode`.
fn unsolved_chain_pairs(sys: &System) -> Vec<(NodeId, NodeId)> {
    sys.goals.iter().filter_map(|(g, st)| {
        if st.solved { return None; }
        if let Goal::Chain(src, tgt) = g {
            Some((src.0.clone(), tgt.0.clone()))
        } else { None }
    }).collect()
}

/// Adjacency for `rawEdgeRel sys = edges ++ unsolvedChains sys`
/// (System.hs:1613-1616).
fn build_raw_edge_adjacency(sys: &System) -> BTreeMap<NodeId, Vec<NodeId>> {
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for e in &sys.edges {
        adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
    }
    for (from, to) in unsolved_chain_pairs(sys) {
        adj.entry(from).or_default().push(to);
    }
    adj
}

fn reachable(
    adj: &BTreeMap<NodeId, Vec<NodeId>>,
    from: &NodeId,
    to: &NodeId,
) -> bool {
    if from == to { return false; }
    let mut stack: Vec<NodeId> = vec![from.clone()];
    let mut visited: BTreeSet<NodeId> = BTreeSet::new();
    visited.insert(from.clone());
    while let Some(cur) = stack.pop() {
        if let Some(nbrs) = adj.get(&cur) {
            for nb in nbrs {
                if nb == to { return true; }
                if visited.insert(nb.clone()) {
                    stack.push(nb.clone());
                }
            }
        }
    }
    false
}

// ---------------------------------------------------------------------
// tryHideNodeId — `Simplification.hs:85-152`
// ---------------------------------------------------------------------

fn try_hide_node_id(v: &NodeId, sys: RenderSystem) -> RenderSystem {
    if v.sort != LSort::Node { return sys; }
    // Mirror Haskell guards on `notOccursIn`:
    //   - unsolved chains (any goal Chain mentioning v)
    //   - sFormulas (Guarded constraints mentioning v)
    if mentioned_in_unsolved_chains(v, &sys) { return sys; }
    if mentioned_in_formulas(v, &sys.formulas) { return sys; }
    // Try hideRule first if v has a node entry, else hideAction.
    if let Some((_, ru)) = sys.nodes.iter().find(|(id, _)| id == v).cloned() {
        match try_hide_rule(v, ru, sys) {
            Ok(updated) => updated,
            Err(restored) => restored,
        }
    } else {
        match try_hide_action(v, sys) {
            Ok(updated) => updated,
            Err(restored) => restored,
        }
    }
}

fn mentioned_in_unsolved_chains(v: &NodeId, sys: &System) -> bool {
    sys.goals.iter().any(|(g, st)| {
        if st.solved { return false; }
        if let Goal::Chain(src, tgt) = g {
            &src.0 == v || &tgt.0 == v
        } else { false }
    })
}

fn mentioned_in_formulas(v: &NodeId, formulas: &[std::sync::Arc<tamarin_theory::guarded::Guarded>]) -> bool {
    formulas.iter().any(|g| guarded_mentions_node(v, g))
}

fn guarded_mentions_node(v: &NodeId, g: &tamarin_theory::guarded::Guarded) -> bool {
    use tamarin_theory::guarded::Guarded;
    match g {
        Guarded::Conj(items) | Guarded::Disj(items) => {
            items.iter().any(|x| guarded_mentions_node(v, x))
        }
        Guarded::GGuarded { guards, body, .. } => {
            // HS `foldFrees` over the `Foldable (Guarded s c)` instance folds
            // BOTH the guard atoms and the body (Guarded.hs:259-263), so a
            // free node-sort var occurring only in a guard atom must count.
            guards.iter().any(|a| atom_mentions_node(v, a))
                || guarded_mentions_node(v, body)
        }
        Guarded::Atom(at) => atom_mentions_node(v, at),
    }
}

fn atom_mentions_node(v: &NodeId, at: &tamarin_theory::guarded_types::GAtom) -> bool {
    use tamarin_theory::guarded_types::{GAtom, GTerm, BVar};
    let mentions_term = |t: &GTerm| -> bool {
        if let GTerm::Var(BVar::Free(spec)) = t {
            // HS `notOccursIn proj = not $ getAny $ foldFrees (Any . (v ==))
            // (proj se)` (Simplification.hs:95-96) folds FULL `LVar` equality
            // (name AND idx AND sort) over the formula's free vars. Comparing
            // the NAME ONLY spuriously matches a different index — e.g. node
            // `#vr.4` matched a formula mentioning `#vr` (idx 0), wrongly
            // rejecting `#vr.4` from compression and keeping a transfer node
            // (`d_0_snd`) HS hides. Match name AND idx (both are node-sort
            // here: `v` is a NodeId and only node vars can equal it).
            return *spec.name == *v.name && spec.idx == v.idx;
        }
        false
    };
    match at {
        GAtom::Action(_, t) => mentions_term(t),
        GAtom::Last(t) => mentions_term(t),
        GAtom::Eq(a, b) | GAtom::Less(a, b) | GAtom::LessMset(a, b)
        | GAtom::Subterm(a, b) => mentions_term(a) || mentions_term(b),
        GAtom::Pred(_) => false,
    }
}

// ---------------------------------------------------------------------
// hideAction — `Simplification.hs:99-122`
// ---------------------------------------------------------------------

fn try_hide_action(v: &NodeId, sys: RenderSystem) -> Result<RenderSystem, RenderSystem> {
    // Collect KU action atoms at v.
    let ku_actions: Vec<(NodeId, tamarin_theory::fact::LNFact)> = sys.goals.iter()
        .filter_map(|(g, st)| {
            if st.solved { return None; }
            if let Goal::Action(n, fa) = g {
                if n == v && matches!(fa.tag, FactTag::Ku) && !fa.terms.is_empty() {
                    return Some((n.clone(), fa.clone()));
                }
            }
            None
        }).collect();
    if ku_actions.is_empty() { return Err(sys); }
    // All KU terms must be pair, inverse, pub, or nat — otherwise bail.
    if !ku_actions.iter().all(|(_, fa)| {
        fa.terms.first().is_some_and(eligible_term)
    }) {
        return Err(sys);
    }
    // Other restrictions: no standard action atoms mentioning v;
    // no last-atom = v; no edges referencing v.
    if sys.goals.iter().any(|(g, st)| {
        if st.solved { return false; }
        if let Goal::Action(n, fa) = g {
            n == v && !matches!(fa.tag, FactTag::Ku)
        } else { false }
    }) { return Err(sys); }
    if sys.last_atom.as_ref() == Some(v) { return Err(sys); }
    if sys.edges.iter().any(|e| &e.src.0 == v || &e.tgt.0 == v) {
        return Err(sys);
    }
    // Self-loop check: lNews must not have i == j.
    let l_ins: Vec<LessAtom> = sys.less_atoms.iter()
        .filter(|la| &la.larger == v).cloned().collect();
    let l_outs: Vec<LessAtom> = sys.less_atoms.iter()
        .filter(|la| &la.smaller == v).cloned().collect();
    let l_news: Vec<LessAtom> = l_ins.iter().flat_map(|i| {
        l_outs.iter().map(move |o| LessAtom {
            smaller: i.smaller.clone(),
            larger: o.larger.clone(),
            reason: o.reason,
        })
    }).collect();
    if l_news.iter().any(|la| la.smaller == la.larger) {
        return Err(sys);
    }
    // Apply.
    let mut new_sys = sys;
    new_sys.content_mut().less_atoms.retain(|la| !l_ins.iter().any(|x| x == la)
        && !l_outs.iter().any(|x| x == la));
    for la in l_news {
        if !new_sys.less_atoms.iter().any(|x| x == &la) {
            new_sys.content_mut().less_atoms.push(la);
        }
    }
    // Remove KU action goals at v.
    new_sys.goals_mut().retain(|(g, _)| match g {
        Goal::Action(n, fa) => !(n == v && matches!(fa.tag, FactTag::Ku)),
        _ => true,
    });
    Ok(new_sys)
}

/// Mirror Haskell `eligibleTerm`:
///   isPair m  || isInverse m  || sortOfLNTerm m == LSortPub  || == LSortNat
fn eligible_term(t: &LNTerm) -> bool {
    tamarin_term::term::is_pair(t)
        || tamarin_term::term::is_inverse(t)
        || sort_of_lnterm(t) == LSort::Pub
        || sort_of_lnterm(t) == LSort::Nat
}

// ---------------------------------------------------------------------
// hideRule — `Simplification.hs:124-152`
// ---------------------------------------------------------------------

fn try_hide_rule(v: &NodeId, ru: RuleACInst, sys: RenderSystem) -> Result<RenderSystem, RenderSystem> {
    // Eligible-rule check: must be one of irecv/isend/coerce/fresh,
    // OR have zero actions and at most-one premise + at most-one conclusion.
    if !rule_eligible(&ru) { return Err(sys); }
    // Edges in (where v is the target) and out (where v is the source).
    let e_ins: Vec<Edge> = sys.edges.iter()
        .filter(|e| &e.tgt.0 == v).cloned().collect();
    let e_outs: Vec<Edge> = sys.edges.iter()
        .filter(|e| &e.src.0 == v).cloned().collect();
    if e_ins.len() != ru.premises.len() { return Err(sys); }
    if e_outs.len() != ru.conclusions.len() { return Err(sys); }
    // Constructed pass-through edges.
    let e_news: Vec<Edge> = e_ins.iter().flat_map(|ei| {
        e_outs.iter().map(move |eo| Edge {
            src: ei.src.clone(),
            tgt: eo.tgt.clone(),
        })
    }).collect();
    if e_news.iter().any(|e| e.src.0 == e.tgt.0) { return Err(sys); }
    // No last-atom, no less-atom, no unsolved-action involving v.
    if sys.last_atom.as_ref() == Some(v) { return Err(sys); }
    if sys.less_atoms.iter().any(|la| &la.smaller == v || &la.larger == v) {
        return Err(sys);
    }
    if sys.goals.iter().any(|(g, st)| {
        if st.solved { return false; }
        if let Goal::Action(n, _) = g { n == v } else { false }
    }) { return Err(sys); }
    // Apply.
    let mut new_sys = sys;
    new_sys.content_mut().edges.retain(|e|
        !e_ins.iter().any(|x| x == e) && !e_outs.iter().any(|x| x == e));
    for e in e_news {
        if !new_sys.edges.iter().any(|x| x == &e) {
            new_sys.content_mut().edges.push(e);
        }
    }
    // Node removal can LOWER the node-component max, so invalidate the
    // node cache.  The full cache is not maintained on this display-only
    // simplify path.
    new_sys.invalidate_node_max_cache();
    new_sys.nodes_mut().retain(|(id, _)| id != v);
    Ok(new_sys)
}

fn rule_eligible(ru: &RuleACInst) -> bool {
    // HS `eligibleRule` (Simplification.hs:148-152):
    //   any ($ ru) [isISendRule, isIRecvRule, isCoerceRule, isFreshRule]
    //   || ( null (get rActs ru) && all (\l -> length (get l ru) <= 1) [rPrems, rConcs] )
    // The `isFooRule` disjunction and the `null rActs && <=1 prem/conc` fallback
    // are INDEPENDENT — the fallback applies to EVERY rule, not just proto rules.
    // In particular an intruder destructor such as `d_0_snd` (no actions, one
    // premise, one conclusion) is eligible via the fallback even though it is
    // not isend/irecv/coerce; HS hides it (bridging its single in/out edge),
    // so RS must too.
    let is_special = match &ru.info {
        RuleInfo::Intr(i) => {
            is_irecv_rule_info(i) || is_isend_rule_info(i) || is_coerce_rule_info(i)
        }
        RuleInfo::Proto(p) => {
            // isFreshRule treats only the Fresh proto-rule as fresh.
            p.name == tamarin_theory::rule::ProtoRuleName::Fresh
        }
    };
    is_special
        || (ru.actions.is_empty()
            && ru.premises.len() <= 1
            && ru.conclusions.len() <= 1)
}

// ---------------------------------------------------------------------
// simplifySystem — `Simplification.hs:53-57` + 61-74
// ---------------------------------------------------------------------

/// Simplification levels — port of `SimplificationLevel`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SimplificationLevel {
    SL0,
    SL1,
    SL2,
    SL3,
}

/// Mirror of Haskell `simplifySystem`:
///   SL2 = transitiveReduction sys False
///   SL3 = transitiveReduction sys True
///   else identity.
pub fn simplify_system(level: SimplificationLevel, sys: RenderSystem) -> RenderSystem {
    match level {
        SimplificationLevel::SL2 => transitive_reduction(sys, false),
        SimplificationLevel::SL3 => transitive_reduction(sys, true),
        _ => sys,
    }
}

/// Transitive reduction of `sLessAtoms`.  Mirror of
/// `Simplification.hs:61-74`.
///
/// `total_red = True`  -> retain only `(x,y) ∈ transRed sLess`
/// `total_red = False` -> retain `(x,y) ∈ transRed sLess` OR reason ∈ {Formula, Adversary}
pub fn transitive_reduction(sys: RenderSystem, total_red: bool) -> RenderSystem {
    // Haskell: `oldLesses = rawLessRel sys`, used for BOTH `Dag.cyclic`
    // and `Dag.transRed` (Simplification.hs:61-74).  `rawLessRel se =
    // getLessRel sLessAtoms ++ rawEdgeRel se` (System.hs:1621-1622), and
    // `rawEdgeRel = edges ++ unsolvedChains` (System.hs:1613-1616).
    let mut old_lesses: Vec<(NodeId, NodeId)> = sys.less_atoms.iter()
        .map(|la| (la.smaller.clone(), la.larger.clone()))
        .collect();
    for e in &sys.edges {
        old_lesses.push((e.src.0.clone(), e.tgt.0.clone()));
    }
    old_lesses.extend(unsolved_chain_pairs(&sys));
    // If there's a cycle in the combined graph we bail, matching Haskell's
    // `Dag.cyclic` guard (Simplification.hs:61-74).
    if tamarin_utils::dag::cyclic(&old_lesses) { return sys; }
    // `Dag.transRed` of the (now acyclic) combined relation.  The transitive
    // reduction of a DAG is unique and `kept` is only consulted via
    // `contains`, so collecting the `Relation` into a set is the faithful
    // shape here.
    let kept: BTreeSet<(NodeId, NodeId)> =
        tamarin_utils::dag::trans_red(&old_lesses).into_iter().collect();
    let mut sys = sys;
    sys.content_mut().less_atoms.retain(|la| {
        let p = (la.smaller.clone(), la.larger.clone());
        if total_red {
            kept.contains(&p)
        } else {
            kept.contains(&p)
                || matches!(la.reason, Reason::Formula | Reason::Adversary)
        }
    });
    sys
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::constraint::system::System;
    use tamarin_theory::fact::{out_fact, fresh_fact, in_fact};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, Rule, RuleInfo,
        IntrRuleACInfo, ConcIdx, PremIdx,
    };
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    fn nid(name: &str, idx: u64) -> NodeId {
        LVar::new(name, LSort::Node, idx)
    }

    #[test]
    fn simplify_sl0_is_identity() {
        let mut sys = System::empty();
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("b", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("c", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("b", 0), nid("c", 0), Reason::Fresh));
        let orig = sys.clone();
        let out = simplify_system(SimplificationLevel::SL0, RenderSystem::from_prover(sys));
        assert_eq!(orig.less_atoms.len(), out.less_atoms.len());
    }

    #[test]
    fn simplify_sl3_drops_transitive_edge() {
        // a < b < c plus the redundant a < c -- SL3 should drop a < c.
        let mut sys = System::empty();
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("b", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("b", 0), nid("c", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("c", 0), Reason::Fresh));
        let out = simplify_system(SimplificationLevel::SL3, RenderSystem::from_prover(sys));
        assert_eq!(out.less_atoms.len(), 2,
            "SL3 should drop the redundant edge: {:?}", out.less_atoms);
        for la in &out.less_atoms {
            assert!(!(la.smaller == nid("a", 0) && la.larger == nid("c", 0)));
        }
    }

    #[test]
    fn simplify_sl2_keeps_formula_edge() {
        // a < b < c plus the redundant a < c with Reason::Formula:
        // SL2 keeps the formula edge but SL3 drops it.
        let mut sys = System::empty();
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("b", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("b", 0), nid("c", 0), Reason::Fresh));
        sys.content_mut().less_atoms.push(LessAtom::new(nid("a", 0), nid("c", 0), Reason::Formula));
        let out2 = simplify_system(SimplificationLevel::SL2, RenderSystem::from_prover(sys.clone()));
        assert_eq!(out2.less_atoms.len(), 3, "SL2 retains Formula edges");
        let out3 = simplify_system(SimplificationLevel::SL3, RenderSystem::from_prover(sys));
        assert_eq!(out3.less_atoms.len(), 2, "SL3 drops Formula edges too");
    }

    #[test]
    fn compress_hides_simple_proto_node() {
        // i:1 (Out) -> i:2 (transfer with one in/one out) -> i:3 (In).
        // After compression, the middle node should be hidden and i:1 -> i:3.
        let mut sys = System::empty();
        let kvar: LNTerm = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        // Three rule instances.
        let r1 = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Source"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![fresh_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
            Vec::new(),
        );
        let r2 = Rule::new(
            // A trivial proto-rule with one premise + one conclusion +
            // no actions -- eligible for compression.
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Transfer"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![in_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
            Vec::new(),
        );
        // Sink with an action — guaranteed not hidden by compress.
        let r3 = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Sink"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![in_fact(kvar.clone())],
            Vec::new(),
            vec![in_fact(kvar.clone())],  // an action -> not eligible
        );
        let n1 = nid("i", 1);
        let n2 = nid("i", 2);
        let n3 = nid("i", 3);
        sys.add_node(n1.clone(), r1);
        sys.add_node(n2.clone(), r2);
        sys.add_node(n3.clone(), r3);
        sys.content_mut().edges.push(Edge {
            src: (n1.clone(), ConcIdx(0)),
            tgt: (n2.clone(), PremIdx(0)),
        });
        sys.content_mut().edges.push(Edge {
            src: (n2.clone(), ConcIdx(0)),
            tgt: (n3.clone(), PremIdx(0)),
        });
        let out = compress_system(RenderSystem::from_prover(sys));
        assert!(out.nodes.iter().all(|(id, _)| id != &n2),
            "Transfer node should have been hidden: {:?}",
            out.nodes.iter().map(|(id, _)| id).collect::<Vec<_>>());
        // A direct edge i:1 -> i:3 should exist now.
        assert!(out.edges.iter().any(|e| e.src.0 == n1 && e.tgt.0 == n3),
            "Expected i:1 -> i:3 edge in: {:?}",
            out.edges.iter().map(|e| (&e.src.0, &e.tgt.0)).collect::<Vec<_>>());
    }

    #[test]
    fn compress_preserves_node_with_actions() {
        let mut sys = System::empty();
        let kvar: LNTerm = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let r1 = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("WithAction"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![in_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],  // has an action
        );
        let n1 = nid("i", 1);
        sys.add_node(n1.clone(), r1);
        let out = compress_system(RenderSystem::from_prover(sys));
        assert!(out.nodes.iter().any(|(id, _)| id == &n1));
    }

    #[test]
    fn compress_hides_coerce_node() {
        // A coerce rule -- eligible.
        let mut sys = System::empty();
        let kvar: LNTerm = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        // Source with an action — guaranteed not hidden, so the
        // coerce node (i:2) sees the i:1 -> i:2 edge intact at the
        // time it's considered.
        let r1 = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Source"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![out_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],  // action -> not eligible
        );
        let r2 = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![in_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
            Vec::new(),
        );
        let r3 = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Sink"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![in_fact(kvar.clone())],
            Vec::new(),
            vec![out_fact(kvar.clone())],  // action -> not eligible
        );
        let n1 = nid("i", 1);
        let n2 = nid("i", 2);
        let n3 = nid("i", 3);
        sys.add_node(n1.clone(), r1);
        sys.add_node(n2.clone(), r2);
        sys.add_node(n3.clone(), r3);
        sys.content_mut().edges.push(Edge {
            src: (n1.clone(), ConcIdx(0)),
            tgt: (n2.clone(), PremIdx(0)),
        });
        sys.content_mut().edges.push(Edge {
            src: (n2.clone(), ConcIdx(0)),
            tgt: (n3.clone(), PremIdx(0)),
        });
        let out = compress_system(RenderSystem::from_prover(sys));
        assert!(out.nodes.iter().all(|(id, _)| id != &n2),
            "Coerce node should have been hidden");
    }
}
