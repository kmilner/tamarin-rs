// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, beschmi, racoucho1u, rsasse, PhilipLukertWork,
//   felixlinker, rkunnema, kevinmorio, yavivanov, arcz, Nick Moore,
//   katrielalex, addap, charlie-j, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Rewriting/Norm.hs,
//   lib/theory/src/Theory/Constraint/Solver/Contradictions.hs,
//   lib/theory/src/Theory/Constraint/Solver/Reduction.hs,
//   lib/theory/src/Theory/Constraint/Solver/Simplify.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Sapic/Substitution.hs,
//   lib/theory/src/Theory/Tools/EquationStore.hs

//! Port of `Theory.Constraint.Solver.Contradictions`.
//!
//! Identifies all reasons a `System` is contradictory. The full
//! Haskell version probes ~12 conditions. Most are pure structural
//! checks (cycles, false formulas, fact incompatibilities); a few
//! consult signature-aware helpers (`nf_via_haskell`,
//! `irreducible_fun_syms`, `enableDH`).  ForbiddenExp/ForbiddenBP are
//! gated on `enable_dh`/`enable_bp` inside `contradictions` itself
//! (matching HS Contradictions.hs `contradictions`); everything has a
//! faithful port below.
//!
//! In addition to the HS-ported conditions, RS emits several RS-only
//! soundness backstops at the IncompatibleEqs slot
//! (`has_sort_conflated_lvars`, `has_incompatible_edge_facts`,
//! `has_fresh_fact_sort_violation`) that have no Haskell counterpart;
//! see the per-check note at the IncompatibleEqs push in `contradictions`.

use std::collections::{BTreeMap, BTreeSet};

use crate::constraint::constraints::{LessAtom, NodeId};
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::System;

/// Reasons why a `System` is contradictory. Variants match Haskell
/// 1-to-1 so downstream pretty printers can reuse the names.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Contradiction {
    /// The `<` order has a cycle.
    Cyclic,
    /// The subterm constraints form a cycle.
    SubtermCyclic,
    /// Has terms that aren't in normal form modulo theory.
    NonNormalTerms,
    /// Forbidden Exp-down rule instance.
    ForbiddenExp,
    /// Forbidden bilinear pairing rule instance.
    ForbiddenBP,
    /// Has a forbidden KD-fact.
    ForbiddenKD,
    /// Has an impossible chain.
    ImpossibleChain,
    /// Has a forbidden chain.
    ForbiddenChain,
    /// Conflicting injective-fact instances.
    NonInjectiveFactInstance(NodeId, NodeId, NodeId),
    /// Equation store became false.
    IncompatibleEqs,
    /// `false` appeared in the formula store.
    FormulasFalse,
    /// A term is derived both before and after a learn step.
    SuperfluousLearn(tamarin_term::lterm::LNTerm, NodeId),
    /// There is a node strictly after `last(...)`.
    NodeAfterLast(NodeId, NodeId),
}

/// Collect every contradiction currently witnessed by the system.
pub fn contradictions(_ctxt: &ProofContext, sys: &System) -> Vec<Contradiction> {
    let mut out = Vec::new();
    // Mirror Haskell's `rawLessRel = sLessAtoms ++ rawEdgeRel` —
    // every graph edge induces a strict ordering src < tgt, and the
    // cyclic check has to fold both relations together.
    //
    // **Apply eq_store subst before cycle detection** (RS-only
    // compensation; NOT a step HS performs inside the cyclic check).
    // HS's `contradictions` calls `D.cyclic $ rawLessRel sys` directly
    // (Contradictions.hs), and `rawLessRel`/`rawEdgeRel`/`nodeConcNode`/
    // `nodePremNode` are pure projections that apply NO eq-store subst
    // (System.hs:1613-1622 `rawEdgeRel`/`rawLessRel`, 923-942
    // `nodePremNode = fst`/`nodeConcNode = fst`; Constraints.hs:133-138
    // `lessAtomToEdge`/`getLessRel`).  HS achieves canonical node
    // identity instead by running `substSystem` — which applies the
    // eq-store subst to sEdges/sLessAtoms/sNodes (Reduction.hs:571-602)
    // — BEFORE the contradiction check (e.g. `solve` → `simplifySystem`
    // ends in `void substSystem`, Simplify.hs:56-158, see line 82, immediately before
    // `contradictorySystem`, Sources.hs:176-178).
    //
    // RS's `subst_system` does the same propagation, but isn't always
    // called between every reduction step (e.g. between `solve_fact_eqs`
    // and the next `contradictions(...)` call from `is_finished`).  This
    // `resolve` reproduces HS's already-substituted state: it uses the
    // identical `apply_vterm`-on-Var op as `subst_system_once`'s `map_var`
    // (reduction.rs map_var), so it is a no-op (idempotent) when subst has
    // already run and a faithful compensation when it lags — never
    // producing a Cyclic that HS's post-substSystem state wouldn't. Pure
    // node-id lookups (LVar variable terms) — no term traversal needed. Do
    // not remove without proving RS always runs `subst_system` before
    // every `contradictions` call.
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let subst = &sys.eq_store.subst;
    let resolve = |v: &LVar| -> LVar {
        let t = tamarin_term::subst::apply_vterm(
            subst,
            Term::Lit(Lit::Var(v.clone())),
        );
        if let Term::Lit(Lit::Var(w)) = t { w } else { v.clone() }
    };
    let mut all_less: Vec<LessAtom> = sys.less_atoms.iter().map(|l| LessAtom {
        smaller: resolve(&l.smaller),
        larger: resolve(&l.larger),
        reason: l.reason,
    }).collect();
    for e in &sys.edges {
        all_less.push(LessAtom {
            smaller: resolve(&e.src.0),
            larger: resolve(&e.tgt.0),
            reason: crate::constraint::constraints::Reason::Adversary,
        });
    }
    // HS-faithful: `rawEdgeRel = sEdges ++ unsolvedChains` (System.hs:1613-
    // 1616) — unsolved chain goals contribute (c.0, p.0) to the less-
    // relation for cycle detection. Without this, RS misses cycles HS
    // catches when the cycle goes through an open chain. Root cause of
    // StatVerif KU(pcs) saturate over-enumeration.
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Chain(c, p) = g {
            all_less.push(LessAtom {
                smaller: resolve(&c.0),
                larger: resolve(&p.0),
                reason: crate::constraint::constraints::Reason::Adversary,
            });
        }
    }
    if cyclic(&all_less) {
        // H14-style diagnostic: dump the actual cycle path so a missing
        // less_atom (vs HS) can be identified by diffing the paths.
        if tamarin_utils::env_gate!("TAM_RS_DBG_CYCLE_PATH") {
            let cp = crate::constraint::solver::trace::case_path_string();
            let path = cyclic_with_path(&all_less);
            let path_str: Vec<String> = path.iter()
                .map(|n| format!("{}_{}", n.name, n.idx)).collect();
            eprintln!("[CYCLE_PATH] path={} cycle: {}", cp, path_str.join(" → "));
        }
        out.push(Contradiction::Cyclic);
    }
    // HS-faithful enumeration ORDER (`contradictions`, Contradictions.hs):
    // the returned list's HEAD is the recorded reason, so the push
    // order MUST mirror HS's `asum [...]` exactly:
    //   Cyclic, SubtermCyclic, NonNormalTerms, ForbiddenKD, ImpossibleChain,
    //   ForbiddenExp, ForbiddenBP, ForbiddenChain, IncompatibleEqs,
    //   FormulasFalse, then NonInjectiveFactInstance, then NodeAfterLast.
    //
    // RS-only soundness backstops are emitted at the IncompatibleEqs slot
    // (NOT a port of the `eqsIsFalse` check, HS Contradictions.hs): they
    // fire where HS's Maude unifier / `solveFactEqs` would already have
    // pruned the branch at CONSTRUCTION time (sort-aware unification, edge
    // tag-matching) so HS's `contradictions` never sees these systems. See
    // the per-check notes below.

    // The `rawLessRel` adjacency (`build_always_before_adj`) is the SAME
    // relation used by all four ordering-dependent checks below —
    // `has_forbidden_exp`, `has_forbidden_chain` (both via
    // `always_before_with`), and `non_injective_fact_instances` /
    // `node_after_last` (both via direct `.map()` walks). `contradictions`
    // holds `sys` immutable for its whole body with no early return, so the
    // relation is invariant across all four; build it ONCE and thread it
    // down. This is a distinct relation from the substituted `all_less`
    // used for the cyclic check above (that one applies the eq-store subst;
    // this one does not), so it is built separately.
    let ab_adj = sys.build_always_before_adj();

    // 2. SubtermCyclic — `isContradictory subtermStore`.
    if sys.subterm_store.is_false() { out.push(Contradiction::SubtermCyclic); }
    if has_subterm_cycle_contra(_ctxt, sys) { out.push(Contradiction::SubtermCyclic); }
    // 3. NonNormalTerms.
    if has_non_normal_terms(_ctxt, sys) { out.push(Contradiction::NonNormalTerms); }
    // 4. ForbiddenKD.
    if has_forbidden_kd(sys) { out.push(Contradiction::ForbiddenKD); }
    // 5. ImpossibleChain.
    if has_impossible_chain(_ctxt, sys) { out.push(Contradiction::ImpossibleChain); }
    // 6. ForbiddenExp (Contradictions.hs `hasForbiddenExp`).  Drops Exp-down rule
    //    instances whose g is simple, whose MsgVar args are KU-known earlier,
    //    and whose exponent factors are already in the up-premise.  enableDH.
    if _ctxt.maude.maude_sig().enable_dh && has_forbidden_exp(sys, &ab_adj) {
        out.push(Contradiction::ForbiddenExp);
    }
    // 7. ForbiddenBP (Contradictions.hs `hasForbiddenBP`).  Drops Pmult-down /
    //    Emap-down rule instances violating BP normal-form (redundant scalars,
    //    simplifiable em-then-exp compositions, Emap tag-order violations).
    //    enableBP.  (Chen_Kudla::key_agreement_reachable relies on this.)
    if _ctxt.maude.maude_sig().enable_bp && has_forbidden_bp(sys) {
        out.push(Contradiction::ForbiddenBP);
    }
    // 8. ForbiddenChain.
    if has_forbidden_chain(sys, &ab_adj) { out.push(Contradiction::ForbiddenChain); }
    // 9. IncompatibleEqs — HS-faithful: `eqsIsFalse sEqStore`
    //    (Contradictions.hs `contradictions`). The three preceding probes are RS-only
    //    soundness backstops, NOT a port of the eqsIsFalse check: each fires
    //    where HS's Maude unifier / `solveFactEqs` would have already pruned
    //    this branch at construction time. The real fix is upstream — make
    //    RS's edge insertion / fact-eq solving reject these systems at
    //    construction (as HS does), after which all three become dead code.
    //    - has_sort_conflated_lvars: MOST suspect — under HS semantics
    //      `~x:Pub.58` and `~x:Fresh.58` are DISTINCT, legitimately-coexisting
    //      vars (LVar Eq is `i1==i2 && s1==s2 && n1==n2`, LTerm.hs:516-517), so
    //      this has genuine over-fire risk relative to HS; if RS conflates them
    //      it is an RS renaming/node-id bug this probe is masking.
    //    - has_incompatible_edge_facts / has_fresh_fact_sort_violation: lower
    //      risk — mirror real HS invariants (edges connect equal fact tags;
    //      Fr requires Fresh sort) that the unifier/solveFactEqs enforce.
    if has_sort_conflated_lvars(sys) { out.push(Contradiction::IncompatibleEqs); }
    if has_incompatible_edge_facts(sys) { out.push(Contradiction::IncompatibleEqs); }
    if has_fresh_fact_sort_violation(sys) { out.push(Contradiction::IncompatibleEqs); }
    if sys.eq_store.is_false() { out.push(Contradiction::IncompatibleEqs); }
    // 10. FormulasFalse — `gfalse ∈ sFormulas` (our `Disj([])`).
    if has_false_formula(sys) { out.push(Contradiction::FormulasFalse); }
    // 11. NonInjectiveFactInstance (×n) — BEFORE NodeAfterLast, matching HS's
    //     list concatenation order in `contradictions` (Contradictions.hs).
    out.extend(non_injective_fact_instances(_ctxt, sys, ab_adj.map()));
    // 12. NodeAfterLast (×n).
    out.extend(node_after_last(sys, ab_adj.map()));
    out
}

/// `hasNonNormalTerms` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasNonNormalTerms`
/// (`Contradictions.hs`).
///
/// HS spec:
/// ```haskell
/// hasNonNormalTerms sig se =
///     any (not . (`runReader` hnd) . nf') (maybeNonNormalTerms hnd se)
///   where hnd = L.get sigmMaudeHandle sig
/// ```
///
/// And `nf' = nfViaHaskell` (Norm.hs:130-131) — a PURE structural
/// NF check that walks the term tree against the reducibility
/// patterns in Norm.hs:60-99.  This is NOT a Maude-driven check;
/// it's pattern-based on the signature's reducibility shape.
///
/// Walks every node's premise, conclusion, action facts and
/// `new_vars`; for each subterm whose head could be reducible,
/// asks `nf_via_haskell` whether the term is in normal form.  If
/// any term is not in NF, the system is contradictory (we only
/// ever construct normal-form-respecting traces).
///
/// Skip optimization: when the proof context's signature has an
/// empty `reducible_fun_syms` set (e.g. pair-only or hashing-only,
/// which have no rewrite rules with a reducible head — all
/// destructors come from intruder rules, not subterm rewriting),
/// no term can be in non-normal form structurally, so we skip
/// the per-term check.
///
/// `nf_via_haskell` ports `nf'` (Norm.hs:130-131): a pure structural
/// NF check, not the Maude-driven `nfViaMaude`.
fn has_non_normal_terms(ctx: &ProofContext, sys: &System) -> bool {
    // NF check is cheap (pure structural walk) but we call this
    // from `is_finished` on every expand step, so the early-exit
    // still helps for pair-only theories with no subterm rewrite
    // rules.
    let sig = ctx.maude.maude_sig();
    if sig.reducible_fun_syms.is_empty() { return false; }
    let irreducible = &sig.irreducible_fun_syms_fast;

    // Short-circuiting structural walk: the moment a candidate subterm — a
    // variable or a reducible-headed `App` (the `_` arm of
    // `maybe_not_nf_subterms`) — fails `nf_via_haskell`, the system has a
    // non-normal term.  Constants are in NF; irreducible-headed apps recurse
    // into their args.  This is the boolean OR of `maybeNonNormalTerms` ∘
    // `maybeNotNfSubterms` over `nf'` (Norm.hs:130-131, see line 131), but without building the
    // `BTreeSet` of every candidate: the dedup is irrelevant to an OR, and
    // `nf_via_haskell` is a side-effect-free structural check, so visiting a
    // subterm more than once cannot change the verdict.
    fn any_non_nf(
        sig: &tamarin_term::maude_sig::MaudeSig,
        irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
        t: &tamarin_term::lterm::LNTerm,
    ) -> bool {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Con(_)) => false,
            // Bare variables are always in normal form (`go_nf` returns true
            // for every `Lit`), so skip the `nf_via_haskell` call.
            Term::Lit(Lit::Var(_)) => false,
            Term::App(sym, args) if irreducible.contains(sym) => {
                args.iter().any(|a| any_non_nf(sig, irreducible, a))
            }
            _ => !tamarin_term::norm::nf_via_haskell(sig, t),
        }
    }

    for (_, rule) in sys.nodes.iter() {
        for f in rule.premises.iter().chain(&rule.conclusions).chain(&rule.actions) {
            for t in f.terms.iter() {
                if any_non_nf(&sig, irreducible, t) { return true; }
            }
        }
        for t in &rule.new_vars {
            if any_non_nf(&sig, irreducible, t) { return true; }
        }
    }
    false
}

/// `maybeNotNfSubterms` — collect subterms that might not be in
/// normal form.  Constants in NF; irreducible-headed apps recurse
/// into args; anything else (variables OR reducible-headed apps)
/// is returned as a candidate.
///
/// Variables MUST be included — for `SubstNfChecker`'s nf check,
/// a variable `z` becomes a reducible term after the variant subst
/// (e.g. `{z → verify(s,m,pkA)}`).  Without including vars we miss
/// the SplitG variant filter and the picked variant pulls the
/// reducible term into the system unfiltered.
/// Mirrors Haskell `maybeNotNfSubterms` exactly (Norm.hs:162-168):
/// the `_` arm catches both `Lit (Var _)` and reducible `FApp`.
///
/// For `has_non_normal_terms` the variable case is harmless:
/// variables are structurally in NF under `nf_via_haskell`, so an
/// included bare variable never triggers a non-normal-term verdict.
fn maybe_not_nf_subterms(
    irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    t: &tamarin_term::lterm::LNTerm,
    out: &mut std::collections::BTreeSet<tamarin_term::lterm::LNTerm>,
) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Con(_)) => {}
        Term::App(sym, args) if irreducible.contains(sym) => {
            for a in args.iter() {
                maybe_not_nf_subterms(irreducible, a, out);
            }
        }
        _ => { out.insert(t.clone()); }
    }
}

/// Run `has_subterm_cycle` against the system's positive subterm
/// dag.  Equivalent to one prong of Haskell's `simpSubterms` →
/// `hasSubtermCycle` check; we run it eagerly during contradiction
/// detection (the `simpSubterms` simplification pass — see
/// `propagate_subterm_obvious` in `simplify.rs` — handles the rest).
fn has_subterm_cycle_contra(ctx: &ProofContext, sys: &System) -> bool {
    let reducible = &ctx.maude.maude_sig().reducible_fun_syms_fast;
    crate::tools::subterm_store::has_subterm_cycle(reducible, &sys.subterm_store)
}

/// `hasImpossibleChain` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasImpossibleChain`
/// (`Contradictions.hs`).
///
/// For every chain goal `(c, p)`:
///   - Collect the root symbols reachable from `t_start = c`'s
///     KD-conclusion term via deconstruction (`possible_root_syms`).
///   - Collect the possible root symbols of `t_end = p`'s KD-prem
///     term (`possible_end_syms` — the set of root symbols any
///     subterm of `t_end` could have).
///
/// If both sets are determined and don't intersect, the chain
/// can never be solved — declare contradictory.
///
/// The DH/BP-specific cases (FExp/FPMult/FEMap) are handled via
/// `dh_view` and the `viewTerm2` special-cases in `possible_end_syms`
/// / `possible_root_syms` (Contradictions.hs).
fn has_impossible_chain(ctx: &ProofContext, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    let dbg = tamarin_utils::env_gate!("TAM_RS_DBG_IMPOSSIBLE_CHAIN");

    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        let Goal::Chain(c, p) = g else { continue };
        let c_rule = sys.nodes.iter().find(|(id, _)| id == &c.0)
            .map(|(_, r)| r);
        let p_rule = sys.nodes.iter().find(|(id, _)| id == &p.0)
            .map(|(_, r)| r);
        let (Some(c_rule), Some(p_rule)) = (c_rule, p_rule) else { continue };
        let conc_fact = match c_rule.conclusions.get(c.1.0) {
            Some(f) => f, None => continue,
        };
        let prem_fact = match p_rule.premises.get(p.1.0) {
            Some(f) => f, None => continue,
        };
        if !matches!(conc_fact.tag, FactTag::Kd) { continue; }
        if !matches!(prem_fact.tag, FactTag::Kd) { continue; }
        let t_start = match conc_fact.terms.first() { Some(t) => t, None => continue };
        let t_end = match prem_fact.terms.first() { Some(t) => t, None => continue };
        let poss_opt = possible_root_syms(t_start);
        if dbg {
            use tamarin_term::pretty::pretty_lnterm;
            eprintln!("[ic] t_start={} t_end={} poss_root={:?} pc_true_subterm={}",
                pretty_lnterm(t_start), pretty_lnterm(t_end),
                poss_opt.is_some(), ctx.pc_true_subterm);
        }
        let Some(poss) = poss_opt else { continue };
        // Haskell:
        //   if pcTrueSubterm
        //      then do req_end <- rootSym t_end
        //              return $ not (req_end `elem` poss)
        //      else do req_end <- possibleEndSyms t_end
        //              return $ null (req_end `intersect` poss)
        // True branch: STRICT — fire if the chain-end's root sym is
        // not among the possible decomposition syms.
        // False branch: LENIENT — fire only if NO subterm sym of the
        // chain-end matches any possible decomposition sym.
        let fires = if ctx.pc_true_subterm {
            match root_sym(t_end) {
                Some(req) => !poss.iter().any(|s| s == &req),
                None => false,
            }
        } else {
            match possible_end_syms(t_end) {
                Some(req) => poss.iter().all(|s| !req.contains(s)),
                None => false,
            }
        };
        if dbg {
            eprintln!("[ic] fires={}", fires);
        }
        if fires {
            return true;
        }
    }
    false
}

/// Determines the root symbol of a term if it can be statically
/// fixed.  Mirrors Haskell's `rootSym`:
///   - `FApp sym _` → `Some(Right sym)`
///   - `Lit _` of sort Msg → `None` (a Msg-var could be anything)
///   - `Lit _` otherwise → `Some(Left sort)` (sort fixes the value)
///
/// Encoding in Rust: we use a tagged enum-like type expressed as
/// an `Option<RootSym>` where RootSym has both branches.
#[derive(Clone, PartialEq, Eq)]
enum RootSym {
    Sym(tamarin_term::function_symbols::FunSym),
    Sort(tamarin_term::lterm::LSort),
}

fn root_sym(t: &tamarin_term::lterm::LNTerm) -> Option<RootSym> {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::App(sym, _) => Some(RootSym::Sym(sym.clone())),
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => None,
        Term::Lit(Lit::Var(v)) => Some(RootSym::Sort(v.sort)),
        Term::Lit(Lit::Con(n)) => {
            use tamarin_term::lterm::NameTag;
            let s = match n.tag {
                NameTag::Pub => LSort::Pub,
                NameTag::Fresh => LSort::Fresh,
                NameTag::Nat => LSort::Nat,
                NameTag::Node => LSort::Node,
            };
            Some(RootSym::Sort(s))
        }
    }
}

/// Match DH-special cases (`FExp`, `FPMult`, `FEMap`) of HS's
/// `viewTerm2`.  Returns one of:
///   - `Some(DhKind::Exp(base))`: term is `exp(base, _)` — caller
///     should recurse into `base` only (the exponent isn't reachable
///     via subterm decomposition).
///   - `Some(DhKind::PMult(scalar_base))`: term is `pmult(_, base)` —
///     recurse into `base` only, prepend `[exp, pmult, emap]`.
///   - `Some(DhKind::EMap)`: term is `em(_, _)` — return `[emap]`.
///   - `None`: not a DH-special form; fall back to generic walk.
fn dh_view(t: &tamarin_term::lterm::LNTerm) -> Option<DhView<'_>> {
    use tamarin_term::function_symbols::{exp_sym, pmult_sym, CSym, FunSym};
    use tamarin_term::term::Term;
    if let Term::App(sym, args) = t {
        match sym {
            FunSym::NoEq(s) if *s == exp_sym() && args.len() == 2 =>
                Some(DhView::Exp(&args[0])),
            FunSym::NoEq(s) if *s == pmult_sym() && args.len() == 2 =>
                Some(DhView::PMult(&args[1])),
            FunSym::C(CSym::EMap) => Some(DhView::EMap),
            _ => None,
        }
    } else { None }
}

enum DhView<'a> {
    Exp(&'a tamarin_term::lterm::LNTerm),
    PMult(&'a tamarin_term::lterm::LNTerm),
    EMap,
}

/// `possibleEndSyms`: HS-faithful port using `viewTerm2` to apply DH-
/// special cases (FExp/FPMult/FEMap).  Mirrors `possibleEndSyms` in
/// Contradictions.hs (defined locally inside `hasImpossibleChain`).
fn possible_end_syms(
    t: &tamarin_term::lterm::LNTerm,
) -> Option<Vec<RootSym>> {
    use tamarin_term::function_symbols::{exp_sym, pmult_sym, CSym, FunSym};
    use tamarin_term::term::Term;
    // HS `viewTerm2` special cases first:
    match dh_view(t) {
        Some(DhView::Exp(base)) => {
            // ((Right (NoEq expSym)):) <$> possibleEndSyms a
            let mut out = vec![RootSym::Sym(FunSym::NoEq(exp_sym()))];
            let rest = possible_end_syms(base)?;
            out.extend(rest);
            return Some(out);
        }
        Some(DhView::PMult(base)) => {
            // ((Right <$> [NoEq expSym, NoEq pmultSym, C EMap])++) <$> possibleEndSyms a
            let mut out = vec![
                RootSym::Sym(FunSym::NoEq(exp_sym())),
                RootSym::Sym(FunSym::NoEq(pmult_sym())),
                RootSym::Sym(FunSym::C(CSym::EMap)),
            ];
            let rest = possible_end_syms(base)?;
            out.extend(rest);
            return Some(out);
        }
        Some(DhView::EMap) => {
            return Some(vec![RootSym::Sym(FunSym::C(CSym::EMap))]);
        }
        None => {}
    }
    // Generic (non-DH) case.  HS:
    //   _ -> case viewTerm t of
    //          Lit _ -> (:[]) <$> rootSym t
    //          FApp o args -> ((Right o):) . concat <$> mapM possibleEndSyms args
    let head = root_sym(t)?;
    match t {
        Term::App(_, args) => {
            let mut out = vec![head];
            for a in args.iter() {
                let sub = possible_end_syms(a)?;
                out.extend(sub);
            }
            Some(out)
        }
        Term::Lit(_) => Some(vec![head]),
    }
}

/// `possibleRootSyms`: HS-faithful port using `viewTerm2` to apply DH-
/// special cases.  Mirrors `possibleRootSyms` in Contradictions.hs
/// (defined locally inside `hasImpossibleChain`).  Returns `Some([])`
/// (no possible decomposition) when the term cannot contain fresh
/// names or private functions — equivalent to
/// `isForbiddenDeconstruction`.
fn possible_root_syms(
    t: &tamarin_term::lterm::LNTerm,
) -> Option<Vec<RootSym>> {
    use tamarin_term::function_symbols::{exp_sym, pmult_sym, CSym, FunSym};
    use tamarin_term::term::Term;
    if never_contains_fresh_priv(t) {
        return Some(Vec::new());
    }
    // HS `viewTerm2` special cases first:
    match dh_view(t) {
        Some(DhView::Exp(base)) => {
            let mut out = vec![RootSym::Sym(FunSym::NoEq(exp_sym()))];
            let rest = possible_root_syms(base)?;
            out.extend(rest);
            return Some(out);
        }
        Some(DhView::PMult(base)) => {
            let mut out = vec![
                RootSym::Sym(FunSym::NoEq(exp_sym())),
                RootSym::Sym(FunSym::NoEq(pmult_sym())),
                RootSym::Sym(FunSym::C(CSym::EMap)),
            ];
            let rest = possible_root_syms(base)?;
            out.extend(rest);
            return Some(out);
        }
        Some(DhView::EMap) => {
            return Some(vec![RootSym::Sym(FunSym::C(CSym::EMap))]);
        }
        None => {}
    }
    // Generic case.
    let head = root_sym(t)?;
    match t {
        Term::App(_, args) => {
            let mut out = vec![head];
            for a in args.iter() {
                let sub = possible_root_syms(a)?;
                out.extend(sub);
            }
            Some(out)
        }
        Term::Lit(_) => Some(vec![head]),
    }
}

/// `hasForbiddenKD` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenKD`
/// (`Contradictions.hs`).
///
/// A KD-conclusion `KD(t)` is forbidden if *no instance* of `t`
/// can ever contain fresh names or private function symbols —
/// because then the adversary already knows `t` (it can be
/// derived from public constants and public function symbols
/// alone), so deconstructing it via KD-chain would be wasteful
/// and violates normal form N6.
///
/// `neverContainsFreshPriv t`:
///   - no subterm uses a private function symbol, AND
///   - every literal (variable or constant) has sort in
///     `{Pub, Nat, Node}` — no `Msg` or `Fresh` literals.
///
/// (A `Msg` literal could instantiate to anything including
/// fresh, so we must conservatively say it *might* contain
/// fresh.  Same for `Fresh` literals.)
///
/// Skipped in diff mode (Haskell guards with `not isDiffSystem`,
/// where `isDiffSystem = L.get sDiffSystem` — a dedicated boolean on
/// the regular `System`, NOT the LHS/RHS `Side`, which in HS lives
/// only on `DiffSystem`).
///
/// LATENT DIVERGENCE: RS has no `sDiffSystem` field, so this guard
/// proxies it via `sys.side`. `formula_to_system` always sets `side`
/// to `None` (diff is not yet handled), so the guard never fires for a
/// diff system. Harmless today (no diff support in the corpus); when
/// diff support lands, add a real `diff_system: bool` to `System` and
/// guard on it instead of `side`.
fn has_forbidden_kd(sys: &System) -> bool {
    use crate::fact::FactTag;
    // Diff-system guard — see LATENT DIVERGENCE note above; `side` is a
    // stand-in for the missing `sDiffSystem` boolean.
    if sys.side.is_some() { return false; }
    for (_, rule) in sys.nodes.iter() {
        for fa in &rule.conclusions {
            if !matches!(fa.tag, FactTag::Kd) { continue; }
            let Some(t) = fa.terms.first() else { continue };
            if never_contains_fresh_priv(t) { return true; }
        }
    }
    false
}

/// True iff no instance of `t` can ever contain fresh names or
/// private function symbols.  Walks the term; rejects Msg/Fresh
/// literals (they could instantiate to anything) and any private
/// function symbol.
fn never_contains_fresh_priv(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{FunSym, Privacy};
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            !matches!(v.sort, LSort::Msg | LSort::Fresh)
        }
        Term::Lit(Lit::Con(n)) => {
            !matches!(n.tag, NameTag::Fresh)
        }
        Term::App(sym, args) => {
            // Reject if the head is a private function symbol.
            let is_private = match sym {
                FunSym::NoEq(s) => s.privacy == Privacy::Private,
                _ => false,
            };
            if is_private { return false; }
            args.iter().all(never_contains_fresh_priv)
        }
    }
}

/// `hasForbiddenChain` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenChain`
/// (`Contradictions.hs`).
///
/// Detects normal-form-violating chains.  A `Chain(c, p)` goal is
/// forbidden when:
///
///   1. The chain start (KD-conc at `c`) is a *message variable*
///      (LVar of sort Msg) — i.e. the adversary doesn't know what
///      term they're deconstructing.
///   2. The chain end (KD-prem at `p`) is *not* an `IEquality`
///      rule instance (those are exempt; they're the diff-mode
///      equality bridge).
///   3. There exists a `KU(t_start)` action somewhere in the
///      system whose node strictly *precedes* the chain start
///      `nodeConcNode c`.
///
/// All three conditions together violate normal form invariant
/// N6: if the adversary already knew `t_start` (KU before), they
/// shouldn't be deconstructing it (KD chain) afterwards.  Hits an
/// otherwise-undetected contradiction earlier than the search
/// would, pruning a search branch.
// equivalence-class value set; membership/union only, never iterated into output;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn has_forbidden_chain(
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::lterm::is_msg_var;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Build a disj-equivalence relation over Msg-Vars: two vars are
    // equivalent if, in some disj subst, they both have the same
    // non-trivial image.  Mirrors HS's behavior at this case state
    // where simp would have folded the disj down to one subst before
    // the contradictions check — but RS's variant-pick produces a
    // 2-subst disj that simp doesn't fold (subst[0] keeps the var,
    // subst[1] binds it to a concrete term).  HS's path commits to
    // subst[0] via simpMinimize+substCreatesNonNormalTerms on subst[1];
    // since RS's NF check doesn't catch this case, walk the disj
    // substs directly and treat vars that coincide in any branch as
    // equivalent.
    //
    // For each disj subst, group vars by their image term.  Vars
    // sharing a non-trivial image in some subst are equivalent under
    // that branch.  Conservative: treat them as equivalent for the
    // ForbiddenChain check, which means firing on chains where t_start
    // would equal a KU-action term in any branch.  Root cause of
    // StatVerif Resolve2_d_1_check_getmsg_d_0_fst_d_1_check_getmsg
    // case survival.
    let mut equivalence_classes: tamarin_utils::FastMap<
        tamarin_term::lterm::LVar,
        std::collections::HashSet<tamarin_term::lterm::LVar>> =
        tamarin_utils::FastMap::default();
    // Compute a coarse "head signature" of a term for grouping: the
    // outermost function symbol (or Var/Const tag).  Two Msg-Vars
    // mapped to App-headed terms with the same outer function symbol
    // in the same disj subst are treated as candidate-equivalent — they
    // would unify modulo the inner witness aliasing.  This catches HS's
    // variant-pick behavior where Maude returns multiple unifiers but
    // simp collapses them to a single canonical form.
    let term_head_sig = |t: &tamarin_term::lterm::LNTerm| -> Option<Vec<u8>> {
        match t {
            Term::App(tamarin_term::function_symbols::FunSym::NoEq(sym), _) =>
                Some(sym.name.to_vec()),
            _ => None,
        }
    };
    for disj in &sys.eq_store.conj {
        for subst in &disj.substs {
            // Group Msg-vars by their image's outermost function symbol.
            let mut by_head: tamarin_utils::FastMap<
                Vec<u8>,
                Vec<tamarin_term::lterm::LVar>> = tamarin_utils::FastMap::default();
            for (v, t) in subst.iter() {
                if v.sort != tamarin_term::lterm::LSort::Msg { continue; }
                let head = match term_head_sig(t) {
                    Some(h) => h, None => continue,
                };
                by_head.entry(head).or_default().push(v.clone());
            }
            for (_, vars) in by_head {
                if vars.len() < 2 { continue; }
                for vi in &vars {
                    for vj in &vars {
                        if vi == vj { continue; }
                        equivalence_classes.entry(vi.clone())
                            .or_default().insert(vj.clone());
                    }
                }
            }
        }
    }

    // The `alwaysBefore` adjacency (`ab_adj`) is built once by the caller
    // (`contradictions`) and shared across all ordering checks; queried here
    // via `always_before_with` in the chain/node/goal loops below.
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        let Goal::Chain(c, p) = g else { continue };
        // Look up the chain-conc fact.
        let c_rule = sys.nodes.iter().find(|(id, _)| id == &c.0)
            .map(|(_, r)| r);
        let p_rule = sys.nodes.iter().find(|(id, _)| id == &p.0)
            .map(|(_, r)| r);
        let (Some(c_rule), Some(p_rule)) = (c_rule, p_rule) else { continue };
        let conc_fact = match c_rule.conclusions.get(c.1.0) {
            Some(f) => f, None => continue,
        };
        let prem_fact = match p_rule.premises.get(p.1.0) {
            Some(f) => f, None => continue,
        };
        // Chain ends and starts must both be KD facts.
        if !matches!(conc_fact.tag, FactTag::Kd) { continue; }
        if !matches!(prem_fact.tag, FactTag::Kd) { continue; }
        // Mirror HS `substNodes` — node conc terms are kept eq-store-
        // substituted by `substSystem` (Reduction.hs:609-611 `modM sNodes . M.map
        // . apply =<< getM sSubst`, run after every reduction/variant fold),
        // and the contradiction check runs after simplifySystem→substSystem
        // (Sources.hs:177-178), so HS's `nodeConcFact` (System.hs:937-938, a
        // plain `nodeRule` lookup that does NOT apply eqsSubst at read time)
        // already returns the canonical term.  RS mirrors substNodes in
        // `subst_system_once`; apply eq_store.subst here so t_start matches
        // HS's already-substituted value.  Idempotent on the canonical path;
        // compensates only if RS's subst_system lagged.
        let raw_t_start = match conc_fact.terms.first() { Some(t) => t.clone(), None => continue };
        let t_start_owned = tamarin_term::subst::apply_vterm(&sys.eq_store.subst, raw_t_start);
        let t_start = &t_start_owned;
        // (1) Chain starts at a message variable.
        if !is_msg_var(t_start) { continue; }
        // (2) End rule is not IEquality.
        if matches!(&p_rule.info,
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IEquality)) {
            continue;
        }
        let t_start_var = match t_start {
            Term::Lit(Lit::Var(v)) => v.clone(),
            _ => continue,
        };
        // Build the set of candidate-equal Msg-Vars: t_start itself
        // plus any var in its disj-equivalence class.
        let mut candidate_vars: tamarin_utils::FastSet<tamarin_term::lterm::LVar>
            = tamarin_utils::FastSet::default();
        candidate_vars.insert(t_start_var.clone());
        if let Some(eqs) = equivalence_classes.get(&t_start_var) {
            for v in eqs {
                candidate_vars.insert(v.clone());
            }
        }
        let candidate_terms: Vec<tamarin_term::lterm::LNTerm> = candidate_vars.iter()
            .map(|v| Term::Lit(Lit::Var(v.clone()))).collect();
        // (3) Some KU(t_start) action node precedes the chain
        // start `c.0`.  HS-faithful: `allKUActions` (System.hs:1582-1585)
        // unions BOTH `unsolvedActionAtoms` (unsolved ActionG goals)
        // AND node `rActs` lists.
        //
        // Walk node actions first:
        for (id, rule) in sys.nodes.iter() {
            for fa in &rule.actions {
                if !matches!(fa.tag, FactTag::Ku) { continue; }
                let t_ku = match fa.terms.first() { Some(t) => t, None => continue };
                if !candidate_terms.contains(t_ku) { continue; }
                if id == &c.0 { continue; }
                if sys.always_before_with(ab_adj, id, &c.0) {
                    return true;
                }
            }
        }
        // Then walk unsolved ActionG goals (HS's `unsolvedActionAtoms`):
        for (g, gst) in sys.goals.iter() {
            if gst.solved { continue; }
            let Goal::Action(id, fa) = g else { continue };
            if !matches!(fa.tag, FactTag::Ku) { continue; }
            let t_ku = match fa.terms.first() { Some(t) => t, None => continue };
            if !candidate_terms.contains(t_ku) { continue; }
            if id == &c.0 { continue; }
            if sys.always_before_with(ab_adj, id, &c.0) {
                return true;
            }
        }
    }
    false
}

/// HS-faithful port of `hasForbiddenExp`
/// (`Theory.Constraint.Solver.Contradictions`).
///
/// Detects an `Exp-down` (d_exp) rule instance whose conclusion is
/// not allowed in a normal dependency graph.
///
/// The check: for each node whose rule has shape
///   [ KD(p1 :: exp(_, _)), KU(b) ] -> [ KD(conc) ]
/// the rule is forbidden iff
///   (1) conc has shape `KD(exp(g, c))` AND
///       - `g` is simple (no fresh names/vars, no private syms)
///       - all `MsgVar` args of `g` are KU-known earlier than `i`
///       - every non-inverse factor of `c` is already a factor of `b`
///         (`niFactors c \\ niFactors b == []`)
///   OR
///   (2) conc has shape `KD(g)` (not an exp) AND
///       - `g` is simple
///       - all `MsgVar` args of `g` are KU-known earlier than `i`
///
/// Without this, RS lets through every variant d_exp chain extend
/// regardless of whether the resulting destruction is constructible
/// from the original KU premise — at the saturate step for
/// `KU(exp(t.1,t.2))`, RS produces 16 cases vs HS's 3, because each
/// of the 4 surviving d_exp chain-extend variants would be dropped
/// by ForbiddenExp in HS.
fn has_forbidden_exp(
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    use crate::fact::FactTag;
    use crate::rule::{IntrRuleACInfo, RuleInfo};
    use tamarin_term::function_symbols::{EXP_SYM_STRING, FunSym};
    use tamarin_term::lterm::{LNTerm, LSort, is_msg_var, frees, contains_private, sort_of_name};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // `niFactors` / multiset-subset are shared at module scope
    // (`ni_factors` / `ni_factors_subset`).

    // `isSimpleTerm`: HS Term/LTerm.hs:383-386.
    // `not (containsPrivate t) && all (LSortFresh /=) (lits t)`.
    fn is_simple_term(t: &LNTerm) -> bool {
        if contains_private(t) { return false; }
        let mut ok = true;
        let mut visit = |term: &LNTerm| {
            match term {
                Term::Lit(Lit::Var(v))
                    if v.sort == LSort::Fresh => { ok = false; }
                Term::Lit(Lit::Con(c))
                    if sort_of_name(c) == LSort::Fresh => {
                        ok = false;
                    }
                _ => {}
            }
        };
        fn walk(t: &LNTerm, f: &mut dyn FnMut(&LNTerm)) {
            f(t);
            if let Term::App(_, args) = t {
                for a in args.iter() { walk(a, f); }
            }
        }
        walk(t, &mut visit);
        ok
    }

    // `kFactView` is shared at module scope (returns `KDir`/term).
    fn view_exp(t: &LNTerm) -> Option<(&LNTerm, &LNTerm)> {
        if let Term::App(FunSym::NoEq(s), args) = t {
            if s.name == EXP_SYM_STRING && args.len() == 2 {
                return Some((&args[0], &args[1]));
            }
        }
        None
    }

    // `allKUActions`: HS System.hs:1582-1585.  Unions
    // `unsolvedActionAtoms sys` (open KU goals) and the
    // `rActs` lists of each node.  Returns (NodeId, fact, term).
    // For "knownEarlier" we only need (NodeId, term).
    let mut all_ku: Vec<(NodeId, LNTerm)> = Vec::new();
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Action(i, fa) = g {
            if matches!(fa.tag, FactTag::Ku) {
                if let Some(m) = fa.terms.first() {
                    all_ku.push((i.clone(), m.clone()));
                }
            }
        }
    }
    for (id, rule) in sys.nodes.iter() {
        for fa in &rule.actions {
            if matches!(fa.tag, FactTag::Ku) {
                if let Some(m) = fa.terms.first() {
                    all_ku.push((id.clone(), m.clone()));
                }
            }
        }
    }

    // The `alwaysBefore` adjacency (`ab_adj`) is built once by the caller
    // (`contradictions`) and shared across all ordering checks; queried here
    // via `always_before_with` in the node loop and the `earlier_msg_vars`
    // scan below.
    // Mirror HS `forbiddenDExp` exactly.
    for (i, ru) in sys.nodes.iter() {
        // Only intruder DestrRules can be exp-down; cheap pre-filter.
        if !matches!(&ru.info,
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(_, _, _, _)))
        { continue; }
        if ru.premises.len() != 2 { continue; }
        if ru.conclusions.len() != 1 { continue; }
        let p1 = &ru.premises[0];
        let p2 = &ru.premises[1];
        let conc = &ru.conclusions[0];

        let (dt1, p1_term) = match k_fact_view(p1) { Some(x) => x, None => continue };
        if dt1 != KDir::Dn { continue; }
        if view_exp(p1_term).is_none() { continue; }
        let (dt2, b) = match k_fact_view(p2) { Some(x) => x, None => continue };
        if dt2 != KDir::Up { continue; }

        let (dtc, conc_term) = match k_fact_view(conc) { Some(x) => x, None => continue };
        if dtc != KDir::Dn { continue; }

        // The "earlier MsgVars" set: KU-known terms which are MsgVars
        // whose node `j` is `alwaysBefore` `i`.
        let earlier_msg_vars = || -> Vec<LNTerm> {
            let mut out = Vec::new();
            for (j, t) in &all_ku {
                if !is_msg_var(t) { continue; }
                if sys.always_before_with(ab_adj, j, i) {
                    out.push(t.clone());
                }
            }
            out
        };
        let all_msg_vars_known_earlier = |g: &LNTerm| -> bool {
            let mvs = earlier_msg_vars();
            // `varTerm <$> frees g` then keep only MsgVars.
            for v in frees(g) {
                let vt: LNTerm = Term::Lit(Lit::Var(v.clone()));
                if !is_msg_var(&vt) { continue; }
                if !mvs.contains(&vt) {
                    return false;
                }
            }
            true
        };

        let forbidden = if let Some((g, c)) = view_exp(conc_term) {
            // (1) conc = exp(g, c): g simple + all msg vars known earlier
            //     + niFactors c \\ niFactors b == []
            if !is_simple_term(g) || !all_msg_vars_known_earlier(g) { false }
            else {
                // niFactors c \\ niFactors b == [] (multiset subset).
                ni_factors_subset(c, b)
            }
        } else {
            // (2) conc = g (not exp-shaped)
            is_simple_term(conc_term) && all_msg_vars_known_earlier(conc_term)
        };

        if forbidden {
            if tamarin_utils::env_gate!("TAM_RS_DBG_FORBIDDEN_EXP") {
                eprintln!("[FORBIDDEN_EXP] node={:?} ru_concl={:?}", i, conc_term);
            }
            return true;
        }
    }
    false
}

/// `hasForbiddenBP` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenBP`
/// (`Contradictions.hs`).  Gated on `enableBP` at the caller.
///
/// Detects three non-normal bilinear-pairing rule instance patterns:
///   1. `isForbiddenDPMult`: `Pmult-down` with redundant scalar
///      (Contradictions.hs `isForbiddenDPMult`).
///   2. `isForbiddenDEMap`:  `Emap-down` → `Exp-down` simplifiable
///      composition (Contradictions.hs `isForbiddenDEMap`).
///   3. `isForbiddenDEMapOrder`: `Emap-down` premise ordering
///      violating tag-priority normal form
///      (Contradictions.hs `isForbiddenDEMapOrder`).
///
/// First found case suffices to flag the system contradictory.
///
/// Triggering example: Chen_Kudla::key_agreement_reachable.  RS's
/// variant fan-out (vs HS's deferred SplitG) produced extra KGC_Setup
/// and Init_1 source cases at runtime that HS dropped via
/// `hasForbiddenBP` (the d_pmult case applied to a KGC_Setup chain
/// is overcomplicated under HS's normal-form).  Without this port,
/// RS kept 5 cases where HS keeps 2 — diverging the proof shape.
fn has_forbidden_bp(sys: &System) -> bool {
    if sys.nodes.iter().any(|(_, ru)| is_forbidden_d_pmult(ru)) {
        if tamarin_utils::env_gate!("TAM_RS_DBG_FORBIDDEN_BP") {
            eprintln!("[FORBIDDEN_BP] dPMult fired");
        }
        return true;
    }
    if sys.nodes.iter().any(|(i, ru)| is_forbidden_d_emap(sys, i, ru)) {
        if tamarin_utils::env_gate!("TAM_RS_DBG_FORBIDDEN_BP") {
            eprintln!("[FORBIDDEN_BP] dEMap fired");
        }
        return true;
    }
    if sys.nodes.iter().any(|(i, ru)| is_forbidden_d_emap_order(sys, i, ru)) {
        if tamarin_utils::env_gate!("TAM_RS_DBG_FORBIDDEN_BP") {
            eprintln!("[FORBIDDEN_BP] dEMapOrder fired");
        }
        return true;
    }
    false
}

/// `isForbiddenDPMult` — Contradictions.hs.
///
/// A `Pmult-down` rule of shape `[KD(pmult(s,p)), KU(b)] → [KD(pmult(c,p))]`
/// is forbidden when:
///   - `p` never contains fresh/private terms, AND
///   - every non-inverse factor of `c` is also a non-inverse factor of `b`.
fn is_forbidden_d_pmult<I>(ru: &crate::rule::Rule<crate::rule::RuleInfo<I, crate::rule::IntrRuleACInfo>>) -> bool {
    if ru.premises.len() != 2 { return false; }
    if ru.conclusions.len() != 1 { return false; }

    let p1 = &ru.premises[0];
    let p2 = &ru.premises[1];
    let conc = &ru.conclusions[0];

    // p1 = KD(pmult(_, p))
    let (dt1, p1_term) = match k_fact_view(p1) { Some(x) => x, None => return false };
    if dt1 != KDir::Dn { return false; }
    let _p = match bp_view_pmult(p1_term) { Some((_s, p)) => p, None => return false };
    // p2 = KU(b)
    let (dt2, b) = match k_fact_view(p2) { Some(x) => x, None => return false };
    if dt2 != KDir::Up { return false; }
    // conc = KD(pmult(c, p))
    let (dtc, conc_term) = match k_fact_view(conc) { Some(x) => x, None => return false };
    if dtc != KDir::Dn { return false; }
    let (c, p_conc) = match bp_view_pmult(conc_term) { Some(x) => x, None => return false };

    // HS `isForbiddenDPMult` (Contradictions.hs) gates ONLY on the
    // structural shape checked above (`[p1,p2]`/`[conc]`, `(DnK, FPMult _ _)`
    // for p1, `(UpK, b)` for p2, `(DnK, FPMult c p)` for conc) — there is no
    // `isDPMultRule` guard (contrast isForbiddenDEMap/Order which DO guard).
    if !never_contains_fresh_priv(p_conc) { return false; }
    ni_factors_subset(c, b)
}

/// `isForbiddenDEMap` — Contradictions.hs.
///
/// A `dExp` rule whose first premise's provider is a `dEMap` rule
/// instance, where the EMap's `[s]P / [r]Q` premises are
/// "overcomplicated" relative to the `dExp`'s `ke` exponent.
fn is_forbidden_d_emap(sys: &System,
                       i: &crate::constraint::constraints::NodeId,
                       ru_exp: &crate::rule::Rule<crate::rule::RuleInfo<
                           crate::rule::ProtoRuleACInstInfo,
                           crate::rule::IntrRuleACInfo>>) -> bool {
    use crate::rule::PremIdx;
    use crate::rule::is_d_exp_rule;
    use crate::rule::is_d_emap_rule;
    if !is_d_exp_rule(ru_exp) { return false; }
    if ru_exp.premises.len() != 2 { return false; }

    // ke_f := premIdx 1 of the dExp rule
    let ke_f = &ru_exp.premises[1];
    let (dt_ke, ke) = match k_fact_view(ke_f) { Some(x) => x, None => return false };
    if dt_ke != KDir::Up { return false; }

    // Find the edge ((ns,_) → (i, PremIdx 0)) i.e. the rule providing
    // the dExp's first premise (the dEMap rule).
    let edge_ns = sys.edges.iter().find_map(|e| {
        if e.tgt.0 == *i && e.tgt.1 == PremIdx(0) {
            Some(e.src.0.clone())
        } else { None }
    });
    let Some(ns) = edge_ns else { return false; };
    let Some((_, ru_emap)) = sys.nodes.iter().find(|(n, _)| n == &ns) else { return false; };
    if !is_d_emap_rule(ru_emap) { return false; }
    if ru_emap.premises.len() != 2 { return false; }

    let sp_f = &ru_emap.premises[0];
    let rq_f = &ru_emap.premises[1];
    let (dt_sp, sp_term) = match k_fact_view(sp_f) { Some(x) => x, None => return false };
    if dt_sp != KDir::Dn { return false; }
    let (s_sc, p_pt) = match bp_view_pmult(sp_term) { Some(x) => x, None => return false };
    let (dt_rq, rq_term) = match k_fact_view(rq_f) { Some(x) => x, None => return false };
    if dt_rq != KDir::Dn { return false; }
    let (r_sc, q_pt) = match bp_view_pmult(rq_term) { Some(x) => x, None => return false };

    bp_over_complicated(s_sc, p_pt, ke) || bp_over_complicated(r_sc, q_pt, ke)
}

/// `isForbiddenDEMapOrder` — Contradictions.hs.
///
/// For a `dEMap` rule instance whose conclusion has the canonical
/// shape `KD(exp(em(p,q), Mult([s,r])))`, find the two protocol
/// rules feeding its premises (through an intermediate `IRecv`).
/// Forbidden iff the first protocol rule's fact tags are strictly
/// greater than the second's (normal-form fact-tag ordering).
fn is_forbidden_d_emap_order(sys: &System,
                             i: &crate::constraint::constraints::NodeId,
                             ru: &crate::rule::Rule<crate::rule::RuleInfo<
                                 crate::rule::ProtoRuleACInstInfo,
                                 crate::rule::IntrRuleACInfo>>) -> bool {
    use crate::rule::{PremIdx, is_d_emap_rule};
    use tamarin_term::function_symbols::{AcSym, CSym, EXP_SYM_STRING, FunSym};
    use tamarin_term::term::Term;
    if !is_d_emap_rule(ru) { return false; }
    if ru.premises.len() != 2 { return false; }
    if ru.conclusions.len() != 1 { return false; }

    let f_p0 = &ru.premises[0];
    let f_p1 = &ru.premises[1];
    let f_c0 = &ru.conclusions[0];

    let (dt0, t0) = match k_fact_view(f_p0) { Some(x) => x, None => return false };
    if dt0 != KDir::Dn { return false; }
    let (s_sc, p_pt) = match bp_view_pmult(t0) { Some(x) => x, None => return false };

    let (dt1, t1) = match k_fact_view(f_p1) { Some(x) => x, None => return false };
    if dt1 != KDir::Dn { return false; }
    let (r_sc, q_pt) = match bp_view_pmult(t1) { Some(x) => x, None => return false };

    let (dtc, tc) = match k_fact_view(f_c0) { Some(x) => x, None => return false };
    if dtc != KDir::Dn { return false; }

    // tc = exp(em(p', q'), Mult([s', r', ...]))
    let (em_t, mult_arg) = match tc {
        Term::App(FunSym::NoEq(s), args)
            if s.name == EXP_SYM_STRING && args.len() == 2 =>
            (&args[0], &args[1]),
        _ => return false,
    };
    let (p_p, q_p) = match em_t {
        Term::App(FunSym::C(CSym::EMap), args) if args.len() == 2 =>
            (&args[0], &args[1]),
        _ => return false,
    };
    let mult_args: Vec<tamarin_term::lterm::LNTerm> = match mult_arg {
        Term::App(FunSym::Ac(AcSym::Mult), args) => args.iter().cloned().collect(),
        _ => return false,
    };

    // guard ((p,q) == (p',q') || (p,q) == (q',p'))
    let ok_pair = (p_pt == p_p && q_pt == q_p) || (p_pt == q_p && q_pt == p_p);
    if !ok_pair { return false; }
    // && (mult_args \\ [s,r] == [])  — every mult_arg appears among [s,r]
    let mut remaining: Vec<tamarin_term::lterm::LNTerm> = vec![s_sc.clone(), r_sc.clone()];
    for a in &mult_args {
        let Some(pos) = remaining.iter().position(|x| x == a) else { return false; };
        remaining.remove(pos);
    }
    // remaining can be non-empty (HS only checks mult_args ⊆ [s,r]).

    // For each premise of i, follow edge backwards through IRecv to
    // the protocol rule.
    let lookup_prem_provider = |k: &crate::constraint::constraints::NodeId,
                                pi: PremIdx| -> Option<crate::constraint::constraints::NodeId> {
        sys.edges.iter().find_map(|e|
            if e.tgt.0 == *k && e.tgt.1 == pi { Some(e.src.0.clone()) } else { None })
    };
    let j1 = lookup_prem_provider(i, PremIdx(0));
    let j2 = lookup_prem_provider(i, PremIdx(1));
    let (Some(j1), Some(j2)) = (j1, j2) else { return false; };

    let ru_proto1 = lookup_prem_provider(&j1, PremIdx(0))
        .and_then(|n| sys.nodes.iter().find(|(nn, _)| nn == &n).map(|(_, r)| r));
    let ru_proto2 = lookup_prem_provider(&j2, PremIdx(0))
        .and_then(|n| sys.nodes.iter().find(|(nn, _)| nn == &n).map(|(_, r)| r));
    let (Some(rp1), Some(rp2)) = (ru_proto1, ru_proto2) else { return false; };

    // isStandRule: standard protocol rule (not Intr/Fresh/Pub).
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, RuleInfo};
    let is_stand = |r: &crate::rule::Rule<RuleInfo<ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>>|
        -> bool {
        match &r.info {
            RuleInfo::Proto(p) => matches!(p.name, ProtoRuleName::Stand(_)),
            _ => false,
        }
    };
    if !is_stand(rp1) || !is_stand(rp2) { return false; }

    // factTags ruProto1 > factTags ruProto2
    //   where factTags ru = map (map factTag) [rPrems ru, rConcs ru, rActs ru]
    // HS compares a list-OF-lists, so each fact group is a distinct inner
    // list whose length is significant — they must NOT be flattened into a
    // single sequence (that would cross group boundaries). Build
    // `[[prem tags], [conc tags], [act tags]]` and compare lexicographically.
    let tags_of = |r: &crate::rule::Rule<RuleInfo<ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>>|
        -> Vec<Vec<crate::fact::FactTag>> {
        vec![
            r.premises.iter().map(|f| f.tag.clone()).collect(),
            r.conclusions.iter().map(|f| f.tag.clone()).collect(),
            r.actions.iter().map(|f| f.tag.clone()).collect(),
        ]
    };
    tags_of(rp1) > tags_of(rp2)
}

/// `kFactView`: returns (KDir, term) for KU / KD facts.
/// `KDir::Up` = KU (constructible), `KDir::Dn` = KD (destruction).
/// Shared by `has_forbidden_exp` and the BP contradiction checks.
#[derive(Copy, Clone, PartialEq, Eq)]
enum KDir { Up, Dn }
fn k_fact_view(fa: &crate::fact::LNFact)
    -> Option<(KDir, &tamarin_term::lterm::LNTerm)>
{
    use crate::fact::FactTag;
    if fa.terms.len() != 1 { return None; }
    match fa.tag {
        FactTag::Ku => Some((KDir::Up, &fa.terms[0])),
        FactTag::Kd => Some((KDir::Dn, &fa.terms[0])),
        _ => None,
    }
}

/// View `pmult(scalar, point)` — returns `(scalar, point)`.
fn bp_view_pmult(t: &tamarin_term::lterm::LNTerm)
    -> Option<(&tamarin_term::lterm::LNTerm, &tamarin_term::lterm::LNTerm)>
{
    use tamarin_term::function_symbols::{FunSym, PMULT_SYM_STRING};
    use tamarin_term::term::Term;
    if let Term::App(FunSym::NoEq(s), args) = t {
        if s.name == PMULT_SYM_STRING && args.len() == 2 {
            return Some((&args[0], &args[1]));
        }
    }
    None
}

/// `niFactors`: HS Term/LTerm.hs:351-355.  The non-inverse factors of a
/// term.  `Mult(ts...)` → concat-map ni_factors; `Inv(t)` → ni_factors t;
/// else `[t]`.  Shared by `has_forbidden_exp` and the BP checks.
fn ni_factors(t: &tamarin_term::lterm::LNTerm) -> Vec<tamarin_term::lterm::LNTerm> {
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::Ac(AcSym::Mult), args) => {
            let mut out = Vec::new();
            for a in args.iter() { out.extend(ni_factors(a)); }
            out
        }
        Term::App(FunSym::NoEq(s), args)
            if s.name == INV_SYM_STRING && args.len() == 1 =>
            ni_factors(&args[0]),
        _ => vec![t.clone()],
    }
}

/// `niFactors c \\ niFactors b == []`: every non-inverse factor of `c`
/// appears in `b`'s non-inverse factors (multiset semantics).
fn ni_factors_subset(c: &tamarin_term::lterm::LNTerm,
                     b: &tamarin_term::lterm::LNTerm) -> bool {
    let nfc = ni_factors(c);
    let mut remaining = ni_factors(b);
    for x in &nfc {
        if let Some(pos) = remaining.iter().position(|y| y == x) {
            remaining.remove(pos);
        } else {
            return false;
        }
    }
    true
}

/// `overComplicated scalar point ke` — Contradictions.hs.
///   `(niFactors scalar \\ niFactors ke == []) && neverContainsFreshPriv point`
fn bp_over_complicated(scalar: &tamarin_term::lterm::LNTerm,
                       point: &tamarin_term::lterm::LNTerm,
                       ke: &tamarin_term::lterm::LNTerm) -> bool {
    ni_factors_subset(scalar, ke) && never_contains_fresh_priv(point)
}

/// Direct port of Haskell's `nonInjectiveFactInstances`
/// (`Theory.Constraint.Solver.Contradictions`).
///
/// For every edge `(i,_) → (k,_)` whose conclusion fact has an
/// injective tag and first term `t`, find every reachable node `j`
/// (via the raw less-relation) such that `j ≠ i, k` and `j`'s rule
/// produces or consumes a fact of the same tag with the same first
/// term, AND `k` is reachable from `j` (or `k` is the last node).
///
/// Such a `(i, j, k)` triple witnesses two simultaneous "live"
/// instances of the injective fact, contradicting injectivity.
fn non_injective_fact_instances(
    ctxt: &ProofContext,
    sys: &System,
    adj: &BTreeMap<NodeId, Vec<NodeId>>,
) -> Vec<Contradiction> {
    let mut out = Vec::new();
    let inj_tags: BTreeSet<&crate::fact::FactTag> =
        ctxt.injective_fact_insts.iter().map(|(t, _)| t).collect();
    if inj_tags.is_empty() { return out; }

    // `adj` is the raw less-relation (`rawLessRel`: less + edges + unsolved
    // chains), built once by the caller (`contradictions`) and shared. We
    // enumerate reachable sets here rather than reuse always_before, which
    // only queries a single pair.
    // `adj` is invariant across this function, so memoize each node's
    // reachable set: `reachable(i)` is taken once per edge and `reachable(j)`
    // once per reachable `j`, with the same `j` recurring across edges.
    // The cache stores the exact value the un-memoized closure returned
    // (the set with `from` removed), so this is a pure speedup.
    let reach_cache: std::cell::RefCell<BTreeMap<NodeId, BTreeSet<NodeId>>> =
        std::cell::RefCell::new(BTreeMap::new());
    let reachable = |from: &NodeId| -> BTreeSet<NodeId> {
        if let Some(cached) = reach_cache.borrow().get(from) {
            return cached.clone();
        }
        // Strictly-reachable set (seed removed) via the shared routine.
        let out = crate::constraint::solver::goals::reachable_set_adj(adj, from, false);
        reach_cache.borrow_mut().insert(from.clone(), out.clone());
        out
    };
    // Resolve node-id → rule via a once-built map instead of a linear
    // `nodes.iter().find` per `i`/`j`.
    let node_rule_map = sys.node_rule_map();
    let lookup_node = |id: &NodeId| -> Option<&crate::rule::RuleACInst> {
        node_rule_map.get(id).copied()
    };

    for e in &sys.edges {
        let (i, conc_idx) = (e.src.0.clone(), e.src.1);
        let k = e.tgt.0.clone();
        // Look up the conclusion fact at (i, conc_idx).
        let i_rule = match lookup_node(&i) { Some(r) => r, None => continue };
        let k_fa_prem = match i_rule.conclusions.get(conc_idx.0) {
            Some(f) => f, None => continue,
        };
        if !inj_tags.contains(&k_fa_prem.tag) { continue; }
        let k_term = match k_fa_prem.terms.first() {
            Some(t) => t, None => continue,
        };
        // Reachable set from i.
        let reach = reachable(&i);
        for j in &reach {
            if j == &i || j == &k { continue; }
            let j_rule = match lookup_node(j) { Some(r) => r, None => continue };
            // Conflicting fact in j's prems or concs.
            let conflicting = |fa: &crate::fact::LNFact| -> bool {
                fa.tag == k_fa_prem.tag && fa.terms.first() == Some(k_term)
            };
            let has_conflict = j_rule.premises.iter().any(conflicting)
                || j_rule.conclusions.iter().any(conflicting);
            if !has_conflict { continue; }
            // k reachable from j OR k is the last node.
            let j_reach = reachable(j);
            let k_after_j = j_reach.contains(&k);
            let k_is_last = sys.last_atom.as_ref() == Some(&k);
            if k_after_j || k_is_last {
                out.push(Contradiction::NonInjectiveFactInstance(
                    i.clone(), j.clone(), k.clone(),
                ));
            }
        }
    }
    out
}

/// Detect two LVars sharing `(name, idx)` but with disjoint sub-sorts.
/// Pub/Fresh/Nat are pairwise disjoint sub-sorts of Msg; if the system
/// contains both `~mw:Pub 58` and `~mw:Fresh 58`, no model can satisfy
/// both occurrences simultaneously.  Returns true if any such conflict
/// exists.
fn has_sort_conflated_lvars(sys: &System) -> bool {
    use tamarin_term::lterm::{HasFrees, LSort, LVar};
    // `LVar.name` is an interned `&'static str` (Copy), so the seen-map key
    // is allocation-free; `&str` hashing/equality is by content, so equal
    // names share one entry even across distinct interned pointers.  The
    // first-seen sort wins for each `(name, idx)` key.
    struct SortSeen {
        seen: tamarin_utils::FastMap<(&'static str, u64), LSort>,
        conflict: bool,
    }
    impl SortSeen {
        fn visit(&mut self, v: &LVar) {
            if self.conflict { return; }
            match self.seen.get(&(v.name, v.idx)).copied() {
                None => { self.seen.insert((v.name, v.idx), v.sort); }
                Some(prev) if prev == v.sort => {}
                Some(prev) => {
                    // Two distinct sorts at same (name, idx).  Pub/Fresh/
                    // Nat are disjoint; pairs that include Msg can be
                    // narrowed (Msg is the join), so don't flag those.
                    let disjoint = matches!((prev, v.sort),
                        (LSort::Pub, LSort::Fresh) | (LSort::Fresh, LSort::Pub) |
                        (LSort::Pub, LSort::Nat)   | (LSort::Nat, LSort::Pub) |
                        (LSort::Fresh, LSort::Nat) | (LSort::Nat, LSort::Fresh));
                    if disjoint {
                        self.conflict = true;
                    }
                }
            }
        }
        /// [`SortSeen::visit`] every free `LVar` of `x`.
        fn scan(&mut self, x: &impl HasFrees) {
            x.for_each_free(&mut |v: &LVar| self.visit(v));
        }
    }
    let mut st = SortSeen { seen: tamarin_utils::FastMap::default(), conflict: false };
    for (id, rule) in sys.nodes.iter() {
        st.scan(id);
        st.scan(rule);
        if st.conflict { return true; }
    }
    for e in &sys.edges {
        st.scan(&e.src.0);
        st.scan(&e.tgt.0);
        if st.conflict { return true; }
    }
    for l in &sys.less_atoms {
        st.scan(&l.smaller);
        st.scan(&l.larger);
        if st.conflict { return true; }
    }
    if let Some(la) = &sys.last_atom { st.scan(la); }
    for (g, _) in sys.goals.iter() {
        match g {
            crate::constraint::constraints::Goal::Action(n, fa) => {
                st.scan(n);
                st.scan(fa);
            }
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                st.scan(&p.0);
                st.scan(fa);
            }
            crate::constraint::constraints::Goal::Chain(c, p) => {
                st.scan(&c.0);
                st.scan(&p.0);
            }
            _ => {}
        }
        if st.conflict { return true; }
    }
    st.conflict
}

/// Has the system's formula list been forced to ⊥?
fn has_false_formula(sys: &System) -> bool {
    use crate::guarded::Guarded;
    sys.formulas.iter().any(|f| matches!(f.as_ref(), Guarded::Disj(v) if v.is_empty()))
}

/// `Fr(t)` requires `t` to be a Fresh-sorted variable. Maude's
/// sort-aware unifier rejects bindings like `seed = f(k)` where
/// `f` is a constructor (returning Msg sort). When our source-case
/// grafting bypasses that check — e.g. on Minimal_HashChain where
/// the Gen_Start direct-to-Gen_Stop precomputed case is grafted
/// onto a runtime `!Final(f(k))` premise, conflating Gen_Start's
/// `seed` with `f(k)` — the resulting `Fr(f(k))` is unsatisfiable.
/// Mirrors the sort-check Haskell's unifier performs implicitly.
fn has_fresh_fact_sort_violation(sys: &System) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use crate::fact::FactTag;
    let subst = &sys.eq_store.subst;
    for (_, rule) in sys.nodes.iter() {
        // Check premises (where Fr lives) and conclusions/actions
        // for completeness — any Fresh-tagged fact with a non-Fresh
        // term is a sort violation.
        for fact in rule.premises.iter()
            .chain(rule.conclusions.iter())
            .chain(rule.actions.iter())
        {
            if !matches!(fact.tag, FactTag::Fresh) { continue; }
            let t = match fact.terms.first() { Some(t) => t, None => continue };
            let t_norm = tamarin_term::subst::apply_vterm(subst, t.clone());
            match t_norm {
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Fresh => {}
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => {
                    // Msg can narrow to Fresh later — don't flag.
                }
                _ => return true,
            }
        }
    }
    false
}

/// Soundness invariant: every edge in a well-formed system must
/// connect a conclusion and premise with identical fact tags (and
/// arity).  Tamarin's `solveChainGoal` / `solvePremise` only ever
/// add edges after `solveFactEqs` succeeds, which requires the
/// fact tags to match.  In our port, an edge with mismatched tags
/// can arise when node-id substitution collapses a case node onto
/// an unrelated live node — the edge survives the rename but
/// connects incompatible facts.  Such a system has no model.
fn has_incompatible_edge_facts(sys: &System) -> bool {
    // One node-id → rule map (instead of two linear `nodes.iter().find`
    // scans per edge → O(edges*nodes)).
    let node_rule_map = sys.node_rule_map();
    for e in &sys.edges {
        let src_rule = node_rule_map.get(&e.src.0).copied();
        let tgt_rule = node_rule_map.get(&e.tgt.0).copied();
        let (Some(sr), Some(tr)) = (src_rule, tgt_rule) else {
            continue;
        };
        let fc = match sr.conclusions.get(e.src.1.0) { Some(f) => f, None => continue };
        let fp = match tr.premises.get(e.tgt.1.0) { Some(f) => f, None => continue };
        if fc.tag != fp.tag || fc.terms.len() != fp.terms.len() {
            return true;
        }
    }
    false
}

/// True if the strict `<` partial order has a cycle.
pub fn cyclic(less: &[LessAtom]) -> bool {
    // Build adjacency list keyed by NodeId.
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in less {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    // Run DFS detecting back-edges.
    let mut color: BTreeMap<NodeId, u8> = BTreeMap::new(); // 0=white,1=gray,2=black
    let nodes: Vec<NodeId> = adj.keys().cloned().collect();
    fn dfs(
        node: &NodeId,
        adj: &BTreeMap<NodeId, Vec<NodeId>>,
        color: &mut BTreeMap<NodeId, u8>,
    ) -> bool {
        match color.get(node).copied().unwrap_or(0) {
            1 => return true,    // gray ancestor → back-edge
            2 => return false,   // already explored
            _ => {}
        }
        color.insert(node.clone(), 1);
        if let Some(succs) = adj.get(node) {
            for s in succs {
                if dfs(s, adj, color) { return true; }
            }
        }
        color.insert(node.clone(), 2);
        false
    }
    for n in &nodes {
        if dfs(n, &adj, &mut color) { return true; }
    }
    false
}

/// `cyclic_with_path` — same as `cyclic` but returns the cycle path
/// when one exists.  Intended for H14-style diagnostics: when HS
/// detects a Cyclic contradiction at some cn but RS doesn't, comparing
/// HS's cycle path against RS's available less_atoms shows EXACTLY
/// which less_atom is missing in RS.
///
/// Returns the cycle as a `Vec<NodeId>` where the first and last
/// entries are equal (the back-edge node).  Empty if no cycle.
pub fn cyclic_with_path(less: &[LessAtom]) -> Vec<NodeId> {
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in less {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    let mut color: BTreeMap<NodeId, u8> = BTreeMap::new();
    let mut path: Vec<NodeId> = Vec::new();
    let nodes: Vec<NodeId> = adj.keys().cloned().collect();
    fn dfs(
        node: &NodeId,
        adj: &BTreeMap<NodeId, Vec<NodeId>>,
        color: &mut BTreeMap<NodeId, u8>,
        path: &mut Vec<NodeId>,
    ) -> Option<NodeId> {
        match color.get(node).copied().unwrap_or(0) {
            1 => return Some(node.clone()),   // back-edge target
            2 => return None,
            _ => {}
        }
        color.insert(node.clone(), 1);
        path.push(node.clone());
        if let Some(succs) = adj.get(node) {
            for s in succs {
                if let Some(target) = dfs(s, adj, color, path) {
                    return Some(target);
                }
            }
        }
        color.insert(node.clone(), 2);
        path.pop();
        None
    }
    for n in &nodes {
        if let Some(target) = dfs(n, &adj, &mut color, &mut path) {
            // Truncate path to the cycle (from `target` onwards).
            if let Some(start) = path.iter().position(|x| x == &target) {
                let mut cycle: Vec<NodeId> = path[start..].to_vec();
                cycle.push(target);
                return cycle;
            }
        }
    }
    Vec::new()
}

/// Detect any node that is strictly after `last(_)`. Mirrors Haskell's
/// `nodesAfterLast`.
///
/// Walks BOTH `less_atoms` AND `edges` to build the < relation.  Each
/// edge `(src, _) → (tgt, _)` induces `src < tgt` (the producer must
/// fire before the consumer).  Without including edges, a `last_atom`
/// at a node that has chain successors via edges (but no explicit
/// `LessAtom`) would survive — losing the contradiction Haskell uses
/// to prune typing-class source cases at precompute.
fn node_after_last(
    sys: &System,
    adj: &BTreeMap<NodeId, Vec<NodeId>>,
) -> Vec<Contradiction> {
    let last = match &sys.last_atom { Some(l) => l.clone(), None => return Vec::new() };
    // Port of Haskell `Theory.Constraint.Solver.Contradictions.nodesAfterLast`:
    //
    //   nodesAfterLast sys = case sLastAtom sys of
    //     Just i  -> [(i,j) | j ∈ reachableSet [i] (rawLessRel sys)
    //                       , j /= i, isInTrace sys j ]
    //
    // where `rawLessRel = lessAtoms ∪ rawEdgeRel` and
    // `isInTrace sys i = i ∈ sNodes ∨ isLast sys i ∨
    //                    any ((i ==) . fst) (unsolvedActionAtoms sys)`.
    //
    // Walk the raw less-relation (less_atoms ∪ edges ∪ unsolved chains —
    // see `build_always_before_adj`).  Without edges the typing-case `Last(#vr_inner)`
    // branch never contradicts even when `vr_inner` has a chain-edge
    // successor that pins down the ordering.  Filter by `isInTrace`: a
    // successor only counts if it's a rule instance in `sNodes`, the
    // system's last, or carries an unsolved Action goal — otherwise
    // abstract precompute-time node-ids spuriously trip the contradiction.
    // `adj` is the raw less-relation, built once by the caller
    // (`contradictions`) and shared.
    // isInTrace: collect every node-id that is "in the trace".
    let mut in_trace: BTreeSet<NodeId> = BTreeSet::new();
    for (id, _) in sys.nodes.iter() {
        in_trace.insert(id.clone());
    }
    in_trace.insert(last.clone()); // isLast is true for `last`
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Action(id, _) = g {
            in_trace.insert(id.clone());
        }
    }
    // Strictly-reachable set from `last` (seed removed) via the shared routine.
    let visited = crate::constraint::solver::goals::reachable_set_adj(adj, &last, false);
    visited.into_iter()
        .filter(|n| in_trace.contains(n))
        .map(|after| Contradiction::NodeAfterLast(last.clone(), after))
        .collect()
}

/// `maybeNonNormalTerms`: walk all node facts + new_vars in `sys`,
/// returning every subterm that could be non-normal under some
/// substitution.  Used by [`SubstNfChecker`] below.
/// Mirrors Haskell's `Contradictions.maybeNonNormalTerms`
/// (Contradictions.hs).
pub fn maybe_non_normal_terms(
    sys: &System,
    irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
) -> Vec<tamarin_term::lterm::LNTerm> {
    // Reads ONLY `sys.nodes`; delegate to the slice form so a shared
    // [`SubstNfChecker`] can pin an O(1) `Arc` snapshot of the nodes and
    // force the identical walk lazily.
    maybe_non_normal_terms_nodes(&sys.nodes, irreducible)
}

/// Nodes-slice form of [`maybe_non_normal_terms`].  The walk reads only
/// the system's `nodes`, so pinning an `Arc<Vec<(NodeId, RuleACInst)>>`
/// snapshot and calling this yields exactly the candidate set the eager
/// whole-`System` walk produces.  The `BTreeSet` dedup is load-bearing
/// for workload downstream — it must stay.
pub fn maybe_non_normal_terms_nodes(
    nodes: &[(NodeId, crate::rule::RuleACInst)],
    irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut candidates: std::collections::BTreeSet<tamarin_term::lterm::LNTerm>
        = std::collections::BTreeSet::new();
    for (_, rule) in nodes.iter() {
        for f in rule.premises.iter().chain(&rule.conclusions).chain(&rule.actions) {
            for t in f.terms.iter() {
                maybe_not_nf_subterms(irreducible, t, &mut candidates);
            }
        }
        for t in &rule.new_vars {
            maybe_not_nf_subterms(irreducible, t, &mut candidates);
        }
    }
    candidates.into_iter().collect()
}

/// Shared-state port of Haskell's `Contradictions.substCreatesNonNormalTerms`
/// (Contradictions.hs): `true` if applying `vfresh_subst` to the system's
/// `maybe-non-normal` terms (already substituted by `fsubst`) creates a
/// non-normal-form term.  Used by `simp_minimize` to filter SplitG variants
/// that would violate the nf-respecting trace semantics.
///
/// ```haskell
/// substCreatesNonNormalTerms hnd sys fsubst =
///     \subst -> any (not . nfApply subst) terms
///   where terms = apply fsubst $ maybeNonNormalTerms hnd sys
///         nfApply subst0 t = t == t' || nf' t' `runReader` hnd
///           where tvars = freesList t
///                 subst = restrictVFresh tvars subst0
///                 t'    = apply (freshToFreeAvoidingFast subst tvars) t
/// ```
///
/// The HS definition is CURRIED: `substCreatesNonNormalTerms hnd sys` shares
/// the `maybeNonNormalTerms hnd sys` whole-system walk across every
/// `fsubst`/`subst` probe (GHC full laziness floats it out of the `fsubst`
/// lambda), and `terms` — the fsubst-applied list — is shared across every
/// candidate `subst` that `simpMinimize` probes within one `simp1` iteration
/// (`isContr (get eqsSubst eqs)`, EquationStore.hs).  This type provides that
/// sharing (production code constructs it directly, e.g. in `reduction.rs`).
///
/// `base` — the `maybeNonNormalTerms hnd sys` walk — is pinned as an
/// O(1) `Arc` node snapshot at construction and forced lazily on the
/// first `check()` that reaches a probe (mirroring HS's unforced
/// thunk).  The fsubst application is recomputed only when
/// the free-subst VALUE changes (at most once per `simp1` iteration:
/// `simp_with_fresh_avoiding` snapshots `self.subst` per iteration and
/// probes every candidate against that same snapshot).  Without this
/// sharing, `simp_minimize` probes each disj subst and every probe
/// re-walks every node of the system — a 20+ minute spin on
/// post-autoprove eCK-class web proof pages (TAK1) that HS serves in
/// under a minute.  Pure predicate — no fresh-counter movement, no
/// output impact.
pub struct SubstNfChecker {
    maude: tamarin_term::maude_proc::MaudeHandle,
    /// O(1) `Arc` snapshot of `sys.nodes`, pinned at construction.
    /// `System.nodes` is `Arc`-COW (mutations go through `Arc::make_mut`
    /// or wholesale replacement), so this snapshot cannot change under
    /// the lazy `base` force below: forcing walks exactly the nodes the
    /// construction-time system held.
    nodes: std::sync::Arc<Vec<(NodeId, crate::rule::RuleACInst)>>,
    /// `maybeNonNormalTerms hnd sys` — forced lazily on the first
    /// `check()` that reaches a candidate probe.  HS keeps this an
    /// unforced thunk (curried `substCreatesNonNormalTerms hnd sys`, only
    /// forced when `simpMinimize` actually probes a subst); the common
    /// empty-conj steady state never probes, so the whole-system walk is
    /// dead there.  Pure predicate — deferral moves no fresh-counter idx
    /// and changes no output byte.  `OnceCell` keeps the checker `Send` +
    /// `!Sync` (matching `applied`'s `RefCell`), so the compiler still
    /// rejects any cross-thread `&`-sharing under the web rayon fan-out;
    /// each thread forces its own pinned snapshot independently.
    base: std::cell::OnceCell<Vec<tamarin_term::lterm::LNTerm>>,
    /// Per-snapshot cache keyed by the free subst.  Holds, for each
    /// `base` term, the `fsubst`-applied term `t` together with the pure
    /// per-term quantities `check()` needs for every probe: `tvars =
    /// freesList t` and `fresh_start = succ (maxIdx tvars)`.  `terms` is
    /// fixed between `fsubst` refreshes, so these are computed once here
    /// instead of once per candidate probe.
    applied: std::cell::RefCell<Option<(
        crate::tools::equation_store::LNSubst,
        Vec<(
            tamarin_term::lterm::LNTerm,
            Vec<tamarin_term::lterm::LVar>,
            u64,
        )>,
    )>>,
}

impl SubstNfChecker {
    pub fn new(maude: &tamarin_term::maude_proc::MaudeHandle, sys: &System) -> Self {
        SubstNfChecker {
            maude: maude.clone(),
            nodes: sys.nodes.clone(),
            base: std::cell::OnceCell::new(),
            applied: std::cell::RefCell::new(None),
        }
    }

    /// `substCreatesNonNormalTerms hnd sys fsubst vfresh_subst`, with
    /// the walk + fsubst application shared as in HS (see type docs).
    pub fn check(
        &self,
        fsubst: &crate::tools::equation_store::LNSubst,
        vfresh_subst: &crate::tools::equation_store::LNSubstVFresh,
    ) -> bool {
        use tamarin_term::subst::apply_vterm;
        use tamarin_term::vterm::vars_vterm;
        // Force the `maybeNonNormalTerms` walk lazily over the pinned node
        // snapshot (see field docs).  Reads only `self.nodes` plus the
        // fixed signature's irreducible set, so the forced base equals the
        // construction-time eager walk.
        let base = {
            let nodes = &self.nodes;
            let maude = &self.maude;
            self.base.get_or_init(|| {
                let sig = maude.maude_sig();
                maybe_non_normal_terms_nodes(nodes, &sig.irreducible_fun_syms_fast)
            })
        };
        if base.is_empty() { return false; }
        let sig = self.maude.maude_sig();
        let mut applied = self.applied.borrow_mut();
        let stale = match applied.as_ref() {
            Some((fs, _)) => fs != fsubst,
            None => true,
        };
        if stale {
            // Precompute per snapshot: apply `fsubst`, then the pure
            // per-term `tvars`/`fresh_start` every probe consumes.
            let terms: Vec<(
                tamarin_term::lterm::LNTerm,
                Vec<tamarin_term::lterm::LVar>,
                u64,
            )> = base.iter()
                .map(|t| {
                    let t = apply_vterm(fsubst, t.clone());
                    let tvars: Vec<tamarin_term::lterm::LVar> = vars_vterm(&t);
                    let fresh_start = tvars.iter().map(|v| v.idx).max().unwrap_or(0)
                        .saturating_add(1);
                    (t, tvars, fresh_start)
                })
                .collect();
            *applied = Some((fsubst.clone(), terms));
        }
        let terms = &applied.as_ref().unwrap().1;
        for (t, tvars, fresh_start) in terms {
            if tvars.is_empty() { continue; }
            // `dom(restrictVFresh tvars subst) == ∅` ⟺ no `tvar` is in the
            // subst's domain; test that directly (`image_of` = domain map
            // lookup) and build the restricted map only on overlap.  Same
            // `continue` condition as `restrict(tvars).dom().count() == 0`,
            // without the empty-map alloc on the common no-overlap probe.
            if !tvars.iter().any(|v| vfresh_subst.image_of(v).is_some()) { continue; }
            let restricted = vfresh_subst.restrict(tvars);
            // HS `freshToFreeAvoidingFast subst tvars` (Substitution.hs:77-81):
            // a PURE uniform-shift rename of the range vars avoiding `tvars`
            // (`rename (map snd l) \`evalFreshAvoiding\` tvars`).  It consumes
            // NO fresh-counter state — the probe subst is local to this
            // predicate.  Drawing real idxs from the shared counter here would
            // advance it on every variant probed, shifting every later
            // persisted mint above HS.  `fresh_start` is the per-term
            // `succ (maxIdx tvars)` precomputed in the snapshot cache.
            let free_subst = restricted.fresh_to_free_uniform_shift(*fresh_start);
            let t_prime = apply_vterm(&free_subst, t.clone());
            // Fast path: if subst doesn't change the term, it's still NF.
            if &t_prime == t { continue; }
            // Slow path: structural NF check (HS-faithful).  Mirrors HS
            // `nfApply subst0 t = t == t' || nf' t' \`runReader\` hnd`
            // where `nf' = nfViaHaskell` (Norm.hs:130-131).  This is a
            // PURE structural check, NOT `maude.reduce(t) == t`.  The
            // distinction matters because Maude canonicalises AC operator
            // arguments (multiset / mult / xor / nat-plus), so
            // `mult(tid, x)` and `mult(x, tid)` are different `Eq`
            // representations but both in NF.
            let is_nf = tamarin_term::norm::nf_via_haskell(&sig, &t_prime);
            if !is_nf {
                if tamarin_utils::env_gate!("TAM_RS_DBG_SUBST_NF") {
                    eprintln!("[rs-subst-nf] CREATES t={:?} t_prime={:?}", t, t_prime);
                }
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::constraints::Reason;
    use tamarin_term::lterm::{LSort, LVar};

    fn n(name: &str) -> NodeId { LVar::new(name, LSort::Node, 0) }

    #[test]
    fn empty_system_has_no_contradictions() {
        let sig = crate::signature::SignaturePure::empty(false);
        // Without a real Maude we shouldn't run contradictions(); but
        // we can call cyclic directly.
        assert!(!cyclic(&[]));
        let _ = sig;
    }

    #[test]
    fn cycle_detected() {
        let l = vec![
            LessAtom::new(n("a"), n("b"), Reason::Fresh),
            LessAtom::new(n("b"), n("c"), Reason::Fresh),
            LessAtom::new(n("c"), n("a"), Reason::Fresh),
        ];
        assert!(cyclic(&l));
    }

    #[test]
    fn no_cycle_detected() {
        let l = vec![
            LessAtom::new(n("a"), n("b"), Reason::Fresh),
            LessAtom::new(n("b"), n("c"), Reason::Fresh),
        ];
        assert!(!cyclic(&l));
    }

    /// `nonInjectiveFactInstances` direct port: feed in a system with
    /// an Init→Stop edge for an injective fact `Inj` and a Copy node
    /// reachable from Init that also produces/consumes Inj with the
    /// same first arg, then check we see exactly one
    /// `NonInjectiveFactInstance(i, j, k)` triple.
    #[test]
    fn non_injective_fact_witness_emitted() {
        use crate::constraint::constraints::{Edge, LessAtom, Reason};
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
    Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
    RuleInfo, IntrRuleACInfo, RuleACInst, ConcIdx, PremIdx,
};
        use tamarin_term::builtin::msg_var;
        use tamarin_term::maude_proc::MaudeHandle;

        // Build the rule instances.
        let inj_tag = FactTag::Proto(Multiplicity::Linear, "Inj", 1);
        let inj_fact = Fact::new(inj_tag.clone(), vec![msg_var("x", 0)]);

        let init: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Init"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![],
            vec![inj_fact.clone()],
            vec![],
        );
        let copy: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Copy"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![inj_fact.clone()],
            vec![inj_fact.clone()],
            vec![],
        );
        let stop: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Stop"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![inj_fact.clone()],
            vec![],
            vec![],
        );

        // Construct a system: i = #1 (Init) → k = #2 (Stop) directly,
        // with j = #3 (Copy) reachable from i and k from j.
        let i = n("1");
        let j = n("3");
        let k = n("2");
        let mut sys = System::empty();
        sys.add_node(i.clone(), init);
        sys.add_node(j.clone(), copy);
        sys.add_node(k.clone(), stop);
        // i → k edge (Inj fact).
        sys.add_edge(Edge {
            src: (i.clone(), ConcIdx(0)),
            tgt: (k.clone(), PremIdx(0)),
        });
        // i < j, j < k via less atoms.
        sys.add_less(LessAtom::new(i.clone(), j.clone(), Reason::Adversary));
        sys.add_less(LessAtom::new(j.clone(), k.clone(), Reason::Adversary));

        // Build the proof context that knows `Inj` is injective.
        fn maude_path() -> Option<String> {
            if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
            for c in ["/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        }
        let mp = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let mut ctx = ProofContext::new(h, Vec::new());
        ctx.injective_fact_insts = vec![(inj_tag.clone(), Vec::new())];

        let cs = contradictions(&ctx, &sys);
        let injs: Vec<_> = cs.iter().filter(|c| matches!(c,
            Contradiction::NonInjectiveFactInstance(_, _, _))).collect();
        assert!(!injs.is_empty(),
            "expected at least one NonInjectiveFactInstance contradiction; got {:?}", cs);
    }

    /// Two LVars sharing `(name, idx)` but with disjoint sub-sorts
    /// (Pub vs Fresh) must be flagged.  This is the soundness fix for
    /// the NSLPK3-class false positives.
    #[test]
    fn sort_conflated_pub_vs_fresh_detected() {
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
            Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, IntrRuleACInfo, RuleACInst,
        };

        // Build a system with two nodes, each containing an action
        // using "x" at idx 58 but with conflicting sorts: Pub vs Fresh.
        let pub_var = LVar::new("x", LSort::Pub, 58);
        let fresh_var = LVar::new("x", LSort::Fresh, 58);
        let tag = FactTag::Proto(Multiplicity::Linear, "X", 1);
        let pub_term = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(pub_var.clone()));
        let fresh_term = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(fresh_var.clone()));
        let mk_rule = |name: &str, t| -> RuleACInst {
            Rule::new(
                RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                    attributes: RuleAttributes::empty(),
                    loop_breakers: Vec::new(),
                }),
                vec![],
                vec![Fact::new(tag.clone(), vec![t])],
                vec![],
            )
        };
        let mut sys = System::empty();
        sys.add_node(LVar::new("i", LSort::Node, 1), mk_rule("R_pub", pub_term));
        sys.add_node(LVar::new("j", LSort::Node, 2), mk_rule("R_fresh", fresh_term));
        assert!(has_sort_conflated_lvars(&sys),
            "expected sort-conflict between ~mw:Pub 58 and ~mw:Fresh 58");
    }

    /// Pub vs Msg should NOT be flagged — Msg is the join sort and
    /// Pub ⊂ Msg, so the pair can be narrowed at unification time.
    #[test]
    fn sort_conflated_pub_vs_msg_not_flagged() {
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
            Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, IntrRuleACInfo, RuleACInst,
        };
        let pub_var = LVar::new("x", LSort::Pub, 58);
        let msg_var = LVar::new("x", LSort::Msg, 58);
        let tag = FactTag::Proto(Multiplicity::Linear, "X", 1);
        let mk = |name: &str, t| -> RuleACInst {
            Rule::new(
                RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(name)),
                    attributes: RuleAttributes::empty(),
                    loop_breakers: Vec::new(),
                }),
                vec![], vec![Fact::new(tag.clone(), vec![t])], vec![],
            )
        };
        let mut sys = System::empty();
        sys.add_node(LVar::new("i", LSort::Node, 1),
            mk("R_p", tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(pub_var))));
        sys.add_node(LVar::new("j", LSort::Node, 2),
            mk("R_m", tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(msg_var))));
        assert!(!has_sort_conflated_lvars(&sys),
            "Pub vs Msg should NOT be flagged (Msg is join sort)");
    }

    /// `isForbiddenDPMult` (Contradictions.hs) gates ONLY on the
    /// structural shape `[KD(pmult(_,p)), KU(b)] -> [KD(pmult(c,p))]` plus
    /// `neverContainsFreshPriv p && (niFactors c \\ niFactors b == [])` —
    /// there is no `isDPMultRule` rule-name guard. Pin that the Rust port
    /// fires on a rule with the pmult shape even when its `info` is NOT a
    /// `_pmult` DestrRule (here: a Coerce intruder rule).
    #[test]
    fn forbidden_d_pmult_fires_without_pmult_rule_name() {
        use crate::fact::{Fact, FactTag};
        use crate::rule::{Rule, RuleInfo, ProtoRuleACInstInfo, IntrRuleACInfo, RuleACInst};
        use tamarin_term::builtin::{msg_var, pmult, pub_var};

        // p (point) is Pub → neverContainsFreshPriv p == true.
        // c == b == msg_var "b" → niFactors c \\ niFactors b == [].
        let p = pub_var("p", 0);
        let b = msg_var("b", 0);
        let s = msg_var("s", 0);
        let kd = |t| Fact::new(FactTag::Kd, vec![t]);
        let ku = |t| Fact::new(FactTag::Ku, vec![t]);

        // info = Coerce, deliberately NOT a `_pmult` DestrRule.
        let ru: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Intr(IntrRuleACInfo::Coerce),
            vec![kd(pmult(s.clone(), p.clone())), ku(b.clone())],
            vec![kd(pmult(b.clone(), p.clone()))],
            vec![],
        );
        assert!(!crate::rule::is_d_pmult_rule(&ru),
            "guard precondition: this rule is NOT a _pmult DestrRule");
        assert!(super::is_forbidden_d_pmult(&ru),
            "HS isForbiddenDPMult fires on the pmult shape regardless of rule name");
    }
}
