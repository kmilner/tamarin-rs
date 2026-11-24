// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.Contradictions`: every reason a
//! `System` is contradictory.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::constraint::constraints::NodeId;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::{NodeRuleMap, System};

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
    /// Has a forbidden AC constructor chain.
    ForbiddenACConstrChain,
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
pub fn contradictions(
    ctxt: &ProofContext,
    sys: &System,
) -> Result<Vec<Contradiction>, crate::prove::ProveError> {
    collect_contradictions(ctxt, sys, false)
}

/// The head of [`contradictions`], or `None` when the system has none.
///
/// HS consumes its lazy `contradictions` list with `null`/`head`, so checks
/// after the first contradiction are never evaluated; this stops there too.
pub fn first_contradiction(
    ctxt: &ProofContext,
    sys: &System,
) -> Result<Option<Contradiction>, crate::prove::ProveError> {
    Ok(collect_contradictions(ctxt, sys, true)?.into_iter().next())
}

/// [`contradictions`] in HS order; with `first_only` it returns as soon as
/// one contradiction is found.
fn collect_contradictions(
    ctxt: &ProofContext,
    sys: &System,
    first_only: bool,
) -> Result<Vec<Contradiction>, crate::prove::ProveError> {
    let mut out = Vec::new();
    macro_rules! found {
        ($c:expr) => {{
            out.push($c);
            if first_only {
                return Ok(out);
            }
        }};
    }
    // HS-faithful enumeration ORDER (`contradictions`, Contradictions.hs):
    // the returned list's HEAD is the recorded reason, so the push
    // order MUST mirror HS's `asum [...]` exactly:
    //   Cyclic, SubtermCyclic, NonNormalTerms, ForbiddenKD, ImpossibleChain,
    //   ForbiddenExp, ForbiddenBP, ForbiddenChain, IncompatibleEqs,
    //   FormulasFalse, then NonInjectiveFactInstance, then NodeAfterLast.

    // Build Haskell's `rawLessRel = sLessAtoms ++ sEdges ++ unsolvedChains`
    // once for cycle detection and every ordering-dependent check below.
    let ab_adj = sys.build_always_before_adj();
    // 1. Cyclic.
    if tamarin_utils::dag::cyclic_adj(ab_adj.map()) {
        found!(Contradiction::Cyclic);
    }

    // Node-id → rule index shared by the checks below, built on first use.
    let node_rules: std::cell::OnceCell<NodeRuleMap<'_>> = std::cell::OnceCell::new();

    // 2. SubtermCyclic — `isContradictory subtermStore`.
    if sys.subterm_store.is_false() {
        found!(Contradiction::SubtermCyclic);
    }
    // 3. NonNormalTerms.
    if has_non_normal_terms(ctxt, sys) {
        found!(Contradiction::NonNormalTerms);
    }
    // 4. ForbiddenKD.
    if has_forbidden_kd(sys) {
        found!(Contradiction::ForbiddenKD);
    }
    // 5. ImpossibleChain.
    if has_impossible_chain(ctxt, sys, &node_rules) {
        found!(Contradiction::ImpossibleChain);
    }
    // 6. ForbiddenExp (Contradictions.hs `hasForbiddenExp`).  Drops Exp-down rule
    //    instances whose g is simple, whose MsgVar args are KU-known earlier,
    //    and whose exponent factors are already in the up-premise.  enableDH.
    if ctxt.maude.maude_sig().enable_dh && has_forbidden_exp(sys, &ab_adj) {
        found!(Contradiction::ForbiddenExp);
    }
    // 7. ForbiddenBP (Contradictions.hs `hasForbiddenBP`).  Drops Pmult-down /
    //    Emap-down rule instances violating BP normal-form (redundant scalars,
    //    simplifiable em-then-exp compositions, Emap tag-order violations).
    //    enableBP.  (Chen_Kudla::key_agreement_reachable relies on this.)
    if ctxt.maude.maude_sig().enable_bp && has_forbidden_bp(sys) {
        found!(Contradiction::ForbiddenBP);
    }
    // 8. ForbiddenChain.
    if has_forbidden_chain(sys, &ab_adj, &node_rules) {
        found!(Contradiction::ForbiddenChain);
    }
    // 8b. ForbiddenACConstrChain — AC-constructor chain check
    //     (Contradictions.hs `hasForbiddenConstrChain`).
    if has_forbidden_constr_chain(sys, &node_rules) {
        found!(Contradiction::ForbiddenACConstrChain);
    }
    // 9. IncompatibleEqs: `eqsIsFalse sEqStore` (Contradictions.hs).
    if sys.eq_store().is_false() {
        found!(Contradiction::IncompatibleEqs);
    }
    // 10. FormulasFalse — `gfalse ∈ sFormulas` (our `Disj([])`).
    if has_false_formula(sys) {
        found!(Contradiction::FormulasFalse);
    }
    // 11. NonInjectiveFactInstance (×n) — BEFORE NodeAfterLast, matching HS's
    //     list concatenation order in `contradictions` (Contradictions.hs).
    non_injective_fact_instances(ctxt, sys, ab_adj.map(), &node_rules, first_only, &mut out)?;
    if first_only && !out.is_empty() {
        return Ok(out);
    }
    // 12. NodeAfterLast (×n).
    node_after_last(sys, ab_adj.map(), first_only, &mut out);
    Ok(out)
}

/// HS `hasNonNormalTerms` (Contradictions.hs): some candidate subterm of a
/// node fails `nf'` (`nfViaHaskell`, Norm.hs), which needs Maude only to
/// match `[AC]` subterm-rule left-hand sides.
fn has_non_normal_terms(ctx: &ProofContext, sys: &System) -> bool {
    // Without reducible symbols every term is in normal form.
    let sig = ctx.maude.maude_sig();
    if sig.reducible_fun_syms.is_empty() {
        return false;
    }
    let irreducible = &sig.irreducible_fun_syms_fast;
    let mut memo = NfMemo::default();

    for (_, rule) in sys.nodes.iter() {
        for f in rule
            .premises
            .iter()
            .chain(&rule.conclusions)
            .chain(&rule.actions)
        {
            for t in f.terms.iter() {
                if any_non_nf(&ctx.maude, &sig, irreducible, &mut memo, t) {
                    return true;
                }
            }
        }
        for t in &rule.new_vars {
            if any_non_nf(&ctx.maude, &sig, irreducible, &mut memo, t) {
                return true;
            }
        }
    }
    false
}

/// Candidate-subterm → NF verdict, for ONE [`has_non_normal_terms`] call.
///
/// The verdict is a pure function of `(signature, term)`: `nfViaHaskell`
/// reads the signature's irreducible set and st-rules and nothing else, and
/// its Maude use is a `match` query with no session state.  The signature is
/// read from the handle once, at the top of `has_non_normal_terms`, and is
/// fixed for the rest of that call, so the term alone is a complete key —
/// and the map dies with the call, so no cross-theory or cross-probe
/// signature change can ever be observed through a stale entry.  `Term`'s
/// `Eq` and `Hash` are both content-based (term.rs), so two separately
/// built copies of one term share an entry.
type NfMemo = tamarin_utils::FastMap<tamarin_term::lterm::LNTerm, bool>;

/// `nf'` on a candidate subterm, answered from `memo` when already seen.
///
/// This is HS's `sortednub` over `maybeNonNormalTerms`
/// (Contradictions.hs): the same candidate recurs
/// across a node's premises and conclusions and across nodes, and on a
/// user-`[AC]` signature each fresh evaluation issues a `struleApplicable`
/// Maude match per Ac-/C-headed st-rule LHS.
fn nf_memoized(
    msig: &tamarin_term::maude_sig::MaudeSig,
    maude: &tamarin_term::maude_proc::MaudeHandle,
    memo: &mut NfMemo,
    t: &tamarin_term::lterm::LNTerm,
) -> bool {
    if let Some(&hit) = memo.get(t) {
        return hit;
    }
    let is_nf = tamarin_term::norm::nf_via_haskell_maude(msig, maude, t);
    memo.insert(t.clone(), is_nf);
    is_nf
}

/// Short-circuiting structural walk: the moment a candidate subterm — a
/// variable or a reducible-headed `App` (the `_` arm of
/// `maybe_not_nf_subterms`) — fails the NF check, the system has a
/// non-normal term.  Constants are in NF; irreducible-headed apps recurse
/// into their args.  This is the boolean OR of `maybeNonNormalTerms` ∘
/// `maybeNotNfSubterms` (Norm.hs) over `nf'` (Norm.hs), but without
/// building the `BTreeSet` of every candidate: the OR needs no ordered
/// candidate list, and [`NfMemo`] carries the dedup.  The check runs
/// through `nf_via_haskell_maude` — HS's `nf'` runs in the
/// `WithMaude` reader, and the handle is what lets `struleApplicable`
/// AC-match the user-`[AC]` cancellation equations (`xorr(x, x) = zeroo`).
fn any_non_nf(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    msig: &tamarin_term::maude_sig::MaudeSig,
    irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    memo: &mut NfMemo,
    t: &tamarin_term::lterm::LNTerm,
) -> bool {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Con(_)) => false,
        // Bare variables are always in normal form (`go_nf` returns true
        // for every `Lit`), so skip the NF-check call.
        Term::Lit(Lit::Var(_)) => false,
        Term::App(sym, args) if irreducible.contains(sym) => args
            .iter()
            .any(|a| any_non_nf(maude, msig, irreducible, memo, a)),
        _ => !nf_memoized(msig, maude, memo, t),
    }
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
/// Mirrors Haskell `maybeNotNfSubterms` exactly (Norm.hs):
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
        _ => {
            out.insert(t.clone());
        }
    }
}

/// The `KD` chain view shared by `has_impossible_chain` and
/// `has_forbidden_chain`: HS `(DnK, t_start) <- kFactView $ nodeConcFact c
/// sys` and `(DnK, t_end) <- kFactView $ nodePremFact p sys`. Gives the
/// premise node's rule with both terms, or `None` when a node or fact is
/// missing or either fact is not a `KD` fact. Each lookup takes the FIRST
/// rule stored for a node id.
fn kd_chain_view<'a>(
    node_rule_map: &NodeRuleMap<'a>,
    c: &crate::constraint::constraints::NodeConc,
    p: &crate::constraint::constraints::NodePrem,
) -> Option<(
    &'a crate::rule::RuleACInst,
    &'a tamarin_term::lterm::LNTerm,
    &'a tamarin_term::lterm::LNTerm,
)> {
    let c_rule = node_rule_map.get(&c.0).copied()?;
    let p_rule = node_rule_map.get(&p.0).copied()?;
    let (KDir::Dn, t_start) = k_fact_view(c_rule.conclusions.get(c.1 .0)?)? else {
        return None;
    };
    let (KDir::Dn, t_end) = k_fact_view(p_rule.premises.get(p.1 .0)?)? else {
        return None;
    };
    Some((p_rule, t_start, t_end))
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
fn has_impossible_chain<'a>(
    ctx: &ProofContext,
    sys: &'a System,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
) -> bool {
    for (c, p) in sys.unsolved_chains() {
        // The first unsolved chain goal forces the shared map.
        let node_rule_map = node_rules.get_or_init(|| sys.node_rule_map());
        let Some((_, t_start, t_end)) = kd_chain_view(node_rule_map, &c, &p) else {
            continue;
        };
        let poss_opt = possible_root_syms(t_start);
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
        Term::App(sym, _) => Some(RootSym::Sym(*sym)),
        // HS's guard `Lit _ | sortOfLNTerm t == LSortMsg -> Nothing`
        // (Contradictions.hs) drops every message-sorted literal, constants
        // (`sortOfName`, LTerm.hs) included.
        Term::Lit(l) => {
            let s = match l {
                Lit::Var(v) => v.sort,
                Lit::Con(n) => tamarin_term::lterm::sort_of_name(n),
            };
            (s != LSort::Msg).then_some(RootSym::Sort(s))
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
            FunSym::NoEq(s) if *s == exp_sym() && args.len() == 2 => Some(DhView::Exp(&args[0])),
            FunSym::NoEq(s) if *s == pmult_sym() && args.len() == 2 => {
                Some(DhView::PMult(&args[1]))
            }
            FunSym::C(CSym::EMap) => Some(DhView::EMap),
            _ => None,
        }
    } else {
        None
    }
}

enum DhView<'a> {
    Exp(&'a tamarin_term::lterm::LNTerm),
    PMult(&'a tamarin_term::lterm::LNTerm),
    EMap,
}

/// `possibleEndSyms`: HS-faithful port using `viewTerm2` to apply DH-
/// special cases (FExp/FPMult/FEMap).  Mirrors `possibleEndSyms` in
/// Contradictions.hs (defined locally inside `hasImpossibleChain`).
fn possible_end_syms(t: &tamarin_term::lterm::LNTerm) -> Option<Vec<RootSym>> {
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
fn possible_root_syms(t: &tamarin_term::lterm::LNTerm) -> Option<Vec<RootSym>> {
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

/// HS `hasForbiddenKD` (Contradictions.hs): a `KD(t)` conclusion where
/// `neverContainsFreshPriv t` (no private symbol, every literal of sort Pub,
/// Nat or Node), so the adversary could have built `t` instead. Haskell skips
/// it when `sDiffSystem` is set.
///
/// Current limitation: `sys.side` is not Haskell's `sDiffSystem` flag.
/// Trace systems have no side and run this check; implementing diff mode
/// requires a separate system-mode flag.
fn has_forbidden_kd(sys: &System) -> bool {
    use crate::fact::FactTag;
    if sys.side.is_some() {
        return false;
    }
    for (_, rule) in sys.nodes.iter() {
        for fa in &rule.conclusions {
            if !matches!(fa.tag, FactTag::Kd) {
                continue;
            }
            let Some(t) = fa.terms.first() else { continue };
            if never_contains_fresh_priv(t) {
                return true;
            }
        }
    }
    false
}

/// True iff no instance of `t` can ever contain fresh names or
/// private function symbols.  Walks the term; rejects Msg/Fresh
/// literals (they could instantiate to anything) and any private
/// function symbol.
fn never_contains_fresh_priv(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => !matches!(v.sort, LSort::Msg | LSort::Fresh),
        Term::Lit(Lit::Con(n)) => !matches!(n.tag, NameTag::Fresh),
        Term::App(sym, args) => {
            // Reject if the head is a private function symbol.
            if sym.is_private() {
                return false;
            }
            args.iter().all(never_contains_fresh_priv)
        }
    }
}

/// `hasForbiddenConstrChain` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenConstrChain`.
///
/// Detects non-normal chains linking two instances of the SAME AC-symbol
/// construction rule where the connected component contains at least two
/// "trivial" instances (a premise that is a plain msg-var KU fact, or the
/// same AC symbol applied to only msg-vars).  Union-find over the
/// `LessAtom … Adversary` edges between AC-constructor nodes whose
/// conclusion feeds the other's premise, run to a fixpoint.
fn has_forbidden_constr_chain<'a>(
    sys: &'a System,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
) -> bool {
    use crate::constraint::constraints::Reason;
    use crate::rule::is_ac_constr_rule;

    // Every candidate pair comes from an `Adversary` less-atom whose two
    // endpoints both carry AC-constructor rules, so lacking either one
    // `extracted` is empty and the fixpoint below cannot report a chain.  This
    // runs on every solver step, so bail out before touching the eq-store.
    if sys
        .less_atoms
        .iter()
        .all(|la| la.reason != Reason::Adversary)
    {
        return false;
    }
    if !sys.nodes.iter().any(|n| is_ac_constr_rule(&n.1).is_some()) {
        return false;
    }

    ac_constr_chain_fixpoint(&extract_ac_constr_pairs(sys, node_rules))
}

/// One `extractNodesAndRules` hit: the two linked node ids, each node's
/// (eq-store-substituted) premises, and the AC symbol both rules construct.
///
/// HS carries the whole `RuleACInst` at each endpoint; the fixpoint only ever
/// reads `rPrems`, so the pair holds those directly.
type AcConstrPair = (
    NodeId,
    Vec<crate::fact::LNFact>,
    NodeId,
    Vec<crate::fact::LNFact>,
    tamarin_term::function_symbols::FunSym,
);

/// `extractNodesAndRules` over `sLessAtoms`: for each `LessAtom n1 n2
/// Adversary` where both nodes carry AC-constructor rules of the same symbol
/// and r1's (single) conclusion appears among r2's premises, record the two
/// nodes' (substituted) premises and the symbol.
///
/// Both endpoints resolve through the pass-shared `node_rule_map` index (forced
/// here, i.e. AFTER [`has_forbidden_constr_chain`]'s early-outs, so the non-AC
/// fast path never builds it) — it is only `.get()`-ed, and it keeps the FIRST
/// rule per id, so it answers exactly as `node_rule_safe` does.
fn extract_ac_constr_pairs<'a>(
    sys: &'a System,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
) -> Vec<AcConstrPair> {
    use crate::constraint::constraints::Reason;
    use crate::rule::is_ac_constr_rule;

    let node_rules = node_rules.get_or_init(|| sys.node_rule_map());
    sys.less_atoms
        .iter()
        .filter_map(|la| {
            if la.reason != Reason::Adversary {
                return None;
            }
            let n1 = la.smaller;
            let n2 = la.larger;
            let r1 = node_rules.get(&n1).copied()?;
            let r2 = node_rules.get(&n2).copied()?;
            let name1 = is_ac_constr_rule(r1)?;
            let name2 = is_ac_constr_rule(r2)?;
            if name1 != name2 {
                return None;
            }
            let conc = r1.conclusions.first()?;
            if r2.premises.contains(conc) {
                Some((n1, r1.premises.clone(), n2, r2.premises.clone(), name1))
            } else {
                None
            }
        })
        .collect()
}

/// `fst finalMap`: `initialMap` plus the union-find fold
/// `fixpoint (\x -> foldr updateMap x extractedNodesAndRules) (False, initialMap)`.
///
/// True as soon as one component has accumulated two trivial instances.
fn ac_constr_chain_fixpoint(extracted: &[AcConstrPair]) -> bool {
    use tamarin_term::function_symbols::FunSym;

    // A node's union-find entry: its component root, the trivial instances
    // accumulated under that root, and the component's AC symbol.
    type NodeInfo = (NodeId, BTreeSet<NodeId>, FunSym);

    // `trivial r n iden`: the singleton {iden} iff some premise of `r` is a
    // trivial or nearly-trivial (same-symbol) KU fact.
    let trivial = |prems: &[crate::fact::LNFact], n: &FunSym, iden: NodeId| -> BTreeSet<NodeId> {
        if prems.iter().any(|fa| {
            crate::fact::is_trivial_ku_fact(fa) || crate::fact::is_nearly_trivial_ku_fact(n, fa)
        }) {
            BTreeSet::from([iden])
        } else {
            BTreeSet::new()
        }
    };

    // `initialMap`: every endpoint maps to (itself, its trivial set, symbol).
    let mut map: BTreeMap<NodeId, NodeInfo> = BTreeMap::new();
    for (n1, p1, n2, p2, n) in extracted {
        map.insert(*n1, (*n1, trivial(p1, n, *n1), *n));
        map.insert(*n2, (*n2, trivial(p2, n, *n2), *n));
    }

    // `finalMap = fixpoint (\x -> foldr updateMap x extracted) (False, initialMap)`.
    let mut found = false;
    loop {
        // Pre-pass value of every entry this pass writes (`None` = key absent).
        // Entries no insert touched cannot differ, so testing just these against
        // the map decides the whole-map `==` the fixpoint needs — and a pass
        // that writes an entry back to the value it started with still counts
        // as unchanged, exactly as a full comparison would have it.
        let mut before: BTreeMap<NodeId, Option<NodeInfo>> = BTreeMap::new();
        // `foldr` walks the list right-to-left.
        for (a, _, b, _, n) in extracted.iter().rev() {
            if found {
                break;
            }
            let (Some((_, t1, _)), Some((c, t2, n2))) = (map.get(a).cloned(), map.get(b).cloned())
            else {
                continue;
            };
            if *n != n2 {
                continue;
            }
            let mut nodes = map
                .get(&c)
                .map(|(_, t3, _)| t3.clone())
                .expect("ac_constr_chain_fixpoint: root must be mapped");
            nodes.extend(t1.iter().copied());
            nodes.extend(t2.iter().copied());
            if nodes.len() >= 2 {
                found = true;
            }
            // HS `M.insert c … $ M.insert b … $ M.insert a … m` applies
            // right-to-left, so when `b == c` (the root itself) the
            // root's accumulated `nodes` entry must win — insert it LAST.
            for (k, v) in [(*a, (c, t1, n2)), (*b, (c, t2, n2)), (c, (c, nodes, n2))] {
                let old = map.insert(k, v);
                before.entry(k).or_insert(old);
            }
        }
        // Once `found` is set the loop above breaks on its first statement, so
        // no later pass can touch the map or the verdict.
        if found || before.iter().all(|(k, v)| map.get(k) == v.as_ref()) {
            return found;
        }
    }
}

/// HS `hasForbiddenChain` (Contradictions.hs): an unsolved chain that starts
/// at a message variable, does not end in `IEquality`, and whose start term
/// is already a `KU` action before the chain start.
fn has_forbidden_chain<'a>(
    sys: &'a System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
) -> bool {
    use tamarin_term::lterm::is_msg_var;

    // The `alwaysBefore` adjacency (`ab_adj`) is built once by the caller
    // (`contradictions`) and shared across all ordering checks; queried here
    // via `always_before_with` in the chain/node/goal loops below.
    for (c, p) in sys.unsolved_chains() {
        let node_rule_map = node_rules.get_or_init(|| sys.node_rule_map());
        let Some((p_rule, t_start, _)) = kd_chain_view(node_rule_map, &c, &p) else {
            continue;
        };
        // (1) Chain starts at a message variable.
        if !is_msg_var(t_start) {
            continue;
        }
        // (2) End rule is not IEquality.
        if matches!(
            &p_rule.info,
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IEquality)
        ) {
            continue;
        }
        // (3) Some KU(t_start) action precedes the chain start (HS
        // `allKUActions`). Only a KU of exactly `t_start` counts.
        if sys
            .all_ku_actions()
            .iter()
            .any(|(id, _, t)| *t == t_start && sys.always_before_with(ab_adj, id, &c.0))
        {
            return true;
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
fn has_forbidden_exp(sys: &System, ab_adj: &crate::constraint::system::PrebuiltAdj) -> bool {
    use crate::constraint::solver::goals::is_simple_term;
    use crate::rule::{IntrRuleACInfo, RuleInfo};
    use tamarin_term::function_symbols::{FunSym, EXP_SYM_STRING};
    use tamarin_term::lterm::{frees, is_msg_var, LNTerm};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // `niFactors` / multiset-subset are shared at module scope
    // (`ni_factors` / `ni_factors_subset`).

    // `kFactView` is shared at module scope (returns `KDir`/term).
    fn view_exp(t: &LNTerm) -> Option<(&LNTerm, &LNTerm)> {
        if let Term::App(FunSym::NoEq(s), args) = t
            && s.name == EXP_SYM_STRING
            && args.len() == 2
        {
            return Some((&args[0], &args[1]));
        }
        None
    }

    let all_ku = sys.all_ku_actions();

    // The `alwaysBefore` adjacency (`ab_adj`) is built once by the caller
    // (`contradictions`) and shared across all ordering checks; queried here
    // via `always_before_with` in the node loop and the `earlier_msg_vars`
    // scan below.
    // Mirror HS `forbiddenDExp` exactly.
    for (i, ru) in sys.nodes.iter() {
        // Only intruder DestrRules can be exp-down; cheap pre-filter.
        if !matches!(&ru.info, RuleInfo::Intr(IntrRuleACInfo::DestrRule { .. })) {
            continue;
        }
        if ru.premises.len() != 2 {
            continue;
        }
        if ru.conclusions.len() != 1 {
            continue;
        }
        let p1 = &ru.premises[0];
        let p2 = &ru.premises[1];
        let conc = &ru.conclusions[0];

        let (dt1, p1_term) = match k_fact_view(p1) {
            Some(x) => x,
            None => continue,
        };
        if dt1 != KDir::Dn {
            continue;
        }
        if view_exp(p1_term).is_none() {
            continue;
        }
        let (dt2, b) = match k_fact_view(p2) {
            Some(x) => x,
            None => continue,
        };
        if dt2 != KDir::Up {
            continue;
        }

        let (dtc, conc_term) = match k_fact_view(conc) {
            Some(x) => x,
            None => continue,
        };
        if dtc != KDir::Dn {
            continue;
        }

        // The "earlier MsgVars" set: KU-known terms which are MsgVars
        // whose node `j` is `alwaysBefore` `i`.
        let earlier_msg_vars = || -> Vec<LNTerm> {
            let mut out = Vec::new();
            for (j, _, t) in &all_ku {
                if !is_msg_var(t) {
                    continue;
                }
                if sys.always_before_with(ab_adj, j, i) {
                    out.push((*t).clone());
                }
            }
            out
        };
        let all_msg_vars_known_earlier = |g: &LNTerm| -> bool {
            let mvs = earlier_msg_vars();
            // `varTerm <$> frees g` then keep only MsgVars.
            for v in frees(g) {
                let vt: LNTerm = Term::Lit(Lit::Var(v));
                if !is_msg_var(&vt) {
                    continue;
                }
                if !mvs.contains(&vt) {
                    return false;
                }
            }
            true
        };

        let forbidden = if let Some((g, c)) = view_exp(conc_term) {
            // (1) conc = exp(g, c): g simple + all msg vars known earlier
            //     + niFactors c \\ niFactors b == []
            if !is_simple_term(g) || !all_msg_vars_known_earlier(g) {
                false
            } else {
                // niFactors c \\ niFactors b == [] (multiset subset).
                ni_factors_subset(c, b)
            }
        } else {
            // (2) conc = g (not exp-shaped)
            is_simple_term(conc_term) && all_msg_vars_known_earlier(conc_term)
        };

        if forbidden {
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
fn has_forbidden_bp(sys: &System) -> bool {
    if sys.nodes.iter().any(|(_, ru)| is_forbidden_d_pmult(ru)) {
        return true;
    }
    if sys
        .nodes
        .iter()
        .any(|(i, ru)| is_forbidden_d_emap(sys, i, ru))
    {
        return true;
    }
    if sys
        .nodes
        .iter()
        .any(|(i, ru)| is_forbidden_d_emap_order(sys, i, ru))
    {
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
fn is_forbidden_d_pmult<I>(
    ru: &crate::rule::Rule<crate::rule::RuleInfo<I, crate::rule::IntrRuleACInfo>>,
) -> bool {
    if ru.premises.len() != 2 {
        return false;
    }
    if ru.conclusions.len() != 1 {
        return false;
    }

    let p1 = &ru.premises[0];
    let p2 = &ru.premises[1];
    let conc = &ru.conclusions[0];

    // p1 = KD(pmult(_, p))
    let (dt1, p1_term) = match k_fact_view(p1) {
        Some(x) => x,
        None => return false,
    };
    if dt1 != KDir::Dn {
        return false;
    }
    // Only p1's SHAPE matters here; HS matches `(DnK, FPMult _ _)` and
    // binds neither component.
    if bp_view_pmult(p1_term).is_none() {
        return false;
    }
    // p2 = KU(b)
    let (dt2, b) = match k_fact_view(p2) {
        Some(x) => x,
        None => return false,
    };
    if dt2 != KDir::Up {
        return false;
    }
    // conc = KD(pmult(c, p))
    let (dtc, conc_term) = match k_fact_view(conc) {
        Some(x) => x,
        None => return false,
    };
    if dtc != KDir::Dn {
        return false;
    }
    let (c, p_conc) = match bp_view_pmult(conc_term) {
        Some(x) => x,
        None => return false,
    };

    // HS `isForbiddenDPMult` (Contradictions.hs) gates ONLY on the
    // structural shape checked above (`[p1,p2]`/`[conc]`, `(DnK, FPMult _ _)`
    // for p1, `(UpK, b)` for p2, `(DnK, FPMult c p)` for conc) — there is no
    // `isDPMultRule` guard (contrast isForbiddenDEMap/Order which DO guard).
    if !never_contains_fresh_priv(p_conc) {
        return false;
    }
    ni_factors_subset(c, b)
}

/// `isForbiddenDEMap` — Contradictions.hs.
///
/// A `dExp` rule whose first premise's provider is a `dEMap` rule
/// instance, where the EMap's `[s]P / [r]Q` premises are
/// "overcomplicated" relative to the `dExp`'s `ke` exponent.
fn is_forbidden_d_emap(
    sys: &System,
    i: &crate::constraint::constraints::NodeId,
    ru_exp: &crate::rule::Rule<
        crate::rule::RuleInfo<crate::rule::ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>,
    >,
) -> bool {
    use crate::rule::is_d_emap_rule;
    use crate::rule::is_d_exp_rule;
    use crate::rule::PremIdx;
    if !is_d_exp_rule(ru_exp) {
        return false;
    }
    if ru_exp.premises.len() != 2 {
        return false;
    }

    // ke_f := premIdx 1 of the dExp rule
    let ke_f = &ru_exp.premises[1];
    let (dt_ke, ke) = match k_fact_view(ke_f) {
        Some(x) => x,
        None => return false,
    };
    if dt_ke != KDir::Up {
        return false;
    }

    // Find the edge ((ns,_) → (i, PremIdx 0)) i.e. the rule providing
    // the dExp's first premise (the dEMap rule).
    let edge_ns = sys.edges.iter().find_map(|e| {
        if e.tgt.0 == *i && e.tgt.1 == PremIdx(0) {
            Some(e.src.0)
        } else {
            None
        }
    });
    let Some(ns) = edge_ns else {
        return false;
    };
    let Some(ru_emap) = sys.node_rule_safe(&ns) else {
        return false;
    };
    if !is_d_emap_rule(ru_emap) {
        return false;
    }
    if ru_emap.premises.len() != 2 {
        return false;
    }

    let sp_f = &ru_emap.premises[0];
    let rq_f = &ru_emap.premises[1];
    let (dt_sp, sp_term) = match k_fact_view(sp_f) {
        Some(x) => x,
        None => return false,
    };
    if dt_sp != KDir::Dn {
        return false;
    }
    let (s_sc, p_pt) = match bp_view_pmult(sp_term) {
        Some(x) => x,
        None => return false,
    };
    let (dt_rq, rq_term) = match k_fact_view(rq_f) {
        Some(x) => x,
        None => return false,
    };
    if dt_rq != KDir::Dn {
        return false;
    }
    let (r_sc, q_pt) = match bp_view_pmult(rq_term) {
        Some(x) => x,
        None => return false,
    };

    bp_over_complicated(s_sc, p_pt, ke) || bp_over_complicated(r_sc, q_pt, ke)
}

/// `isForbiddenDEMapOrder` — Contradictions.hs.
///
/// For a `dEMap` rule instance whose conclusion has the canonical
/// shape `KD(exp(em(p,q), Mult([s,r])))`, find the two protocol
/// rules feeding its premises (through an intermediate `IRecv`).
/// Forbidden iff the first protocol rule's fact tags are strictly
/// greater than the second's (normal-form fact-tag ordering).
fn is_forbidden_d_emap_order(
    sys: &System,
    i: &crate::constraint::constraints::NodeId,
    ru: &crate::rule::Rule<
        crate::rule::RuleInfo<crate::rule::ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>,
    >,
) -> bool {
    use crate::rule::{is_d_emap_rule, PremIdx};
    use tamarin_term::function_symbols::{AcSym, CSym, FunSym, EXP_SYM_STRING};
    use tamarin_term::term::Term;
    if !is_d_emap_rule(ru) {
        return false;
    }
    if ru.premises.len() != 2 {
        return false;
    }
    if ru.conclusions.len() != 1 {
        return false;
    }

    let f_p0 = &ru.premises[0];
    let f_p1 = &ru.premises[1];
    let f_c0 = &ru.conclusions[0];

    let (dt0, t0) = match k_fact_view(f_p0) {
        Some(x) => x,
        None => return false,
    };
    if dt0 != KDir::Dn {
        return false;
    }
    let (s_sc, p_pt) = match bp_view_pmult(t0) {
        Some(x) => x,
        None => return false,
    };

    let (dt1, t1) = match k_fact_view(f_p1) {
        Some(x) => x,
        None => return false,
    };
    if dt1 != KDir::Dn {
        return false;
    }
    let (r_sc, q_pt) = match bp_view_pmult(t1) {
        Some(x) => x,
        None => return false,
    };

    let (dtc, tc) = match k_fact_view(f_c0) {
        Some(x) => x,
        None => return false,
    };
    if dtc != KDir::Dn {
        return false;
    }

    // tc = exp(em(p', q'), Mult([s', r', ...]))
    let (em_t, mult_arg) = match tc {
        Term::App(FunSym::NoEq(s), args) if s.name == EXP_SYM_STRING && args.len() == 2 => {
            (&args[0], &args[1])
        }
        _ => return false,
    };
    let (p_p, q_p) = match em_t {
        Term::App(FunSym::C(CSym::EMap), args) if args.len() == 2 => (&args[0], &args[1]),
        _ => return false,
    };
    let mult_args: Vec<tamarin_term::lterm::LNTerm> = match mult_arg {
        Term::App(FunSym::Ac(AcSym::Mult), args) => args.iter().cloned().collect(),
        _ => return false,
    };

    // guard ((p,q) == (p',q') || (p,q) == (q',p'))
    let ok_pair = (p_pt == p_p && q_pt == q_p) || (p_pt == q_p && q_pt == p_p);
    if !ok_pair {
        return false;
    }
    // && (mult_args \\ [s,r] == [])  — every mult_arg appears among [s,r]
    let mut remaining: Vec<tamarin_term::lterm::LNTerm> = vec![s_sc.clone(), r_sc.clone()];
    for a in &mult_args {
        let Some(pos) = remaining.iter().position(|x| x == a) else {
            return false;
        };
        remaining.remove(pos);
    }
    // remaining can be non-empty (HS only checks mult_args ⊆ [s,r]).

    // For each premise of i, follow edge backwards through IRecv to
    // the protocol rule.
    let lookup_prem_provider = |k: &crate::constraint::constraints::NodeId,
                                pi: PremIdx|
     -> Option<crate::constraint::constraints::NodeId> {
        sys.edges.iter().find_map(|e| {
            if e.tgt.0 == *k && e.tgt.1 == pi {
                Some(e.src.0)
            } else {
                None
            }
        })
    };
    let j1 = lookup_prem_provider(i, PremIdx(0));
    let j2 = lookup_prem_provider(i, PremIdx(1));
    let (Some(j1), Some(j2)) = (j1, j2) else {
        return false;
    };

    let ru_proto1 = lookup_prem_provider(&j1, PremIdx(0)).and_then(|n| sys.node_rule_safe(&n));
    let ru_proto2 = lookup_prem_provider(&j2, PremIdx(0)).and_then(|n| sys.node_rule_safe(&n));
    let (Some(rp1), Some(rp2)) = (ru_proto1, ru_proto2) else {
        return false;
    };

    // isStandRule: standard protocol rule (not Intr/Fresh/Pub).
    use crate::rule::{ProtoRuleACInstInfo, ProtoRuleName, RuleInfo};
    let is_stand = |r: &crate::rule::Rule<
        RuleInfo<ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>,
    >|
     -> bool {
        match &r.info {
            RuleInfo::Proto(p) => matches!(p.name, ProtoRuleName::Stand(_)),
            _ => false,
        }
    };
    if !is_stand(rp1) || !is_stand(rp2) {
        return false;
    }

    // factTags ruProto1 > factTags ruProto2
    //   where factTags ru = map (map factTag) [rPrems ru, rConcs ru, rActs ru]
    // HS compares a list-OF-lists, so each fact group is a distinct inner
    // list whose length is significant — they must NOT be flattened into a
    // single sequence (that would cross group boundaries). Build
    // `[[prem tags], [conc tags], [act tags]]` and compare lexicographically.
    let tags_of = |r: &crate::rule::Rule<
        RuleInfo<ProtoRuleACInstInfo, crate::rule::IntrRuleACInfo>,
    >|
     -> Vec<Vec<crate::fact::FactTag>> {
        vec![
            r.premises.iter().map(|f| f.tag).collect(),
            r.conclusions.iter().map(|f| f.tag).collect(),
            r.actions.iter().map(|f| f.tag).collect(),
        ]
    };
    tags_of(rp1) > tags_of(rp2)
}

/// `kFactView`: returns (KDir, term) for KU / KD facts.
/// `KDir::Up` = KU (constructible), `KDir::Dn` = KD (destruction).
/// Shared by `has_forbidden_exp`, the BP contradiction checks and
/// `kd_chain_view`.
#[derive(Copy, Clone, PartialEq, Eq)]
enum KDir {
    Up,
    Dn,
}
fn k_fact_view(fa: &crate::fact::LNFact) -> Option<(KDir, &tamarin_term::lterm::LNTerm)> {
    use crate::fact::FactTag;
    if fa.terms.len() != 1 {
        return None;
    }
    match fa.tag {
        FactTag::Ku => Some((KDir::Up, &fa.terms[0])),
        FactTag::Kd => Some((KDir::Dn, &fa.terms[0])),
        _ => None,
    }
}

/// View `pmult(scalar, point)` — returns `(scalar, point)`.
fn bp_view_pmult(
    t: &tamarin_term::lterm::LNTerm,
) -> Option<(&tamarin_term::lterm::LNTerm, &tamarin_term::lterm::LNTerm)> {
    use tamarin_term::function_symbols::{FunSym, PMULT_SYM_STRING};
    use tamarin_term::term::Term;
    if let Term::App(FunSym::NoEq(s), args) = t
        && s.name == PMULT_SYM_STRING
        && args.len() == 2
    {
        return Some((&args[0], &args[1]));
    }
    None
}

/// `niFactors`: HS Term/LTerm.hs.  The non-inverse factors of a
/// term.  `Mult(ts...)` → concat-map ni_factors; `Inv(t)` → ni_factors t;
/// else `[t]`.  Shared by `has_forbidden_exp` and the BP checks.
fn ni_factors(t: &tamarin_term::lterm::LNTerm) -> Vec<tamarin_term::lterm::LNTerm> {
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::Ac(AcSym::Mult), args) => {
            let mut out = Vec::new();
            for a in args.iter() {
                out.extend(ni_factors(a));
            }
            out
        }
        Term::App(FunSym::NoEq(s), args) if s.name == INV_SYM_STRING && args.len() == 1 => {
            ni_factors(&args[0])
        }
        _ => vec![t.clone()],
    }
}

/// `niFactors c \\ niFactors b == []`: every non-inverse factor of `c`
/// appears in `b`'s non-inverse factors (multiset semantics).
fn ni_factors_subset(c: &tamarin_term::lterm::LNTerm, b: &tamarin_term::lterm::LNTerm) -> bool {
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
fn bp_over_complicated(
    scalar: &tamarin_term::lterm::LNTerm,
    point: &tamarin_term::lterm::LNTerm,
    ke: &tamarin_term::lterm::LNTerm,
) -> bool {
    ni_factors_subset(scalar, ke) && never_contains_fresh_priv(point)
}

/// Direct port of Haskell's `nonInjectiveFactInstances`
/// (`Theory.Constraint.Solver.Contradictions`).
///
/// For every edge `(i,_) → (k,_)` whose conclusion fact has an
/// injective tag and first term `t`, find every reachable node `j`
/// (via the raw less-relation) such that `j ≠ i, k` and `j`'s rule
/// produces or consumes a fact of the same tag with the same first
/// term, AND `k` is reachable from `j` (or `k` is a last node whose
/// rule instance cannot unify with `j`).
///
/// Such a `(i, j, k)` triple witnesses two simultaneous "live"
/// instances of the injective fact, contradicting injectivity.
fn non_injective_fact_instances<'a>(
    ctxt: &ProofContext,
    sys: &'a System,
    adj: &tamarin_utils::FastMap<NodeId, Vec<NodeId>>,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
    first_only: bool,
    out: &mut Vec<Contradiction>,
) -> Result<(), crate::prove::ProveError> {
    let candidates =
        injective_interference_candidates_with_graph(ctxt, sys, adj, node_rules, |_| true);
    let mut reach = BTreeMap::new();
    for (i, j, k) in candidates {
        let ordered = reach
            .entry(j)
            .or_insert_with(|| crate::constraint::solver::goals::reachable_set_adj(adj, &j, false))
            .contains(&k);
        let incompatible_last = if !ordered && sys.last_atom == Some(k) {
            let rules = node_rules.get_or_init(|| sys.node_rule_map());
            crate::constraint::solver::simplify::non_unifiable_nodes(&ctxt.maude, rules, &j, &k)
                .map_err(|error| crate::prove::ProveError::maude("last-node unification", error))?
        } else {
            false
        };
        if ordered || incompatible_last {
            out.push(Contradiction::NonInjectiveFactInstance(i, j, k));
            if first_only {
                break;
            }
        }
    }
    Ok(())
}

/// Upstream aec550a2: identify interference independently of the final-node
/// contradiction test so simplification can merge compatible final events.
pub(crate) fn injective_interference_candidates(
    ctxt: &ProofContext,
    sys: &System,
    adj: &crate::constraint::system::PrebuiltAdj,
    endpoint: impl Fn(NodeId) -> bool,
) -> Vec<(NodeId, NodeId, NodeId)> {
    injective_interference_candidates_with_graph(
        ctxt,
        sys,
        adj.map(),
        &std::cell::OnceCell::new(),
        endpoint,
    )
}

fn injective_interference_candidates_with_graph<'a>(
    ctxt: &ProofContext,
    sys: &'a System,
    adj: &tamarin_utils::FastMap<NodeId, Vec<NodeId>>,
    node_rules: &std::cell::OnceCell<NodeRuleMap<'a>>,
    endpoint: impl Fn(NodeId) -> bool,
) -> Vec<(NodeId, NodeId, NodeId)> {
    let mut out = Vec::new();
    if ctxt.injective_fact_insts.is_empty() {
        return out;
    }

    // `adj` is the raw less-relation (`rawLessRel`: less + edges + unsolved
    // chains), built once by the caller (`contradictions`) and shared. We
    // enumerate reachable sets here rather than reuse always_before, which
    // only queries a single pair.
    // `adj` is invariant across this function, so memoize each node's
    // reachable set: `reachable(i)` is taken once per edge and `reachable(j)`
    // once per reachable `j`, with the same `j` recurring across edges.
    // Cached reachable sets exclude the starting node.
    fn reachable(
        cache: &mut BTreeMap<NodeId, Rc<BTreeSet<NodeId>>>,
        adj: &tamarin_utils::FastMap<NodeId, Vec<NodeId>>,
        from: &NodeId,
    ) -> Rc<BTreeSet<NodeId>> {
        if let Some(cached) = cache.get(from) {
            return Rc::clone(cached);
        }
        // Strictly-reachable set (seed removed) via the shared routine.
        let out = Rc::new(crate::constraint::solver::goals::reachable_set_adj(
            adj, from, false,
        ));
        cache.insert(*from, Rc::clone(&out));
        out
    }
    let mut reach_cache: BTreeMap<NodeId, Rc<BTreeSet<NodeId>>> = BTreeMap::new();
    // Resolve node-id → rule via the pass-shared map (forced here, after
    // the injective-tag early-out) instead of a linear `nodes.iter().find`
    // per `i`/`j`.
    let node_rule_map = node_rules.get_or_init(|| sys.node_rule_map());
    let lookup_node =
        |id: &NodeId| -> Option<&crate::rule::RuleACInst> { node_rule_map.get(id).copied() };

    let mut edges: Vec<_> = sys.edges.iter().collect();
    edges.sort();
    for e in edges {
        let (i, conc_idx) = (e.src.0, e.src.1);
        let k = e.tgt.0;
        if !endpoint(k) {
            continue;
        }
        // Look up the conclusion fact at (i, conc_idx).
        let i_rule = match lookup_node(&i) {
            Some(r) => r,
            None => continue,
        };
        let k_fa_prem = match i_rule.conclusions.get(conc_idx.0) {
            Some(f) => f,
            None => continue,
        };
        if !ctxt.is_injective_tag(&k_fa_prem.tag) {
            continue;
        }
        let k_term = k_fa_prem.terms.first();
        // Reachable set from i.
        let reach = reachable(&mut reach_cache, adj, &i);
        for j in reach.iter() {
            if j == &i || j == &k {
                continue;
            }
            let j_rule = match lookup_node(j) {
                Some(r) => r,
                None => continue,
            };
            // Conflicting fact in j's prems or concs.
            let conflicting = |fa: &crate::fact::LNFact| -> bool {
                fa.tag == k_fa_prem.tag && fa.terms.first() == k_term
            };
            let has_conflict = j_rule.premises.iter().any(conflicting)
                || j_rule.conclusions.iter().any(conflicting);
            if !has_conflict {
                continue;
            }
            out.push((i, *j, k));
        }
    }
    out
}

/// Has the system's formula list been forced to ⊥?
fn has_false_formula(sys: &System) -> bool {
    use crate::guarded::Guarded;
    sys.formulas
        .iter()
        .any(|f| matches!(f.as_ref(), Guarded::Disj(v) if v.is_empty()))
}

/// HS `nodesAfterLast` (Contradictions.hs): in-trace nodes reachable from
/// the last node through `rawLessRel`.
fn node_after_last(
    sys: &System,
    adj: &tamarin_utils::FastMap<NodeId, Vec<NodeId>>,
    first_only: bool,
    out: &mut Vec<Contradiction>,
) {
    let Some(last) = sys.last_atom else {
        return;
    };
    // `adj` is `rawLessRel`; `j /= i` drops the seed.
    let visited = crate::constraint::solver::goals::reachable_set_adj(adj, &last, false);
    let after = visited
        .into_iter()
        .filter(|n| sys.is_in_trace(n))
        .map(|after| Contradiction::NodeAfterLast(last, after));
    if first_only {
        out.extend(after.take(1));
    } else {
        out.extend(after);
    }
}

/// `maybeNonNormalTerms`: walk all node facts + new_vars, returning every
/// subterm that could be non-normal under some substitution.  Used by
/// [`SubstNfChecker`] below.  Mirrors Haskell's
/// `Contradictions.maybeNonNormalTerms` (Contradictions.hs).
///
/// The walk reads only the system's `nodes`, so a shared [`SubstNfChecker`]
/// can pin an O(1) `Arc<Vec<(NodeId, RuleACInst)>>` snapshot and force the
/// identical walk lazily.  The `BTreeSet` dedup is load-bearing for workload
/// downstream — it must stay.
pub fn maybe_non_normal_terms_nodes(
    nodes: &[(NodeId, crate::rule::RuleACInst)],
    irreducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut candidates: std::collections::BTreeSet<tamarin_term::lterm::LNTerm> =
        std::collections::BTreeSet::new();
    for (_, rule) in nodes.iter() {
        for f in rule
            .premises
            .iter()
            .chain(&rule.conclusions)
            .chain(&rule.actions)
        {
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
/// `EquationStore::simp` snapshots `self.subst` per iteration and
/// probes every candidate against that same snapshot). The predicate does
/// not advance the fresh counter.
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
    applied: std::cell::RefCell<
        Option<(
            crate::tools::equation_store::LNSubst,
            Vec<(
                tamarin_term::lterm::LNTerm,
                Vec<tamarin_term::lterm::LVar>,
                u64,
            )>,
        )>,
    >,
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
        if base.is_empty() {
            return false;
        }
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
            )> = base
                .iter()
                .map(|t| {
                    let t = apply_vterm(fsubst, t.clone());
                    let tvars: Vec<tamarin_term::lterm::LVar> = vars_vterm(&t);
                    let fresh_start = tvars
                        .iter()
                        .map(|v| v.idx)
                        .max()
                        .unwrap_or(0)
                        .saturating_add(1);
                    (t, tvars, fresh_start)
                })
                .collect();
            *applied = Some((fsubst.clone(), terms));
        }
        let terms = &applied.as_ref().unwrap().1;
        let sig = self.maude.maude_sig();
        for (t, tvars, fresh_start) in terms {
            if tvars.is_empty() {
                continue;
            }
            // `dom(restrictVFresh tvars subst) == ∅` ⟺ no `tvar` is in the
            // subst's domain; test that directly (`image_of` = domain map
            // lookup) and build the restricted map only on overlap.  Same
            // `continue` condition as `restrict(tvars).dom().count() == 0`,
            // without the empty-map alloc on the common no-overlap probe.
            if !tvars.iter().any(|v| vfresh_subst.image_of(v).is_some()) {
                continue;
            }
            let restricted = vfresh_subst.restrict(tvars);
            // HS `freshToFreeAvoidingFast subst tvars` (Term/Substitution.hs):
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
            if &t_prime == t {
                continue;
            }
            // Slow path: structural NF check (HS-faithful).  Mirrors HS
            // `nfApply subst0 t = t == t' || nf' t' \`runReader\` hnd`
            // where `nf' = nfViaHaskell` (Norm.hs) — run with the
            // handle, as HS does: the st-rule arm needs Maude AC matching
            // for rules whose LHS contains an Ac-/C-headed subterm, including
            // user `[AC]` cancellation equations. This is
            // the STRUCTURAL check, NOT `maude.reduce(t) == t`.  The
            // distinction matters because Maude canonicalises AC operator
            // arguments (multiset / mult / xor / nat-plus), so
            // `mult(tid, x)` and `mult(x, tid)` are different `Eq`
            // representations but both in NF.
            let is_nf = tamarin_term::norm::nf_via_haskell_maude(&sig, &self.maude, &t_prime);
            if !is_nf {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
#[path = "contradictions_tests.rs"]
mod tests;
