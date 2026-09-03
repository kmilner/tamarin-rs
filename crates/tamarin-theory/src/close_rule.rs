// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! No-deconstruction-chain (NDC) check — port of the NDC parts of HS
//! `CloseRule.hs` (`prettyNDCcheck` / `applyNDCcheck` / `ndcCheck` /
//! `chainedRulesDeductionTest` / `deductionCheck` / `dedNaive`).
//!
//! HS runs the check once at theory-load time (`checkCloseIntrRule`,
//! TheoryLoader.hs) on the freshly assembled intruder-rule cache:
//! non-built-in deconstruction rules are grouped per head function
//! (all-subterm groups are skipped), and each remaining group is tested
//! for the NDC property — "any chain of two rules of this function can be
//! reduced" — by unifying rule conclusions with KD-premises (`ndcCheck`)
//! and then checking, per unifier, that the chained conclusion is
//! derivable WITHOUT chaining (`chainedRulesDeductionTest`): first the
//! cheap syntactic `dedNaive`, then the full `deductionCheck`, which
//! synthesises a one-rule tamarin theory per KU-decomposition and runs
//! the auto-prover on a `Deduction` lemma, accepting only `TraceFound`.
//!
//! A function found NDC is (a) tagged in the signature (the `functions:`
//! header prints `[NDC]`) and (b) tagged on its deconstruction rules'
//! head `FunSym`, which activates `forbidden_edge`'s no-consecutive-NDC
//! clause in `solveChain`.  The final cache order is
//! `checked groups ++ (built-in | constructor | pre-tagged NDC rules) ++
//! all-subterm groups` — the same permutation `ndc_check_cache_order`
//! mirrors when the property check itself is suppressed.
//!
//! RS wiring: [`check_close_intr_rule`] runs the pass ONCE per theory at
//! load time (batch `run.rs` and the web server's `theory_io.rs`), before
//! the message-derivation checks — mirroring HS `checkTranslatedTheory`.
//! The caller joins the returned NDC verdicts into its printed signature
//! (`join_ndc_in_sig`) and INJECTS the returned tagged+permuted cache into
//! every later `ProofContext` construction for the theory (the
//! `intr_override` constructor parameter), so no context re-runs the
//! check — HS's `closeRuleCache` likewise consumes `_thyCache` verbatim.
//! The synthetic deduction theories are built STRUCTURALLY — the `Out0`
//! rule, the restriction(s) and the `Deduction` lemma constructed as
//! values, mirroring HS's `addRules`/`addLemmas`/`addRestrictions` over
//! `emptyThy` (CloseRule.hs:242-252) — and proved with an INJECTED
//! intruder cache (`bound_to_one` of the parent's pre-check cache),
//! mirroring HS's `closeTheoryWithMaude sig t` with
//! `thyCache = intrRmodified`.  A text render → parse → elaborate
//! pipeline of the same theories is kept under `cfg(test)` as the
//! differential reference for the structural builders (see the tests).

use tamarin_term::function_symbols::{FunSym, NdcState, Privacy};
use tamarin_term::lterm::{BVar, HasFrees, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::rewriting::Equal;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;
use tamarin_term::vterm::var_term;

use crate::atom::ProtoAtom;
use crate::constraint::solver::context::IntrRuleCache;
use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
use crate::formula::{exists_var, for_all_var, lift_free, BLNTerm, LNFormula, ProtoFormula};
use crate::guarded::Guarded;
use crate::rule::{
    apply_subst_rule, get_conc_fact, get_deconstr_rule_kd_prem, get_deconstr_rule_prems_tail,
    get_destr_rule_function, IntrRuleAC, IntrRuleACInfo,
};

// =============================================================================
// Load-time entry (HS `checkCloseIntrRule`)
// =============================================================================

/// Result of the once-per-theory load-time NDC pass.
pub struct NdcCheckedCache {
    /// The theory's final intruder-rule cache: NDC-tagged and permuted
    /// when the check ran, raw assembly order under `--no-ndc`.  Callers
    /// inject this into every `ProofContext` built for the theory (the
    /// `intr_override` constructor parameter) — HS's `closeRuleCache`
    /// consumes the checked `_thyCache` verbatim.
    pub cache: Vec<IntrRuleAC>,
    /// Function symbols found to have the NDC property (HS
    /// `joinNDCinSigWMaude` targets).  Callers join these into the
    /// theory's signature so every rendering of the `functions:` header
    /// shows `[NDC]`.  Empty when the check is disabled or tags nothing.
    pub ndc_funs: Vec<FunSym>,
}

/// Once-per-theory NDC pass at theory load — HS `checkCloseIntrRule`
/// (TheoryLoader.hs): assemble the intruder-rule cache from the handle's
/// signature and, when `deduction_chain_check` holds (HS
/// `_deductionChainCheck`; `--no-ndc` clears it), run [`pretty_ndc_check`]
/// over it — stderr markers, per-function verdict lines, rule tagging and
/// the cache permutation.  With the check disabled the cache keeps raw
/// assembly order and nothing is tagged, exactly as HS's `else (sign,
/// intrRules)` branch.
///
/// `theory_name` feeds the two `[Theory NAME] No Deconstruction Chain
/// checks started/ended` markers; `None` suppresses them.
pub fn check_close_intr_rule(
    maude: &MaudeHandle,
    theory_name: Option<&str>,
    deduction_chain_check: bool,
    initial: &[IntrRuleAC],
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> NdcCheckedCache {
    let assembled = crate::constraint::solver::context::ProofContext::assemble_intruder_rules(
        &maude.maude_sig(),
        maude,
        initial,
    );
    if !deduction_chain_check {
        return NdcCheckedCache {
            cache: assembled,
            ndc_funs: Vec::new(),
        };
    }
    let (ndc_funs, cache) = pretty_ndc_check(maude, theory_name, assembled, parameters);
    NdcCheckedCache { cache, ndc_funs }
}

// =============================================================================
// Cache partition (shared with `ndc_check_cache_order`)
// =============================================================================

/// `isNDCRule` on a not-yet-instantiated cache rule: deconstruction rule
/// whose head function carries the trace-mode NDC flag.
fn is_ndc_cache_rule(r: &IntrRuleAC) -> bool {
    get_destr_rule_function(r).is_some_and(|f| f.is_ndc_fun_sym())
}

/// The partition/group/sort skeleton of HS `prettyNDCcheck`:
///
/// ```haskell
/// (builtInOrConstrOrNDC, nonBuiltInDestr) = partition
///     (\x -> isBuiltInIntruderRule x || isConstrRule x
///            || isJust (isNDCRule x)) initRules
/// t' = groupBy ((==) `on` getDestrRuleFunction)
///          $ sortOn getDestrRuleFunction nonBuiltInDestr
/// (subtermRules, t) = partition (all isSubtermRule) t'
/// ```
///
/// Returns `(builtin_or_constr_or_ndc, checked_groups, all_subterm_rules)`;
/// both sorts are stable so within a group the assembly order survives.
pub(crate) fn partition_for_ndc(
    rules: Vec<IntrRuleAC>,
) -> (Vec<IntrRuleAC>, Vec<Vec<IntrRuleAC>>, Vec<IntrRuleAC>) {
    use crate::rule::{is_built_in_intruder_rule, is_constr_rule_info, is_subterm_rule_info};
    let (builtin_or_constr_or_ndc, mut non_builtin_destr): (Vec<_>, Vec<_>) =
        rules.into_iter().partition(|r| {
            is_built_in_intruder_rule(r) || is_constr_rule_info(&r.info) || is_ndc_cache_rule(r)
        });
    non_builtin_destr.sort_by_key(get_destr_rule_function);
    let mut checked_groups: Vec<Vec<IntrRuleAC>> = Vec::new();
    let mut all_subterm: Vec<IntrRuleAC> = Vec::new();
    let mut iter = non_builtin_destr.into_iter().peekable();
    while let Some(first) = iter.next() {
        let key = get_destr_rule_function(&first);
        let mut group = vec![first];
        while iter
            .peek()
            .is_some_and(|r| get_destr_rule_function(r) == key)
        {
            group.push(iter.next().expect("peeked"));
        }
        if group.iter().all(|r| is_subterm_rule_info(&r.info)) {
            all_subterm.extend(group);
        } else {
            checked_groups.push(group);
        }
    }
    (builtin_or_constr_or_ndc, checked_groups, all_subterm)
}

/// Final cache permutation of HS `prettyNDCcheck`: `concat t ++
/// builtInOrConstrOrNDC ++ concat subtermRules` — checked destructor
/// groups first, then the builtin/constructor/pre-tagged-NDC rules in
/// assembly order, then the all-subterm groups.  The order feeds chain
/// extension and source-case numbering, so it is parity-relevant; this is
/// the single place that fixes it.  Callers: [`pretty_ndc_check`] (checked
/// groups tagged by the property check) and `ProofContext`'s non-injected
/// construction (context.rs `ndc_check_cache_order`, check bypassed).
pub(crate) fn ndc_cache_order(
    checked: Vec<IntrRuleAC>,
    builtin_or_constr_or_ndc: Vec<IntrRuleAC>,
    all_subterm: Vec<IntrRuleAC>,
) -> Vec<IntrRuleAC> {
    let mut out = checked;
    out.extend(builtin_or_constr_or_ndc);
    out.extend(all_subterm);
    out
}

// =============================================================================
// dedNaive / decompose
// =============================================================================

/// Privacy of a function symbol's declaration.
fn fun_sym_private(f: &FunSym) -> bool {
    match f {
        FunSym::NoEq(s) => s.privacy == Privacy::Private,
        FunSym::Ac(tamarin_term::function_symbols::AcSym::AcFct(s)) => {
            s.privacy == Privacy::Private
        }
        _ => false,
    }
}

/// HS `dedNaive`: `fact` is directly present in `terms` or derivable from
/// them by construction alone (recursively over public applications).
fn ded_naive(fact: &LNTerm, terms: &[LNTerm]) -> bool {
    if terms.contains(fact) {
        return true;
    }
    match fact {
        Term::App(f, args) => !fun_sym_private(f) && args.iter().all(|a| ded_naive(a, terms)),
        Term::Lit(_) => false,
    }
}

/// HS `decompose`: enumerate the KU-decompositions of a fact list.  A KU
/// fact with an applied head either stays (as a KD fact) or — when the
/// head is not private — is decomposed into KU facts of its arguments
/// (recursively).  Non-KU facts (and KU facts of literals) pass through
/// unchanged.
fn decompose(facts: &[LNFact]) -> Vec<Vec<LNFact>> {
    let Some((f, rest)) = facts.split_first() else {
        return vec![vec![]];
    };
    let rest_d = decompose(rest);
    if f.tag == FactTag::Ku
        && f.terms.len() == 1
        && let Term::App(head, args) = &f.terms[0]
    {
        let as_kd = Fact::fresh_annotated(FactTag::Kd, f.annotations.clone(), f.terms.to_vec());
        let mut out: Vec<Vec<LNFact>> = rest_d
            .iter()
            .map(|l| {
                let mut l2 = Vec::with_capacity(l.len() + 1);
                l2.push(as_kd.clone());
                l2.extend(l.iter().cloned());
                l2
            })
            .collect();
        if !fun_sym_private(head) {
            let arg_kus: Vec<LNFact> = args
                .iter()
                .map(|a| Fact::fresh_annotated(FactTag::Ku, f.annotations.clone(), vec![a.clone()]))
                .collect();
            for x1 in decompose(&arg_kus) {
                for y in &rest_d {
                    let mut l = x1.clone();
                    l.extend(y.iter().cloned());
                    out.push(l);
                }
            }
        }
        return out;
    }
    rest_d
        .into_iter()
        .map(|mut l| {
            l.insert(0, f.clone());
            l
        })
        .collect()
}

// =============================================================================
// Synthetic deduction theory (HS `deductionCheck`)
// =============================================================================

/// HS `msgToFreshVars`: retype an `LSortMsg` variable to `LSortFresh`.
fn msg_to_fresh_var(v: &LVar) -> LVar {
    if v.sort == LSort::Msg {
        LVar::new(v.name, LSort::Fresh, v.idx)
    } else {
        *v
    }
}

/// HS `msgToFreshTerms`: retype every Msg-sorted variable inside a term.
fn msg_to_fresh_terms(t: &LNTerm) -> LNTerm {
    match t {
        Term::Lit(tamarin_term::vterm::Lit::Var(v)) => {
            Term::Lit(tamarin_term::vterm::Lit::Var(msg_to_fresh_var(v)))
        }
        Term::Lit(_) => t.clone(),
        Term::App(f, args) => Term::App(*f, args.iter().map(msg_to_fresh_terms).collect()),
    }
}

/// HS `newRules` (CloseRule.hs:257-262): the `Out0` source rule for one
/// decomposition `s`, built as a value.  Premises `Fr` each free variable
/// of `s`'s terms (`pre = freesToFresh . varFresh`: Msg vars retyped
/// Fresh by `msgToFreshVars`, Nat vars by `lvarToLnterm`); conclusions
/// `Out` every fact term with Msg vars retyped (`co`); actions
/// `Generated_0` over the retyped variables plus `OnlyOnce` (`a`).
/// `rNewVars` is HS's literal `[]` — the structural rule never runs the
/// parser's `newVariables` computation (Parser/Rule.hs:135).
fn deduction_rule(s: &[LNFact]) -> crate::theory::OpenProtoRule {
    // varD s (HS: `frees $ concatMap factTerms s` — `sortednub .
    // freesList`; the ordering fixes the `Generated_0` argument order,
    // used consistently on the rule and lemma sides).
    let var_d: Vec<LVar> = tamarin_term::lterm::frees(&s.to_vec());
    let prems: Vec<LNFact> = var_d
        .iter()
        .map(|v| crate::fact::fresh_fact(crate::fact::lvar_to_lnterm(&msg_to_fresh_var(v))))
        .collect();
    let concs: Vec<LNFact> = s
        .iter()
        .flat_map(|f| f.terms.iter())
        .map(|t| crate::fact::out_fact(msg_to_fresh_terms(t)))
        .collect();
    let gen_args: Vec<LNTerm> = var_d
        .iter()
        .map(|v| msg_to_fresh_terms(&crate::fact::lvar_to_lnterm(v)))
        .collect();
    let acts = vec![
        crate::fact::proto_fact(Multiplicity::Linear, "Generated_0", gen_args),
        crate::fact::proto_fact(Multiplicity::Linear, "OnlyOnce", vec![]),
    ];
    crate::theory::OpenProtoRule::new(crate::rule::Rule::new(
        crate::rule::ProtoRuleEInfo::standard("Out0"),
        prems,
        concs,
        acts,
    ))
}

/// A `#`-sorted idx-0 variable — the timepoint/binder shape the restriction
/// and lemma formulas quantify over (HS `LVar x LSortNode 0`,
/// CloseRule.hs:273-274).
fn ndc_node_var(name: &str) -> LVar {
    LVar::new(name, LSort::Node, 0)
}

/// A timepoint as a formula term: `LIT (Var (Free v))` (CloseRule.hs:273).
fn free_time(v: &LVar) -> BLNTerm {
    var_term(BVar::Free(*v))
}

/// `FACT() @ #tv` — HS `factAnd`/`factAndD` (CloseRule.hs:273,277): a
/// nullary Linear proto fact at a Node-sorted timepoint.
fn nullary_action_at(fact_name: &str, tv: &LVar) -> LNFormula {
    ProtoFormula::Atom(ProtoAtom::Action(
        free_time(tv),
        crate::fact::proto_fact(Multiplicity::Linear, fact_name, Vec::new()).map_ref(lift_free),
    ))
}

/// `#a = #b` — HS `factEq` (CloseRule.hs:274).
fn time_eq(a: &LVar, b: &LVar) -> LNFormula {
    ProtoFormula::Atom(ProtoAtom::EqE(free_time(a), free_time(b)))
}

/// `foldr (hinted forAll) f vs` (Theory/Text/Parser/Formula.hs:73-77, over
/// `forAll` Theory/Model/Formula.hs:355-356 and `hinted` :364-365): close
/// the binders from the last to the first, so the first variable of `vs`
/// carries the outermost quantifier.  The hint is
/// `hint (LVar n s _) = (n, s)` (Theory/Model/Formula.hs:227-228).
fn close_all(vs: &[LVar], body: LNFormula) -> LNFormula {
    vs.iter().rev().fold(body, |acc, v| {
        for_all_var((v.name.to_string(), v.sort), v, acc)
    })
}

/// [`close_all`] at `exists` (Theory/Model/Formula.hs:359-360).
fn close_ex(vs: &[LVar], body: LNFormula) -> LNFormula {
    vs.iter().rev().fold(body, |acc, v| {
        exists_var((v.name.to_string(), v.sort), v, acc)
    })
}

/// HS `newRestriction0` (CloseRule.hs:269-275):
/// `All #ndci #ndcj. OnlyOnce() @ #ndci & OnlyOnce() @ #ndcj ==> #ndci = #ndcj`.
/// HS names the binders `i`/`j` and closes them with `forAllFormula`, a
/// `foldl` over ascending `frees` that makes the LAST variable the outermost
/// binder (Theory/Model/Formula.hs:537-538), where [`close_all`] keeps the
/// written order.  Names and prefix order are hints only, invisible outside
/// the synthetic proof search.
fn only_once_restriction() -> LNFormula {
    let i = ndc_node_var("ndci");
    let j = ndc_node_var("ndcj");
    close_all(
        &[i, j],
        nullary_action_at("OnlyOnce", &i)
            .and(nullary_action_at("OnlyOnce", &j))
            .implies(time_eq(&i, &j)),
    )
}

/// HS `newRestriction2` (CloseRule.hs:280-283):
/// `All #ndci #ndcj #ndck. OnlyOnceD() @ #ndci & OnlyOnceD() @ #ndcj &
/// OnlyOnceD() @ #ndck ==> #ndci = #ndcj | #ndci = #ndck | #ndcj = #ndck`
/// (`.&&.` and `.||.` are `infixl`, and both bind tighter than `.==>.` —
/// Theory/Model/Formula.hs:233-235).
fn only_once_d_restriction() -> LNFormula {
    let i = ndc_node_var("ndci");
    let j = ndc_node_var("ndcj");
    let k = ndc_node_var("ndck");
    close_all(
        &[i, j, k],
        nullary_action_at("OnlyOnceD", &i)
            .and(nullary_action_at("OnlyOnceD", &j))
            .and(nullary_action_at("OnlyOnceD", &k))
            .implies(time_eq(&i, &j).or(time_eq(&i, &k)).or(time_eq(&j, &k))),
    )
}

/// HS `addRestrictions [newRestriction0, newRestriction2]` (theory-1) /
/// `[newRestriction0]` (theory-2) — CloseRule.hs:247,252 — as guarded
/// values in theory order (`OnlyOnce` first).  The formulas are closed
/// constants whose every binder is action-guarded, so the conversion
/// cannot fail.
fn deduction_restrictions(with_only_once_d: bool) -> Vec<Guarded> {
    let mut formulas = vec![only_once_restriction()];
    if with_only_once_d {
        formulas.push(only_once_d_restriction());
    }
    formulas
        .iter()
        .map(|f| {
            crate::guarded::formula_to_guarded(f).unwrap_or_else(|e| {
                panic!(
                    "[ndc] deduction restriction failed guarded conversion: {}",
                    e.message
                )
            })
        })
        .collect()
}

/// HS `newLemmas`' formula (CloseRule.hs:263-267):
/// `Not (existFormula (landFormula (aLemma s ++ [kLogFact fact_term])))`,
/// i.e. ¬∃ vars #t0 #t1. Generated_0(varD s) @ #t0 ∧ K(fact_term) @ #t1
/// — with `aLemma`'s arguments NOT Msg→Fresh-retyped (only
/// `lvarToLnterm`'s Nat→Fresh), and `kLogFact = protoFact Linear "K"`
/// (Theory/Model/Fact.hs:301-303).  `landFormula` lifts each fact with
/// `fmap (fmap (fmap Free))` (CloseRule.hs:200-201) — [`Fact::map_ref`] of
/// [`lift_free`].
///
/// Binder names and order: HS quantifies `frees` under their own names with
/// timepoints `"0"`/`"1"`; here the data binders keep first-occurrence order
/// with `ndct`-named timepoints last — names and prefix order are hints
/// only, invisible outside the synthetic search.  Same-named binders stay
/// distinct because a binder closes exactly the occurrences equal to its
/// whole `LVar` (HS `quantify`'s `v == x`, Theory/Model/Formula.hs:350-352),
/// so a Nat variable (Fresh in the `Generated_0` args via `lvarToLnterm`,
/// Nat inside the K term) and dotted-index unifier variables (`x.5`) each
/// close their own occurrences.
fn deduction_lemma_guarded(s: &[LNFact], fact_term: &LNTerm) -> Guarded {
    let var_d: Vec<LVar> = tamarin_term::lterm::frees(&s.to_vec());
    // aLemma s (CloseRule.hs:263): `map lvarToLnterm (varD s)`.
    let gen_args: Vec<LNTerm> = var_d.iter().map(crate::fact::lvar_to_lnterm).collect();
    let mut binders: Vec<LVar> = Vec::new();
    for t in gen_args.iter().chain(std::iter::once(fact_term)) {
        t.for_each_free(&mut |v| {
            if !binders.contains(v) {
                binders.push(*v);
            }
        });
    }
    let t0 = ndc_node_var("ndct0");
    let t1 = ndc_node_var("ndct1");
    let gen_at = ProtoFormula::Atom(ProtoAtom::Action(
        free_time(&t0),
        crate::fact::proto_fact(Multiplicity::Linear, "Generated_0", gen_args).map_ref(lift_free),
    ));
    let k_at = ProtoFormula::Atom(ProtoAtom::Action(
        free_time(&t1),
        crate::fact::k_log_fact(fact_term.clone()).map_ref(lift_free),
    ));
    binders.push(t0);
    binders.push(t1);
    let fm = close_ex(&binders, gen_at.and(k_at)).not();
    // Every binder occurs in one of the two Action guard atoms by
    // construction, so the conversion cannot fail on guardedness.
    crate::guarded::formula_to_guarded(&fm).unwrap_or_else(|e| {
        panic!(
            "[ndc] deduction lemma failed guarded conversion: {}",
            e.message
        )
    })
}

/// Build and auto-prove one synthetic deduction theory; `true` iff the
/// `Deduction` lemma's proof status folds to `TraceFound` (an attack on
/// the all-traces lemma = the fact IS derivable without chaining).
///
/// The theory is HS `modifiedTheory1/2` (CloseRule.hs:247-252), built
/// structurally over the parent signature already on `maude`: the `Out0`
/// rule, the restriction(s) and the `Deduction` lemma are constructed as
/// values ([`deduction_rule`], [`deduction_restrictions`],
/// [`deduction_lemma_guarded`]) — no text render, parse or re-elaborate.
/// The guarded-term instantiation inside the search reads the ambient
/// user-fun bundle; the load paths (run.rs, theory_io.rs) hold the
/// parent theory's guard around the whole NDC pass, and the synthetic
/// theory's signature IS the parent's, so the sets match.  Solver panics
/// propagate (HS aborts the load on the same failures, and a panic
/// raised while the shared Maude mutex guard is held leaves the handle
/// poisoned), so `false` means exactly one thing: the proof search
/// completed without finding a trace.
///
/// `run_proof_search` re-reads the opt-in `TAM_PROVE_DEADLINE_MS` wall-clock
/// cap for every search it runs (search.rs `proof_deadline`), this one
/// included; a deduction search that exhausts the cap returns a proof
/// without `TraceFound` and so answers `false`.  Unset (the default) the
/// search is unbounded, which is the HS-faithful configuration.
fn prove_deduction_theory(
    maude: &MaudeHandle,
    intr_modified: &IntrRuleCache,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> bool {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::search::{proof_status, run_proof_search, ProofStatus};
    use crate::constraint::system::{formula_to_system, SourceKind};

    let rules = vec![deduction_rule(s)];
    let restrictions = deduction_restrictions(with_only_once_d);
    let g = deduction_lemma_guarded(s, fact_term);
    let ctx = ProofContext::new_with_restrictions_pool_forced_and_parameters(
        maude.clone(),
        None,
        rules,
        restrictions.clone(),
        &[],
        Some(intr_modified.clone()),
        parameters,
    );
    ctx.ensure_saturated();
    let sys = formula_to_system(
        restrictions,
        SourceKind::RefinedSources,
        crate::theory::TraceQuantifier::AllTraces,
        &g,
    );
    let root = run_proof_search(&ctx, sys, usize::MAX)
        .expect("the deduction proof context has no fallible ranking or source provider");
    proof_status(&root) == ProofStatus::TraceFound
}

/// HS `deductionCheck` (CloseRule.hs:215): can `fact` be derived from
/// `facts` without chaining?  `intr_modified` is the `boundToOne`-mapped
/// cache injected into every decomposition's theory.
fn deduction_check(
    maude: &MaudeHandle,
    intr_modified: &BoundToOneCache<'_>,
    fact: &LNFact,
    facts: &[LNFact],
) -> bool {
    let fact_term = fact
        .terms
        .first()
        .expect("deductionCheck: KD facts carry exactly one term");
    let set_d: Vec<Vec<LNFact>> = decompose(facts)
        .into_iter()
        .filter(|s| {
            let terms: Vec<LNTerm> = s.iter().flat_map(|f| f.terms.iter().cloned()).collect();
            !ded_naive(fact_term, &terms)
        })
        .collect();
    if set_d.is_empty() {
        return true;
    }
    // `checkProofd tabProof1 || checkProofd tabProof2`: every
    // decomposition's proof must find a trace; theory-1 carries both
    // restrictions, theory-2 only `OnlyOnce`.
    let all_traces_found = |with_ood: bool| -> bool {
        set_d.iter().all(|s| {
            prove_deduction_theory(
                maude,
                intr_modified.modified(),
                s,
                fact_term,
                with_ood,
                intr_modified.parameters,
            )
        })
    };
    all_traces_found(true) || all_traces_found(false)
}

// =============================================================================
// ndcCheck / chainedRulesDeductionTest
// =============================================================================

/// HS `boundToOne` (inside `chainedRulesDeductionTest`), clause order
/// preserved: rules of the checked function get an `OnlyOnceD` action and
/// an NDC-set head fun; built-in deconstruction rules pass through;
/// other unbounded (budget 0) destructors are bounded to one application.
fn bound_to_one(rule: &IntrRuleAC, checked_fun: Option<FunSym>) -> IntrRuleAC {
    let mut out = rule.clone();
    if let IntrRuleACInfo::DestrRule {
        name,
        remaining_applications,
        funs,
        ..
    } = &mut out.info
    {
        if get_destr_rule_function(rule) == checked_fun {
            if let Some(f) = funs.first_mut() {
                *f = f.set_ndc(NdcState::IsNdc);
            }
            out.actions.push(crate::fact::proto_fact(
                Multiplicity::Linear,
                "OnlyOnceD",
                vec![],
            ));
        } else {
            let is_built_in = crate::rule::has_builtin_suffix(
                name.as_slice(),
                &crate::rule::built_in_destr_rule_incl_pair(),
            );
            if !is_built_in && *remaining_applications == 0 {
                *remaining_applications = 1;
            }
        }
    }
    out
}

/// The `boundToOne`-mapped intruder cache of one `apply_ndc_check` group.
/// Every `chainedRulesDeductionTest` of a group maps the cache with the same
/// `checked_fun` — the group's head function, which `apply_subst_rule`
/// leaves untouched — so the mapping is shared by the whole group and is
/// built on the first pair that actually reaches a deduction check.
struct BoundToOneCache<'a> {
    intr_r: &'a [IntrRuleAC],
    checked_fun: Option<FunSym>,
    modified: std::cell::OnceCell<IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
}

impl<'a> BoundToOneCache<'a> {
    fn new(
        intr_r: &'a [IntrRuleAC],
        checked_fun: Option<FunSym>,
        parameters: crate::constraint::solver::sources::IntegerParameters,
    ) -> Self {
        Self {
            intr_r,
            checked_fun,
            modified: std::cell::OnceCell::new(),
            parameters,
        }
    }

    /// The mapped cache as a shared handle: one group runs a deduction proof
    /// per decomposition per chainable pair, and each of those builds a
    /// `ProofContext` off this same rule list.
    fn modified(&self) -> &IntrRuleCache {
        self.modified.get_or_init(|| {
            IntrRuleCache::from(
                self.intr_r
                    .iter()
                    .map(|r| bound_to_one(r, self.checked_fun))
                    .collect::<Vec<_>>(),
            )
        })
    }
}

/// HS `chainedRulesDeductionTest`: after chaining `inst_sigma` into
/// `inst1_sigma`, is the chained conclusion derivable from the combined
/// premises without chaining?
fn chained_rules_deduction_test(
    maude: &MaudeHandle,
    intr_modified: &BoundToOneCache<'_>,
    inst_sigma: &IntrRuleAC,
    inst1_sigma: &IntrRuleAC,
) -> bool {
    let mut facts: Vec<LNFact> = Vec::new();
    facts.extend_from_slice(get_deconstr_rule_prems_tail(inst_sigma));
    facts.extend_from_slice(get_deconstr_rule_prems_tail(inst1_sigma));
    facts.push(get_deconstr_rule_kd_prem(inst_sigma).clone());
    let terms: Vec<LNTerm> = facts.iter().flat_map(|f| f.terms.iter().cloned()).collect();
    let fact_to_deduce = get_conc_fact(inst1_sigma);
    if !(fact_to_deduce.tag == FactTag::Kd && fact_to_deduce.terms.len() == 1) {
        panic!(
            "No Deconstruction Chain Check: This case should not happen, please report it on the github page"
        );
    }
    if ded_naive(&fact_to_deduce.terms[0], &terms) {
        return true;
    }
    deduction_check(maude, intr_modified, fact_to_deduce, &facts)
}

/// Shape guard of HS `ndcCheck`'s first clause: a deconstruction rule with
/// a leading KD premise, a single KD conclusion, and budget ≠ 1.
fn ndc_checkable(r: &IntrRuleAC) -> bool {
    let budget_ok = matches!(
        &r.info,
        IntrRuleACInfo::DestrRule {
            remaining_applications,
            ..
        } if *remaining_applications != 1
    );
    budget_ok
        && r.premises.first().is_some_and(|f| f.tag == FactTag::Kd)
        && matches!(r.conclusions.as_slice(), [c] if c.tag == FactTag::Kd)
}

/// A chainable ordered rule pair: the unifiers of `conc(r)` with
/// `kd_prem(r1)`, the two rules they instantiate, and the fresh supply
/// seeded above both rules' free variables.  [`ndc_check_eval`] builds
/// `applySubsts subst r freshInst1` from these, one unifier at a time.
struct ChainablePair<'a> {
    r: &'a IntrRuleAC,
    fresh_inst1: IntrRuleAC,
    unifs: Vec<Vec<(LVar, LNTerm)>>,
    counter: u64,
}

/// Chainability phase of HS `ndcCheck`: `None` when the pair cannot chain
/// (shape mismatch or no unifier of `conc(r)` with `kd_prem(r1)`);
/// otherwise the pair's unifiers for [`ndc_check_eval`].  HS keeps this
/// same split implicitly: forcing `ndcCheck` to WHNF runs only the
/// unification, both the instantiation and the deduction work stay
/// thunks inside the `Just`.
fn ndc_check_prepare<'a>(
    maude: &MaudeHandle,
    r: &'a IntrRuleAC,
    r1: &IntrRuleAC,
) -> Option<ChainablePair<'a>> {
    if !(ndc_checkable(r) && ndc_checkable(r1)) {
        return None;
    }
    // `r1 `renameAvoiding` r` — same idiom as
    // `equal_duplicate_rule_up_to_renaming`.
    let fresh_inst1 = tamarin_term::lterm::rename_avoiding(r1.clone(), r);
    let conc = r.conclusions[0].clone();
    let kd_prem1 = get_deconstr_rule_kd_prem(&fresh_inst1).clone();
    let unifs = crate::rule::unify_ln_fact_eqs(
        maude,
        &[Equal {
            lhs: conc,
            rhs: kd_prem1,
        }],
    )
    .unwrap_or_default();
    if unifs.is_empty() {
        return None;
    }
    // The fresh supply `applySubsts` threads across the unifier list,
    // avoiding both rules.
    let mut counter: u64 = 0;
    let mut track = |v: &LVar| counter = counter.max(v.idx + 1);
    r.for_each_free(&mut track);
    fresh_inst1.for_each_free(&mut track);
    Some(ChainablePair {
        r,
        fresh_inst1,
        unifs,
        counter,
    })
}

/// Deduction phase of HS `ndcCheck` (`checkDeduction`): every unifier-
/// instantiated pair must pass `chainedRulesDeductionTest`; the `&&`
/// chain short-circuits on the first failure, so the unifiers past it are
/// never instantiated.
fn ndc_check_eval(
    maude: &MaudeHandle,
    intr_modified: &BoundToOneCache<'_>,
    pair: ChainablePair<'_>,
) -> bool {
    let ChainablePair {
        r,
        fresh_inst1,
        unifs,
        mut counter,
    } = pair;
    unifs.into_iter().all(|u_pairs| {
        // `applySubsts subst r freshInst1` — freshToFree this unifier off
        // the pair's supply, which the whole list shares in order.
        let s_fresh = LNSubstVFresh::from_list(u_pairs);
        let sigma = s_fresh.fresh_to_free_avoiding(|n| {
            let b = counter;
            counter += n;
            b
        });
        chained_rules_deduction_test(
            maude,
            intr_modified,
            &apply_subst_rule(&sigma, r),
            &apply_subst_rule(&sigma, &fresh_inst1),
        )
    })
}

// =============================================================================
// applyNDCcheck / prettyNDCcheck
// =============================================================================

/// HS `applyNDCcheck` over the checked groups: for each group, the head
/// function has the NDC property iff at least one ordered rule pair
/// chains AND every chainable pair reduces.  Tagged groups get their
/// rules' head fun NDC-joined; returns the tagged functions plus the
/// concatenated (possibly tagged) groups in group order.
fn apply_ndc_check(
    maude: &MaudeHandle,
    intr_r: &[IntrRuleAC],
    groups: Vec<Vec<IntrRuleAC>>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> (Vec<FunSym>, Vec<IntrRuleAC>) {
    let mut tagged: Vec<FunSym> = Vec::new();
    let mut out: Vec<IntrRuleAC> = Vec::new();
    for group in groups {
        let f = get_destr_rule_function(
            group
                .first()
                .expect("applyNDCcheck: groups are non-empty by construction"),
        )
        .expect("applyNDCcheck: checked groups are destructor groups");
        // `boundToOne` maps the cache against this group's head function, so
        // one mapping serves every pair below.
        let intr_modified = BoundToOneCache::new(intr_r, Some(f), parameters);
        // `checkChainReductionIter [(x,y) | x <- t1, y <- t1]` is a
        // `foldr` whose lazy `&&` chain runs the cheap per-pair
        // unifications in FORWARD pair order but forces the expensive
        // per-pair deduction tests in REVERSE order — `resSoFar &&
        // result` demands the fold over the LATER pairs before this
        // pair's own result — short-circuiting the remaining (earlier)
        // pairs once one fails.  Verdict `== (True, False)`: at least
        // one pair chains AND every forced deduction test passed.
        let chainable: Vec<ChainablePair<'_>> = group
            .iter()
            .flat_map(|x| group.iter().map(move |y| (x, y)))
            .filter_map(|(x, y)| ndc_check_prepare(maude, x, y))
            .collect();
        let is_ndc = !chainable.is_empty()
            && chainable
                .into_iter()
                .rev()
                .all(|pair| ndc_check_eval(maude, &intr_modified, pair));
        let fun_name = crate::intruder_rules::show_fun_sym_name(&f);
        if is_ndc {
            eprintln!("Function {} has the NDC property.", fun_name);
            tagged.push(f);
            for mut r in group {
                if let IntrRuleACInfo::DestrRule { funs, .. } = &mut r.info
                    && let Some(h) = funs.first_mut()
                {
                    *h = h.add_ndc(NdcState::IsNdc);
                }
                out.push(r);
            }
        } else {
            eprintln!("Function {} does not have the NDC property.", fun_name);
            out.extend(group);
        }
    }
    (tagged, out)
}

/// HS `prettyNDCcheck` (trace mode): run the NDC property check over the
/// assembled intruder-rule cache.  Emits the two `[Theory NAME] No
/// Deconstruction Chain checks started/ended` stderr markers
/// unconditionally (HS `traceM`s them even when no group is checkable);
/// `theory_name = None` suppresses them.
/// Returns the NDC-tagged function symbols (for the signature join /
/// `functions:` header) and the final cache
/// `checked ++ builtInOrConstrOrNDC ++ all-subterm`.
pub fn pretty_ndc_check(
    maude: &MaudeHandle,
    theory_name: Option<&str>,
    init_rules: Vec<IntrRuleAC>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> (Vec<FunSym>, Vec<IntrRuleAC>) {
    let (builtin_or_constr_or_ndc, checked_groups, all_subterm) =
        partition_for_ndc(init_rules.clone());
    let marker = |suffix: &str| {
        if let Some(name) = theory_name {
            eprintln!(
                "[Theory {}] No Deconstruction Chain checks {}",
                name, suffix
            );
        }
    };
    marker("started");
    // The deduction checks advance the shared Maude fresh counter; the
    // check is observationally pure (its verdicts alone are kept), so
    // restore the counter — mirroring the `ensure_saturated` purity
    // bracket.
    let cnt_before = maude.fresh_counter_peek();
    let (tagged, checked_rules) = apply_ndc_check(maude, &init_rules, checked_groups, parameters);
    maude.reset_counter_to(cnt_before);
    marker("ended");
    (
        tagged,
        ndc_cache_order(checked_rules, builtin_or_constr_or_ndc, all_subterm),
    )
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "close_rule_tests.rs"]
mod tests;
