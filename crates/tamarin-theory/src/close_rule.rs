// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, kevinmorio, rkunnema, arcz, PhilipLukertWork,
//   yavivanov, Hong-Thai, beschmi, racoucho1u, rsasse, Azurios-git,
//   Nynko, ValentinYuri, felixlinker, charlie-j, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/CloseRule.hs, src/Main/TheoryLoader.hs

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
//! The synthetic deduction theories are rendered to `.spthy` TEXT via the
//! parity-grade pretty-printers, re-parsed, and proved with an INJECTED
//! intruder cache (`bound_to_one` of the parent's pre-check cache) —
//! mirroring HS's `closeTheoryWithMaude sig t` with
//! `thyCache = intrRmodified`.

use tamarin_term::function_symbols::{FunSym, NdcState, Privacy};
use tamarin_term::lterm::{HasFrees, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::rewriting::Equal;
use tamarin_term::subst::apply_vterm;
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::constraint::solver::context::IntrRuleCache;
use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
use crate::rule::{
    get_conc_fact, get_deconstr_rule_kd_prem, get_deconstr_rule_prems_tail,
    get_destr_rule_function, IntrRuleAC, IntrRuleACInfo,
};
use tamarin_term::lterm::LNTerm;

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
/// checks started/ended` markers; `None` suppresses them (the `--quiet`
/// batch path, matching the other `[Theory X]` progress markers).
pub fn check_close_intr_rule(
    maude: &MaudeHandle,
    theory_name: Option<&str>,
    deduction_chain_check: bool,
) -> NdcCheckedCache {
    let assembled = crate::constraint::solver::context::ProofContext::assemble_intruder_rules(
        &maude.maude_sig(),
        maude,
    );
    if !deduction_chain_check {
        return NdcCheckedCache {
            cache: assembled,
            ndc_funs: Vec::new(),
        };
    }
    let (ndc_funs, cache) = pretty_ndc_check(maude, theory_name, assembled);
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
    if f.tag == FactTag::Ku && f.terms.len() == 1 {
        if let Term::App(head, args) = &f.terms[0] {
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
                    .map(|a| {
                        Fact::fresh_annotated(FactTag::Ku, f.annotations.clone(), vec![a.clone()])
                    })
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

fn pretty_term(t: &LNTerm) -> String {
    tamarin_term::pretty::pretty_lnterm(t)
}

fn pretty_var(v: &LVar) -> String {
    pretty_term(&tamarin_term::vterm::var_term(*v))
}

/// Render the synthetic deduction theory for one decomposition `s`
/// (HS `modifiedTheory1/2`): the parent signature `sig_text`, the `Out0`
/// source rule, the `OnlyOnce` (and optionally `OnlyOnceD`) restrictions,
/// and the `Deduction` lemma.  Rendered as `.spthy` text via the
/// parity-grade printers and re-parsed — this reuses the battle-tested
/// print/parse pipeline instead of hand-unparsing terms.
fn render_deduction_theory(
    sig_text: &str,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
) -> String {
    // Alpha-rename every variable of `s` and `fact_term` to a simple
    // idx-0 name (`ndcvN`).  Verdict-invariant, and keeps the rendered
    // theory parseable (unifier-instantiated rules carry dotted indices)
    // while sidestepping the name-keyed binder resolution in
    // `formula_to_guarded` for same-named vars of different sorts.
    let mut all_vars: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    for f in s {
        f.for_each_free(&mut |v| {
            all_vars.insert(*v);
        });
    }
    fact_term.for_each_free(&mut |v| {
        all_vars.insert(*v);
    });
    let rename: Vec<(LVar, LNTerm)> = all_vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            (
                *v,
                tamarin_term::vterm::var_term(LVar::new(format!("ndcv{}", i), v.sort, 0)),
            )
        })
        .collect();
    let sigma = tamarin_term::subst::Subst::from_list(rename);
    let ren_fact = |f: &LNFact| -> LNFact {
        let terms: Vec<LNTerm> = f
            .terms
            .iter()
            .map(|t| apply_vterm(&sigma, t.clone()))
            .collect();
        Fact::fresh_annotated(f.tag, f.annotations.clone(), terms)
    };
    let s: Vec<LNFact> = s.iter().map(ren_fact).collect();
    let fact_term = apply_vterm(&sigma, fact_term.clone());

    // varD s (HS: `frees $ concatMap factTerms s` — `sortednub . freesList`;
    // the ordering fixes the `Generated_0` argument order, used consistently
    // on the rule and lemma sides).
    let var_d: Vec<LVar> = tamarin_term::lterm::frees(&s);

    // Rule premises: `freesToFresh . varFresh` — Fr(lvarToLnterm
    // (msgToFreshVars v)).
    let prems: Vec<LNFact> = var_d
        .iter()
        .map(|v| crate::fact::fresh_fact(crate::fact::lvar_to_lnterm(&msg_to_fresh_var(v))))
        .collect();
    // Conclusions: `map (outFact . msgToFreshTerms) (concatMap factTerms s)`.
    let concs: Vec<LNFact> = s
        .iter()
        .flat_map(|f| f.terms.iter())
        .map(|t| crate::fact::out_fact(msg_to_fresh_terms(t)))
        .collect();
    // Actions: Generated_0 over the retyped vars, plus OnlyOnce.
    let gen_args_rule: Vec<LNTerm> = var_d
        .iter()
        .map(|v| msg_to_fresh_terms(&crate::fact::lvar_to_lnterm(v)))
        .collect();
    let act_gen = crate::fact::proto_fact(Multiplicity::Linear, "Generated_0", gen_args_rule);
    let act_oo = crate::fact::proto_fact(Multiplicity::Linear, "OnlyOnce", vec![]);

    // Lemma-side Generated_0 args: `map lvarToLnterm (varD s)` — NO
    // msg→fresh retype.  A nat→fresh retype changes the variable's sort
    // relative to any occurrence inside the K term; give the retyped var
    // a distinct name so the two remain independent binders under the
    // name-keyed guarded conversion (HS distinguishes them by sort-aware
    // LVar identity).
    let gen_args_lemma: Vec<LNTerm> = var_d
        .iter()
        .map(|v| {
            let vt = crate::fact::lvar_to_lnterm(v);
            match &vt {
                Term::Lit(tamarin_term::vterm::Lit::Var(nv)) if nv.sort != v.sort => {
                    tamarin_term::vterm::var_term(LVar::new(
                        format!("{}f", nv.name),
                        nv.sort,
                        nv.idx,
                    ))
                }
                _ => vt,
            }
        })
        .collect();

    let pf = crate::pretty_system::pretty_fact;
    let mut out = String::new();
    out.push_str("theory checkDeduction\nbegin\n\n");
    out.push_str(sig_text);
    out.push('\n');
    out.push_str(&format!(
        "rule Out0:\n  [ {} ]\n  --[ {}, {} ]->\n  [ {} ]\n\n",
        prems.iter().map(pf).collect::<Vec<_>>().join(", "),
        pf(&act_gen),
        pf(&act_oo),
        concs.iter().map(pf).collect::<Vec<_>>().join(", "),
    ));
    out.push_str(
        "restriction OnlyOnce:\n  \"All #ndci #ndcj. OnlyOnce() @ #ndci & OnlyOnce() @ #ndcj ==> #ndci = #ndcj\"\n\n",
    );
    if with_only_once_d {
        out.push_str(
            "restriction OnlyOnceD:\n  \"All #ndci #ndcj #ndck. OnlyOnceD() @ #ndci & OnlyOnceD() @ #ndcj & OnlyOnceD() @ #ndck ==> #ndci = #ndcj | #ndci = #ndck | #ndcj = #ndck\"\n\n",
        );
    }
    // Lemma: Not(Ex vars #t0 #t1. Generated_0(..) @ #t0 & K(t) @ #t1).
    let mut binder_vars: Vec<String> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for t in gen_args_lemma.iter().chain(std::iter::once(&fact_term)) {
        t.for_each_free(&mut |v: &LVar| {
            let r = pretty_var(v);
            if seen.insert(r.clone()) {
                binder_vars.push(r);
            }
        });
    }
    let gen_args_str: Vec<String> = gen_args_lemma.iter().map(pretty_term).collect();
    // Data-var binder prefix: each var followed by exactly one space, so
    // the quantifier list reads `Ex v0 v1 #ndct0 #ndct1.` (and just
    // `Ex #ndct0 #ndct1.` with zero data vars).
    let binder_prefix = if binder_vars.is_empty() {
        String::new()
    } else {
        format!("{} ", binder_vars.join(" "))
    };
    out.push_str(&format!(
        "lemma Deduction:\n  all-traces\n  \"not(Ex {}#ndct0 #ndct1. Generated_0({}) @ #ndct0 & K({}) @ #ndct1)\"\n\nend\n",
        binder_prefix,
        gen_args_str.join(", "),
        pretty_term(&fact_term),
    ));
    out
}

/// Head and tail of a rendered deduction theory, for panic context: the
/// header/signature and the `Out0` rule plus `Deduction` lemma, without
/// dumping a signature of arbitrary size.
fn theory_snippet(src: &str) -> String {
    const HEAD: usize = 300;
    const TAIL: usize = 300;
    let n = src.chars().count();
    if n <= HEAD + TAIL {
        return src.to_string();
    }
    let head: String = src.chars().take(HEAD).collect();
    let tail: String = src.chars().skip(n - TAIL).collect();
    format!("{}\n...\n{}", head, tail)
}

/// Close and auto-prove one synthetic deduction theory; `true` iff the
/// `Deduction` lemma's proof status folds to `TraceFound` (an attack on
/// the all-traces lemma = the fact IS derivable without chaining).
///
/// The theory is generated by [`render_deduction_theory`], so a parse,
/// elaboration, guarded-conversion or lemma-lookup failure is an
/// internal-consistency violation rather than a user error: each aborts —
/// HS builds the same theory structurally, where such a failure aborts the
/// load — instead of answering "not derivable".  Solver panics propagate for
/// the same reason (and because a panic raised while the shared Maude mutex
/// guard is held leaves the handle poisoned).  `false` therefore means
/// exactly one thing: the proof search completed without finding a trace.
///
/// `run_proof_search` re-reads the opt-in `TAM_PROVE_DEADLINE_MS` wall-clock
/// cap for every search it runs (search.rs `proof_deadline`), this one
/// included; a deduction search that exhausts the cap returns a proof
/// without `TraceFound` and so answers `false`.  Unset (the default) the
/// search is unbounded, which is the HS-faithful configuration.
fn prove_deduction_theory(
    maude: &MaudeHandle,
    intr_modified: &IntrRuleCache,
    sig_text: &str,
    s: &[LNFact],
    fact_term: &LNTerm,
    with_only_once_d: bool,
) -> bool {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::search::{proof_status, run_proof_search, ProofStatus};
    use crate::constraint::system::{formula_to_system, SourceKind};

    let src = render_deduction_theory(sig_text, s, fact_term, with_only_once_d);
    let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory failed to parse ({}); theory:\n{}",
            e,
            theory_snippet(&src)
        )
    });
    let _user_funs_guard = crate::elaborate::set_user_funs_for_theory(&parsed);
    let elaborated = crate::elaborate::elaborate(&parsed).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory failed to elaborate ({}); theory:\n{}",
            e.message,
            theory_snippet(&src)
        )
    });
    let rules: Vec<crate::theory::OpenProtoRule> = elaborated.rules().cloned().collect();
    let mut restrictions: Vec<crate::guarded::Guarded> = Vec::new();
    for r in elaborated.restrictions() {
        let g = crate::guarded::formula_to_guarded(&r.formula).unwrap_or_else(|e| {
            panic!(
                "[ndc] synthetic deduction theory restriction {} is not guarded ({}); theory:\n{}",
                r.name,
                e.message,
                theory_snippet(&src)
            )
        });
        restrictions.push(g);
    }
    let ctx = ProofContext::new_with_injected_intruder_rules(
        maude.clone(),
        rules,
        restrictions.clone(),
        intr_modified.clone(),
    );
    ctx.ensure_saturated();
    let lemma = elaborated.lookup_lemma("Deduction").unwrap_or_else(|| {
        panic!(
            "[ndc] synthetic deduction theory has no Deduction lemma; theory:\n{}",
            theory_snippet(&src)
        )
    });
    let g = crate::guarded::formula_to_guarded(&lemma.formula).unwrap_or_else(|e| {
        panic!(
            "[ndc] synthetic deduction theory Deduction lemma is not guarded ({}); theory:\n{}",
            e.message,
            theory_snippet(&src)
        )
    });
    let sys = formula_to_system(
        restrictions,
        SourceKind::RefinedSources,
        tamarin_parser::ast::TraceQuantifier::AllTraces,
        false,
        &g,
    );
    let root = run_proof_search(&ctx, sys, usize::MAX);
    proof_status(&root) == ProofStatus::TraceFound
}

/// HS `deductionCheck`: can `fact` be derived from `facts` without
/// chaining?  `intr_modified` is the `boundToOne`-mapped cache,
/// `sig_text` the rendered parent signature every decomposition's theory
/// carries.
fn deduction_check(
    maude: &MaudeHandle,
    intr_modified: &IntrRuleCache,
    sig_text: &str,
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
        set_d
            .iter()
            .all(|s| prove_deduction_theory(maude, intr_modified, sig_text, s, fact_term, with_ood))
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
    if let IntrRuleACInfo::DestrRule(name, i, _, _, funs) = &mut out.info {
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
            if !is_built_in && *i == 0 {
                *i = 1;
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
}

impl<'a> BoundToOneCache<'a> {
    fn new(intr_r: &'a [IntrRuleAC], checked_fun: Option<FunSym>) -> Self {
        Self {
            intr_r,
            checked_fun,
            modified: std::cell::OnceCell::new(),
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

/// Apply a free substitution to every fact (and new-var term) of a rule.
fn apply_subst_rule(
    sigma: &tamarin_term::subst::Subst<tamarin_term::lterm::Name, LVar>,
    r: &IntrRuleAC,
) -> IntrRuleAC {
    let app_facts = |fs: &[LNFact]| -> Vec<LNFact> {
        fs.iter()
            .map(|f| {
                let terms: Vec<LNTerm> = f
                    .terms
                    .iter()
                    .map(|t| apply_vterm(sigma, t.clone()))
                    .collect();
                Fact::fresh_annotated(f.tag, f.annotations.clone(), terms)
            })
            .collect()
    };
    IntrRuleAC {
        info: r.info.clone(),
        premises: app_facts(&r.premises),
        conclusions: app_facts(&r.conclusions),
        actions: app_facts(&r.actions),
        new_vars: r
            .new_vars
            .iter()
            .map(|t| apply_vterm(sigma, t.clone()))
            .collect(),
    }
}

/// HS `chainedRulesDeductionTest`: after chaining `inst_sigma` into
/// `inst1_sigma`, is the chained conclusion derivable from the combined
/// premises without chaining?  `sig_cell` holds the parent signature text
/// shared by every synthetic theory of the pass (see [`apply_ndc_check`]).
fn chained_rules_deduction_test(
    maude: &MaudeHandle,
    intr_modified: &BoundToOneCache<'_>,
    sig_cell: &std::cell::OnceCell<String>,
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
    let sig_text =
        sig_cell.get_or_init(|| crate::pretty_theory::render_signature(&maude.maude_sig()));
    deduction_check(
        maude,
        intr_modified.modified(),
        sig_text,
        fact_to_deduce,
        &facts,
    )
}

/// Shape guard of HS `ndcCheck`'s first clause: a deconstruction rule with
/// a leading KD premise, a single KD conclusion, and budget ≠ 1.
fn ndc_checkable(r: &IntrRuleAC) -> bool {
    let budget_ok = matches!(&r.info, IntrRuleACInfo::DestrRule(_, i, _, _, _) if *i != 1);
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
    sig_cell: &std::cell::OnceCell<String>,
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
            sig_cell,
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
) -> (Vec<FunSym>, Vec<IntrRuleAC>) {
    let mut tagged: Vec<FunSym> = Vec::new();
    let mut out: Vec<IntrRuleAC> = Vec::new();
    // Every synthetic deduction theory of this pass opens with the same
    // parent signature — `maude`'s `Arc<MaudeSig>` is fixed at handle
    // construction and the printer is a pure function of it — so the text is
    // rendered once, on the first pair that reaches a deduction check.
    let sig_cell: std::cell::OnceCell<String> = std::cell::OnceCell::new();
    for group in groups {
        let f = get_destr_rule_function(
            group
                .first()
                .expect("applyNDCcheck: groups are non-empty by construction"),
        )
        .expect("applyNDCcheck: checked groups are destructor groups");
        // `boundToOne` maps the cache against this group's head function, so
        // one mapping serves every pair below.
        let intr_modified = BoundToOneCache::new(intr_r, Some(f));
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
                .all(|pair| ndc_check_eval(maude, &intr_modified, &sig_cell, pair));
        let fun_name = crate::intruder_rules::show_fun_sym_name(&f);
        if is_ndc {
            eprintln!("Function {} has the NDC property.", fun_name);
            tagged.push(f);
            for mut r in group {
                if let IntrRuleACInfo::DestrRule(_, _, _, _, funs) = &mut r.info {
                    if let Some(h) = funs.first_mut() {
                        *h = h.add_ndc(NdcState::IsNdc);
                    }
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
/// `theory_name = None` suppresses them (the `--quiet` batch path).
/// Returns the NDC-tagged function symbols (for the signature join /
/// `functions:` header) and the final cache
/// `checked ++ builtInOrConstrOrNDC ++ all-subterm`.
pub fn pretty_ndc_check(
    maude: &MaudeHandle,
    theory_name: Option<&str>,
    init_rules: Vec<IntrRuleAC>,
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
    let (tagged, checked_rules) = apply_ndc_check(maude, &init_rules, checked_groups);
    maude.reset_counter_to(cnt_before);
    marker("ended");
    let mut out = checked_rules;
    out.extend(builtin_or_constr_or_ndc);
    out.extend(all_subterm);
    (tagged, out)
}
