// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Dynamic message-derivation check.
//!
//! Mirrors HS's `Theory.Tools.MessageDerivationChecks.checkVariableDeducibility`
//! (lib/theory/src/Theory/Tools/MessageDerivationChecks.hs:36-50).  For each
//! protocol rule, asks the prover: "given that the intruder has access to all
//! of this rule's premise terms, can it derive each of the rule's free
//! variables?"  When a variable IS bound by some premise fact but cannot
//! actually be derived by the intruder (because the fact's containing rule
//! is unreachable / requires private knowledge), HS flags it as an
//! "unintended pattern match".
//!
//! How HS does it (see `MessageDerivationChecks.hs:36-50,170-188`):
//!
//!   For each rule R indexed by idx:
//!     1. Drop ALL rules/lemmas/restrictions from the theory, carrying over
//!        the signature items (builtins/functions/equations/macros) VERBATIM
//!        — privacy flags included.  HS's `makeFunsPublic` and `replacePrivate`
//!        both look like they make symbols public but neither changes the
//!        verdict: `makeFunsPublic` only sets the OPEN theory's pure signature,
//!        which `closeTheoryWithMaude sig` overwrites with the ORIGINAL private-
//!        preserving maude signature (so intruder-rule generation stays private);
//!        and `replacePrivate` rewrites Out-term heads to a same-name Public
//!        variant that gets no construction/destruction rule, leaving the term
//!        opaque exactly as the private application would be.  See
//!        `synthesise_probe_theory` for the full citation.
//!     2. Add a single generated rule (HS names it `StandRule (show idx)`):
//!          rule <idx>:
//!            [ Fr(v1), Fr(v2), ... ]                     // each free var of R,
//!                                                        // keeping its own sort
//!                                                        // (only nat → fresh)
//!            --[ Generated_<idx>(v1, v2, ...) ]->        // sole action
//!            [ Out(t1), Out(t2), ... ]                   // R's premise terms
//!     3. Add one exists-trace lemma per free var v.  HS's `landFormula`
//!        gives each conjunct its OWN timepoint via `zip [0..]`, and the
//!        intruder-knowledge predicate is `KU` (`lntermToKUFact = kuFact`):
//!          lemma deriv_v: exists-trace
//!            "Ex v1 v2 ... #t0 #t1. Generated_<idx>(v1, v2, ...) @ #t0 & KU(v) @ #t1"
//!     4. Run the prover on each lemma with `--derivcheck-timeout`.
//!     5. Lemmas whose proof did NOT find a trace identify non-derivable
//!        variables — report them.
//!
//! Note: `prove_probe` builds the `ProofContext` + runs `ensure_saturated()`
//! ONCE per probe and then iterates the per-variable lemmas reusing that
//! shared, already-saturated context, so a rule with N free vars incurs N
//! proof attempts but only one context build.  Each attempt is bounded by
//! the user's timeout (default 5s, mirrored on the HS side).  The check is
//! gated by `args.derivcheck_timeout`; passing `0` disables it entirely (HS:
//! `Main.TheoryLoader.hs`).

use std::time::Duration;
use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::lterm::LSort;
use tamarin_term::maude_proc::MaudeHandle;

use crate::constraint::solver::context::IntrRuleCache;

/// Run HS's per-variable derivability check on every rule.
///
/// `timeout_secs == 0` disables the check (returns `vec![]`).  Otherwise
/// each per-variable prove call is bounded by `timeout_secs` of wall-clock
/// time (mirrors HS's `--derivcheck-timeout`).
///
/// `ndc_cache` is the parent theory's once-per-load NDC-checked intruder
/// cache: HS's probe theories inherit the parent's checked `_thyCache`
/// verbatim (`deleteRulesAndLemmasAndRestrictionsFromTheory` keeps the
/// cache field; `deductionChainCheck = False` only prevents re-checking,
/// MessageDerivationChecks.hs), so the probe contexts are built with it
/// injected — NDC tags stay active in `forbidden_edge` during probe
/// proofs.  `None` falls back to signature assembly with the cache
/// permutation applied.  A `Some` argument is one shared handle for the
/// whole per-rule walk below: each probe context points at that rule list
/// instead of copying it.
pub fn check_message_derivation(
    parsed: &p::Theory,
    maude: &MaudeHandle,
    timeout_secs: u32,
    ndc_cache: Option<IntrRuleCache>,
) -> Vec<WfError> {
    if timeout_secs == 0 {
        return Vec::new();
    }
    let timeout = Duration::from_secs(timeout_secs as u64);
    let dbg = tamarin_utils::env_gate!("TAM_DBG_DERIV_CHECK");
    // TAM_DBG_DERIV_TIMING=1: emit per-rule / per-variable wall-clock
    // timings on stderr.  Off-path when env var is absent.
    let dbg_timing = tamarin_utils::env_gate!("TAM_DBG_DERIV_TIMING");
    let t_total_start = std::time::Instant::now();

    // Theory-level `macros:` declarations.  HS expands these into every
    // protocol rule via `applyMacroInProtoRule (theoryMacros thy)`
    // (MessageDerivationChecks.hs:36-50, see line 40) BEFORE collecting free vars / building
    // the probe.  The caller hands us the RAW parsed theory (theory macros
    // un-expanded), so we must expand them here ourselves; otherwise a rule
    // whose body uses a macro that introduces fresh vars (e.g.
    // `macros: test() = ~x`) mis-collects vars and the rule is silently
    // skipped.
    let theory_macros: Vec<p::Macro> = parsed
        .items
        .iter()
        .flat_map(|i| match i {
            p::TheoryItem::Macros(ms) => ms.clone(),
            _ => Vec::new(),
        })
        .collect();

    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    let mut rule_count = 0usize;
    let mut var_count = 0usize;
    let mut total_synth = Duration::ZERO;
    let mut total_prove = Duration::ZERO;
    for (idx, raw_rule) in protocol_rules(parsed).enumerate() {
        if raw_rule
            .attributes
            .iter()
            .any(|a| matches!(a, p::RuleAttr::NoDerivCheck))
        {
            continue;
        }
        // HS applies theory macros before the deriv check
        // (MessageDerivationChecks.hs:36-50, see line 40 -- `originalRules = map
        // (applyMacroInProtoRule (theoryMacros thy)) $ theoryRules thy`).
        // Mirror that here: first expand theory-level `macros:` into the
        // rule's premise/action/conclusion facts (the only parts the deriv
        // check inspects), THEN substitute the rule-local `let { }` block.
        // Theory macros are a DISTINCT AST node (`TheoryItem::Macros`) from
        // the rule-local let-block (`Rule.let_block`); both must be resolved
        // so we walk the same shape HS does.  Without macro expansion, a rule
        // whose body uses a fresh-introducing macro is silently skipped; and
        // without let-block substitution, RS flags every let-bound name
        // (`pkB`, `mtr`, `ci2`, ...) as non-derivable.
        let macro_expanded;
        let macro_src = if theory_macros.is_empty() {
            raw_rule
        } else {
            macro_expanded = apply_theory_macros_to_rule(raw_rule, &theory_macros);
            &macro_expanded
        };
        let expanded = crate::elaborate::apply_let_block(macro_src);
        let rule = &expanded;
        let free_vars = collect_rule_free_vars(rule);
        if free_vars.is_empty() {
            continue;
        }
        rule_count += 1;

        // Build the probe theory ONCE per rule (it contains all the
        // per-variable lemmas).  The synthesised theory is small —
        // one rule, N lemmas, the original signature.
        let t_synth = std::time::Instant::now();
        let probe = synthesise_probe_theory(parsed, rule, idx, &free_vars);
        let synth_dt = t_synth.elapsed();
        total_synth += synth_dt;
        if dbg {
            eprintln!(
                "[deriv] rule={} free_vars={:?}",
                rule.name,
                free_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
            );
            eprintln!("[deriv] probe theory items:");
            for it in &probe.items {
                match it {
                    p::TheoryItem::Rule(r) => eprintln!(
                        "  rule {}: prem={} act={} conc={}",
                        r.name,
                        r.premises.len(),
                        r.actions.len(),
                        r.conclusions.len()
                    ),
                    p::TheoryItem::Lemma(l) => {
                        eprintln!("  lemma {} ({:?})", l.name, l.trace_quantifier)
                    }
                    _ => {}
                }
            }
        }

        // Try each variable's lemma.  HS's "TraceFound" status maps
        // to RS's `NodeStatus::Solved` for exists-trace lemmas.
        //
        // HS-faithful structure: `closeTheoryWithMaude` is called ONCE
        // per probe theory (HS `MessageDerivationChecks.hs:41-43`
        // calls `closeTheoryWithMaude` once per modified theory; then
        // `proveTheory` walks the N lemmas reusing the closed theory's
        // sources/cache — `CloseRule.hs:144-155`).  `prove_probe` mirrors
        // this: build the `ProofContext` + run `ensure_saturated()` ONCE
        // per probe, then iterate the per-variable lemmas reusing it.
        let outcome = match prove_probe(
            &probe,
            maude.clone(),
            idx,
            &free_vars,
            timeout,
            dbg_timing,
            &rule.name,
            ndc_cache.as_ref(),
        ) {
            Some(o) => o,
            None => continue,
        };
        // Fold the probe's debug-only timing/count into the running totals.
        total_prove += outcome.prove_time;
        var_count += outcome.var_count;
        if dbg_timing {
            eprintln!(
                "[deriv-timing] rule={} synth={:.3}s nvars={} prove={:.3}s",
                rule.name,
                synth_dt.as_secs_f64(),
                free_vars.len(),
                outcome.prove_time.as_secs_f64(),
            );
        }
        let undecidable = outcome.undecidable;
        if !undecidable.is_empty() {
            per_rule.push((rule.name.clone(), undecidable));
        }
    }
    if dbg_timing {
        eprintln!(
            "[deriv-timing] TOTAL rules={} vars={} synth={:.3}s prove={:.3}s wall={:.3}s",
            rule_count,
            var_count,
            total_synth.as_secs_f64(),
            total_prove.as_secs_f64(),
            t_total_start.elapsed().as_secs_f64(),
        );
    }
    format_deriv_report(&per_rule)
}

/// Expand theory-level `macros:` into a rule's premise / action / conclusion
/// facts and its `let { }` block — the parts the deriv check inspects.  Mirror
/// of HS `applyMacroInProtoRule (theoryMacros thy)`
/// (MessageDerivationChecks.hs:36-50, see line 40).
fn apply_theory_macros_to_rule(rule: &p::Rule, macros: &[p::Macro]) -> p::Rule {
    let mut r = rule.clone();
    for f in &mut r.premises {
        *f = crate::macro_expand::apply_macros_fact(macros, f);
    }
    for f in &mut r.actions {
        *f = crate::macro_expand::apply_macros_fact(macros, f);
    }
    for f in &mut r.conclusions {
        *f = crate::macro_expand::apply_macros_fact(macros, f);
    }
    for b in &mut r.let_block {
        b.value = crate::macro_expand::apply_macros_term(macros, &b.value);
        b.var = crate::macro_expand::apply_macros_term(macros, &b.var);
    }
    r
}

/// Iterate over Rule items in declaration order.  Skips IntrRule
/// declarations (intruder rules), Restrictions, Lemmas.
fn protocol_rules(thy: &p::Theory) -> impl Iterator<Item = &p::Rule> {
    thy.items.iter().filter_map(|it| match it {
        p::TheoryItem::Rule(r) => Some(r),
        _ => None,
    })
}

/// All variables that appear anywhere in a rule's premise / action /
/// conclusion terms, deduped and returned sorted by HS `LVar` Ord
/// (idx, then sort, then name) — matching HS `frees`/`S.toList`, which
/// yields elements in ascending LVar Ord.  (Internally the dedup pass
/// collects in first-occurrence order, but the result is re-sorted before
/// return.)  EXCLUDING:
///   - `Pub`-sort vars (`$x`) — RS drops these up-front as a sound
///     optimization.  HS keeps them in `freeVars` (its `freesInThyRules`,
///     MessageDerivationChecks.hs:157-161, filters out only `LSortNode`,
///     not `LSortPub`) and generates a `KU($x)` lemma for each; but the
///     intruder knows every public name, so those lemmas are ALWAYS
///     TraceFound and the pub var is never reported.  (`deleteGlobals`,
///     MessageDerivationChecks.hs:179-180, does drop Pub vars, but only
///     inside the generated rule/action, not from the reported var list.)
///   - `Node`-sort vars (`#i`) — timepoints, not message vars.  HS's
///     `freesInThyRules` filters these out (the only sort it drops).
///   - Suffix-sorted vars whose underlying sort is Pub or Node, for the
///     same reason.
fn collect_rule_free_vars(r: &p::Rule) -> Vec<p::VarSpec> {
    let mut out: Vec<p::VarSpec> = Vec::new();
    // HS `frees` keys on the full LVar (name AND sort AND idx), so `~ltk`
    // (fresh) and `ltk` (msg) are DISTINCT free vars — both become
    // derivability candidates.  Key the dedup set on (name, sort, idx) too;
    // a (name, idx)-only key would let `~ltk` mask `ltk` and silently drop
    // the non-derivable msg var (Register_pk `ltk`).
    let mut seen: std::collections::BTreeSet<(String, LSort, u64)> =
        std::collections::BTreeSet::new();
    let push = |v: &p::VarSpec,
                out: &mut Vec<p::VarSpec>,
                seen: &mut std::collections::BTreeSet<(String, LSort, u64)>| {
        if matches!(v.sort, LSort::Pub | LSort::Node) {
            return;
        }
        let key = (v.name.clone(), v.sort, v.idx);
        if seen.insert(key) {
            out.push(v.clone());
        }
    };
    let visit_term = |t: &p::Term, out: &mut Vec<p::VarSpec>, seen: &mut _| {
        let mut vs = Vec::new();
        collect_term_vars(t, &mut vs);
        for v in vs {
            push(&v, out, seen);
        }
    };
    for f in &r.premises {
        for a in &f.args {
            visit_term(a, &mut out, &mut seen);
        }
    }
    for f in &r.actions {
        for a in &f.args {
            visit_term(a, &mut out, &mut seen);
        }
    }
    for f in &r.conclusions {
        for a in &f.args {
            visit_term(a, &mut out, &mut seen);
        }
    }
    // HS-faithful: sort by (idx, sort, name) to match HS's `LVar Ord`
    // (LTerm.hs:545-548: `compare x3 y3 <> compare x2 y2 <> compare x1 y1`
    //  where x3=idx, x2=sort, x1=name).  HS uses `frees . L.get oprRuleE` →
    // `S.toList` which returns elements in ascending LVar Ord.
    out.sort_by(|a, b| {
        a.idx
            .cmp(&b.idx)
            .then_with(|| a.sort.cmp(&b.sort))
            .then_with(|| a.name.cmp(&b.name))
    });
    out
}

/// HS `lvarToLnterm`: retype an LSortNat var to LSortFresh; otherwise keep
/// the var's sort unchanged (Theory/Model/Fact.hs:331-333).
fn nat_to_fresh_var(v: &p::VarSpec) -> p::VarSpec {
    let mut nv = v.clone();
    if v.sort == LSort::Nat {
        nv.sort = LSort::Fresh;
    }
    nv
}

/// Rename a premise term's variables for the probe: a free var (matched by
/// (name, sort, idx)) becomes its `dvar<k>` probe var; any other var is
/// retyped nat→fresh (HS `natToFreshVars`).  Keeps `Out(...)` referencing the
/// same probe vars as the `Fr(...)` premises.
// (name,sort,idx)->probe-var rename map; keyed lookup only;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn rename_term_to_probe(
    t: &p::Term,
    map: &std::collections::HashMap<(String, LSort, u64), p::VarSpec>,
) -> p::Term {
    match t {
        p::Term::Var(v) => {
            let key = (v.name.clone(), v.sort, v.idx);
            match map.get(&key) {
                Some(pv) => p::Term::Var(pv.clone()),
                None => p::Term::Var(nat_to_fresh_var(v)),
            }
        }
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| rename_term_to_probe(a, map)).collect(),
        ),
        p::Term::Pair(args) => {
            p::Term::Pair(args.iter().map(|a| rename_term_to_probe(a, map)).collect())
        }
        p::Term::BinOp(op, l, r) => p::Term::BinOp(
            *op,
            Box::new(rename_term_to_probe(l, map)),
            Box::new(rename_term_to_probe(r, map)),
        ),
        p::Term::AlgApp(name, l, r) => p::Term::AlgApp(
            name.clone(),
            Box::new(rename_term_to_probe(l, map)),
            Box::new(rename_term_to_probe(r, map)),
        ),
        _ => t.clone(),
    }
}

fn collect_term_vars(t: &p::Term, out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => out.push(v.clone()),
        p::Term::App(_, args) | p::Term::Pair(args) => {
            for a in args {
                collect_term_vars(a, out);
            }
        }
        p::Term::BinOp(_, l, rt) => {
            collect_term_vars(l, out);
            collect_term_vars(rt, out);
        }
        p::Term::AlgApp(_, l, rt) => {
            collect_term_vars(l, out);
            collect_term_vars(rt, out);
        }
        _ => {}
    }
}

/// Build the per-rule probe theory:
///
/// ```text
///   theory Probe_<idx>
///     <copy of original signature: builtins, functions, equations, macros>
///
///     rule Probe_<idx>:
///       [ Fr(v) for each free var, keeping its sort (only nat → fresh) ]
///       --[ Generated_<idx>(v1, v2, ...) ]->
///       [ Out(t) for each premise term in R ]
///
///     lemma deriv_check_<idx>_<v>: exists-trace
///       "Ex v1 v2 ... #t0 #t1. Generated_<idx>(...) @ #t0 & KU(v) @ #t1"
/// ```
///
/// ...one per free var, each with two distinct timepoints and the
/// intruder-knowledge predicate `KU` (not `K`).
// (name,sort,idx)->probe-var rename map; keyed lookup only;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn synthesise_probe_theory(
    src: &p::Theory,
    rule: &p::Rule,
    idx: usize,
    free_vars: &[p::VarSpec],
) -> p::Theory {
    let mut probe = p::Theory {
        is_diff: false,
        name: format!("Probe_{}", idx),
        configuration: None,
        items: Vec::new(),
    };
    // Carry over the signature items VERBATIM.  Drops rules/lemmas/restrictions.
    //
    // HS keeps the maude signature PRIVATE for the deriv-check probe.  Two HS
    // operations look like they make symbols public, but neither affects the
    // verdict:
    //   * `makeFunsPublic` (MessageDerivationChecks.hs:36-50, see line 46; definition at
    //     MessageDerivationChecks.hs:104-105) is just
    //     `L.set thySignature (toSignaturePure sig)` — it sets the OPEN theory's
    //     *pure* signature, which `closeTheoryWithMaude sig ...`
    //     (MessageDerivationChecks.hs:36-50, see line 42, CloseRule.hs:56-64) immediately
    //     OVERWRITES with the ORIGINAL `SignatureWithMaude sig` (the 5th field
    //     of the `Theory` record).  Intruder-rule generation runs off that
    //     original maude signature (`closeRuleCache ... sig ...`,
    //     CloseRule.hs:391-402, called at CloseRule.hs:70),
    //     so destructor/constructor rules see the symbols as Private exactly as
    //     in the real theory.  `makeFunsPublic` is a misnomer that touches only
    //     pretty/storage state, never the verdict.
    //   * `replacePrivate` (MessageDerivationChecks.hs:36-50, see line 49; definition at
    //     MessageDerivationChecks.hs:97-102) rewrites a
    //     private NoEq head on the Out terms to a Public-headed variant of the
    //     SAME name/arity.  That variant is never inserted into `stFunSyms`/
    //     `stRules`, so it gets no construction rule (constructionRules iterates
    //     `stFunSyms`, IntruderRules.hs:218-221) and no destruction rule (stRules
    //     is keyed on the original private symbol; the variant matches nothing).
    //     The intruder can coerce the whole opaque application KD→KU but cannot
    //     peel a sub-variable out of it — behaviorally identical to leaving the
    //     private application in place.  In RS, privacy is resolved by NAME
    //     against the theory signature (elaborate.rs `head_sym`), so there is
    //     no per-occurrence public variant; emulating `replacePrivate` would
    //     resolve to the real public signature symbol and re-introduce the
    //     divergence.  So we mirror HS by doing NEITHER: keep privacy as-is.
    //
    // The Rust intruder-rule generation (intruder_rules.rs: `destruction_rules`'
    // private/free-var skip, `construction_rules`' Public-only filter and
    // `private_constructor_rules`) already matches IntruderRules.hs:129-157,
    // see line 149/219 once the privacy flags survive.
    for it in &src.items {
        match it {
            p::TheoryItem::Functions(_)
            | p::TheoryItem::Builtins(_)
            | p::TheoryItem::Equations { .. }
            | p::TheoryItem::Macros(_) => {
                probe.items.push(it.clone());
            }
            _ => {}
        }
    }
    // HS `generateRule` (MessageDerivationChecks.hs:170-171) keeps each free
    // var's ORIGINAL sort: premises = `freesToFresh . deleteGlobals` and
    // `freesToFresh = map (freshFact . lvarToLnterm)` where `lvarToLnterm`
    // only retypes LSortNat → LSortFresh (everything else stays as-is).
    // So `~ltk` (fresh) and `ltk` (msg) become Fr(~ltk) and Fr(ltk) — two
    // DISTINCT premises; Out(~ltk) makes ~ltk derivable while KU(ltk) is
    // not.  Keying the rename map on (name, sort, idx) — not (name, idx)
    // alone — is required so same-named vars of different sorts (e.g.
    // Register_pk's `~ltk` vs `ltk`) stay distinct.
    // A probe var's name (`dvar<k>`) and index carry nothing: derivability
    // reads sorts and structure alone, and `prove_probe` reports the
    // undecidable variable from the original `free_vars` entry through
    // `show_lvar`.  `nat_to_fresh_var` gives the probe var the sort
    // `lvarToLnterm` gives the premise.
    let probe_vars: Vec<p::VarSpec> = free_vars
        .iter()
        .enumerate()
        .map(|(k, v)| {
            let mut nv = nat_to_fresh_var(v);
            nv.name = format!("dvar{}", k);
            nv.idx = 0;
            nv
        })
        .collect();
    // Sort-aware (name, sort, idx) → probe-var map for renaming premise terms
    // (so `Out(~ltk)` references the same `dvar<k>` as `Fr(dvar<k>)`).
    let rename: std::collections::HashMap<(String, LSort, u64), p::VarSpec> = free_vars
        .iter()
        .enumerate()
        .map(|(k, v)| ((v.name.clone(), v.sort, v.idx), probe_vars[k].clone()))
        .collect();
    let fresh_premises: Vec<p::Fact> = probe_vars
        .iter()
        .map(|v| p::Fact {
            persistent: false,
            name: "Fr".into(),
            args: vec![p::Term::Var(v.clone())],
            annotations: Vec::new(),
        })
        .collect();
    // HS `generateAction vars idx = protoFact Persistent ("Generated_" ++
    // show idx) (...)` (MessageDerivationChecks.hs:173-174, see line 174) — the Generated fact
    // is Persistent.  For a ProtoFact the multiplicity rides in the tag, and
    // both the probe rule's action and the lemma's action atom are built from
    // this same `action`, so they stay mutually consistent.  Match HS exactly.
    let action = p::Fact {
        persistent: true,
        name: format!("Generated_{}", idx),
        args: probe_vars.iter().map(|v| p::Term::Var(v.clone())).collect(),
        annotations: Vec::new(),
    };
    // premisesToOut = map (outFact . natToFreshVars) . concatMap factTerms:
    // Out each premise term, with free-var occurrences renamed to their
    // `dvar<k>` probe var (and nat-sort non-free vars retyped to fresh).
    let out_concs: Vec<p::Fact> = rule
        .premises
        .iter()
        .flat_map(|f| f.args.iter().cloned())
        .map(|t| p::Fact {
            persistent: false,
            name: "Out".into(),
            args: vec![rename_term_to_probe(&t, &rename)],
            annotations: Vec::new(),
        })
        .collect();
    let probe_rule = p::Rule {
        name: format!("Probe_{}", idx),
        modulo: None,
        attributes: Vec::new(),
        let_block: Vec::new(),
        premises: fresh_premises,
        actions: vec![action.clone()],
        conclusions: out_concs,
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    };
    probe.items.push(p::TheoryItem::Rule(probe_rule));

    // Build one lemma per free var.  HS's `landFormula` gives each
    // conjoined fact its OWN timepoint (MessageDerivationChecks.hs:186-188):
    //   `Generated_<idx>(...) @ #t0  ∧  KU(v) @ #t1`
    // Two DIFFERENT timepoints — asking "is there ever a time the
    // intruder knows v AND a (possibly different) time Generated fires?"
    // not "are these simultaneous".  The intruder-knowledge predicate
    // is `KU` (HS's `lntermToKUFact = kuFact`), not `K`.
    let action_atom = |action: p::Fact, t: p::Term| -> p::Formula {
        p::Formula::Atom(p::Atom::Action(action, t))
    };
    for k in 0..free_vars.len() {
        // Lemma named by free-var INDEX (not name) so same-named vars don't
        // collide; prove_probe re-derives the same name from the index.
        let lemma_name = format!("deriv_check_{}_{}", idx, k);
        let v_renamed = probe_vars[k].clone();
        let t0 = p::VarSpec {
            name: "t0".into(),
            idx: 0,
            sort: LSort::Node,
            typ: None,
        };
        let t1 = p::VarSpec {
            name: "t1".into(),
            idx: 0,
            sort: LSort::Node,
            typ: None,
        };
        let gen_at = action_atom(action.clone(), p::Term::Var(t0.clone()));
        let ku_fact = p::Fact {
            // KU is Persistent per factTagMultiplicity (Theory/Model/Fact.hs:382-388,
            // see line 386);
            // keep the "for special names, persistent == tag multiplicity"
            // invariant so GFact equality with parsed KU facts is faithful.
            persistent: true,
            name: "KU".into(),
            args: vec![p::Term::Var(v_renamed)],
            annotations: Vec::new(),
        };
        let ku_at = action_atom(ku_fact, p::Term::Var(t1.clone()));
        let conj = p::Formula::And(Box::new(gen_at), Box::new(ku_at));
        // Ex t0 t1 vars... . <conj>
        let mut all_quant = probe_vars.clone();
        all_quant.push(t0);
        all_quant.push(t1);
        let body = p::Formula::Exists(all_quant, Box::new(conj));
        probe.items.push(p::TheoryItem::Lemma(p::Lemma {
            name: lemma_name,
            modulo: None,
            attributes: Vec::new(),
            trace_quantifier: p::TraceQuantifier::ExistsTrace,
            formula: body,
            proof: None,
            plaintext: String::new(),
        }));
    }

    probe
}

/// Result of probing a single rule: the non-derivable variable names plus
/// debug-only timing/count accumulators (folded into the caller's running
/// totals at the call site).
struct ProbeOutcome {
    /// Variable names whose lemma did NOT find a trace (= non-derivable).
    undecidable: Vec<String>,
    /// Wall-clock spent in `run_proof_search` across this probe's lemmas.
    prove_time: Duration,
    /// Number of per-variable proof attempts made for this probe.
    var_count: usize,
}

/// HS-faithful per-probe prover.  Builds the elaborated probe theory
/// and a single `ProofContext` (with one `ensure_saturated` call),
/// then iterates the per-variable lemmas, invoking `run_proof_search`
/// directly on each lemma's `System` with the shared, already-saturated
/// context.
///
/// Mirrors HS's `closeTheoryWithMaude` (called once per modified theory
/// in `MessageDerivationChecks.hs:41-43`) followed by `proveTheory`'s
/// per-lemma walk (`CloseRule.hs:144-155`).  Returns `None` on elaboration
/// failure (caller continues to the next probe rule); otherwise returns
/// a `ProbeOutcome` whose `undecidable` lists the variable names whose
/// lemma did NOT find a trace (= non-derivable variables).
#[allow(clippy::too_many_arguments)]
fn prove_probe(
    probe: &p::Theory,
    maude: MaudeHandle,
    idx: usize,
    free_vars: &[p::VarSpec],
    timeout: Duration,
    dbg_timing: bool,
    rule_name: &str,
    ndc_cache: Option<&IntrRuleCache>,
) -> Option<ProbeOutcome> {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::search::{run_proof_search, NodeStatus};
    use crate::constraint::system::{formula_to_system, SourceKind};
    use crate::elaborate::elaborate;
    use crate::guarded::formula_to_guarded_parsed;
    use crate::theory::OpenProtoRule;

    // Per-prove deadline gate: cap each variable's `run_proof_search` at
    // `timeout`.  The cap is THREAD-scoped (not the process-global
    // `TAM_PROVE_DEADLINE_MS` env var) so it bounds only the probe proofs
    // below and cannot truncate an unrelated search another thread starts
    // while a probe is running.  The RAII guard restores the prior cap on
    // EVERY exit path, so the deadline cannot leak into the main prove loop.
    let ms = (timeout.as_millis() as u64).max(1);
    let _deadline_guard = crate::constraint::solver::search::ProofDeadlineGuard::set_ms(ms);

    let elaborated = match elaborate(probe) {
        Ok(t) => t,
        Err(_) => return None,
    };
    let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();
    // Probe contexts inherit the parent theory's checked cache verbatim
    // (HS keeps `_thyCache` on the probe theory; `closeRuleCache`
    // consumes it as-is), so the NDC tags — and the permutation — carry
    // into probe proofs without re-running the check per probe.
    let mut ctx = match ndc_cache {
        Some(cache) => {
            ProofContext::new_with_injected_intruder_rules(maude, rules, Vec::new(), cache.clone())
        }
        None => ProofContext::new_with_restrictions(maude, rules, Vec::new()),
    };
    ctx.is_exists_trace = true;
    // Probes have no `[sources]`-tagged lemmas, so no typing
    // assumptions — but `ensure_saturated()` still must run to compute
    // the source-case cache exactly as HS's `closeTheoryWithMaude`
    // does once per modified theory (CloseRule.hs:56-70).
    ctx.ensure_saturated();

    let mut undecidable = Vec::new();
    let mut prove_time = Duration::ZERO;
    let mut var_count = 0usize;
    for (k, v) in free_vars.iter().enumerate() {
        // Lemma name keyed by free-var INDEX (matches synthesise_probe_theory);
        // the reported var name below uses the ORIGINAL `v` (sort + name).
        let lemma_name = format!("deriv_check_{}_{}", idx, k);
        let lemma = match elaborated.lookup_lemma(&lemma_name) {
            Some(l) => l,
            None => continue,
        };
        let g = match formula_to_guarded_parsed(&lemma.formula, &elaborated.signature.maude_sig) {
            Ok(g) => g,
            Err(_) => continue,
        };
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            p::TraceQuantifier::ExistsTrace,
            false,
            &g,
        );
        let t_prove = std::time::Instant::now();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_proof_search(&ctx, sys, 1000)
        }));
        // A panic inside the prover is an INTERNAL bug, not a timeout
        // (timeouts return a non-Solved status, not a panic).  Log it to
        // stderr so it isn't silently mis-reported to the user as a
        // "Failed to derive Variable(s)" wellformedness result.  We still
        // fall through to `ok = false` (the variable is left in the report)
        // to preserve the existing conservative behaviour.
        if result.is_err() {
            eprintln!(
                "[deriv] WARNING: solver panicked while checking derivability of \
                 variable `{}` in rule `{}`; reporting it as non-derivable. \
                 This is an internal prover bug, not necessarily a theory problem.",
                v.name, rule_name,
            );
        }
        let ok = matches!(result, Ok(ref n) if matches!(n.status, NodeStatus::Solved));
        let prove_dt = t_prove.elapsed();
        prove_time += prove_dt;
        var_count += 1;
        if dbg_timing {
            eprintln!(
                "[deriv-timing] rule={} var={} prove={:.3}s ok={}",
                rule_name,
                v.name,
                prove_dt.as_secs_f64(),
                ok,
            );
        }
        if !ok {
            // HS reports `show LVar` (sortPrefix ++ body) for the
            // undecidable variable (MessageDerivationChecks.hs:131-133, see line 133).
            undecidable.push(show_lvar(v));
        }
    }

    Some(ProbeOutcome {
        undecidable,
        prove_time,
        var_count,
    })
}

/// HS `Show LVar` (LTerm.hs:550-557): `sortPrefix s ++ body`, where body is
/// the name (or, if `idx /= 0`, `name.idx`; if the name is empty, just the
/// index).
fn show_lvar(v: &p::VarSpec) -> String {
    let prefix = tamarin_term::lterm::sort_prefix(v.sort);
    let body = if v.name.is_empty() {
        v.idx.to_string()
    } else if v.idx == 0 {
        v.name.clone()
    } else {
        format!("{}.{}", v.name, v.idx)
    };
    format!("{}{}", prefix, body)
}

fn format_deriv_report(per_rule: &[(String, Vec<String>)]) -> Vec<WfError> {
    if per_rule.is_empty() {
        return Vec::new();
    }
    // HS `reportVars` (Theory/Tools/MessageDerivationChecks.hs:117-122)
    //   `[(underlineTopic "Message Derivation Checks",
    //     text $ "The variables of the following rule(s) ... pattern matching.\n\n" ++ errors)]`
    // The renderer in HS (`prettyWfErrorReport`) lays the topic + body
    // out as `<title>\n<====>\n\n  <body>\n`. The body is then indented
    // by 2 spaces at its first line via `nest 2`-equivalent, then the
    // per-rule blocks follow at col 0. See HS output bytes — the intro
    // line has a 2-space leading indent.
    let mut msg = tamarin_parser::wf::underline_topic("Message Derivation Checks");
    msg.push('\n');
    msg.push_str(
        "  The variables of the following rule(s) are not derivable \
         from their premises, you may be performing unintended pattern \
         matching.\n\n",
    );
    // The per-rule blocks are intentionally NOT 2-space-indented: HughesPJ
    // `nest 2` re-indents only the first line of a `text`, leaving text that
    // follows a literal `\n` un-reindented, so HS's 2-space indent lands on
    // the intro line only and every `Rule X:` block starts at column 0.
    let blocks: Vec<String> = per_rule
        .iter()
        .map(|(rule_name, vars)| {
            format!(
                "Rule {}: \nFailed to derive Variable(s): {}",
                rule_name,
                vars.join(", ")
            )
        })
        .collect();
    msg.push_str(&blocks.join("\n\n"));
    vec![WfError::new("Message Derivation Checks", msg)]
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    use crate::test_maude::maude_path;

    /// A pair-signature handle.  The result is `None` only when
    /// [`maude_path`] resolves nothing.  That case is the documented
    /// `TAM_ALLOW_NO_MAUDE` skip.  A maude that resolves but does not start
    /// is the same misconfiguration as a `MAUDE_PATH` that points at nothing.
    /// So this function panics.  It does not silently skip every maude-backed
    /// test in this file.
    fn maude() -> Option<MaudeHandle> {
        Some(start_maude(
            &maude_path()?,
            tamarin_term::maude_sig::pair_maude_sig(),
        ))
    }

    /// See [`maude`] for why a failed start is a panic, not a skip.
    fn start_maude(path: &str, sig: tamarin_term::maude_sig::MaudeSig) -> MaudeHandle {
        MaudeHandle::start(path, sig).unwrap_or_else(|e| {
            panic!(
                "maude at {path} failed to start: {e:?} — every maude-backed \
                 test here would otherwise skip silently"
            )
        })
    }

    #[test]
    fn deriv_check_passes_on_derivable_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [In(x)] --[Use(x)]-> [Out(x)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5, None);
        // `x` appears in `In(x)` which is intruder-known → derivable.
        assert!(report.is_empty(), "expected no warnings, got {:?}", report);
    }

    #[test]
    fn deriv_check_flags_unbound_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5, None);
        // Free `unbound` has no premise → not derivable.
        assert_eq!(report.len(), 1);
        assert!(
            report[0].message.contains("unbound"),
            "expected 'unbound' in report, got {:?}",
            report
        );
    }

    #[test]
    fn deriv_check_disabled_by_zero_timeout() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 0, None);
        assert!(report.is_empty(), "timeout=0 should disable the check");
    }

    /// Start a Maude handle whose signature is elaborated from `src` (so the
    /// theory's own `functions:`/`equations:` symbols — including a private
    /// destructor — are present), exactly as the real driver does via
    /// `elaborated.signature.maude_sig` (run.rs).  The function skips on the
    /// same terms as [`maude`].
    fn maude_for(src: &str) -> Option<(p::Theory, MaudeHandle)> {
        let p = maude_path()?;
        let thy = parse_theory(src, &[]).expect("parse");
        // `elaborate` installs the per-theory user-funs guards internally.
        let elaborated = crate::elaborate::elaborate(&thy).expect("elaborate");
        let sig = elaborated.signature.maude_sig.clone();
        Some((thy, start_maude(&p, sig)))
    }

    // The privacy of a function symbol is load-bearing for the deriv-check
    // verdict, and HS keeps it PRIVATE for the probe theory (it does NOT flip
    // privacy: `makeFunsPublic` is overwritten by `closeTheoryWithMaude sig`
    // and `replacePrivate` is inert — see `synthesise_probe_theory`).  The two
    // tests below pin HS's discriminating behaviour, confirmed against the
    // real prover (tamarin-prover v1.13.0, `--derivcheck-timeout=10`):
    //   * private `dec`  → `m` reported "Failed to derive Variable(s)".
    //   * public  `dec`  → `m` derivable, nothing reported.

    #[test]
    fn deriv_check_flags_var_recoverable_only_via_private_destructor() {
        // `m` is recoverable from the premise terms ONLY by applying the
        // PRIVATE destructor `dec`, which the intruder may not use.  HS reports
        // `m` as non-derivable.  (Probed: tamarin-prover 1.13.0 emits
        // "Rule Reveal: \nFailed to derive Variable(s): m".)
        let src = r#"
            theory T begin
              functions: dec/2 [private], enc/2
              equations: dec(enc(m, k), k) = m
              rule Reveal:
                [ In(enc(m, k)), In(k) ]
                --[ Got(m) ]->
                [ Out(dec(enc(m, k), k)) ]
              lemma trivial: exists-trace "Ex m #i. Got(m) @ i"
            end
        "#;
        let Some((thy, m)) = maude_for(src) else {
            return;
        };
        let report = check_message_derivation(&thy, &m, 10, None);
        assert_eq!(report.len(), 1, "expected one report, got {:?}", report);
        assert!(
            report[0].message.contains("Reveal")
                && report[0].message.contains("Failed to derive Variable(s)")
                && report[0].message.contains("m"),
            "expected `m` flagged in Rule Reveal, got {:?}",
            report
        );
    }

    #[test]
    fn deriv_check_passes_when_destructor_is_public() {
        // Same theory but `dec` is PUBLIC, so the intruder can apply it and
        // recover `m`.  HS reports nothing.  (Probed: tamarin-prover 1.13.0
        // emits no "Message Derivation Checks" section.)
        let src = r#"
            theory T begin
              functions: dec/2, enc/2
              equations: dec(enc(m, k), k) = m
              rule Reveal:
                [ In(enc(m, k)), In(k) ]
                --[ Got(m) ]->
                [ Out(dec(enc(m, k), k)) ]
              lemma trivial: exists-trace "Ex m #i. Got(m) @ i"
            end
        "#;
        let Some((thy, m)) = maude_for(src) else {
            return;
        };
        let report = check_message_derivation(&thy, &m, 10, None);
        assert!(
            report.is_empty(),
            "public `dec` → `m` derivable; expected no report, got {:?}",
            report
        );
    }
}
