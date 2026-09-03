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
//!     1. Drop ALL rules/lemmas/restrictions from the theory, keeping the
//!        signature — privacy flags included.  HS's `makeFunsPublic` and
//!        `replacePrivate` both look like they make symbols public but neither
//!        changes the verdict: `makeFunsPublic` only sets the OPEN theory's
//!        pure signature, which `closeTheoryWithMaude sig` overwrites with the
//!        ORIGINAL private-preserving maude signature (so intruder-rule
//!        generation stays private); and `replacePrivate` rewrites Out-term
//!        heads to a same-name Public variant that gets no
//!        construction/destruction rule, leaving the term opaque exactly as
//!        the private application would be.  See [`synthesise_probe`] for the
//!        full citation.
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

use crate::wellformedness::WfError;
use std::time::Duration;
use tamarin_term::lterm::{HasFrees, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::vterm::var_term;

use crate::constraint::solver::context::IntrRuleCache;
use crate::fact::{fresh_fact, ku_fact, out_fact, proto_fact, LNFact, Multiplicity};
use crate::formula::{exists_var, lift_free, LNFormula};
use crate::rule::{ProtoRuleE, ProtoRuleEInfo};
use crate::theory::{Theory, TraceQuantifier};

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
    thy: &Theory,
    maude: &MaudeHandle,
    timeout_secs: u32,
    ndc_cache: Option<IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> Vec<WfError> {
    if timeout_secs == 0 {
        return Vec::new();
    }
    let timeout = Duration::from_secs(timeout_secs as u64);
    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    // HS `originalRules = map (applyMacroInProtoRule (theoryMacros thy)) $
    // theoryRules thy` (MessageDerivationChecks.hs:36-50, see line 40): the
    // rules with the theory's `macros:` applied, which is the form
    // `elaborate` stores (`apply_macro_in_rule`).
    for (idx, opr) in thy.rules().enumerate() {
        let rule = &opr.rule;
        // HS filters on `ignoreDerivChecks` when it builds the report
        // (`reportVars`, MessageDerivationChecks.hs:117-133); skipping the
        // probe is the same verdict and keeps `idx`, which HS assigns with
        // `zipWith3 ... [0..]` over ALL rules
        // (MessageDerivationChecks.hs:47-48).
        if rule.info.attributes.ignore_deriv_checks {
            continue;
        }
        let free_vars = rule_free_vars(rule);
        if free_vars.is_empty() {
            continue;
        }
        let rule_name = opr.name();

        // Build the probe ONCE per rule (it holds all the per-variable
        // lemmas): one rule and N formulas over the parent theory's terms.
        let probe = synthesise_probe(rule, idx, &free_vars);

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
        let undecidable = prove_probe(
            &probe,
            maude.clone(),
            &free_vars,
            timeout,
            rule_name,
            ndc_cache.as_ref(),
            parameters,
        );
        if !undecidable.is_empty() {
            per_rule.push((rule_name.to_string(), undecidable));
        }
    }
    format_deriv_report(&per_rule)
}

/// All variables that appear anywhere in a rule's premise / action /
/// conclusion terms, returned in ascending HS `LVar` Ord — idx, then sort,
/// then name (LTerm.hs:545-548) — which is the order HS `frees`/`S.toList`
/// yields them in.  EXCLUDING:
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
///
/// The `LVar` keys name AND sort AND idx, so `~ltk` (fresh) and `ltk` (msg)
/// are DISTINCT free vars — both become derivability candidates.  A
/// (name, idx)-only key would let `~ltk` mask `ltk` and silently drop the
/// non-derivable msg var (Register_pk `ltk`).
fn rule_free_vars(r: &ProtoRuleE) -> Vec<LVar> {
    let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    let mut collect = |f: &LNFact| {
        f.for_each_free(&mut |v| {
            if !matches!(v.sort, LSort::Pub | LSort::Node) {
                seen.insert(*v);
            }
        });
    };
    for f in &r.premises {
        collect(f);
    }
    for f in &r.actions {
        collect(f);
    }
    for f in &r.conclusions {
        collect(f);
    }
    seen.into_iter().collect()
}

/// HS `lvarToLnterm`: retype an LSortNat var to LSortFresh; otherwise keep
/// the var's sort unchanged (Theory/Model/Fact.hs:331-333).
fn nat_to_fresh_var(v: LVar) -> LVar {
    if v.sort == LSort::Nat {
        LVar {
            sort: LSort::Fresh,
            ..v
        }
    } else {
        v
    }
}

/// Rename a premise term's variables for the probe: a free var becomes its
/// `dvar<k>` probe var; any other var is retyped nat→fresh (HS
/// `natToFreshVars`).  Keeps `Out(...)` referencing the same probe vars as
/// the `Fr(...)` premises.
fn rename_term_to_probe(t: LNTerm, map: &tamarin_utils::FastMap<LVar, LVar>) -> LNTerm {
    t.map_free(&mut |v| match map.get(&v) {
        Some(pv) => *pv,
        None => nat_to_fresh_var(v),
    })
}

/// The probe rule's name, keyed by the rule's index; HS's `generateRule`
/// names it `StandRule (show idx)` (MessageDerivationChecks.hs:170-171).
fn probe_rule_name(idx: usize) -> String {
    format!("Probe_{}", idx)
}

/// The per-rule probe: HS's generated rule plus one exists-trace formula per
/// free variable, in `free_vars` order.
struct Probe {
    rule: ProtoRuleE,
    lemmas: Vec<LNFormula>,
}

/// Build the per-rule probe:
///
/// ```text
///   rule Probe_<idx>:
///     [ Fr(v) for each free var, keeping its sort (only nat → fresh) ]
///     --[ Generated_<idx>(v1, v2, ...) ]->
///     [ Out(t) for each premise term in R ]
///
///   lemma deriv_check_<idx>_<k>: exists-trace
///     "Ex v1 v2 ... #t0 #t1. Generated_<idx>(...) @ #t0 & KU(v) @ #t1"
/// ```
///
/// ...one lemma per free var, each with two distinct timepoints and the
/// intruder-knowledge predicate `KU` (not `K`).
///
/// The probe proofs run against the parent theory's Maude signature, which
/// keeps every symbol's privacy flag.  That is what HS does too, although two
/// of its operations look like they make symbols public:
///   * `makeFunsPublic` (MessageDerivationChecks.hs:36-50, see line 46;
///     definition at MessageDerivationChecks.hs:104-105) is just
///     `L.set thySignature (toSignaturePure sig)` — it sets the OPEN theory's
///     *pure* signature, which `closeTheoryWithMaude sig ...`
///     (MessageDerivationChecks.hs:36-50, see line 42, CloseRule.hs:56-64)
///     immediately OVERWRITES with the ORIGINAL `SignatureWithMaude sig` (the
///     5th field of the `Theory` record).  Intruder-rule generation runs off
///     that original maude signature (`closeRuleCache ... sig ...`,
///     CloseRule.hs:391-402, called at CloseRule.hs:70), so
///     destructor/constructor rules see the symbols as Private exactly as in
///     the real theory.  `makeFunsPublic` is a misnomer that touches only
///     pretty/storage state, never the verdict.
///   * `replacePrivate` (MessageDerivationChecks.hs:36-50, see line 49;
///     definition at MessageDerivationChecks.hs:97-102) rewrites a private
///     NoEq head on the Out terms to a Public-headed variant of the SAME
///     name/arity.  That variant is never inserted into `stFunSyms`/`stRules`,
///     so it gets no construction rule (constructionRules iterates
///     `stFunSyms`, IntruderRules.hs:218-221) and no destruction rule
///     (stRules is keyed on the original private symbol; the variant matches
///     nothing).  The intruder can coerce the whole opaque application KD→KU
///     but cannot peel a sub-variable out of it — behaviorally identical to
///     leaving the private application in place.  In RS, privacy is resolved
///     by NAME against the theory signature (elaborate.rs `head_sym`), so
///     there is no per-occurrence public variant; emulating `replacePrivate`
///     would resolve to the real public signature symbol and re-introduce the
///     divergence.  So we mirror HS by doing NEITHER: keep privacy as-is.
///
/// The Rust intruder-rule generation (intruder_rules.rs: `destruction_rules`'
/// private/free-var skip, `construction_rules`' Public-only filter and
/// `private_constructor_rules`) already matches IntruderRules.hs:129-157,
/// see line 149/219 once the privacy flags survive.
fn synthesise_probe(rule: &ProtoRuleE, idx: usize, free_vars: &[LVar]) -> Probe {
    // HS `generateRule` (MessageDerivationChecks.hs:170-171) keeps each free
    // var's ORIGINAL sort: premises = `freesToFresh . deleteGlobals` and
    // `freesToFresh = map (freshFact . lvarToLnterm)` where `lvarToLnterm`
    // only retypes LSortNat → LSortFresh (everything else stays as-is).
    // So `~ltk` (fresh) and `ltk` (msg) become Fr(~ltk) and Fr(ltk) — two
    // DISTINCT premises; Out(~ltk) makes ~ltk derivable while KU(ltk) is
    // not.  Keying the rename map on the whole `LVar` — not on the name
    // alone — is required so same-named vars of different sorts (e.g.
    // Register_pk's `~ltk` vs `ltk`) stay distinct.
    // A probe var's name (`dvar<k>`) and index carry nothing: derivability
    // reads sorts and structure alone, and `prove_probe` reports the
    // undecidable variable from the original `free_vars` entry.
    // `nat_to_fresh_var` gives the probe var the sort `lvarToLnterm` gives
    // the premise.
    let probe_vars: Vec<LVar> = free_vars
        .iter()
        .enumerate()
        .map(|(k, v)| LVar::new(format!("dvar{}", k), nat_to_fresh_var(*v).sort, 0))
        .collect();
    // Whole-`LVar` → probe-var map for renaming premise terms (so `Out(~ltk)`
    // references the same `dvar<k>` as `Fr(dvar<k>)`).
    let rename: tamarin_utils::FastMap<LVar, LVar> = free_vars
        .iter()
        .zip(probe_vars.iter())
        .map(|(v, pv)| (*v, *pv))
        .collect();
    let fresh_premises: Vec<LNFact> = probe_vars
        .iter()
        .map(|v| fresh_fact(var_term(*v)))
        .collect();
    // HS `generateAction vars idx = protoFact Persistent ("Generated_" ++
    // show idx) (...)` (MessageDerivationChecks.hs:173-174, see line 174) — the
    // Generated fact is Persistent.  For a ProtoFact the multiplicity rides in
    // the tag, and both the probe rule's action and the lemma's action atom
    // are built from this same `action`, so they stay mutually consistent.
    // Match HS exactly.
    let action = proto_fact(
        Multiplicity::Persistent,
        &format!("Generated_{}", idx),
        probe_vars.iter().map(|v| var_term(*v)).collect(),
    );
    // premisesToOut = map (outFact . natToFreshVars) . concatMap factTerms:
    // Out each premise term, with free-var occurrences renamed to their
    // `dvar<k>` probe var (and nat-sort non-free vars retyped to fresh).
    let out_concs: Vec<LNFact> = rule
        .premises
        .iter()
        .flat_map(|f| f.terms.iter().cloned())
        .map(|t| out_fact(rename_term_to_probe(t, &rename)))
        .collect();
    // `Rule::new` leaves `new_vars` empty, which is the `[]` HS's
    // `generateRule` passes as the probe rule's `rNewVars`
    // (MessageDerivationChecks.hs:170-171).
    let probe_rule = ProtoRuleE::new(
        ProtoRuleEInfo::standard(probe_rule_name(idx)),
        fresh_premises,
        out_concs,
        vec![action.clone()],
    );

    // Build one lemma per free var.  HS's `landFormula` gives each
    // conjoined fact its OWN timepoint (MessageDerivationChecks.hs:186-188):
    //   `Generated_<idx>(...) @ #t0  ∧  KU(v) @ #t1`
    // Two DIFFERENT timepoints — asking "is there ever a time the
    // intruder knows v AND a (possibly different) time Generated fires?"
    // not "are these simultaneous".  The intruder-knowledge predicate
    // is `KU` (HS's `lntermToKUFact = kuFact`), not `K`.
    let t0 = LVar::new("t0", LSort::Node, 0);
    let t1 = LVar::new("t1", LSort::Node, 0);
    let gen_at = LNFormula::Atom(crate::atom::ProtoAtom::Action(
        var_term(tamarin_term::lterm::BVar::Free(t0)),
        action.map_ref(lift_free),
    ));
    let mut binders: Vec<LVar> = probe_vars.clone();
    binders.push(t0);
    binders.push(t1);
    let lemmas: Vec<LNFormula> = probe_vars
        .iter()
        .map(|v| {
            let ku_at = LNFormula::Atom(crate::atom::ProtoAtom::Action(
                var_term(tamarin_term::lterm::BVar::Free(t1)),
                ku_fact(var_term(*v)).map_ref(lift_free),
            ));
            // `Ex dvar0 … dvarN-1 #t0 #t1. …`, the last binder innermost.
            binders
                .iter()
                .rev()
                .fold(gen_at.clone().and(ku_at), |acc, b| {
                    exists_var((b.name.to_string(), b.sort), b, acc)
                })
        })
        .collect();

    Probe {
        rule: probe_rule,
        lemmas,
    }
}

/// HS-faithful per-probe prover.  Builds a single `ProofContext` (with one
/// `ensure_saturated` call) over the probe's rule, then iterates the
/// per-variable lemmas, invoking `run_proof_search` directly on each lemma's
/// `System` with the shared, already-saturated context.
///
/// Mirrors HS's `closeTheoryWithMaude` (called once per modified theory
/// in `MessageDerivationChecks.hs:41-43`) followed by `proveTheory`'s
/// per-lemma walk (`CloseRule.hs:144-155`).  The returned `undecidable`
/// lists the variable names whose lemma did NOT find a trace (= non-derivable
/// variables).
fn prove_probe(
    probe: &Probe,
    maude: MaudeHandle,
    free_vars: &[LVar],
    timeout: Duration,
    rule_name: &str,
    ndc_cache: Option<&IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> Vec<String> {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::search::{run_proof_search, NodeStatus};
    use crate::constraint::system::{formula_to_system, SourceKind};
    use crate::guarded::formula_to_guarded;
    use crate::theory::OpenProtoRule;

    // Per-prove deadline gate: cap each variable's `run_proof_search` at
    // `timeout`.  The cap is THREAD-scoped (not the process-global
    // `TAM_PROVE_DEADLINE_MS` env var) so it bounds only the probe proofs
    // below and cannot truncate an unrelated search another thread starts
    // while a probe is running.  The RAII guard restores the prior cap on
    // EVERY exit path, so the deadline cannot leak into the main prove loop.
    let ms = (timeout.as_millis() as u64).max(1);
    let _deadline_guard = crate::constraint::solver::search::ProofDeadlineGuard::set_ms(ms);

    let rules = vec![OpenProtoRule::new(probe.rule.clone())];
    // Probe contexts inherit the parent theory's checked cache verbatim
    // (HS keeps `_thyCache` on the probe theory; `closeRuleCache`
    // consumes it as-is), so the NDC tags — and the permutation — carry
    // into probe proofs without re-running the check per probe.
    let mut ctx = ProofContext::new_with_restrictions_pool_forced_and_parameters(
        maude,
        None,
        rules,
        Vec::new(),
        &[],
        ndc_cache.cloned(),
        parameters,
    );
    ctx.is_exists_trace = true;
    // Probes have no `[sources]`-tagged lemmas, so no typing
    // assumptions — but `ensure_saturated()` still must run to compute
    // the source-case cache exactly as HS's `closeTheoryWithMaude`
    // does once per modified theory (CloseRule.hs:56-70).
    ctx.ensure_saturated();

    let mut undecidable = Vec::new();
    for (v, fm) in free_vars.iter().zip(probe.lemmas.iter()) {
        let g = match formula_to_guarded(fm) {
            Ok(g) => g,
            Err(_) => continue,
        };
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            TraceQuantifier::ExistsTrace,
            &g,
        );
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_proof_search(&ctx, sys, 1000)
                .expect("the derivation proof context has no fallible ranking or source provider")
        }));
        // A panic inside the prover is an INTERNAL bug, not a timeout
        // (timeouts return a non-Solved status, not a panic).  Log it to
        // stderr so it isn't silently mis-reported to the user as a
        // "Failed to derive Variable(s)" wellformedness result.  We still
        // fall through to `ok = false`, the conservative verdict that leaves
        // the variable in the report.
        if result.is_err() {
            eprintln!(
                "[deriv] WARNING: solver panicked while checking derivability of \
                 variable `{}` in rule `{}`; reporting it as non-derivable. \
                 This is an internal prover bug, not necessarily a theory problem.",
                v.name, rule_name,
            );
        }
        let ok = matches!(result, Ok(ref n) if matches!(n.status, NodeStatus::Solved));
        if !ok {
            // HS reports `show LVar` for the undecidable variable
            // (MessageDerivationChecks.hs:131-133, see line 133); `Display
            // for LVar` is `instance Show LVar` (LTerm.hs:550-557).
            undecidable.push(v.to_string());
        }
    }

    undecidable
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
    let mut msg = crate::wellformedness::underline_topic("Message Derivation Checks");
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

    use tamarin_test_support::require_maude_path;

    /// A pair-signature handle.  The result is `None` only when
    /// [`maude_path`] resolves nothing.  That case is the documented
    /// `TAM_ALLOW_NO_MAUDE` skip.  A maude that resolves but does not start
    /// is the same misconfiguration as a `MAUDE_PATH` that points at nothing.
    /// So this function panics.  It does not silently skip every maude-backed
    /// test in this file.
    fn maude() -> Option<MaudeHandle> {
        Some(start_maude(
            &require_maude_path()?,
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

    /// The internal theory the driver hands the check.
    fn theory(src: &str) -> Theory {
        let parsed = parse_theory(src, &[]).expect("parse");
        crate::elaborate::elaborate(&parsed).expect("elaborate")
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
        let report = check_message_derivation(&theory(src), &m, 5, None, Default::default());
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
        let report = check_message_derivation(&theory(src), &m, 5, None, Default::default());
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
        let report = check_message_derivation(&theory(src), &m, 0, None, Default::default());
        assert!(report.is_empty(), "timeout=0 should disable the check");
    }

    /// `ignoreDerivChecks` on the rule's attributes keeps the rule out of
    /// the report (HS `reportVars`, MessageDerivationChecks.hs:117-133), so
    /// the same underivable variable as above is not named.
    #[test]
    fn deriv_check_skips_a_no_derivcheck_rule() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R [no_derivcheck]: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let report = check_message_derivation(&theory(src), &m, 5, None, Default::default());
        assert!(
            report.is_empty(),
            "a no_derivcheck rule is not reported, got {:?}",
            report
        );
    }

    /// HS `frees` keys on the whole `LVar`, so a rule binding both `~ltk`
    /// and `ltk` offers two candidates (issue527's `Register_pk`).  A
    /// name-only key would let the fresh one mask the message-sorted one,
    /// which is the variable the report names.
    #[test]
    fn free_vars_keep_same_named_vars_of_different_sorts_apart() {
        let thy = theory(
            r#"
            theory T begin
              rule Register_pk: [ Fr( ~ltk ), In( ltk ) ] --[ Reg( ltk ) ]-> [ Out( ~ltk ) ]
            end
        "#,
        );
        let rule = &thy.rules().next().expect("one rule item").rule;
        let shown: Vec<String> = rule_free_vars(rule).iter().map(|v| v.to_string()).collect();
        assert_eq!(shown, vec!["~ltk".to_string(), "ltk".to_string()]);
    }

    /// The free variables come back in ascending `LVar` Ord — index first,
    /// then sort, then name (LTerm.hs:545-548) — which is the order HS's
    /// `frees` (a `S.toList`) yields and the order the `dvar<k>` probe
    /// variables and their lemmas are numbered in.
    #[test]
    fn probe_free_vars_follow_the_lvar_order() {
        let thy = theory(
            r#"
            theory T begin
              rule R: [ In( <x.1, ~b, a> ), Fr( ~z ) ] --[ Act( x.1 ) ]-> [ Out( a ) ]
            end
        "#,
        );
        let rule = &thy.rules().next().expect("one rule item").rule;
        let shown: Vec<String> = rule_free_vars(rule).iter().map(|v| v.to_string()).collect();
        assert_eq!(
            shown,
            vec![
                "~b".to_string(),
                "~z".to_string(),
                "a".to_string(),
                "x.1".to_string()
            ]
        );
    }

    /// Start a Maude handle whose signature is the theory's own (so the
    /// theory's `functions:`/`equations:` symbols — including a private
    /// destructor — are present), exactly as the real driver does via
    /// `elaborated.signature` (run.rs).  The function skips on the
    /// same terms as [`maude`].
    fn theory_and_maude(src: &str) -> Option<(Theory, MaudeHandle)> {
        let p = require_maude_path()?;
        let thy = theory(src);
        let sig = thy.signature.clone();
        Some((thy, start_maude(&p, sig)))
    }

    // The privacy of a function symbol is load-bearing for the deriv-check
    // verdict, and HS keeps it PRIVATE for the probe theory (it does NOT flip
    // privacy: `makeFunsPublic` is overwritten by `closeTheoryWithMaude sig`
    // and `replacePrivate` is inert — see `synthesise_probe`).  The two
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
        let Some((thy, m)) = theory_and_maude(src) else {
            return;
        };
        let report = check_message_derivation(&thy, &m, 10, None, Default::default());
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
        let Some((thy, m)) = theory_and_maude(src) else {
            return;
        };
        let report = check_message_derivation(&thy, &m, 10, None, Default::default());
        assert!(
            report.is_empty(),
            "public `dec` → `m` derivable; expected no report, got {:?}",
            report
        );
    }
}
