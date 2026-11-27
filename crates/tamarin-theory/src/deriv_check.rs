// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Dynamic message-derivation check: HS `checkVariableDeducibility`
//! (Theory/Tools/MessageDerivationChecks.hs).
//!
//! For each protocol rule HS builds a probe theory with the original
//! signature, privacy kept (see [`synthesise_probe`] for why `makeFunsPublic`
//! and `replacePrivate` change nothing), and one generated rule over the
//! rule's free variables (nat re-sorted to fresh) and premise terms:
//!
//! ```text
//! rule <idx>: [ Fr(v1), ... ] --[ Generated_<idx>(v1, ...) ]-> [ Out(t1), ... ]
//! ```
//!
//! It then proves one exists-trace lemma per variable,
//! `Ex v1 ... #t0 #t1. Generated_<idx>(v1, ...) @ #t0 & KU(v) @ #t1`, within
//! `--derivcheck-timeout`, and reports each variable whose lemma finds no
//! trace.  [`prove_probe`] saturates one context per rule and reuses it for
//! all the rule's variables.

use crate::wellformedness::WfError;
use std::num::NonZeroU32;
use std::time::Duration;
use tamarin_term::lterm::{HasFrees, LNTerm, LSort, LVar};
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::vterm::var_term;

use crate::constraint::solver::context::IntrRuleCache;
use crate::fact::{
    fresh_fact, ku_fact, nat_to_fresh_var, out_fact, proto_fact, LNFact, Multiplicity,
};
use crate::formula::{lift_free, quantify_vars, LNFormula, Quantifier};
use crate::rule::{ProtoRuleE, ProtoRuleEInfo};
use crate::theory::{Theory, TraceQuantifier};

/// `--derivcheck-timeout`, with HS's three readings of its `Int` kept
/// apart instead of folded into one integer sentinel.
///
/// HS (TheoryLoader.hs) skips the check on `compare derivChecks 0 == EQ`
/// and otherwise wraps it in `timeout (1000000 * derivChecks)`; GHC's
/// `System.Timeout.timeout` treats a negative duration as "no timeout", so
/// every negative value means unbounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerivCheckTimeout {
    /// `0`: skip the checks.
    Disabled,
    /// `N > 0`: cap each per-variable probe proof at N seconds.
    Secs(NonZeroU32),
    /// `N < 0`: run the checks without a time limit.
    Unbounded,
}

impl DerivCheckTimeout {
    /// HS `defaultTheoryLoadOptions.derivationChecks`: 5 seconds.
    pub const DEFAULT: Self = match NonZeroU32::new(5) {
        Some(n) => Self::Secs(n),
        None => unreachable!(),
    };

    /// False only for [`Self::Disabled`]: whether the check runs at all.
    pub fn is_enabled(self) -> bool {
        self != Self::Disabled
    }

    /// The per-probe wall-clock cap, `None` when unbounded or disabled.
    fn per_probe(self) -> Option<Duration> {
        match self {
            Self::Secs(s) => Some(Duration::from_secs(s.get().into())),
            Self::Disabled | Self::Unbounded => None,
        }
    }
}

impl std::str::FromStr for DerivCheckTimeout {
    type Err = String;

    /// Any `i64`: `0` disables, negatives are unbounded, and positives
    /// must fit a `u32` — HS would accept larger values as a long timeout,
    /// but a positive value is never silently narrowed here.
    fn from_str(s: &str) -> Result<Self, String> {
        let n: i64 = s.parse().map_err(|e| format!("{e}"))?;
        match n {
            0 => Ok(Self::Disabled),
            n if n < 0 => Ok(Self::Unbounded),
            n => u32::try_from(n)
                .ok()
                .and_then(NonZeroU32::new)
                .map(Self::Secs)
                .ok_or_else(|| format!("{n} seconds exceeds the maximum of {}", u32::MAX)),
        }
    }
}

/// Run HS's per-variable derivability check on every rule, each probe
/// proof bounded by `timeout`.
///
/// Independent rule probes each run on a Maude process of their own: the
/// caller's, or an idle one from `pool`. Each probe is timed, so probes never
/// queue for a shared process. Warnings and errors are collected in rule
/// order. A rule's variables share one context.
///
/// `ndc_cache` is the parent theory's NDC-checked intruder cache, which HS's
/// probe theories inherit verbatim (`deleteRulesAndLemmasAndRestrictionsFromTheory`
/// keeps `_thyCache`, MessageDerivationChecks.hs); `None` assembles the cache
/// from the signature.
pub fn check_message_derivation(
    thy: &Theory,
    maude: &MaudeHandle,
    pool: Option<&std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    timeout: DerivCheckTimeout,
    ndc_cache: Option<IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> Result<Vec<WfError>, crate::prove::ProveError> {
    if !timeout.is_enabled() {
        return Ok(Vec::new());
    }
    let timeout = timeout.per_probe();
    // Each probe emits its own ordered source and intruder-rule dumps.
    let pool = pool.filter(|_| {
        !tamarin_utils::env_gate!("TAM_RS_DBG_SOURCES_DUMP")
            && !tamarin_utils::env_gate!("TAM_RS_DBG_INTR_DUMP")
    });
    let rules = thy.rules().enumerate().filter_map(|(idx, opr)| {
        if opr.rule.info.attributes.ignore_deriv_checks {
            return None;
        }
        let vars = rule_free_vars(&opr.rule);
        (!vars.is_empty()).then_some((idx, opr, vars))
    });
    let run = move |idx, name: String, rule: &ProtoRuleE, vars: Vec<LVar>, handle: MaudeHandle| {
        tamarin_utils::cancellation::check()?;
        let probe = synthesise_probe(rule, idx, &vars);
        let warnings = prove_probe(
            &probe,
            handle,
            &vars,
            timeout,
            ndc_cache.as_ref(),
            parameters,
        )?;
        Ok::<_, crate::prove::ProveError>((name, warnings))
    };
    let results = if let Some(pool) = pool.filter(|_| rayon::current_num_threads() > 1) {
        let items = rules
            .map(|(idx, opr, vars)| (idx, opr.name().to_owned(), opr.rule.clone(), vars))
            .collect();
        let primary = maude.clone();
        let pool = pool.clone();
        // Every rule is checked. The ordered map is used only so that the
        // error reported is the first failing rule's, as in the serial arm.
        tamarin_utils::parallel::try_map_until_with_helpers(
            items,
            move || {
                pool.try_take_idle_owned()
                    .map(tamarin_utils::parallel::Helper::Own)
            },
            move |lease, (idx, name, rule, vars)| {
                let maude = lease
                    .as_deref()
                    .unwrap_or(&primary)
                    .with_fresh_counter_from(0);
                run(idx, name, &rule, vars, maude)
            },
            |_| false,
        )?
    } else {
        rules
            .map(|(idx, opr, vars)| run(idx, opr.name().to_owned(), &opr.rule, vars, maude.clone()))
            .collect::<Result<Vec<_>, _>>()?
    };
    let per_rule = results
        .into_iter()
        .filter(|(_, warnings)| !warnings.is_empty())
        .collect::<Vec<_>>();
    Ok(format_deriv_report(&per_rule))
}

/// All variables that appear anywhere in a rule's premise / action /
/// conclusion terms, returned in ascending HS `LVar` Ord — idx, then sort,
/// then name (LTerm.hs) — which is the order HS `frees`/`S.toList`
/// yields them in.  EXCLUDING:
///   - `Pub`-sort vars (`$x`) — RS drops these up-front as a sound
///     optimization.  HS keeps them in `freeVars` (its `freesInThyRules`,
///     MessageDerivationChecks.hs, filters out only `LSortNode`,
///     not `LSortPub`) and generates a `KU($x)` lemma for each; but the
///     intruder knows every public name, so those lemmas are ALWAYS
///     TraceFound and the pub var is never reported.  (`deleteGlobals`,
///     MessageDerivationChecks.hs, does drop Pub vars, but only
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
/// names it `StandRule (show idx)` (MessageDerivationChecks.hs).
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
///   * `makeFunsPublic` (MessageDerivationChecks.hs;
///     definition at MessageDerivationChecks.hs) is just
///     `L.set thySignature (toSignaturePure sig)` — it sets the OPEN theory's
///     *pure* signature, which `closeTheoryWithMaude sig ...`
///     (MessageDerivationChecks.hs, CloseRule.hs)
///     immediately OVERWRITES with the ORIGINAL `SignatureWithMaude sig` (the
///     5th field of the `Theory` record).  Intruder-rule generation runs off
///     that original maude signature (`closeRuleCache ... sig ...`,
///     CloseRule.hs, called at CloseRule.hs), so
///     destructor/constructor rules see the symbols as Private exactly as in
///     the real theory.  `makeFunsPublic` is a misnomer that touches only
///     pretty/storage state, never the verdict.
///   * `replacePrivate` (MessageDerivationChecks.hs;
///     definition at MessageDerivationChecks.hs) rewrites a private
///     NoEq head on the Out terms to a Public-headed variant of the SAME
///     name/arity.  That variant is never inserted into `stFunSyms`/`stRules`,
///     so it gets no construction rule (constructionRules iterates
///     `stFunSyms`, IntruderRules.hs) and no destruction rule
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
/// `private_constructor_rules`) already matches IntruderRules.hs once the privacy flags survive.
fn synthesise_probe(rule: &ProtoRuleE, idx: usize, free_vars: &[LVar]) -> Probe {
    // HS `generateRule` (MessageDerivationChecks.hs) keeps each free
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
    // show idx) (...)` (MessageDerivationChecks.hs) — the
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
        .flat_map(|f| f.terms().iter().cloned())
        .map(|t| out_fact(rename_term_to_probe(t, &rename)))
        .collect();
    // `Rule::new` leaves `new_vars` empty, which is the `[]` HS's
    // `generateRule` passes as the probe rule's `rNewVars`
    // (MessageDerivationChecks.hs).
    let probe_rule = ProtoRuleE::new(
        ProtoRuleEInfo::standard(probe_rule_name(idx)),
        fresh_premises,
        out_concs,
        vec![action.clone()],
    );

    // Build one lemma per free var.  HS's `landFormula` gives each
    // conjoined fact its OWN timepoint (MessageDerivationChecks.hs):
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
            quantify_vars(Quantifier::Ex, &binders, gen_at.clone().and(ku_at))
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
/// in `MessageDerivationChecks.hs`) followed by `proveTheory`'s
/// per-lemma walk (`CloseRule.hs`).  The returned `undecidable`
/// lists the variable names whose lemma did NOT find a trace (= non-derivable
/// variables).
fn prove_probe(
    probe: &Probe,
    maude: MaudeHandle,
    free_vars: &[LVar],
    timeout: Option<Duration>,
    ndc_cache: Option<&IntrRuleCache>,
    parameters: crate::constraint::solver::sources::IntegerParameters,
) -> Result<Vec<String>, crate::prove::ProveError> {
    use crate::constraint::solver::context::{ProofContext, ProofContextOptions};
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
    // `None` (a negative `--derivcheck-timeout`) lifts every cap, so the
    // probes cannot inherit one from an outer guard or the env var.
    use crate::constraint::solver::search::ProofDeadlineGuard;
    let _deadline_guard = match timeout {
        Some(t) => ProofDeadlineGuard::set_ms((t.as_millis() as u64).max(1)),
        None => ProofDeadlineGuard::unbounded(),
    };

    let rules = vec![OpenProtoRule::new(probe.rule.clone())];
    // Probe contexts inherit the parent theory's checked cache verbatim
    // (HS keeps `_thyCache` on the probe theory; `closeRuleCache`
    // consumes it as-is), so the NDC tags — and the permutation — carry
    // into probe proofs without re-running the check per probe.
    let mut ctx = ProofContext::try_with_options(
        maude,
        rules,
        ProofContextOptions {
            intruder_rules: ndc_cache.cloned(),
            parameters,
            ..Default::default()
        },
    )?;
    ctx.is_exists_trace = true;
    // Probes have no `[sources]`-tagged lemmas, so no typing
    // assumptions — but `ensure_saturated()` still must run to compute
    // the source-case cache exactly as HS's `closeTheoryWithMaude`
    // does once per modified theory (CloseRule.hs).
    ctx.ensure_saturated()?;

    let mut undecidable = Vec::new();
    for (v, fm) in free_vars.iter().zip(probe.lemmas.iter()) {
        let g = formula_to_guarded(fm)
            .map_err(|error| crate::prove::ProveError::Guarded(error.to_string()))?;
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            TraceQuantifier::ExistsTrace,
            &g,
        );
        let ok = probe_with_timeout(timeout, || {
            run_proof_search(&ctx, sys, 1000)
                .map(|proof| matches!(proof.status, NodeStatus::Solved))
        })?;
        if !ok {
            // HS reports `show LVar` for the undecidable variable
            // (MessageDerivationChecks.hs); `Display
            // for LVar` is `instance Show LVar` (LTerm.hs).
            undecidable.push(v.to_string());
        }
    }

    Ok(undecidable)
}

/// Interrupt blocking Maude I/O as well as the search itself when a variable's
/// time is up. Only this variable becomes undecidable on local expiry.
fn probe_with_timeout(
    timeout: Option<Duration>,
    search: impl FnOnce() -> Result<bool, crate::prove::ProveError>,
) -> Result<bool, crate::prove::ProveError> {
    use std::sync::mpsc;
    use tamarin_utils::cancellation::{self, CancellationGuard, CancellationScope};
    let Some(duration) = timeout else {
        return search();
    };

    let scope = CancellationScope::new(cancellation::current());
    let token = scope.token();
    let start = std::time::Instant::now();
    let result = std::thread::scope(|threads| {
        let (finished, wait) = mpsc::channel::<()>();
        let timer_token = &token;
        threads.spawn(move || {
            let remaining = duration.saturating_sub(start.elapsed());
            if wait.recv_timeout(remaining) == Err(mpsc::RecvTimeoutError::Timeout) {
                timer_token.cancel();
            }
        });
        let _guard = CancellationGuard::new(Some(token.clone()));
        let result = search();
        drop(finished);
        result
    });
    cancellation::check()?;
    if token.is_cancelled() {
        Ok(false)
    } else {
        result
    }
}

fn format_deriv_report(per_rule: &[(String, Vec<String>)]) -> Vec<WfError> {
    if per_rule.is_empty() {
        return Vec::new();
    }
    // HS `reportVars` (Theory/Tools/MessageDerivationChecks.hs)
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

    fn secs(n: u32) -> DerivCheckTimeout {
        DerivCheckTimeout::Secs(NonZeroU32::new(n).expect("nonzero"))
    }

    /// The internal theory the driver hands the check.
    fn theory(src: &str) -> Theory {
        let parsed = parse_theory(src, &[]).expect("parse");
        crate::elaborate::elaborate(&parsed).expect("elaborate")
    }

    #[test]
    fn deriv_check_reports_unbound_vars_in_declaration_order() {
        let Some(path) = require_maude_path() else {
            return;
        };
        let thy = theory(
            r#"
            theory T begin
              rule Z: [] --[Use(z)]-> [Out(z)]
              rule A: [] --[Use(a)]-> [Out(a)]
              lemma trivial: "T"
            end
        "#,
        );
        let sig = thy.signature.clone();
        let primary = start_maude(&path, sig.clone());
        let helpers = std::sync::Arc::new(
            tamarin_term::maude_proc::MaudePool::new(&path, sig, 1, Default::default()).unwrap(),
        );
        let workers = rayon::ThreadPoolBuilder::new()
            .num_threads(2)
            .build()
            .unwrap();
        for pool in [None, Some(&helpers)] {
            let reports = workers
                .install(|| {
                    check_message_derivation(
                        &thy,
                        &primary,
                        pool,
                        secs(5),
                        None,
                        Default::default(),
                    )
                })
                .unwrap();
            assert_eq!(reports.len(), 1);
            assert!(reports[0].message.ends_with(
                "Rule Z: \nFailed to derive Variable(s): z\n\nRule A: \nFailed to derive Variable(s): a"
            ), "{reports:?}");
        }
    }

    #[test]
    fn probe_timeout_interrupts_blocked_work_and_preserves_request_cancellation() {
        use tamarin_utils::cancellation::{self, CancellationGuard, CancellationToken};
        let parent = CancellationToken::default();
        let _parent = CancellationGuard::new(Some(parent.clone()));
        let blocked = || {
            let (wake, wait) = std::sync::mpsc::channel();
            let _registration = cancellation::current().unwrap().on_cancel(move || {
                wake.send(()).unwrap();
            });
            wait.recv_timeout(Duration::from_secs(5))
                .expect("probe did not interrupt blocked work");
            cancellation::check()?;
            Ok(true)
        };
        assert!(!probe_with_timeout(Some(Duration::from_millis(20)), blocked).unwrap());
        assert!(probe_with_timeout(Some(Duration::from_secs(5)), || Ok(true)).unwrap());
        assert!(matches!(
            probe_with_timeout(Some(Duration::from_secs(5)), || {
                parent.cancel();
                blocked()
            }),
            Err(crate::prove::ProveError::Cancelled)
        ));
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
        let report = check_message_derivation(
            &theory(src),
            &m,
            None,
            DerivCheckTimeout::Disabled,
            None,
            Default::default(),
        )
        .expect("solver operation");
        assert!(report.is_empty(), "timeout=0 should disable the check");
    }

    /// A negative `--derivcheck-timeout` still runs the check (HS only
    /// skips on `EQ 0`), just without a per-probe cap.
    #[test]
    fn deriv_check_runs_without_a_cap_when_unbounded() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let report = check_message_derivation(
            &theory(src),
            &m,
            None,
            DerivCheckTimeout::Unbounded,
            None,
            Default::default(),
        )
        .expect("solver operation");
        assert_eq!(
            report.len(),
            1,
            "expected 'unbound' reported, got {report:?}"
        );
    }

    /// An unbounded check is never cut short by a wall-clock cap.  A 0 ms
    /// cap on this thread kills every search that inherits it the moment it
    /// starts, which would turn the derivable `x` into a reported variable;
    /// `Unbounded` must lift it so the probe runs to its trace.
    #[test]
    fn deriv_check_unbounded_is_not_killed_by_a_deadline() {
        use crate::constraint::solver::search::ProofDeadlineGuard;
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [In(x)] --[Use(x)]-> [Out(x)]
              lemma trivial: "T"
            end
        "#;
        let _instant_kill = ProofDeadlineGuard::set_ms(0);
        let report = check_message_derivation(
            &theory(src),
            &m,
            None,
            DerivCheckTimeout::Unbounded,
            None,
            Default::default(),
        )
        .expect("solver operation");
        assert!(
            report.is_empty(),
            "the unbounded probe was cut short: {report:?}"
        );
    }

    #[test]
    fn deriv_check_timeout_parses_hs_int_readings() {
        assert_eq!("0".parse(), Ok(DerivCheckTimeout::Disabled));
        assert_eq!("5".parse(), Ok(secs(5)));
        assert_eq!("-1".parse(), Ok(DerivCheckTimeout::Unbounded));
        assert_eq!("-300".parse(), Ok(DerivCheckTimeout::Unbounded));
        assert_eq!("4294967295".parse(), Ok(secs(u32::MAX)));
        assert!("4294967296".parse::<DerivCheckTimeout>().is_err());
        assert!("five".parse::<DerivCheckTimeout>().is_err());
        assert_eq!(DerivCheckTimeout::DEFAULT, secs(5));
    }

    /// The free variables come back in ascending `LVar` Ord — index first,
    /// then sort, then name (LTerm.hs) — which is the order HS's
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
}
