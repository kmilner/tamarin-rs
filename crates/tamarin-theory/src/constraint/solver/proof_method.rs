// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Constraint.Solver.ProofMethod`: the small-step
//! interface to the constraint solver. `exec_proof_method` maps a method and
//! a system to its named cases, or `None` when the method does not apply.

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::contradictions::{contradictions, Contradiction};
use crate::constraint::system::System;

/// Each case in a proof tree gets a unique name.
pub type CaseName = String;

/// Outcome of a finished proof method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Result {
    /// A dependency graph was found that satisfies the system.
    Solved,
    /// A contradiction could be derived.
    Contradictory(Option<Contradiction>),
    /// Unresolved constraints prevent a trace, or no proof method applies.
    Unfinishable,
}

/// One small-step transformation of a sequent.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofMethod {
    Sorry(Option<String>),
    Simplify,
    SolveGoal(Goal),
    Induction,
    Finished(Result),
    Invalidated,
}

/// `isFinished`: returns the appropriate `Result` if the system is in
/// a terminal state — solved, contradictory, or unfinishable.
pub fn is_finished(
    ctx: &ProofContext,
    sys: &System,
) -> std::result::Result<Option<Result>, crate::prove::ProveError> {
    if sys.is_initial() {
        return Ok(None);
    }
    #[cfg(test)]
    super::cancellation_tests::checkpoint(ctx, super::cancellation_tests::Work::Terminal);
    let cs = contradictions(ctx, sys)?;
    if let Some(c) = cs.into_iter().next() {
        return Ok(Some(Result::Contradictory(Some(c))));
    }
    // HS `isFinished` (ProofMethod.hs) tests the filtered `openGoals`.
    use crate::constraint::solver::goals::open_goals;
    if !open_goals(sys).is_empty() {
        return Ok(None);
    }
    // Haskell only forces the witness check once no open goals remain.
    Ok(Some(
        if super::subterm_witness::finished_subterms(&ctx.maude.maude_sig(), sys) {
            Result::Solved
        } else {
            Result::Unfinishable
        },
    ))
}

/// Recognize exhausted states independently of heuristic ranking. Only use
/// this when checking a saved UNFINISHABLE step or after method exhaustion.
pub fn is_finished_or_stuck(
    ctx: &ProofContext,
    sys: &System,
) -> std::result::Result<Option<Result>, crate::prove::ProveError> {
    if let Some(result) = is_finished(ctx, sys)? {
        return Ok(Some(result));
    }
    if !crate::constraint::solver::goals::open_goals(sys).is_empty()
        || exec_proof_method(ctx, &ProofMethod::Simplify, sys)?.is_some()
        || (sys.is_initial() && exec_proof_method(ctx, &ProofMethod::Induction, sys)?.is_some())
    {
        return Ok(None);
    }
    // A timed-out method has no cases but is not evidence of exhaustion.
    Ok((!crate::constraint::solver::search::deadline_reached()).then_some(Result::Unfinishable))
}

/// Applicability as the web UI's method list forces it: HS evaluates
/// `execProofMethod` only to `Just`/`Nothing`, and the `SolveGoal` arm is
/// always `Just` with its case fan-out left unevaluated. Only `Simplify` and
/// `Induction` can be dropped there, so only they are executed.
pub fn is_applicable_for_display(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> std::result::Result<bool, crate::prove::ProveError> {
    Ok(match method {
        ProofMethod::SolveGoal(_) => true,
        ProofMethod::Simplify | ProofMethod::Induction => {
            exec_proof_method(ctx, method, sys)?.is_some()
        }
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => true,
        ProofMethod::Invalidated => false,
    })
}

/// HS `uniqueListBy (comparing fst) id distinguish` (ProofMethod.hs): a
/// unique name stays bare; each of the `n` cases sharing a name gets its
/// running index `i`, as `show i` for an empty name and otherwise as
/// `<name>_case_<i>` zero-padded to the width of `show n`. Order is kept.
// Counter maps are lookup-only; output order follows `cases`.
#[allow(clippy::disallowed_types)]
fn distinguish_case_names(cases: Vec<(String, System)>) -> Vec<(String, System)> {
    use std::collections::HashMap;
    let mut counts: HashMap<String, usize> = HashMap::new();
    for (name, _) in &cases {
        *counts.entry(name.clone()).or_default() += 1;
    }
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut out = Vec::with_capacity(cases.len());
    for (name, s) in cases.into_iter() {
        let total = counts[&name];
        let key = if total == 1 {
            name
        } else {
            let n = seen.entry(name.clone()).or_default();
            *n += 1;
            if name.is_empty() {
                n.to_string()
            } else {
                let width = total.to_string().len();
                format!("{}_case_{:0width$}", name, *n, width = width)
            }
        };
        out.push((key, s));
    }
    out
}

/// HS `process` (ProofMethod.hs) applied to the systems `runReduction (m <*
/// simplifySystem)` returned: drop the branches whose equation store is
/// false (the Disj `mzero`s), `cleanup` the rest, `removeRedundantCases ctxt
/// [] snd`, then name them with [`distinguish_case_names`].
fn process(ctx: &ProofContext, cases: Vec<(String, System)>) -> Vec<(String, System)> {
    let cleaned = cases
        .into_iter()
        .filter(|(_, s)| !s.eq_store().is_false())
        .map(|(name, s)| (name, s.cleanup()))
        .collect();
    let msig = ctx.maude.maude_sig();
    let deduped = crate::constraint::solver::sources::remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &std::collections::BTreeSet::new(),
        |case: &(String, System)| &case.1,
        cleaned,
    );
    distinguish_case_names(deduped)
}

/// HS `execProofMethod` (ProofMethod.hs). Cases come back in production
/// order; callers sort them by name, as Haskell's `M.fromListWith` does.
pub fn exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> std::result::Result<Option<Vec<(CaseName, System)>>, crate::prove::ProveError> {
    use crate::constraint::solver::reduction::{GoalCases, Reduction};

    crate::constraint::solver::search::check_cancelled()?;
    // Rust-only deadline guard: past the deadline no method applies, which
    // bounds the remaining work by the proof depth.
    if crate::constraint::solver::search::deadline_reached() {
        return Ok(None);
    }

    // `runReduction ... (avoid sys)`: every step's FreshT counter starts at
    // `avoid sys`.
    let avoid = crate::constraint::solver::reduction::avoid_fresh_state(sys);
    ctx.maude.reset_counter_to(avoid);

    let result = match method {
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => Some(Vec::new()),
        ProofMethod::Invalidated => None,
        ProofMethod::Simplify => {
            // `process (return "")`: simplification may fan out (DisjT), and
            // each branch becomes a case.
            let case_systems =
                crate::constraint::solver::simplify::simplify_system_with_fanout(ctx, sys.clone())?;
            // Shortcut for a simplification that changed nothing: `process`
            // would yield no case (false store) or the cleaned input.
            if case_systems.len() == 1 && case_systems[0] == *sys {
                return Ok(sys.eq_store().is_false().then(Vec::new));
            }
            let cases = process(
                ctx,
                case_systems
                    .into_iter()
                    .map(|s| (String::new(), s))
                    .collect(),
            );
            // A single case equal to the cleaned input means the method
            // does not apply. No case at all is a successful leaf.
            if let [(_, single)] = cases.as_slice()
                && *single == sys.clone().cleanup()
            {
                return Ok(None);
            }
            Some(cases)
        }
        ProofMethod::SolveGoal(g) => {
            // The node-driving search/replay/interactive caller emits the
            // state; record the selected goal without duplicating that line.
            crate::constraint::solver::trace::trace_pick(g);
            let mut r = Reduction::new(ctx, sys.clone());
            let outcome = crate::constraint::solver::goals::dispatch_solve_goal(&mut r, g)?;
            let adopted_counter = r.maude.fresh_counter_peek();
            // `process (solve goal)`: each goal case continues with its own
            // fresh counter through `simplifySystem`, which may fan out.
            let cases: Vec<(String, System, u64)> = match outcome {
                GoalCases::LinearNamed(name) => vec![(name, r.sys, adopted_counter)],
                GoalCases::Cases(cases) => cases
                    .into_iter()
                    .map(|branch| (branch.name, branch.sys, branch.counter))
                    .collect(),
                GoalCases::Contradictory => return Ok(Some(Vec::new())),
            };
            let mut simplified = Vec::new();
            for (name, sys, seed) in cases {
                for s in crate::constraint::solver::simplify::simplify_system_with_fanout_seeded(
                    ctx, sys, seed,
                )? {
                    simplified.push((name.clone(), s));
                }
            }
            Some(process(ctx, simplified))
        }
        ProofMethod::Induction => {
            // Search and replay must enforce the same applicability checks.
            if !sys.nodes.is_empty()
                || !sys.solved_formulas.is_empty()
                || !sys.goals.is_empty()
                || sys.formulas.len() != 1
            {
                return Ok(None);
            }
            // Take the first formula and try `ginduct`.
            let Some(fm) = sys.formulas.first().cloned() else {
                return Ok(None);
            };
            let (base, step) = match crate::guarded::ginduct(&fm) {
                Ok(p) => p,
                Err(_) => return Ok(None),
            };
            // `process . induction`: each case replaces the formula store
            // (`setM sFormulas`, not `insertFormula`, so no goals are created
            // before simplification) and is simplified with fan-out.
            let mut named: Vec<(String, System)> = Vec::new();
            for (name, fm_case) in [("empty_trace", base), ("non_empty_trace", step)] {
                let mut case_sys = sys.clone();
                case_sys.clear_formulas();
                case_sys.insert_open_formula(fm_case);
                for s in
                    crate::constraint::solver::simplify::simplify_system_with_fanout(ctx, case_sys)?
                {
                    named.push((name.to_string(), s));
                }
            }
            Some(process(ctx, named))
        }
    };
    Ok(result)
}

/// Validate a stored terminal marker by result kind. Contradiction reasons
/// are runtime details; an UNFINISHABLE marker additionally checks exhaustion.
pub(crate) fn finished_step_is_valid(
    ctx: &ProofContext,
    sys: &System,
    expected: &Result,
) -> std::result::Result<bool, crate::prove::ProveError> {
    let actual = if matches!(expected, Result::Unfinishable) {
        is_finished_or_stuck(ctx, sys)?
    } else {
        is_finished(ctx, sys)?
    };
    Ok(actual.is_some_and(|actual| same_kind(expected, &actual)))
}

fn same_kind(a: &Result, b: &Result) -> bool {
    matches!(
        (a, b),
        (Result::Solved, Result::Solved)
            | (Result::Unfinishable, Result::Unfinishable)
            | (Result::Contradictory(_), Result::Contradictory(_))
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    use tamarin_test_support::require_maude_path;

    /// The result is `None` only when [`maude_path`] resolves nothing.  That
    /// case is the documented `TAM_ALLOW_NO_MAUDE` skip.  A maude that
    /// resolves but does not start is the same misconfiguration as a dangling
    /// `MAUDE_PATH`.  An `.ok()?` here would silently skip every maude-backed
    /// test in this file.
    fn ctx() -> Option<ProofContext> {
        let path = require_maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig())
            .unwrap_or_else(|e| {
                panic!(
                    "maude at {path} failed to start: {e:?} — every maude-backed \
                     test here would otherwise skip silently"
                )
            });
        Some(ProofContext::new(h, Vec::new()))
    }

    #[test]
    fn empty_system_is_not_finished() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let s = System::empty();
        assert!(
            is_finished(&ctx, &s).unwrap().is_none(),
            "initial system shouldn't be finished"
        );
    }

    #[test]
    fn solved_when_no_goals_and_subterms_done() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut s = System::empty();
        // Force the system out of its initial state by recording a
        // solved formula (Haskell `isInitialSystem` checks
        // `solved_formulas.is_empty() && no_gfalse`; setting one to
        // gtrue makes the system non-initial).
        s.solved_formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gtrue()));
        // Add a placeholder node too so the structure is non-trivial.
        let nid = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
        use crate::rule::{
            IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst, RuleAttributes,
            RuleInfo,
        };
        let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Test"),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule: RuleACInst = Rule::new(info, Vec::new(), Vec::new(), Vec::new());
        s.add_node(nid, rule);
        match is_finished(&ctx, &s).unwrap() {
            Some(Result::Solved) => {}
            r => panic!("expected Solved, got {:?}", r),
        }
    }

    #[test]
    fn residual_subterm_without_a_public_witness_is_unfinishable() {
        use tamarin_term::lterm::{fresh_term, pub_term, LSort, LVar};
        use tamarin_term::vterm::var_term;
        let Some(ctx) = ctx() else { return };
        for (small, expected) in [
            (fresh_term("secret"), Result::Unfinishable),
            (pub_term("public"), Result::Solved),
        ] {
            let mut sys = System::empty();
            sys.solved_formulas_mut()
                .push(std::sync::Arc::new(crate::guarded::gtrue()));
            sys.subterm_store_mut()
                .add(small, var_term(LVar::new("x", LSort::Msg, 0)));
            assert_eq!(is_finished(&ctx, &sys).unwrap(), Some(expected));
        }
    }

    #[test]
    fn gfalse_formula_is_contradictory_not_unfinishable() {
        // HS `isFinished` (ProofMethod.hs) routes any
        // contradiction — including `gfalse ∈ sFormulas`
        // (`FormulasFalse`) — to `Contradictory`, BEFORE the
        // `null ogs && not stFinished => Unfinishable` arm.  A negated
        // false lemma collapses to `gfalse`, closes the branch as
        // Contradictory, and the prover reports `falsified - found
        // trace` (verified against the v1.13.0 binary on a minimal
        // `Setup() @ i ==> F` lemma).  This pins that routing so the
        // gfalse-in-formulas path can never be misread as Unfinishable.
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let mut s = System::empty();
        // gfalse in formulas makes the system non-initial AND yields a
        // `FormulasFalse` contradiction.
        s.formulas_mut()
            .push(std::sync::Arc::new(crate::guarded::gfalse()));
        match is_finished(&ctx, &s).unwrap() {
            Some(Result::Contradictory(Some(Contradiction::FormulasFalse))) => {}
            r => panic!("expected Contradictory(FormulasFalse), got {:?}", r),
        }
    }

    #[test]
    fn distinguish_numbers_empty_names_without_a_prefix() {
        let names = |cases: &[&str]| {
            distinguish_case_names(
                cases
                    .iter()
                    .map(|n| (n.to_string(), System::empty()))
                    .collect(),
            )
            .into_iter()
            .map(|(n, _)| n)
            .collect::<Vec<_>>()
        };
        assert_eq!(names(&["", "R", ""]), ["1", "R", "2"]);
        assert_eq!(names(&[""]), [""]);
        let ten = names(&["R"; 10]);
        assert_eq!(
            (ten[0].as_str(), ten[9].as_str()),
            ("R_case_01", "R_case_10")
        );
    }

    #[test]
    fn exec_sorry_is_empty_cases() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let s = System::empty();
        let cases = exec_proof_method(&ctx, &ProofMethod::Sorry(None), &s)
            .unwrap()
            .unwrap();
        assert!(cases.is_empty());
    }

    #[test]
    fn induction_on_open_formula_returns_none() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        let s = System::empty();
        // No formula → ginduct can't run.
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s).unwrap();
        assert!(r.is_none());
    }

    #[test]
    fn induction_creates_two_cases() {
        let ctx = match ctx() {
            Some(c) => c,
            None => return,
        };
        // Build a closed action-bearing formula:
        //   Ex k #i. Setup(k) @ #i
        // tracked as a guarded GGuarded::Ex with a single Action guard.
        use crate::atom::ProtoAtom;
        use crate::fact::{proto_fact, Multiplicity};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::var_term;
        let k = LVar::new("k", LSort::Msg, 0);
        let i = LVar::new("i", LSort::Node, 0);
        let action_atom = ProtoAtom::Action(
            var_term(i),
            proto_fact(Multiplicity::Linear, "Setup", vec![var_term(k)]),
        );
        let body = crate::guarded::Guarded::Conj(Vec::new().into());
        // Build with close_guarded so the binder's `k` and `i` are
        // properly substituted to `Bound` in the guard atom.
        let fm = crate::guarded::close_guarded(
            crate::formula::Quantifier::Ex,
            vec![k, i],
            vec![action_atom],
            body,
        );
        let mut s = System::empty();
        s.formulas_mut().push(std::sync::Arc::new(fm));
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s)
            .expect("source materialisation")
            .expect("induction");
        // Two case names: empty_trace and non_empty_trace.
        assert_eq!(r.len(), 2);
        assert!(r.iter().any(|(n, _)| n == "empty_trace"));
        assert!(r.iter().any(|(n, _)| n == "non_empty_trace"));
    }
}
