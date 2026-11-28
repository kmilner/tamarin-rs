// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Wiring: run the SAPIC translation and inject the generated rules,
//! restrictions and heuristic into the theory.
//!
//! Mirrors the tail of HS `translate` (sapic/src/Sapic.hs):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
//!   - `setforcedInjectiveFacts` under the state-channel optimisation
//!
//! HS's final `_thyIsSapic = True` has no stored counterpart here: the theory
//! derives the translation gate from its top-level process items.
//!
//! HS adds these items to the OPEN theory and applies the theory's macros to
//! every rule and restriction at close time (`closeTheoryItem`,
//! CloseRule.hs).  The port applies macros while elaborating, so the
//! injection applies them here too, recording the pre-macro rule as the
//! `cprRuleE` half `closeProtoRule` keeps (lib/theory/src/Rule.hs).

use tamarin_theory::wellformedness::WfError;

use tamarin_theory::elaborate::{add_restriction, lifted_add_proto_rule, ElabError};
use tamarin_theory::fact::{FactTag, Multiplicity};
use tamarin_theory::predicate::Predicate;
use tamarin_theory::restriction::apply_macro_in_restriction;
use tamarin_theory::theory::{LNMacro, Theory};

use crate::translate::{needs_in_ev_res, translate, TranslateOptions};

/// HS `Sapic.checkWellformedness` (Warnings.hs) over every top-level process
/// before typing, as `translateTheory` (TheoryLoader.hs) computes it for every
/// output module.
pub fn sapic_pre_report(thy: &Theory) -> Vec<WfError> {
    thy.processes()
        .flat_map(crate::warnings::check_wellformedness)
        .collect()
}

/// HS `Sapic.typeTheory >=> Sapic.translate` (TheoryLoader.hs
/// `processOpenTheory`): type every process of the theory, then translate the
/// single top-level process.  `translate` (sapic/src/Sapic.hs) throws
/// `MoreThanOneProcess` for several, and `ReliableTransmissionButNoProcess`
/// for none under `builtins: reliable-channel`.
///
/// `user_set_heuristic` is true when the source or CLI already set a heuristic,
/// so `addHeuristic` adds no `p`.  Returns the [`sapic_pre_report`], which the
/// caller puts in front of the wellformedness report (`preReport ++
/// postReport`, TheoryLoader.hs).
pub fn apply_sapic(thy: &mut Theory, user_set_heuristic: bool) -> Result<Vec<WfError>, ElabError> {
    // The warnings read the untyped process; translation proceeds regardless.
    let wf_report = sapic_pre_report(thy);
    crate::type_theory::type_theory(thy)?;
    let trans_reliable = thy.has_signature_builtin("reliable-channel");
    let processes: Vec<_> = thy.processes().take(2).collect();
    let typed = match processes[..] {
        [p] => p,
        [] if trans_reliable => {
            return Err(ElabError {
                message: "The builtin support for reliable channels currently only affects \
                          the process calculus, but you have not specified a top-level \
                          process. Please remove \"builtins: reliable-channel\" to proceed."
                    .to_string(),
            });
        }
        [] => return Ok(wf_report),
        _ => {
            return Err(ElabError {
                message: "More than one top-level process is defined. This is not supported \
                          by the translation."
                    .to_string(),
            });
        }
    };
    let maude_sig = &thy.signature;

    let needs_in_ev = needs_in_ev_res(thy);
    let st_rules = &maude_sig.st_rules;
    let opts = TranslateOptions {
        trans_progress: thy.options.trans_progress(),
        trans_reliable,
        async_channels: thy.options.asynchronous_channels(),
        compress_events: thy.options.compress_events(),
        trans_report: thy.has_signature_builtin("locations-report"),
        state_channel_opt: thy.options.state_channel_opt(),
    };
    // Process lets and generated rules/restrictions use the same macro
    // declarations (`closeTheoryItem`, CloseRule.hs).
    let macros: Vec<LNMacro> = thy.macros().cloned().collect();
    // A translation exception escapes to GHC's runtime, which prints its
    // `show` alone after `tamarin-prover: `.
    let translation = translate(typed, needs_in_ev, st_rules, &macros, opts)
        .map_err(|message| ElabError { message })?;

    // `foldM liftedAddProtoRule th` over the generated rules.  HS `addActions`
    // rebuilds `rActs` alone (Theory/Text/Parser.hs), so each rule keeps the
    // `_preRestriction` formulas `toRule` gave it (sapic/src/Sapic/Facts.hs)
    // and the `rNewVars` the translation computed.  A user rule named like a
    // generated one, e.g. `rule Init` beside a `process:`, is a
    // `duplicate rule` unless the open rules are equal.
    let predicates: Vec<Predicate> = thy.predicates().cloned().collect();
    for rule in translation.rules {
        lifted_add_proto_rule(thy, rule, Vec::new(), &predicates, &macros, true)?;
    }

    // `foldM liftedAddRestriction th1 rest` over the global restrictions
    // (set_in/set_notin, predicate_eq/not_eq, single_session, ...).
    for restr in translation.restrictions {
        add_restriction(thy, apply_macro_in_restriction(&macros, restr))?;
    }

    // `addHeuristic [SapicRanking]` unless a heuristic is already set
    // (sapic/src/Sapic.hs).  `SapicRanking` renders as `p`
    // and drives the prover's goal ranking.
    if !user_set_heuristic && thy.heuristic.is_empty() {
        thy.heuristic
            .push(tamarin_theory::constraint::solver::goals::GoalRanking::Sapic);
    }

    // For the state optimisation, force `pureStateFactTag` and
    // `pureStateLockFactTag` (Facts.hs) to be injective (sapic/src/Sapic.hs).
    if thy.options.state_channel_opt() {
        thy.options.forced_injective_facts = [
            FactTag::Proto(Multiplicity::Linear, "L_PureState", 2),
            FactTag::Proto(Multiplicity::Linear, "L_CellLocked", 2),
        ]
        .into();
    }

    Ok(wf_report)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `translation-state-optimisation` forces the pure-state facts injective
    /// only through a translated process: `translate` returns an MSR theory
    /// unchanged (sapic/src/Sapic.hs).
    #[test]
    fn state_optimisation_forces_injective_facts_only_with_a_process() {
        let forced = |body: &str| {
            let src =
                format!("theory T begin\noptions: translation-state-optimisation\n{body}\nend");
            let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            apply_sapic(&mut thy, false).unwrap();
            thy.options
                .forced_injective_facts
                .iter()
                .map(tamarin_theory::fact::show_fact_tag)
                .collect::<Vec<_>>()
        };
        assert!(forced("rule A: [Fr(~k)] --> [L_PureState(~k, 'a')]").is_empty());
        assert_eq!(forced("process:\n  0"), ["L_CellLocked", "L_PureState"]);
    }

    /// The `tamarin-prover: <show e>` texts of the exceptions SAPIC typing
    /// and translation throw, as the pinned oracle (a75fec7f) prints them.
    #[test]
    fn translation_exceptions_print_as_haskell_shows_them() {
        for (body, want) in [
            (
                "process:\nnew k; out(<k, x>)",
                "Process not well-formed: The variable(s) x are not bound.\n  out(<k.1, x>)",
            ),
            (
                "functions: f(lol):lol, g(foo):foo\nprocess:\nnew k:lol; out(g(f(k)))",
                "Process not well-formed: Typing error: expected term f(k.1) to have \
                 Just \"foo\" but actual type is Just \"lol\".\n  out(g(f(k.1)))",
            ),
            (
                "process:\nlock 'a'; !(out('b'))",
                "Process not well-formed: Process contains lock that extends over \
                 replication which is not allowed.\n  !(out('b'))",
            ),
            (
                "builtins: reliable-channel\nprocess:\nout('d', 'a')",
                "If reliable channels are activated, processes should only contain \
                 in('r',m), out('r',m), in('c',m) or out('c',m) for communication.",
            ),
            (
                "builtins: reliable-channel\nrule A: [] --> []",
                "The builtin support for reliable channels currently only affects the \
                 process calculus, but you have not specified a top-level process. \
                 Please remove \"builtins: reliable-channel\" to proceed.",
            ),
            (
                "process:\nout('a')\nprocess:\nout('b')",
                "More than one top-level process is defined. This is not supported by \
                 the translation.",
            ),
            // `zip vars ts` drops the formal with no argument, which typing
            // then finds unbound.
            (
                "let P(x, y) = out(<x, y>)\nprocess:\nnew k; P(k)",
                "Process not well-formed: The variable(s) y are not bound.\n  out(<k.1, y>)",
            ),
            (
                "process:\nin(x); if a = b then out(x)",
                "Process not well-formed: The variable(s) a are not bound.\n  \
                 if a=b then\n      out(x.1)",
            ),
            (
                "process:\nlock 's'; (0 | 0)",
                "Process not well-formed: Process contains lock that extends over \
                 a parallel which is not allowed.\n  0 | 0",
            ),
            (
                "functions: d/2 [AC,destructor]\nprocess:\nlet x=d('a','b') in event Done(x)",
                "This feature is not implemented yet. Sorry! SAPIC does not support AC \
                 destructor calls.",
            ),
            (
                "functions: d/2 [AC,destructor], c/1\nprocess:\n\
                 let x=c(d('a','b')) in event Done(x)",
                "This feature is not implemented yet. Sorry! SAPIC does not support AC \
                 destructor calls.",
            ),
            (
                "process:\nlet x = 'v' in in(=x); 0",
                "CapturedEx CapturedIn x.1",
            ),
            // `_restrict` expansion errors reach the user as their bare show.
            (
                "process:\nin(x); if Foo(x) then out('a')",
                "undefined predicate Foo/1",
            ),
            // `liftedAddRestriction` and `liftedAddProtoRule`
            // (Theory/Text/Parser.hs) reject a generated restriction whose
            // name the user already declared.
            (
                "restriction single_session: \"T\"\nprocess: 0",
                "duplicate restriction: single_session",
            ),
            (
                "restriction Restr_Init_1: \"T\"\noptions: translation-progress\n\
                 process: [] --[ _restrict(F) ]-> []; event E()",
                "duplicate restriction: Restr_Init_1",
            ),
        ] {
            let src = format!("theory T begin\n{body}\nend");
            let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            let err = apply_sapic(&mut thy, false).unwrap_err();
            assert_eq!(err.message, want, "{body}");
        }
    }
}
