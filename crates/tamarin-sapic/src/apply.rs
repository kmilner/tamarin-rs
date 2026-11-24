// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Wiring: run the SAPIC translation and inject the generated rules,
//! restrictions and heuristic into the theory.
//!
//! Mirrors the tail of HS `translate` (sapic/src/Sapic.hs):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
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

    Ok(wf_report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::rule::ProtoRuleName;
    use tamarin_theory::theory::TheoryItem;

    /// The `else` arm of a pattern `let` carries the restriction
    /// `∀ y w. (<y, w> = z) ⇒ ⊥` (Basetranslation.hs), so the
    /// translated theory gets one generated `Restr_letywz_2_1_1` restriction
    /// plus the action that reaches it on rule `letywz_2_1`.
    const LET_ELSE: &str = "theory T begin\n\
        process:\n\
          in(z); let <y, w> = z in out(y) else out('n')\n\
        end";

    /// The generated restriction and the appended action land in the theory,
    /// the restriction immediately before its rule (HS adds the expanded
    /// restrictions and then the rule, Theory/Text/Parser.hs), and the
    /// rule keeps the premises, conclusions and new variables the translation
    /// built — the lift only appends actions (`addActions`,
    /// Theory/Text/Parser.hs).
    #[test]
    fn generated_rule_carries_its_restrict_formulas() {
        let parsed = tamarin_parser::parse_theory(LET_ELSE, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();

        // The same translation `apply_sapic` runs, so the rule it injects can
        // be compared against the values the translation produced.
        let maude_sig = thy.signature.clone();
        let mut typed_thy = thy.clone();
        crate::type_theory::type_theory(&mut typed_thy).unwrap();
        let typed = typed_thy.processes().next().unwrap().clone();
        let translation = translate(
            &typed,
            false,
            &maude_sig.st_rules,
            &[],
            TranslateOptions::default(),
        )
        .unwrap();
        let translated = translation
            .rules
            .iter()
            .find(|r| !r.info.restrictions.is_empty())
            .expect("no generated rule carries a `_restrict` formula");

        apply_sapic(&mut thy, false).unwrap();

        let restr_pos = thy
            .items
            .iter()
            .position(|i| matches!(i, TheoryItem::Restriction(r) if r.name == "Restr_letywz_2_1_1"))
            .expect("restriction not generated");
        let rule_pos = thy
            .items
            .iter()
            .position(|i| {
                matches!(i, TheoryItem::Rule(r)
                    if r.rule.info.name == ProtoRuleName::Stand("letywz_2_1"))
            })
            .expect("rule missing");
        assert_eq!(restr_pos + 1, rule_pos, "restriction must precede rule");
        let TheoryItem::Restriction(er) = &thy.items[restr_pos] else {
            panic!("item at {restr_pos} is not the restriction");
        };
        assert_eq!(er.original_formula.as_ref(), Some(&er.formula));

        let TheoryItem::Rule(er) = &thy.items[rule_pos] else {
            panic!("item at {rule_pos} is not the rule");
        };
        let injected = &er.rule;
        assert_eq!(injected.premises, translated.premises);
        assert_eq!(injected.conclusions, translated.conclusions);
        assert_eq!(injected.new_vars, translated.new_vars);
        assert_eq!(
            injected.actions.len(),
            translated.actions.len() + 1,
            "the lift appends exactly the generated action"
        );
        assert_eq!(
            injected.actions[..translated.actions.len()],
            translated.actions[..]
        );
        assert_eq!(
            tamarin_theory::fact::show_fact_tag(&injected.actions[translated.actions.len()].tag),
            "Restr_letywz_2_1_1"
        );
        assert_eq!(injected.info.restrictions, translated.info.restrictions);
    }

    /// Under progress, path compression absorbs the `_restrict` step into
    /// `Init`.  `mergeInfo` keeps the first name and concatenates the
    /// `_preRestriction` lists (Compression.hs), so the oracle still emits
    /// `Restr_Init_1` and the `Restr_Init_1( )` action on `Init`.
    #[test]
    fn compression_keeps_the_absorbed_rule_restriction() {
        let src = "theory T begin\n\
            options: translation-progress\n\
            process:\n\
              [] --[ _restrict(F) ]-> []; event E()\n\
            end";
        let parsed = tamarin_parser::parse_theory(src, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        apply_sapic(&mut thy, false).unwrap();
        assert!(thy.lookup_restriction("Restr_Init_1").is_some());
        let init = thy
            .rules()
            .find(|r| r.rule.info.name == ProtoRuleName::Stand("Init"))
            .expect("rule missing");
        assert!(init
            .rule
            .actions
            .iter()
            .any(|f| tamarin_theory::fact::show_fact_tag(&f.tag) == "Restr_Init_1"));
    }

    /// Haskell types the whole theory before translating (`typeTheory >=>
    /// translate`), so the function types an `equivLemma` process teaches
    /// reach the top-level process: the oracle names the output rule
    /// `outfclol_0_1`, with `process="out(f(c.1:lol));"`.
    #[test]
    fn earlier_processes_type_the_translated_process() {
        let src = "theory T begin\n\
            functions: f/1\n\
            equivLemma: (new a:lol; out(f(a))) (new b; out(f(b)))\n\
            process:\n\
              new c; out(f(c))\n\
            end";
        let parsed = tamarin_parser::parse_theory(src, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        apply_sapic(&mut thy, false).unwrap();
        assert!(
            thy.rules()
                .any(|r| r.rule.info.name == ProtoRuleName::Stand("outfclol_0_1")),
            "the top-level process was typed without the equivLemma's types"
        );
    }

    /// Translation and `_restrict` expansion exceptions reach the user as
    /// their bare `show`: the oracle prints `undefined predicate Foo/1` here.
    #[test]
    fn restrict_expansion_errors_are_reported_bare() {
        let src = "theory T begin\nprocess:\n  in(x); if Foo(x) then out('a')\nend";
        let parsed = tamarin_parser::parse_theory(src, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        let err = apply_sapic(&mut thy, false).unwrap_err();
        assert_eq!(err.message, "undefined predicate Foo/1");
    }

    /// `liftedAddRestriction` and `liftedAddProtoRule` (Theory/Text/Parser.hs)
    /// reject a generated restriction whose name the user already declared,
    /// as the oracle does for both of these theories.
    #[test]
    fn generated_restrictions_reject_declared_names() {
        for (body, name) in [
            (
                "restriction single_session: \"T\"\nprocess: 0",
                "single_session",
            ),
            (
                "restriction Restr_Init_1: \"T\"\noptions: translation-progress\n\
                 process: [] --[ _restrict(F) ]-> []; event E()",
                "Restr_Init_1",
            ),
        ] {
            let src = format!("theory T begin\n{body}\nend");
            let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            let err = apply_sapic(&mut thy, false).unwrap_err();
            assert_eq!(err.message, format!("duplicate restriction: {name}"));
        }
    }

    /// A `macros:` declaration whose call sits in the process body, so the
    /// rules the translation generates carry it.
    const MACRO_PROCESS: &str = "theory T begin\n\
        macros: tag(x) = <'t', x>\n\
        process:\n\
          in(z); out(tag(z))\n\
        end";

    /// `closeTheoryItem` applies the theory's macros to every rule of the
    /// TRANSLATED theory, the generated ones included (CloseRule.hs),
    /// and `closeProtoRule` narrows `applyMacroInRule macros ruE` while
    /// keeping the unexpanded `ruE` as the `cprRuleE` half
    /// (lib/theory/src/Rule.hs).
    #[test]
    fn generated_rules_carry_the_macro_applied_rule_beside_the_call() {
        let parsed = tamarin_parser::parse_theory(MACRO_PROCESS, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        apply_sapic(&mut thy, false).unwrap();

        let shown = |r: &tamarin_theory::rule::ProtoRuleE| {
            r.premises
                .iter()
                .chain(&r.actions)
                .chain(&r.conclusions)
                .map(|f| tamarin_theory::fact::pretty_lnfact(f).render())
                .collect::<Vec<_>>()
                .join(" ")
        };
        let mut with_call = 0;
        for r in thy.rules() {
            let call = shown(r.rule_e());
            let applied = shown(&r.rule);
            if !call.contains("tag(") {
                assert!(
                    !applied.contains("<'t', "),
                    "a rule applies a macro its `cprRuleE` never called: {applied}"
                );
                continue;
            }
            with_call += 1;
            assert!(
                applied.contains("<'t', ") && !applied.contains("tag("),
                "the macro reached the closed rule unapplied: {applied}"
            );
        }
        assert!(
            with_call > 0,
            "no generated rule kept the process's macro call"
        );
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
        ] {
            let src = format!("theory T begin\n{body}\nend");
            let parsed = tamarin_parser::parse_theory(&src, &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            let err = apply_sapic(&mut thy, false).unwrap_err();
            assert_eq!(err.message, want, "{body}");
        }
    }
}
