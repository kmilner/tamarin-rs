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

use std::collections::BTreeSet;
use tamarin_theory::fact::fact_tag_name;
use tamarin_theory::sapic::{PlainProcess, Process, SapicAction};
use tamarin_theory::wellformedness::WfError;

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::formula::LNFormula;
use tamarin_theory::predicate::{expand_formula, Predicate};
use tamarin_theory::restriction::{apply_macro_in_restriction, Restriction};
use tamarin_theory::rule::{apply_macro_in_rule, ProtoRuleName};
use tamarin_theory::rule_restriction::rule_restrictions;
use tamarin_theory::theory::{LNMacro, OpenProtoRule, Theory, TheoryItem};

use crate::translate::{needs_in_ev_res, translate, TranslateOptions};
use crate::typing::{collect_user_fun_typings, type_and_rename_process};

/// HS `Sapic.checkWellformedness` (Warnings.hs) over the UNTRANSLATED
/// theory: warn-check the single top-level process.  The process arrives with
/// its `P(args)` calls already inlined (HS inlines at parse time) but BEFORE
/// `typeTheory` / `renameUnique`, so two binders sharing a name (e.g.
/// `new x; new x`) are still alpha-identical and detected as captured.
///
/// `translateTheory` computes this report on the open theory before any
/// translation step (TheoryLoader.hs), so both the
/// translating path ([`apply_sapic`]) and the `-m spthy` / `-m spthytyped`
/// paths that skip translation report exactly these warnings.
///
/// Empty when the theory carries no top-level process.
pub fn sapic_pre_report(thy: &Theory) -> Vec<WfError> {
    match thy.processes().next() {
        Some(top) => crate::warnings::check_wellformedness(top),
        None => Vec::new(),
    }
}

/// Apply the SAPIC `process:` translation to a theory that contains exactly one
/// top-level process.  A no-op for non-process theories (`thy.is_sapic()` is
/// false), so non-SAPIC corpus files are byte-unchanged.
///
/// `user_set_heuristic` is true when the source / CLI already fixed a heuristic
/// (in which case HS's `addHeuristic` returns `Nothing` and we do NOT add `p`).
///
/// Returns the SAPIC-process wellformedness report (HS `Sapic.checkWellformedness`,
/// Warnings.hs), which the caller PREPENDS to the overall report — HS
/// computes it in `translateTheory` on the OpenTheory *before* translation, so
/// it sorts before every other check (TheoryLoader.hs;
/// `preReport ++ postReport`).  Empty for a well-formed (or
/// non-SAPIC) theory.
pub fn apply_sapic(thy: &mut Theory, user_set_heuristic: bool) -> Result<Vec<WfError>, ElabError> {
    if !thy.is_sapic() {
        return Ok(Vec::new());
    }

    // The single top-level process, inlined, plus its warning report — the
    // report is returned to the caller and translation proceeds regardless
    // (these are warnings, not hard errors).
    let Some(plain) = thy.processes().next().cloned() else {
        return Ok(Vec::new());
    };
    let wf_report = sapic_pre_report(thy);
    let user_names = user_names(thy, &plain);
    let mut restriction_names: BTreeSet<_> = thy.restrictions().map(|r| r.name.clone()).collect();

    // `typeTheory` (renameUnique + type inference), using the theory
    // signature's MaudeSig (HS `initTEFromSig`).  The user `functions:` typing
    // declarations (`theoryFunctionTypingInfos`, e.g. `f(bitstring):bitstring`)
    // seed the function-typing environment so `typeWith` can back-propagate a
    // declared argument/return type onto the bound variables.
    let user_fun_typings = collect_user_fun_typings(thy);
    let maude_sig = &thy.signature;
    let typed =
        type_and_rename_process(maude_sig, &user_fun_typings, &plain).map_err(|e| ElabError {
            message: format!("SAPIC typing: {e}"),
        })?;

    // translate → rules + restrictions.  `needs_in_ev_res = any
    // lemmaNeedsInEvRes (theoryLemmas th)` (sapic/src/Sapic.hs): gates the
    // `EventEmpty`/`ChannelIn` actions + the `in_event` restriction.  HS
    // `theoryLemmas` = the (non-diff, non-accountability) `Lemma` items.
    let needs_in_ev = needs_in_ev_res(thy);
    // The signature's CtxtStRules drive `translateLetDestr` (let-destructor /
    // let-elimination pass).
    let st_rules = &maude_sig.st_rules;
    // Thread the theory options (HS `_thyOptions`) into the translation.
    let opts = TranslateOptions {
        trans_progress: thy.options.trans_progress(),
        trans_reliable: thy.has_signature_builtin("reliable-channel"),
        async_channels: thy.options.asynchronous_channels(),
        compress_events: thy.options.compress_events(),
        trans_report: thy.has_signature_builtin("locations-report"),
        state_channel_opt: thy.options.state_channel_opt(),
    };
    let macros: Vec<LNMacro> = thy.macros().cloned().collect();
    let translation =
        translate(&typed, needs_in_ev, st_rules, &macros, opts).map_err(|e| ElabError {
            message: format!("SAPIC translation: {e}"),
        })?;

    // The `predicate:` declarations the embedded `_restrict` formulas expand
    // against: HS `liftedExpandFormula` reads `theoryPredicates thy`
    // (Theory/Text/Parser.hs), the list `elaborate` built from the
    // theory's `predicates:` items.
    let predicates: Vec<Predicate> = thy.predicates().cloned().collect();
    // The `macros:` declarations `closeTheoryItem` applies to every rule and
    // restriction of the translated theory (CloseRule.hs).

    // Inject each generated rule, running the `_restrict` expansion HS
    // `liftedAddProtoRule` (Theory/Text/Parser.hs) performs per rule:
    // for each embedded restriction formula, mint a fresh action
    // `Restr_<rule>_<i>` + a global restriction `∀ … #NOW. Restr…@#NOW ⇒ φ`,
    // insert the restrictions BEFORE the rule, and append the actions to the
    // rule.
    let mut restricted_actions = BTreeSet::new();
    for (rule, restr_formulas) in &translation.rules {
        let rname = match rule.info.name {
            ProtoRuleName::Stand(n) => n,
            // HS `liftedAddProtoRule` throws `TryingToAddFreshRule` for the
            // reserved name (Theory/Text/Parser.hs); the translation gives
            // every generated rule a process position, so it never reaches
            // this arm.
            ProtoRuleName::Fresh => "Fresh",
        };

        // HS `addActions` rebuilds `rActs` alone (Theory/Text/Parser.hs), so
        // the rule keeps the `_preRestriction` formulas (Theory/Model/Rule.hs)
        // `toRule` gave it (sapic/src/Sapic/Facts.hs) and the `rNewVars`
        // the translation computed.
        let mut lifted = rule.clone();
        lifted.info.restrictions = restr_formulas.clone();
        // `if <formula>` / `let … else` arm: expand the predicate atoms of
        // every embedded formula (HS `liftedExpandFormula`,
        // Theory/Text/Parser.hs).
        let mut closed: Vec<LNFormula> = Vec::with_capacity(restr_formulas.len());
        for phi in restr_formulas {
            closed.push(expand_formula(&predicates, phi).map_err(|e| ElabError {
                message: format!("SAPIC _restrict expansion: {e}"),
            })?);
        }
        let mut generated: Vec<Restriction> = Vec::with_capacity(closed.len());
        for (restr, action) in rule_restrictions(rname, &closed) {
            restricted_actions.insert(fact_tag_name(&action.tag).to_owned());
            generated.push(restr);
            lifted.actions.push(action);
        }

        // HS `foldM liftedAddProtoRule th (map (`OpenProtoRule` []) eProtoRule)`
        // (sapic/src/Sapic.hs): each generated rule goes through the same
        // `addOpenProtoRule` name guard as a parsed rule (OpenTheory.hs)
        // — `maybe True (ru ==)` over the rule bound to that name, so a user
        // rule named like a generated one (e.g. `rule Init` alongside a
        // `process:`) aborts the translation with `duplicate rule: <name>`.
        // The comparison is between open rules: the macro-unexpanded
        // `_oprRuleE` half plus the manual `_oprRuleAC` variants, against the
        // generated rule as it stands after the `_restrict` lift.  The thrown
        // `DuplicateItem` exception escapes to GHC's runtime, which prints
        // `tamarin-prover: duplicate rule: <name>` to stderr and exits 1; here
        // the message rides the existing `ElabError` channel.  (Generated rules
        // never collide with each other — their names encode unique process
        // positions — and never compare equal to a user rule: the parser drops
        // `process=` attributes while the translation sets them.)
        if let Some(prev) = thy.items.iter().find_map(|i| match i {
            TheoryItem::Rule(r) if r.name() == rname => Some(r),
            _ => None,
        }) && (prev.rule_e() != &lifted || !prev.rule_ac.is_empty())
        {
            return Err(ElabError {
                message: format!("duplicate rule: {rname}"),
            });
        }

        // The restrictions precede the rule (Theory/Text/Parser.hs).
        for restr in generated {
            add_generated_restriction(thy, &macros, &mut restriction_names, restr)?;
        }
        let mut opr = OpenProtoRule::new(apply_macro_in_rule(&macros, lifted.clone()));
        if opr.rule != lifted {
            opr.rule_e = Some(Box::new(lifted));
        }
        thy.items.push(TheoryItem::Rule(opr));
    }

    for restriction in &translation.restrictions {
        formula_action_names(&restriction.formula, &mut restricted_actions);
    }
    for (kind, name) in user_names {
        let reserved = if kind == "action" {
            &restricted_actions
        } else {
            &translation.internal_facts
        };
        if reserved.contains(&name) {
            return Err(ElabError { message: format!(
                "The {kind} name {name} is reserved: the process translation uses it for {kind}s of its own. Rename the {kind} in the process or rule that uses it."
            ) });
        }
    }

    // Inject the global restrictions (set_in/set_notin, predicate_eq/not_eq,
    // single_session).
    for restr in &translation.restrictions {
        add_generated_restriction(thy, &macros, &mut restriction_names, restr.clone())?;
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

/// Match HS `addRestriction`: even an identical existing restriction reserves its name.
fn add_generated_restriction(
    thy: &mut Theory,
    macros: &[LNMacro],
    names: &mut BTreeSet<String>,
    restriction: Restriction,
) -> Result<(), ElabError> {
    if !names.insert(restriction.name.clone()) {
        return Err(ElabError {
            message: format!("duplicate restriction: {}", restriction.name),
        });
    }
    thy.items
        .push(TheoryItem::Restriction(apply_macro_in_restriction(
            macros,
            restriction,
        )));
    Ok(())
}

fn formula_action_names(f: &LNFormula, names: &mut BTreeSet<String>) {
    use tamarin_theory::{atom::ProtoAtom, formula::ProtoFormula};
    match f {
        ProtoFormula::Atom(ProtoAtom::Action(_, fact)) => {
            names.insert(fact_tag_name(&fact.tag).to_owned());
        }
        ProtoFormula::Not(f) | ProtoFormula::Qua(_, _, f) => formula_action_names(f, names),
        ProtoFormula::Conn(_, l, r) => {
            formula_action_names(l, names);
            formula_action_names(r, names);
        }
        _ => {}
    }
}

fn user_names(thy: &Theory, process: &PlainProcess) -> Vec<(&'static str, String)> {
    let mut actions = Vec::new();
    let mut facts = Vec::new();
    tamarin_theory::sapic::for_each_process(process, &mut |node| match node {
        Process::Action(SapicAction::Event(f), _, _) => {
            actions.push(("action", fact_tag_name(&f.tag).to_owned()))
        }
        Process::Action(
            SapicAction::Msr {
                prems, acts, concs, ..
            },
            _,
            _,
        ) => {
            actions.extend(
                acts.iter()
                    .map(|f| ("action", fact_tag_name(&f.tag).to_owned())),
            );
            facts.extend(
                prems
                    .iter()
                    .chain(concs)
                    .map(|f| ("fact", fact_tag_name(&f.tag).to_owned())),
            );
        }
        _ => {}
    });
    actions.extend(facts);
    for rule in thy.rules() {
        for member in std::iter::once(rule.rule_e()).chain(&rule.rule_ac) {
            actions.extend(
                member
                    .actions
                    .iter()
                    .map(|f| ("action", fact_tag_name(&f.tag).to_owned())),
            );
            actions.extend(
                member
                    .premises
                    .iter()
                    .chain(&member.conclusions)
                    .map(|f| ("fact", fact_tag_name(&f.tag).to_owned())),
            );
        }
    }
    actions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_restrictions_reject_existing_names() {
        for source in [
            "restriction Restr_letywz_2_1_1: \"T\" \
             rule User: [] --[ Restr_letywz_2_1_1(<'a','b'>) ]-> [] \
             process: in(z); let <y,w> = z in out(y) else out('n')",
            "restriction single_session: \"T\" process: 0",
            "restriction single_session: \
             \"All #i #j. Init() @ #i & Init() @ #j ==> #i = #j\" process: 0",
        ] {
            let parsed =
                tamarin_parser::parse_theory(&format!("theory T begin {source} end"), &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            let duplicate = thy.restrictions().next().unwrap().name.clone();
            let error = apply_sapic(&mut thy, false).unwrap_err();
            assert_eq!(error.message, format!("duplicate restriction: {duplicate}"));
            assert_eq!(
                thy.restrictions().filter(|r| r.name == duplicate).count(),
                1
            );
        }
    }

    #[test]
    fn generated_restriction_guards_are_reserved_actions() {
        let source = "theory T begin \
            rule User: [] --[ Restr_letywz_2_1_1(<'a','b'>) ]-> [] \
            process: in(z); let <y,w> = z in out(y) else out('n') end";
        let parsed = tamarin_parser::parse_theory(source, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        assert!(apply_sapic(&mut thy, false)
            .unwrap_err()
            .message
            .contains("action name Restr_letywz_2_1_1 is reserved"));
    }

    #[test]
    fn generated_names_are_reserved_in_their_own_namespace() {
        for (source, collision) in [
            ("process: event Init()", Some("action name Init")),
            ("rule User: [] --> [State_1()] process: event Fine()", Some("fact name State_1")),
            ("options: translation-state-optimisation rule User: [] --> [L_PureState('a','b')] process: 0", Some("fact name L_PureState")),
            ("rule User: [] --> [L_PureState('a','b')] process: 0", None),
            ("process: event State_1()", None),
        ] {
            let parsed = tamarin_parser::parse_theory(&format!("theory T begin {source} end"), &[]).unwrap();
            let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
            let result = apply_sapic(&mut thy, false);
            if let Some(expected) = collision {
                assert!(result.unwrap_err().message.contains(expected), "{source}");
            } else { result.unwrap(); }
        }
    }

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
        let plain = thy.processes().next().unwrap().clone();
        let typed = type_and_rename_process(&maude_sig, &[], &plain).unwrap();
        let translation = translate(
            &typed,
            false,
            &maude_sig.st_rules,
            &[],
            TranslateOptions::default(),
        )
        .unwrap();
        let (translated, restr_formulas) = translation
            .rules
            .iter()
            .find(|(_, r)| !r.is_empty())
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
        assert_eq!(&injected.info.restrictions, restr_formulas);
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
}
