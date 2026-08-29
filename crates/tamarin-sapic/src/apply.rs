// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Wiring: run the SAPIC translation and inject the generated rules,
//! restrictions and heuristic into the theory.
//!
//! Mirrors the tail of HS `translate` (sapic/src/Sapic.hs:69-85):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
//!
//! HS's final `_thyIsSapic = True` has no counterpart here: `Theory::is_sapic`
//! is already set while elaborating the parsed theory (elaborate.rs), and this
//! module reads it as the gate that decides whether to translate at all.
//!
//! HS adds these items to the OPEN theory and applies the theory's macros to
//! every rule and restriction at close time (`closeTheoryItem`,
//! CloseRule.hs:82-84).  The port applies macros while elaborating, so the
//! injection applies them here too, recording the pre-macro rule as the
//! `cprRuleE` half `closeProtoRule` keeps (lib/theory/src/Rule.hs:82-86).

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

/// HS `Sapic.checkWellformedness` (Warnings.hs:37-38) over the UNTRANSLATED
/// theory: warn-check the single top-level process.  The process arrives with
/// its `P(args)` calls already inlined (HS inlines at parse time) but BEFORE
/// `typeTheory` / `renameUnique`, so two binders sharing a name (e.g.
/// `new x; new x`) are still alpha-identical and detected as captured.
///
/// `translateTheory` computes this report on the open theory before any
/// translation step (TheoryLoader.hs:487-499, see line 497), so both the
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
/// top-level process.  A no-op for non-process theories (`thy.is_sapic` is
/// false), so non-SAPIC corpus files are byte-unchanged.
///
/// `user_set_heuristic` is true when the source / CLI already fixed a heuristic
/// (in which case HS's `addHeuristic` returns `Nothing` and we do NOT add `p`).
///
/// Returns the SAPIC-process wellformedness report (HS `Sapic.checkWellformedness`,
/// Warnings.hs:37-38), which the caller PREPENDS to the overall report — HS
/// computes it in `translateTheory` on the OpenTheory *before* translation, so
/// it sorts before every other check (TheoryLoader.hs:487-499, see line 497;
/// `preReport ++ postReport` at :730-732).  Empty for a well-formed (or
/// non-SAPIC) theory.
pub fn apply_sapic(thy: &mut Theory, user_set_heuristic: bool) -> Result<Vec<WfError>, ElabError> {
    if !thy.is_sapic {
        return Ok(Vec::new());
    }

    // The single top-level process, inlined, plus its warning report — the
    // report is returned to the caller and translation proceeds regardless
    // (these are warnings, not hard errors).  `is_sapic` set with no
    // `TopLevelProcess` is a defensive no-op.
    let Some(plain) = thy.processes().next().cloned() else {
        return Ok(Vec::new());
    };
    let wf_report = sapic_pre_report(thy);

    // `typeTheory` (renameUnique + type inference), using the theory
    // signature's MaudeSig (HS `initTEFromSig`).  The user `functions:` typing
    // declarations (`theoryFunctionTypingInfos`, e.g. `f(bitstring):bitstring`)
    // seed the function-typing environment so `typeWith` can back-propagate a
    // declared argument/return type onto the bound variables.
    let user_fun_typings = collect_user_fun_typings(thy);
    let maude_sig = &thy.signature.maude_sig;
    let typed =
        type_and_rename_process(maude_sig, &user_fun_typings, &plain).map_err(|e| ElabError {
            message: format!("SAPIC typing: {e}"),
        })?;

    // translate → rules + restrictions.  `needs_in_ev_res = any
    // lemmaNeedsInEvRes (theoryLemmas th)` (sapic/src/Sapic.hs:45-101, see line 101): gates the
    // `EventEmpty`/`ChannelIn` actions + the `in_event` restriction.  HS
    // `theoryLemmas` = the (non-diff, non-accountability) `Lemma` items.
    let needs_in_ev = needs_in_ev_res(thy);
    // The signature's CtxtStRules drive `translateLetDestr` (let-destructor /
    // let-elimination pass).
    let st_rules = &maude_sig.st_rules;
    // Thread the theory options (HS `_thyOptions`) into the translation.
    let opts = TranslateOptions {
        trans_progress: thy.options.trans_progress(),
        trans_reliable: thy.options.trans_reliable,
        async_channels: thy.options.asynchronous_channels(),
        compress_events: thy.options.compress_events(),
        trans_report: thy.options.trans_report,
        state_channel_opt: thy.options.state_channel_opt(),
    };
    let translation = translate(&typed, needs_in_ev, st_rules, opts).map_err(|e| ElabError {
        message: format!("SAPIC translation: {e}"),
    })?;

    // The `predicate:` declarations the embedded `_restrict` formulas expand
    // against: HS `liftedExpandFormula` reads `theoryPredicates thy`
    // (Theory/Text/Parser.hs:112-114), the list `elaborate` built from the
    // theory's `predicates:` items.
    let predicates: Vec<Predicate> = thy.predicates().cloned().collect();
    // The `macros:` declarations `closeTheoryItem` applies to every rule and
    // restriction of the translated theory (CloseRule.hs:82-84).
    let macros: Vec<LNMacro> = thy.macros().cloned().collect();

    // Inject each generated rule, running the `_restrict` expansion HS
    // `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) performs per rule:
    // for each embedded restriction formula, mint a fresh action
    // `Restr_<rule>_<i>` + a global restriction `∀ … #NOW. Restr…@#NOW ⇒ φ`,
    // insert the restrictions BEFORE the rule, and append the actions to the
    // rule.
    for (rule, restr_formulas) in &translation.rules {
        let rname = match rule.info.name {
            ProtoRuleName::Stand(n) => n,
            // HS `liftedAddProtoRule` throws `TryingToAddFreshRule` for the
            // reserved name (Theory/Text/Parser.hs:182); the translation gives
            // every generated rule a process position, so it never reaches
            // this arm.
            ProtoRuleName::Fresh => "Fresh",
        };

        // HS `addActions` rebuilds `rActs` alone (Theory/Text/Parser.hs:188), so
        // the rule keeps the `_preRestriction` formulas (Theory/Model/Rule.hs:424)
        // `toRule` gave it (sapic/src/Sapic/Facts.hs:376-379) and the `rNewVars`
        // the translation computed.
        let mut lifted = rule.clone();
        lifted.info.restrictions = restr_formulas.clone();
        // `if <formula>` / `let … else` arm: expand the predicate atoms of
        // every embedded formula (HS `liftedExpandFormula`,
        // Theory/Text/Parser.hs:178).
        let mut closed: Vec<LNFormula> = Vec::with_capacity(restr_formulas.len());
        for phi in restr_formulas {
            closed.push(expand_formula(&predicates, phi).map_err(|e| ElabError {
                message: format!("SAPIC _restrict expansion: {e}"),
            })?);
        }
        let mut generated: Vec<Restriction> = Vec::with_capacity(closed.len());
        for (restr, action) in rule_restrictions(rname, &closed) {
            generated.push(restr);
            lifted.actions.push(action);
        }

        // HS `foldM liftedAddProtoRule th (map (`OpenProtoRule` []) eProtoRule)`
        // (sapic/src/Sapic.hs:75): each generated rule goes through the same
        // `addOpenProtoRule` name guard as a parsed rule (OpenTheory.hs:690-700)
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
        }) {
            if prev.rule_e() != &lifted || !prev.rule_ac.is_empty() {
                return Err(ElabError {
                    message: format!("duplicate rule: {rname}"),
                });
            }
        }

        // The restrictions precede the rule (Theory/Text/Parser.hs:179-180).
        for restr in generated {
            thy.items
                .push(TheoryItem::Restriction(apply_macro_in_restriction(
                    &macros, restr,
                )));
        }
        let mut opr = OpenProtoRule::new(apply_macro_in_rule(&macros, lifted.clone()));
        if opr.rule != lifted {
            opr.rule_e = Some(Box::new(lifted));
        }
        thy.items.push(TheoryItem::Rule(opr));
    }

    // Inject the global restrictions (set_in/set_notin, predicate_eq/not_eq,
    // single_session).
    for restr in &translation.restrictions {
        thy.items
            .push(TheoryItem::Restriction(apply_macro_in_restriction(
                &macros,
                restr.clone(),
            )));
    }

    // `addHeuristic [SapicRanking]` unless a heuristic is already set
    // (sapic/src/Sapic.hs:45-101, see line 82).  `SapicRanking` renders as `p`
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

    /// The `else` arm of a pattern `let` carries the restriction
    /// `∀ y w. (<y, w> = z) ⇒ ⊥` (Basetranslation.hs:261-269), so the
    /// translated theory gets one generated `Restr_letywz_2_1_1` restriction
    /// plus the action that reaches it on rule `letywz_2_1`.
    const LET_ELSE: &str = "theory T begin\n\
        process:\n\
          in(z); let <y, w> = z in out(y) else out('n')\n\
        end";

    /// The generated restriction and the appended action land in the theory,
    /// the restriction immediately before its rule (HS adds the expanded
    /// restrictions and then the rule, Theory/Text/Parser.hs:179-180), and the
    /// rule keeps the premises, conclusions and new variables the translation
    /// built — the lift only appends actions (`addActions`,
    /// Theory/Text/Parser.hs:188).
    #[test]
    fn generated_rule_carries_its_restrict_formulas() {
        let parsed = tamarin_parser::parse_theory(LET_ELSE, &[]).unwrap();
        let mut thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();

        // The same translation `apply_sapic` runs, so the rule it injects can
        // be compared against the values the translation produced.
        let maude_sig = thy.signature.maude_sig.clone();
        let plain = thy.processes().next().unwrap().clone();
        let typed = type_and_rename_process(&maude_sig, &[], &plain).unwrap();
        let translation = translate(
            &typed,
            false,
            &maude_sig.st_rules,
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
    /// TRANSLATED theory, the generated ones included (CloseRule.hs:82-83),
    /// and `closeProtoRule` narrows `applyMacroInRule macros ruE` while
    /// keeping the unexpanded `ruE` as the `cprRuleE` half
    /// (lib/theory/src/Rule.hs:82-86).
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
