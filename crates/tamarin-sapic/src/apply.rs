// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Wiring: run the SAPIC translation and inject the generated rules +
//! restrictions + heuristic into BOTH the parsed theory (so the pretty-printer
//! renders them via the existing rule/restriction path) and the elaborated
//! theory (so the solver + AC-variant pre-computation see them).
//!
//! Mirrors the tail of HS `translate` (sapic/src/Sapic.hs:69-85):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
//!
//! HS's final `_thyIsSapic = True` has no counterpart here: `Theory::is_sapic`
//! is already set while elaborating the parsed theory (elaborate.rs), and this
//! module reads it as the gate that decides whether to translate at all.

use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::maude_sig::MaudeSig;

use tamarin_theory::elaborate::{proto_rule_to_parsed, ElabError};
use tamarin_theory::formula::LNFormula;
use tamarin_theory::predicate::{expand_formula, Predicate};
use tamarin_theory::pretty_formula::lnformula_to_parser;
use tamarin_theory::restriction::Restriction;
use tamarin_theory::rule_restriction::rule_restrictions;
use tamarin_theory::sapic::PlainProcess;
use tamarin_theory::theory::{OpenProtoRule, Theory, TheoryItem};

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
/// Returns the report together with the process the caller goes on to type and
/// translate, or `None` when the theory carries no top-level process.
pub fn sapic_pre_report(thy: &Theory) -> Option<(Vec<WfError>, PlainProcess)> {
    let top = thy.processes().next()?.clone();
    Some((crate::warnings::check_wellformedness(&top), top))
}

/// Apply the SAPIC `process:` translation to a theory that contains exactly one
/// top-level process.  A no-op for non-process theories (`elaborated.is_sapic`
/// is false), so non-SAPIC corpus files are byte-unchanged.
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
pub fn apply_sapic(
    parsed: &mut p::Theory,
    elaborated: &mut Theory,
    user_set_heuristic: bool,
) -> Result<Vec<WfError>, ElabError> {
    if !elaborated.is_sapic {
        return Ok(Vec::new());
    }

    // The single top-level process, inlined, plus its warning report — the
    // report is returned to the caller and translation proceeds regardless
    // (these are warnings, not hard errors).  `is_sapic` set with no
    // `TopLevelProcess` is a defensive no-op.
    let Some((wf_report, plain)) = sapic_pre_report(elaborated) else {
        return Ok(Vec::new());
    };

    // `typeTheory` (renameUnique + type inference), using the elaborated
    // signature's MaudeSig (HS `initTEFromSig`).  The user `functions:` typing
    // declarations (`theoryFunctionTypingInfos`, e.g. `f(bitstring):bitstring`)
    // seed the function-typing environment so `typeWith` can back-propagate a
    // declared argument/return type onto the bound variables.
    let user_fun_typings = collect_user_fun_typings(elaborated);
    let maude_sig = &elaborated.signature.maude_sig;
    let typed =
        type_and_rename_process(maude_sig, &user_fun_typings, &plain).map_err(|e| ElabError {
            message: format!("SAPIC typing: {e}"),
        })?;

    // translate → rules + restrictions.  `needs_in_ev_res = any
    // lemmaNeedsInEvRes (theoryLemmas th)` (sapic/src/Sapic.hs:45-101, see line 101): gates the
    // `EventEmpty`/`ChannelIn` actions + the `in_event` restriction.  HS
    // `theoryLemmas` = the (non-diff, non-accountability) `Lemma` items.
    let needs_in_ev = needs_in_ev_res(elaborated);
    // The signature's CtxtStRules drive `translateLetDestr` (let-destructor /
    // let-elimination pass).
    let st_rules = &maude_sig.st_rules;
    // Thread the theory options (HS `_thyOptions`) into the translation.
    let opts = TranslateOptions {
        trans_progress: elaborated.options.trans_progress,
        trans_reliable: elaborated.options.trans_reliable,
        async_channels: elaborated.options.asynchronous_channels,
        compress_events: elaborated.options.compress_events,
        trans_report: elaborated.options.trans_report,
        state_channel_opt: elaborated.options.state_channel_opt,
    };
    let translation = translate(&typed, needs_in_ev, st_rules, opts).map_err(|e| ElabError {
        message: format!("SAPIC translation: {e}"),
    })?;

    // The `predicate:` declarations the embedded `_restrict` formulas expand
    // against: HS `liftedExpandFormula` reads `theoryPredicates thy`
    // (Theory/Text/Parser.hs:112-114), the list `elaborate` built from the
    // theory's `predicates:` items.
    let predicates: Vec<Predicate> = elaborated.predicates().cloned().collect();

    // Inject each generated rule into BOTH theories, running the `_restrict`
    // expansion HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) performs
    // per rule: for each embedded restriction formula, mint a fresh action
    // `Restr_<rule>_<i>` + a global restriction `∀ … #NOW. Restr…@#NOW ⇒ φ`,
    // insert the restrictions BEFORE the rule, and append the actions to the
    // rule.  The lift runs on the internal formulas the translation carries;
    // `elaborated` receives its outputs and `parsed` their projection.
    for (rule, restr_formulas) in &translation.rules {
        // Synthesise the parser-AST rule as it stands BEFORE the lift, which
        // is the shape the name guard below compares.  `proto_rule_to_parsed`
        // projects the elaborated E-rule back to parser facts and carries
        // color / process / no_derivcheck / issapicrule / role exactly as HS's
        // `toRule` produced them.
        let parsed_rule = proto_rule_to_parsed(rule);

        // HS `foldM liftedAddProtoRule th (map (`OpenProtoRule` []) eProtoRule)`
        // (sapic/src/Sapic.hs:75): each generated rule goes through the same
        // `addOpenProtoRule` name guard as a parsed rule (OpenTheory.hs:
        // 691-702) — it fails when the name is already bound to a DIFFERENT
        // rule, so a user rule named like a generated one (e.g. `rule Init`
        // alongside a `process:`) aborts the translation with
        // `duplicate rule: <name>`.  The thrown `DuplicateItem` exception
        // escapes to GHC's runtime, which prints `tamarin-prover: duplicate
        // rule: <name>` to stderr and exits 1; here the message rides the
        // existing `ElabError` channel.  (Generated rules never collide with
        // each other — their names encode unique process positions — and never
        // compare equal to a user rule: the parser drops `process=` attributes
        // while `proto_rule_to_parsed` keeps them.)
        if let Some(prev) = parsed.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) if r.name == parsed_rule.name => Some(r),
            _ => None,
        }) {
            if *prev != parsed_rule {
                return Err(ElabError {
                    message: format!("duplicate rule: {}", parsed_rule.name),
                });
            }
        }

        if restr_formulas.is_empty() {
            // No `_restrict` — inject directly (linear / state / lookup rules).
            parsed.items.push(p::TheoryItem::Rule(parsed_rule));
            elaborated
                .items
                .push(TheoryItem::Rule(OpenProtoRule::new(rule.clone())));
            continue;
        }

        // `if <formula>` / `let … else` arm: expand the predicate atoms of
        // every embedded formula (HS `liftedExpandFormula`,
        // Theory/Text/Parser.hs:178).
        let mut closed: Vec<LNFormula> = Vec::with_capacity(restr_formulas.len());
        for phi in restr_formulas {
            closed.push(expand_formula(&predicates, phi).map_err(|e| ElabError {
                message: format!("SAPIC _restrict expansion: {e}"),
            })?);
        }

        // HS `addActions` rebuilds `rActs` alone (Theory/Text/Parser.hs:188), so
        // the rule keeps the `_preRestriction` formulas (Theory/Model/Rule.hs:424)
        // `toRule` gave it (sapic/src/Sapic/Facts.hs:376-379) and the `rNewVars`
        // the translation computed.
        let mut lifted = rule.clone();
        lifted.info.restrictions = restr_formulas.clone();
        for (mut restr, action) in rule_restrictions(&parsed_rule.name, &closed) {
            // Restrictions precede the rule in both theories.
            parsed
                .items
                .push(p::TheoryItem::Restriction(p::Restriction {
                    name: restr.name.clone(),
                    formula: lnformula_to_parser(&restr.formula),
                    attributes: Vec::new(),
                }));
            // HS `applyMacroInRestriction` records the formula as it stands as
            // the original one for every restriction of a closed theory
            // (Theory/Model/Restriction.hs:164-166, CloseRule.hs:84).
            restr.original_formula = Some(restr.formula.clone());
            elaborated.items.push(TheoryItem::Restriction(restr));
            lifted.actions.push(action);
        }
        parsed
            .items
            .push(p::TheoryItem::Rule(proto_rule_to_parsed(&lifted)));
        elaborated
            .items
            .push(TheoryItem::Rule(OpenProtoRule::new(lifted)));
    }

    // Inject the global restrictions (set_in/set_notin, predicate_eq/not_eq,
    // single_session) into both theories.
    for restr in &translation.restrictions {
        let elab_restr = elaborate_restriction(restr, &elaborated.signature.maude_sig)?;
        parsed.items.push(p::TheoryItem::Restriction(restr.clone()));
        elaborated.items.push(TheoryItem::Restriction(elab_restr));
    }

    // `addHeuristic [SapicRanking]` unless a heuristic is already set
    // (sapic/src/Sapic.hs:45-101, see line 82).  `SapicRanking` renders as `p`.
    // Add it to BOTH theories:
    //   - `elaborated.heuristic` drives the rendered `heuristic: p` line; and
    //   - the `parsed` theory drives the PROVER's heuristic — `ProverSession`
    //     re-elaborates the parsed theory (`prove.rs:461`), so without the
    //     parser-AST `Heuristic` item the prover would fall back to
    //     `SmartRanking` instead of `SapicRanking`.
    if !user_set_heuristic && elaborated.heuristic.is_empty() {
        elaborated.heuristic.push("p".to_string());
        // Only add to parsed if the parser theory doesn't already carry one
        // (mirrors HS `addHeuristic` returning `Nothing` when present).
        let parsed_has_heuristic = parsed
            .items
            .iter()
            .any(|i| matches!(i, p::TheoryItem::Heuristic(_)));
        if !parsed_has_heuristic {
            parsed.items.push(p::TheoryItem::Heuristic("p".to_string()));
        }
    }

    Ok(wf_report)
}

/// Lower one of the translation's global restrictions — `baseRestr`'s
/// hardcoded and locking ones (Basetranslation.hs:449-468) plus the progress
/// and reliable-channel ones — into the elaborated theory's [`Restriction`]:
/// the parser-AST formula those builders write is closed by `from_parser`, and
/// `original_formula` repeats it, as HS's `applyMacroInRestriction` fills that
/// field for every restriction of a closed theory
/// (Theory/Model/Restriction.hs:164-166, CloseRule.hs:84).
fn elaborate_restriction(r: &p::Restriction, msig: &MaudeSig) -> Result<Restriction, ElabError> {
    let syn = tamarin_theory::formula::from_parser(&r.formula, msig)?;
    let formula = tamarin_theory::formula::to_lnformula(&syn).ok_or_else(|| ElabError {
        message: format!(
            "SAPIC restriction {} carries an unexpanded predicate atom",
            r.name
        ),
    })?;
    Ok(Restriction {
        name: r.name.clone(),
        original_formula: Some(formula.clone()),
        formula,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::rule::ProtoRuleName;

    /// The `else` arm of a pattern `let` carries the restriction
    /// `∀ y w. (<y, w> = z) ⇒ ⊥` (Basetranslation.hs:261-269), so the
    /// translated theory gets one generated `Restr_letywz_2_1_1` restriction
    /// plus the action that reaches it on rule `letywz_2_1`.
    const LET_ELSE: &str = "theory T begin\n\
        process:\n\
          in(z); let <y, w> = z in out(y) else out('n')\n\
        end";

    /// The generated restriction and the appended action land in both
    /// theories, the restriction immediately before its rule (HS adds the
    /// expanded restrictions and then the rule, Theory/Text/Parser.hs:179-180),
    /// and the internal rule keeps the premises, conclusions and new variables
    /// the translation built — the lift only appends actions
    /// (`addActions`, Theory/Text/Parser.hs:188).
    #[test]
    fn generated_rule_carries_its_restrict_formulas() {
        let mut parsed = tamarin_parser::parse_theory(LET_ELSE, &[]).unwrap();
        let mut elaborated = tamarin_theory::elaborate::elaborate(&parsed).unwrap();

        // The same translation `apply_sapic` runs, so the rule it injects can
        // be compared against the values the translation produced.
        let maude_sig = elaborated.signature.maude_sig.clone();
        let (_, plain) = sapic_pre_report(&elaborated).unwrap();
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

        apply_sapic(&mut parsed, &mut elaborated, false).unwrap();

        let restr_pos = parsed
            .items
            .iter()
            .position(
                |i| matches!(i, p::TheoryItem::Restriction(r) if r.name == "Restr_letywz_2_1_1"),
            )
            .expect("restriction not generated");
        let rule_pos = parsed
            .items
            .iter()
            .position(|i| matches!(i, p::TheoryItem::Rule(r) if r.name == "letywz_2_1"))
            .expect("rule missing");
        assert_eq!(restr_pos + 1, rule_pos, "restriction must precede rule");
        let p::TheoryItem::Rule(pr) = &parsed.items[rule_pos] else {
            panic!("item at {rule_pos} is not the rule");
        };
        assert_eq!(
            pr.actions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["Restr_letywz_2_1_1"],
            "the projected rule carries the generated action"
        );

        let erestr_pos = elaborated
            .items
            .iter()
            .position(|i| matches!(i, TheoryItem::Restriction(r) if r.name == "Restr_letywz_2_1_1"))
            .expect("internal restriction not generated");
        let erule_pos = elaborated
            .items
            .iter()
            .position(|i| {
                matches!(i, TheoryItem::Rule(r)
                    if r.rule.info.name == ProtoRuleName::Stand("letywz_2_1"))
            })
            .expect("internal rule missing");
        assert_eq!(erestr_pos + 1, erule_pos);
        let TheoryItem::Restriction(er) = &elaborated.items[erestr_pos] else {
            panic!("item at {erestr_pos} is not the restriction");
        };
        assert_eq!(er.original_formula.as_ref(), Some(&er.formula));

        let TheoryItem::Rule(er) = &elaborated.items[erule_pos] else {
            panic!("item at {erule_pos} is not the rule");
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
}
