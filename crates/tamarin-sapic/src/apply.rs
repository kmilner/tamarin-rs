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

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::restriction::Restriction;
use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::sapic::PlainProcess;
use tamarin_theory::theory::{OpenProtoRule, Theory, TheoryItem};

use crate::convert::ConvertError;
use crate::inline::{collect_process_defs, convert_process_with_defs};
use crate::translate::{needs_in_ev_res, translate, TranslateOptions};
use crate::typing::{collect_user_fun_typings, type_and_rename_process};

/// HS `Sapic.checkWellformedness` (Warnings.hs:37-38) over the UNTRANSLATED
/// theory: locate the single top-level process, inline its process-definition
/// calls, and warn-check the resulting `PlainProcess`.  The check runs AFTER
/// inlining (HS inlines at parse time) but BEFORE `typeTheory` /
/// `renameUnique`, so two binders sharing a name (e.g. `new x; new x`) are
/// still alpha-identical and detected as captured.
///
/// `translateTheory` computes this report on the open theory before any
/// translation step (TheoryLoader.hs:487-499, see line 497), so both the
/// translating path ([`apply_sapic`]) and the `-m spthy` / `-m spthytyped`
/// paths that skip translation report exactly these warnings.
///
/// Returns the report together with the inlined process the caller goes on to
/// type and translate, or `None` when the theory carries no top-level process.
/// The inlining error is handed back unwrapped: callers word it differently.
pub fn sapic_pre_report(
    parsed: &p::Theory,
    sig: &MaudeSig,
) -> Result<Option<(Vec<WfError>, PlainProcess)>, ConvertError> {
    let top = parsed.items.iter().find_map(|i| match i {
        p::TheoryItem::TopLevelProcess(proc) => Some(proc.clone()),
        _ => None,
    });
    let Some(top) = top else {
        return Ok(None);
    };
    // parser AST → theory AST, inlining process-definition calls
    // (`let P = ..` / `P(args)`) with parameter substitution.  HS inlines at
    // parse time (`Theory.Text.Parser.Sapic.actionprocess`); we do it here,
    // resolving every `Call` against the theory's `ProcessDef`s.
    let defs = collect_process_defs(parsed);
    let plain = convert_process_with_defs(&top, &defs, sig)?;
    Ok(Some((crate::warnings::check_wellformedness(&plain), plain)))
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
    let Some((wf_report, plain)) = sapic_pre_report(parsed, &elaborated.signature.maude_sig)
        .map_err(|e| ElabError {
            message: format!("SAPIC translation: {}", e.message),
        })?
    else {
        return Ok(Vec::new());
    };

    // `typeTheory` (renameUnique + type inference), using the elaborated
    // signature's MaudeSig (HS `initTEFromSig`).  The user `functions:` typing
    // declarations (`theoryFunctionTypingInfos`, e.g. `f(bitstring):bitstring`)
    // seed the function-typing environment so `typeWith` can back-propagate a
    // declared argument/return type onto the bound variables.
    let maude_sig = &elaborated.signature.maude_sig;
    let user_fun_typings = collect_user_fun_typings(parsed);
    let typed =
        type_and_rename_process(maude_sig, &user_fun_typings, &plain).map_err(|e| ElabError {
            message: format!("SAPIC typing: {e}"),
        })?;

    // translate → rules + restrictions.  `needs_in_ev_res = any
    // lemmaNeedsInEvRes (theoryLemmas th)` (sapic/src/Sapic.hs:45-101, see line 101): gates the
    // `EventEmpty`/`ChannelIn` actions + the `in_event` restriction.  HS
    // `theoryLemmas` = the (non-diff, non-accountability) `Lemma` items.
    let lemmas: Vec<p::Lemma> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Lemma(l) => Some(l.clone()),
            _ => None,
        })
        .collect();
    let needs_in_ev = needs_in_ev_res(&lemmas);
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
    // against (HS `liftedExpandFormula`).  Collected from the parsed theory.
    let predicates: Vec<p::Predicate> = parsed
        .items
        .iter()
        .filter_map(|i| match i {
            p::TheoryItem::Predicates(ps) => Some(ps.clone()),
            _ => None,
        })
        .flatten()
        .collect();

    // Inject each generated rule into BOTH theories, running the `_restrict`
    // expansion HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) performs
    // per rule: for each embedded restriction formula, mint a fresh action
    // `Restr_<rule>_<i>` + a global restriction `∀ … #NOW. Restr…@#NOW ⇒ φ`,
    // insert the restrictions BEFORE the rule, and append the actions to the
    // rule.  We share the parser-AST lift (`lift_one_rule`) for both theories:
    //   - parsed:     the generated restrictions + rewritten parser rule;
    //   - elaborated: the same restrictions (as `Restriction`, internal
    //                 formula) + the elaborated rewritten rule (the original
    //                 `ProtoRuleE` attributes/name with the rewritten body, so
    //                 the appended `Restr_*` actions are present).
    for (rule, restr_formulas) in &translation.rules {
        // Synthesise the parser-AST rule, carrying the embedded restrictions.
        // `proto_rule_to_parsed` projects the elaborated E-rule back to parser
        // facts and carries color / process / no_derivcheck / issapicrule /
        // role exactly as HS's `toRule` produced them.
        let mut parsed_rule = tamarin_theory::elaborate::proto_rule_to_parsed(rule);
        // `lift_one_rule` reads parser-AST formulas, so the embedded
        // restrictions cross back to the AST here.
        parsed_rule.embedded_restrictions = restr_formulas
            .iter()
            .map(tamarin_theory::pretty_formula::syntactic_lnformula_to_parser)
            .collect();

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

        // `if <formula>` arm: expand the embedded restriction.
        let (gen_restrs, rewritten) =
            tamarin_theory::rule_restriction::lift_one_rule(parsed_rule, &predicates).map_err(
                |e| ElabError {
                    message: format!("SAPIC _restrict expansion: {}", e.message),
                },
            )?;

        // Restrictions precede the rule in both theories.
        for r in &gen_restrs {
            let restr = elaborate_restriction(r, &elaborated.signature.maude_sig)?;
            parsed.items.push(p::TheoryItem::Restriction(r.clone()));
            elaborated.items.push(TheoryItem::Restriction(restr));
        }

        // Elaborated rule: re-elaborate the rewritten parser-rule body to
        // LNFacts and pair it with the original `ProtoRuleE`'s info (which holds
        // the SAPIC attributes + name).  Re-elaborating the whole body keeps the
        // appended `Restr_*` actions byte-faithful to the parsed rule.
        let elab_rule = reelaborate_rule_body(rule, &rewritten, &elaborated.signature.maude_sig)?;
        elaborated
            .items
            .push(TheoryItem::Rule(OpenProtoRule::new(elab_rule)));
        parsed.items.push(p::TheoryItem::Rule(rewritten));
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

/// Lower one generated restriction into the elaborated theory's
/// [`Restriction`]: the formula is closed by `from_parser` and stripped of
/// its predicate sugar, which `lift_one_rule` already inlined, and
/// `original_formula` repeats it — HS's `applyMacroInRestriction` fills that
/// field for every restriction of a closed theory
/// (Theory/Model/Restriction.hs:164-166, CloseRule.hs:82-84).
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

/// Re-elaborate a `_restrict`-rewritten parser-AST rule body into a
/// `ProtoRuleE`, reusing the original SAPIC rule's `info` (name + attributes).
///
/// The rewrite appended `Restr_<rule>_<i>(...)` actions to the rule; elaborating
/// the rewritten body (premises/actions/conclusions) regenerates the rule's
/// LNFacts including those actions, byte-faithful to the parsed rendering.  The
/// `new_vars` are recomputed (HS `newVariables l (c ++ a)`), though the Restr
/// action args are always already premise-bound so they add nothing.
fn reelaborate_rule_body(
    original: &ProtoRuleE,
    rewritten: &p::Rule,
    sig: &MaudeSig,
) -> Result<ProtoRuleE, ElabError> {
    use tamarin_theory::elaborate::fact_to_lnfact;
    let prems = rewritten
        .premises
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let acts = rewritten
        .actions
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let concs = rewritten
        .conclusions
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let new_vars = crate::facts::compute_new_vars(&prems, &concs, &acts);
    Ok(
        tamarin_theory::rule::Rule::new(original.info.clone(), prems, concs, acts)
            .with_new_vars(new_vars),
    )
}
