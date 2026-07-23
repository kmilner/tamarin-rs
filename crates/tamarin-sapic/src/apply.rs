// Currently GPL 3.0 until granted permission by the following authors:
//   arcz, rkunnema, kevinmorio, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/Warnings.hs,
//   lib/theory/src/Theory/Text/Parser.hs, src/Main/TheoryLoader.hs

//! Wiring: run the SAPIC translation and inject the generated rules +
//! restriction + heuristic into BOTH the parsed theory (so the pretty-printer
//! renders them via the existing rule/restriction path — P0f) and the
//! elaborated theory (so the solver + AC-variant pre-computation see them).
//!
//! Mirrors the tail of HS `translate` (Sapic.hs:69-90):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
//!   - `_thyIsSapic = True`
//!
//! Scope: the CORE LINEAR subset (see `translate`/`base_translation`).

use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::pretty_sapic::pretty_sapic_top_level;
use tamarin_theory::pretty_theory::lnfact_to_parser;
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleName};
use tamarin_theory::theory::{OpenProtoRule, OpenRestriction, Theory, TheoryItem};

use crate::inline::{collect_process_defs, convert_process_with_defs};
use crate::translate::{needs_in_ev_res, translate, TranslateOptions};
use crate::typing::{type_and_rename_process, UserFunTyping};

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
/// it sorts before every other check (`preReport ++ postReport`,
/// TheoryLoader.hs:448-460, see line 455/631).  Empty for a well-formed (or non-SAPIC) theory.
pub fn apply_sapic(
    parsed: &mut p::Theory,
    elaborated: &mut Theory,
    user_set_heuristic: bool,
) -> Result<Vec<WfError>, ElabError> {
    if !elaborated.is_sapic {
        return Ok(Vec::new());
    }

    // Locate the single top-level process in the parsed theory.
    let top = parsed.items.iter().find_map(|i| match i {
        p::TheoryItem::TopLevelProcess(proc) => Some(proc.clone()),
        _ => None,
    });
    let Some(top) = top else {
        // `is_sapic` was set but no TopLevelProcess found — defensive no-op.
        return Ok(Vec::new());
    };

    // parser AST → theory AST, inlining process-definition
    // calls (`let P = ..` / `P(args)`) with parameter substitution.  HS inlines
    // at parse time (`Theory.Text.Parser.Sapic.actionprocess`); we do it here,
    // resolving every `Call` against the theory's `ProcessDef`s.
    let defs = collect_process_defs(parsed);
    let plain = convert_process_with_defs(&top, &defs).map_err(|e| ElabError {
        message: format!("SAPIC translation: {}", e.message),
    })?;

    // HS `Sapic.checkWellformedness = concatMap (toWfErrorReport . warnProcess)
    // . theoryProcesses` (Warnings.hs:37-38) runs on the parsed process —
    // AFTER inlining (HS inlines at parse time) but BEFORE `typeTheory` /
    // `renameUnique` — so two binders sharing a name (e.g. `new x; new x`) are
    // still alpha-identical and detected as captured.  `plain` is exactly that
    // process.  We collect the report and return it to the caller; translation
    // proceeds regardless (these are warnings, not hard errors).
    let wf_report = crate::warnings::check_wellformedness(&plain);

    // P0e: typeTheory (renameUnique + type inference), using the elaborated
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
    // lemmaNeedsInEvRes (theoryLemmas th)` (Sapic.hs:45-101, see line 101): gates the
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

    // The 0-arity function-symbol set the `if`-conditional restriction formulas
    // resolve their bare constant tokens against (HS `nullaryApp`, resolved at
    // parse time): user `functions: f/0` + enabled builtins' constants.  Threads
    // into `lift_one_rule` so a comparison against a constant (`if IsNormal(a)`,
    // `IsNormal(a) <=> a = NormalReq`) keeps `NormalReq` inlined in the generated
    // restriction rather than abstracting it into a second fact argument.
    let nullary = tamarin_theory::elaborate::nullary_fun_names(&parsed.items);

    // Inject each generated rule into BOTH theories, running the `_restrict`
    // expansion HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) performs
    // per rule: for each embedded restriction formula, mint a fresh action
    // `Restr_<rule>_<i>` + a global restriction `∀ … #NOW. Restr…@#NOW ⇒ φ`,
    // insert the restrictions BEFORE the rule, and append the actions to the
    // rule.  We share the parser-AST lift (`lift_one_rule`) for both theories:
    //   - parsed:     the generated restrictions + rewritten parser rule;
    //   - elaborated: the same restrictions (as `OpenRestriction`, parser-AST
    //                 formula) + the elaborated rewritten rule (the original
    //                 `ProtoRuleE` attributes/name with the rewritten body, so
    //                 the appended `Restr_*` actions are present).
    for (rule, restr_formulas) in &translation.rules {
        // Synthesise the parser-AST rule, carrying the embedded restrictions.
        let mut parsed_rule = synth_parsed_rule(rule);
        parsed_rule.embedded_restrictions = restr_formulas.clone();

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
            tamarin_theory::rule_restriction::lift_one_rule(parsed_rule, &predicates, &nullary)
                .map_err(|e| ElabError {
                    message: format!("SAPIC _restrict expansion: {}", e.message),
                })?;

        // Restrictions precede the rule in both theories.
        for r in &gen_restrs {
            parsed.items.push(p::TheoryItem::Restriction(r.clone()));
            elaborated
                .items
                .push(TheoryItem::Restriction(OpenRestriction::new(
                    r.name.clone(),
                    r.formula.clone(),
                )));
        }

        // Elaborated rule: re-elaborate the rewritten parser-rule body to
        // LNFacts and pair it with the original `ProtoRuleE`'s info (which holds
        // the SAPIC attributes + name).  Re-elaborating the whole body keeps the
        // appended `Restr_*` actions byte-faithful to the parsed rule.
        let elab_rule = reelaborate_rule_body(rule, &rewritten)?;
        elaborated
            .items
            .push(TheoryItem::Rule(OpenProtoRule::new(elab_rule)));
        parsed.items.push(p::TheoryItem::Rule(rewritten));
    }

    // Inject the global restrictions (set_in/set_notin, predicate_eq/not_eq,
    // single_session) into both theories.
    for restr in &translation.restrictions {
        parsed.items.push(p::TheoryItem::Restriction(restr.clone()));
        elaborated
            .items
            .push(TheoryItem::Restriction(OpenRestriction::new(
                restr.name.clone(),
                restr.formula.clone(),
            )));
    }

    // `addHeuristic [SapicRanking]` unless a heuristic is already set
    // (Sapic.hs:45-101, see line 82).  `SapicRanking` renders as `p`.  Add it to BOTH theories:
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

/// Collect the user `functions:` typing declarations (HS
/// `theoryFunctionTypingInfos`).  Every parsed `FunctionDecl` becomes a
/// `FunctionTypingInfo` (Theory/Text/Parser.hs:254-257 `addFunctionTypingInfo`),
/// so we map each to its `(name, arg_types, out_type)` triple.  Plain `f/2`
/// declarations carry `Nothing` types (the `defaultFunctionType`), which the
/// typing env already holds — so they are harmless overlays.
fn collect_user_fun_typings(parsed: &p::Theory) -> Vec<UserFunTyping> {
    let mut out = Vec::new();
    for item in &parsed.items {
        if let p::TheoryItem::Functions(decls) = item {
            for d in decls {
                out.push((d.name.clone(), d.arg_types.clone(), d.out_type.clone()));
            }
        }
    }
    out
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
) -> Result<ProtoRuleE, ElabError> {
    use tamarin_theory::elaborate::fact_to_lnfact;
    let prems = rewritten
        .premises
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let acts = rewritten
        .actions
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let concs = rewritten
        .conclusions
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let new_vars = crate::facts::compute_new_vars(&prems, &concs, &acts);
    Ok(
        tamarin_theory::rule::Rule::new(original.info.clone(), prems, concs, acts)
            .with_new_vars(new_vars),
    )
}

/// Build the synthetic parsed-AST rule for a SAPIC-generated `ProtoRuleE`.
/// The body (premises/actions/conclusions) is the elaborated E-rule converted
/// back to parser facts; the attributes carry color / process / issapicrule /
/// role exactly as HS's `toRule` produced them.
fn synth_parsed_rule(rule: &ProtoRuleE) -> p::Rule {
    let name = match &rule.info.name {
        ProtoRuleName::Stand(n) => n.to_string(),
        ProtoRuleName::Fresh => "Fresh".to_string(),
    };
    let attrs = synth_attrs(&rule.info.attributes);
    p::Rule {
        name,
        modulo: None,
        attributes: attrs,
        let_block: Vec::new(),
        premises: rule.premises.iter().map(lnfact_to_parser).collect(),
        actions: rule.actions.iter().map(lnfact_to_parser).collect(),
        conclusions: rule.conclusions.iter().map(lnfact_to_parser).collect(),
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    }
}

/// Render the elaborated `RuleAttributes` into the parser-AST attribute list,
/// in HS's order: color, process, (no_derivcheck), issapicrule, role.  The
/// pretty-printer's `rule_attribute_parts` re-orders to the canonical render
/// order, so list order here is not load-bearing — but we keep it tidy.
fn synth_attrs(attr: &tamarin_theory::rule::RuleAttributes) -> Vec<p::RuleAttr> {
    let mut out = Vec::new();
    if let Some(c) = &attr.color {
        // `color=#rrggbb` — pretty_theory lowercases + strips the leading `#`,
        // so pass the hex without the `#` here.
        let hex = tamarin_utils::color::rgb_to_hex(*c);
        out.push(p::RuleAttr::Color(hex.trim_start_matches('#').to_string()));
    }
    if let Some(proc) = &attr.process {
        out.push(p::RuleAttr::Process(pretty_sapic_top_level(proc)));
    }
    if attr.ignore_deriv_checks {
        out.push(p::RuleAttr::NoDerivCheck);
    }
    if attr.is_sapic_rule {
        out.push(p::RuleAttr::IsSapicRule);
    }
    if let Some(r) = &attr.role {
        out.push(p::RuleAttr::Role(r.clone()));
    }
    out
}
