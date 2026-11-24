// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Elaboration: parser AST → typed `Theory`.
//!
//! This pass takes a `tamarin_parser::ast::Theory` (the surface syntax
//! tree) and produces a `crate::theory::Theory` (typed), mirroring the
//! Haskell `processOpenTheory`. It handles:
//!
//! - Theory header (`name`, `in_file`, `is_diff`)
//! - `builtins:` → `MaudeSig` (we record the names; full sig
//!   composition starts from `minimal_maude_sig`)
//! - `functions:`/`equations:`/`macros:` → signature registration
//!   (`st_fun_syms`, `CtxtStRule`s when convertible, macro definitions), plus a
//!   `TranslationElement::FunctionTypingInfo` item per `functions:` declaration
//! - `predicates:` → `theory::Predicate`, which the later items of the same
//!   theory are expanded against (`predicate::expand_formula`)
//! - Rules — `parser::Rule` → `OpenProtoRule(ProtoRuleE, [])`
//! - Lemmas and restrictions — the formula is converted to `LNFormula`
//!   (`item_formula`)
//! - The declared macros applied to the internal rule, lemma and restriction
//!   (`rule::apply_macro_in_rule`, `theory::apply_macro_in_lemma`,
//!   `restriction::apply_macro_in_restriction`), which also records the
//!   pre-macro formula HS keeps as `_lOriginalFormula` /
//!   `_rstrOriginalFormula`
//!
//! It also provides the parser→internal conversion helpers used above:
//! `term_to_lnterm` and the SAPIC term/fact converters
//! (`term_to_sapic_term`/`fact_to_sapic_fact`).
//!
//! Returned errors describe the surface offence (e.g. "duplicate process:
//! P"), with no internal panics.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_parser::ast as p;
use tamarin_term::apply::Apply;
use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
use tamarin_term::lterm::{occurs_free, LVar};

use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{minimal_maude_sig, MaudeSig};
use tamarin_term::term::{f_app_no_eq, Term};
use tamarin_term::vterm::{Lit, VTerm};

use crate::constraint::constraints::{Disj, Goal, SplitId};
use crate::formula::LNFormula;
use crate::guarded::{formula_to_guarded, GuardError};
use crate::restriction::{apply_macro_in_restriction, Restriction};
use crate::rule::{
    ConcIdx, PremIdx, ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes,
};
use crate::theory::{
    apply_macro_in_lemma, AccLemma, CaseTest, LNMacro, Lemma, OpenProtoRule, ProcessDef, ProofTree,
    SapicFunSym, Theory, TheoryItem, TranslationElement,
};
use crate::tools::equation_store::LNSubst;

#[derive(Debug, Clone)]
pub struct ElabError {
    pub message: String,
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "elaboration error: {}", self.message)
    }
}
impl std::error::Error for ElabError {}

/// Collect every `Name` constant of a term in traversal order — HS
/// `universeBi t` at `[Name]`, which both name reports filter by
/// `sortOfName` (Wellformedness.hs).  Generic over the variable
/// type so it serves both `LNTerm` (rule facts) and `SapicTerm` (process
/// terms).
pub(crate) fn collect_names<V>(t: &VTerm<Name, V>, out: &mut Vec<Name>) {
    match t {
        Term::Lit(Lit::Con(n)) => out.push(*n),
        Term::Lit(Lit::Var(_)) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                collect_names(a, out);
            }
        }
    }
}

/// Walk every node of a SAPIC process (`pfoldMap`), collecting the `Name`
/// constants of each node's terms — the `universeBi` reach over the source
/// subprocess HS attaches to a generated rule.  HS's `universeBi` is
/// field-exhaustive: it also descends into each node's
/// `ProcessParsedAnnotation.location` term, into a `Cond` combinator's
/// condition formula and into an `Msr` action's embedded `_restrict`
/// formulas (all `Data` in HS), so those are harvested here too.
pub(crate) fn collect_process_names(p: &crate::sapic::PlainProcess, out: &mut Vec<Name>) {
    use crate::sapic::{Process, ProcessCombinator as PC, SapicAction as SA};
    crate::sapic::for_each_process(p, &mut |node| {
        let ann = match node {
            Process::Null(a) => a,
            Process::Action(_, a, _) => a,
            Process::Comb(_, a, _, _) => a,
        };
        if let Some(loc) = &ann.location {
            collect_names(loc, out);
        }
        match node {
            Process::Null(_) => {}
            Process::Action(ac, _, _) => match ac {
                SA::ChIn { chan, msg, .. } => {
                    if let Some(c) = chan {
                        collect_names(c, out);
                    }
                    collect_names(msg, out);
                }
                SA::ChOut { chan, msg } => {
                    if let Some(c) = chan {
                        collect_names(c, out);
                    }
                    collect_names(msg, out);
                }
                SA::Insert(a, b) => {
                    collect_names(a, out);
                    collect_names(b, out);
                }
                SA::Delete(a) | SA::Lock(a) | SA::Unlock(a) => collect_names(a, out),
                SA::Event(fa) => {
                    for t in fa.terms.iter() {
                        collect_names(t, out);
                    }
                }
                SA::ProcessCall(_, args) => {
                    for t in args {
                        collect_names(t, out);
                    }
                }
                SA::Msr {
                    prems,
                    acts,
                    concs,
                    rest,
                    ..
                } => {
                    for fa in prems.iter().chain(acts).chain(concs) {
                        for t in fa.terms.iter() {
                            collect_names(t, out);
                        }
                    }
                    // An embedded `_restrict` formula is part of the source
                    // subprocess the generated rule carries, so its `'c'`
                    // literals are `Name` constants `universeBi` reaches.
                    for f in rest {
                        crate::formula::for_each_formula_term(f, &mut |t| collect_names(t, out));
                    }
                }
                SA::Rep | SA::New(_) => {}
            },
            Process::Comb(c, _, _, _) => match c {
                PC::CondEq(a, b) => {
                    collect_names(a, out);
                    collect_names(b, out);
                }
                PC::Lookup(t, _) => collect_names(t, out),
                PC::Let { left, right, .. } => {
                    collect_names(left, out);
                    collect_names(right, out);
                }
                // A condition is a `SapicNFormula`, so its `'c'` literals are
                // the same `Name` constants `universeBi` collects everywhere
                // else; a declared nullary symbol is an `App` and contributes
                // nothing.
                PC::Cond(f) => {
                    crate::formula::for_each_formula_term(f, &mut |t| collect_names(t, out))
                }
                PC::Parallel | PC::Ndc => {}
            },
        }
    });
}

/// Elaborate a parser theory with no source path ([`elaborate_with_in_file`]
/// with an empty one): a `heuristic:` header's bare `o` ranking then falls
/// back to the plain `oracle` name.
pub fn elaborate(parser_thy: &p::Theory) -> Result<Theory, ElabError> {
    elaborate_with_in_file(parser_thy, "")
}

/// Elaborate a parser theory into a typed `Theory`. The signature is
/// initialised from the union of `builtins:` declarations, and every
/// formula-bearing item is expanded against the `predicates:` declared before
/// it (`elaborate_items`).
///
/// `in_file` is the theory's source path.  HS's parser resolves the
/// `heuristic:` header's default oracle names against it while building the
/// theory (`defaultOracleNames`, Theory/Text/Parser.hs).
pub fn elaborate_with_in_file(parser_thy: &p::Theory, in_file: &str) -> Result<Theory, ElabError> {
    let sig = minimal_maude_sig(parser_thy.is_diff);
    let mut thy: Theory = Theory::new(parser_thy.name.clone(), sig);
    thy.in_file = in_file.to_string();
    if let Some(cfg) = &parser_thy.configuration {
        thy.items.push(TheoryItem::ConfigBlock(cfg.clone()));
    }

    elaborate_items(&parser_thy.items, &mut thy)?;
    // The `heuristic:` headers, parsed once the whole item list is known so
    // that a `{name}` ranking finds a `tactic:` declared after it.  HS parses
    // them into `[GoalRanking ProofContext]` in the parser itself
    // (`heuristic`, Theory/Text/Parser/Signature.hs) and stores that
    // list (`addHeuristic`, TheoryObject.hs).
    let mut heuristic_headers = parser_thy.items.iter().filter_map(|item| match item {
        p::TheoryItem::Heuristic { raw, source_file } => Some((raw, source_file)),
        _ => None,
    });
    if let Some((h, source_file)) = heuristic_headers.next() {
        let source_file = source_file.as_deref().unwrap_or(in_file);
        thy.heuristic = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            h,
            source_file,
            &thy.tactic,
        );
        thy.heuristic_in_file = Some(source_file.to_string());
    }
    if heuristic_headers.next().is_some() {
        return Err(ElabError {
            message: "default heuristic already defined".to_string(),
        });
    }

    // Freeze every lemma-local ranking after the full tactic list is known.
    // The declaring file was copied directly during elaboration, so this
    // needs no fragile parser-item/name join and handles repeated attributes.
    let tactics = &thy.tactic;
    for item in &mut thy.items {
        let (attributes, source_file) = match item {
            TheoryItem::Lemma(lemma) => (&mut lemma.attributes, &lemma.heuristic_in_file),
            TheoryItem::Translation(TranslationElement::AccLemma(lemma)) => {
                (&mut lemma.attributes, &lemma.heuristic_in_file)
            }
            _ => continue,
        };
        let source_file = source_file.as_deref().unwrap_or(in_file);
        for attribute in attributes {
            if let crate::theory::LemmaAttr::Heuristic(raw) = attribute {
                let rankings = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
                    raw,
                    source_file,
                    tactics,
                );
                *raw = crate::pretty_theory::pretty_goal_rankings(&rankings);
            }
        }
    }
    Ok(thy)
}

/// Join of the `[NDC]` and `[NDC-diff]` attributes (HS `function`'s `joinNDC`).
fn ndc_state_of(ndc: bool, ndc_diff: bool) -> NdcState {
    let a = if ndc {
        NdcState::IsNdc
    } else {
        NdcState::NotNdc
    };
    let b = if ndc_diff {
        NdcState::IsNdcDiff
    } else {
        NdcState::NotNdc
    };
    a.join(b)
}

/// The symbol a `functions:` declaration adds to the signature (HS
/// `function`, Theory/Text/Parser/Signature.hs): the declared name, arity
/// and attribute flags.
fn function_decl_sym(d: &p::FunctionDecl) -> tamarin_term::function_symbols::UserDefinedSym {
    use tamarin_term::function_symbols::UserDefinedSym;
    let privacy = if d.private {
        Privacy::Private
    } else {
        Privacy::Public
    };
    let constructability = if d.destructor {
        Constructability::Destructor
    } else {
        Constructability::Constructor
    };
    let ndc = ndc_state_of(d.ndc, d.ndc_diff);
    if d.ac {
        UserDefinedSym::AcFctUser(AcFctSym::new(
            d.name.as_bytes().to_vec(),
            privacy,
            constructability,
            ndc,
        ))
    } else {
        UserDefinedSym::NoEqUser(
            NoEqSym::new(
                d.name.as_bytes().to_vec(),
                d.arg_types.len(),
                privacy,
                constructability,
            )
            .with_ndc(ndc),
        )
    }
}

/// The `SapicFunSym` a `functions:` declaration records as its
/// `FunctionTypingInfo` item (HS `function`,
/// Theory/Text/Parser/Signature.hs): the declared symbol paired with the
/// declared SAPIC argument and result types.
pub(crate) fn function_decl_typing_info(d: &p::FunctionDecl) -> SapicFunSym {
    SapicFunSym {
        sym: function_decl_sym(d),
        arg_types: d.arg_types.clone(),
        out_type: d.out_type.clone(),
    }
}

/// The signature and translation-option contribution of one theory item.
/// `builtins:`, `functions:`, `equations:` and `macros:` declarations build
/// `out.signature` and `out.options`; every other item kind leaves
/// `out` untouched.
///
/// The returned macros are a `macros:` item's declarations elaborated against
/// the signature as it stands at each one, which is why they are built here
/// and not from the finished signature; `elaborate_items` pushes them as a
/// `TheoryItem::Macros`. Every other item kind returns an empty list.
///
/// Signature-conflict rules (HS `extendSig` / `function`,
/// Theory/Text/Parser/Signature.hs) are enforced at parse
/// time (`Parser::enable_builtin` / `Parser::function_decl`) — the single
/// point where theories are ingested — so the declarations reaching here are
/// conflict-free and this step only BUILDS the signature.
fn maude_sig_step(item: &p::TheoryItem, out: &mut Theory) -> Result<Vec<LNMacro>, ElabError> {
    match item {
        p::TheoryItem::Builtins(names) => {
            let mut s = std::mem::take(&mut out.signature);
            for name in names {
                if let Some(sig) = tamarin_parser::parser::builtin_maude_sig(name) {
                    s = s.merge(sig);
                }
                // NOTE: `diffie-hellman` already arrives with `enable_dh`
                // set (its MaudeSig is `dh_maude_sig`, see
                // builtinsDiffNames in
                // Theory/Text/Parser/Signature.hs),
                // and `merge` ORs `enable_dh`, so no explicit force is
                // needed here.  `diff` is a header/CLI flag handled via
                // the base signature's diff bit, never a `builtins:` entry.
            }
            out.signature = s;
        }
        p::TheoryItem::Functions(decls) => {
            for d in decls {
                // HS `function`'s fst/snd short-circuit (Theory/Text/
                // Parser/Signature.hs, name-only by design — it tests
                // neither arity nor privacy): a re-declared fst/snd
                // resolves to the EXISTING symbol and `addFunSym` is
                // never reached, so `functions: fst/1 [destructor]`
                // alone must NOT flip the signature to the destructor
                // variant (only `builtins: dest-pairing` does that).
                if (d.name == "fst" || d.name == "snd")
                    && out
                        .signature
                        .st_fun_syms
                        .iter()
                        .any(|s| s.name == d.name.as_bytes())
                {
                    continue;
                }
                // `add_fun_sym` consumes `self`; move the signature out
                // rather than clone it per declaration.
                let cur = std::mem::take(&mut out.signature);
                out.signature = cur.add_fun_sym(function_decl_sym(d));
            }
        }
        p::TheoryItem::Equations { eqs, convergent } => {
            // Port of Haskell `addEquationsM` (Theory.hs).
            // Convert each LHS=RHS pair to a CtxtStRule via
            // `rrule_to_ctxt_st_rule` and install it on the MaudeSig
            // so Maude sees the rewrite rule in its `fmod MSG ...`
            // module.  Convergent flag is stored as informational.
            let mut s = std::mem::take(&mut out.signature);
            s.eq_convergent = *convergent;
            for eq in eqs {
                // Haskell's `equation` parser hard-fails with
                // "Not a correct equation: ..." when an LHS=RHS pair
                // cannot be converted to a CtxtStRule
                // (Theory/Text/Parser/Signature.hs).  Match
                // that failure behaviour rather than silently dropping.
                let (Some(l), Some(r)) = (term_to_lnterm(&eq.lhs, &s), term_to_lnterm(&eq.rhs, &s))
                else {
                    return Err(ElabError {
                        message: "Not a correct equation".to_string(),
                    });
                };
                let rrule = tamarin_term::rewriting::RRule::new(l, r);
                match tamarin_term::subterm_rule::rrule_to_ctxt_st_rule(&rrule) {
                    Some(ctxt) => s = s.add_ctxt_st_rule(ctxt),
                    None => {
                        return Err(ElabError {
                            message: "Not a correct equation".to_string(),
                        });
                    }
                }
            }
            out.signature = s;
        }
        p::TheoryItem::Macros(macros) => {
            let mut ms = Vec::new();
            for m in macros {
                let args: Vec<LVar> = m.args.iter().map(varspec_to_lvar).collect();
                // HS `macro` parses the body with `msetterm False llit`
                // (Theory/Text/Parser/Macro.hs), which has no pattern-match (`=t`)
                // production, so a body that converts to a `PatMatch`
                // here would be a hard parse failure in HS — and
                // `addMacroSym` (Theory/Text/Parser/Macro.hs) always runs for any parsed
                // macro.  Returning an error therefore matches HS's
                // parse-fail semantics: silently skipping would drop both
                // the `LNMacro` push and the fun-sym registration.
                // `term_to_lnterm` returns None only on `PatMatch`, which
                // the surface macro parser never places in a body.
                let body = match term_to_lnterm(&m.body, &out.signature) {
                    Some(t) => t,
                    None => {
                        return Err(ElabError {
                            message: format!("could not elaborate macro body for `{}`", m.name),
                        });
                    }
                };
                // Register macro fun-sym in MaudeSig — mirrors HS
                // `addMacroSym (op,(k,Private,Destructor,NotNDC))`
                // (Theory/Text/Parser/Macro.hs) and
                // `macroToFunSym` (Term/Macro.hs).  After parser-
                // AST macro expansion (run in `elaborate()` above)
                // no call site references the macro name, but
                // the fun-sym must still be present in MaudeSig so
                // Maude / source precomputation / round-trip parsers
                // see the same signature as HS.
                let sym = NoEqSym::new(
                    m.name.as_bytes().to_vec(),
                    args.len(),
                    Privacy::Private,
                    Constructability::Destructor,
                );
                // Move the sig out via `take` (add_macro_sym consumes
                // `self`) to avoid a per-macro deep clone; behaviour and
                // ordering are identical.
                let cur = std::mem::take(&mut out.signature);
                out.signature = cur.add_macro_sym(sym);
                ms.push(LNMacro::new(m.name.as_bytes().to_vec(), args, body));
            }
            return Ok(ms);
        }
        _ => {}
    }
    Ok(Vec::new())
}

fn elaborate_items(items: &[p::TheoryItem], out: &mut Theory) -> Result<(), ElabError> {
    // The predicates declared so far, in source order.  HS expands a lemma or
    // restriction against `theoryPredicates thy` as it is added
    // (Theory/Text/Parser.hs, TheoryObject.hs), so an item
    // textually before a `predicates:` block does not see it.
    let mut preds: Vec<crate::predicate::Predicate> = Vec::new();
    // The macros declared so far, read back from the items pushed for them.
    // HS applies `theoryMacros thy0` to every item at close time
    // (`closeTheoryItem`, CloseRule.hs); a macro call that precedes its
    // `macros:` block is an "unknown operator" parse failure
    // (`lookupArity`, Theory/Text/Parser/Term.hs), so the two lists
    // agree on every theory that parses.
    let mut macros: Vec<LNMacro> = Vec::new();
    // HS's parser inlines a `P(args)` call against only the definitions the
    // theory holds when the call is read (`checkProcess`,
    // Theory/Text/Parser/Sapic.hs). The RS parser keeps calls, so this
    // environment grows in source order. It stores already-converted bodies:
    // later definitions cannot retroactively satisfy an earlier call.
    let mut process_defs = crate::process_inline::ProcessDefMap::new();
    for item in items.iter() {
        match item {
            p::TheoryItem::Builtins(names) => {
                maude_sig_step(item, out)?;
                for name in names {
                    out.items.push(TheoryItem::Translation(
                        TranslationElement::SignatureBuiltin(name.clone()),
                    ));
                }
            }
            p::TheoryItem::Functions(decls) => {
                maude_sig_step(item, out)?;
                // HS folds `addFunctionTypingInfo` over the block's
                // declarations (Theory/Text/Parser.hs,
                // TheoryObject.hs): one `FunctionTypingInfo` item per
                // declaration, in source order.
                for d in decls {
                    out.items.push(TheoryItem::Translation(
                        TranslationElement::FunctionTypingInfo(function_decl_typing_info(d)),
                    ));
                }
            }
            p::TheoryItem::Equations { .. } => {
                maude_sig_step(item, out)?;
            }
            p::TheoryItem::Macros(_) => {
                let ms = maude_sig_step(item, out)?;
                if !ms.is_empty() {
                    out.items.push(TheoryItem::Macros(ms));
                    macros = out.macros().cloned().collect();
                }
            }
            p::TheoryItem::Predicates(predicates) => {
                // HS `preddeclaration` folds `liftedAddPredicate` over the
                // block (Theory/Text/Parser/Signature.hs), which
                // appends a `PredicateItem` per declaration.
                for pd in predicates {
                    let pred = crate::predicate::from_parser(pd, &out.signature)?;
                    preds.push(pred.clone());
                    out.items.push(TheoryItem::Predicate(pred));
                }
            }
            p::TheoryItem::Options(opts) => {
                for n in opts {
                    out.options.set_declarable(n);
                }
            }
            // The `heuristic:` header is parsed after the item walk, where
            // the theory's whole tactic list is known.
            p::TheoryItem::Heuristic { .. } => {}
            p::TheoryItem::Tactic(t) => {
                out.tactic.push(t.clone());
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                let restr = Restriction {
                    name: r.name.clone(),
                    formula: item_formula(&r.formula, &out.signature, &preds)?,
                    original_formula: None,
                };
                out.items
                    .push(TheoryItem::Restriction(apply_macro_in_restriction(
                        &macros, restr,
                    )));
            }
            // HS routes these into `_thyCache`, outside the printable item
            // stream; the close pass appends generated deduction rules later.
            p::TheoryItem::IntrRule(r) => {
                let rule = crate::intruder_variants::ast_rule_to_intr_rule_ac(&out.signature, r)
                    .map_err(|message| ElabError { message })?;
                if !out.intruder_rules.contains(&rule) {
                    out.intruder_rules.push(rule);
                }
            }
            p::TheoryItem::Rule(r) => {
                let e = rule_to_proto_rule_e(r, &out.signature)?;
                // `protoRule`'s `variants` block
                // (Theory/Text/Parser/Rule.hs).
                let rule_ac = r
                    .variants
                    .iter()
                    .map(|v| rule_to_proto_rule_e(v, &out.signature))
                    .collect::<Result<Vec<_>, _>>()?;
                // Diff theories skip the duplicate guard, as the parser's
                // does: `liftedAddDiffRule` is not ported.
                let guard = !out.signature.enable_diff;
                lifted_add_proto_rule(out, e, rule_ac, &preds, &macros, guard)?;
            }
            p::TheoryItem::Lemma(l) => {
                let msig = &out.signature;
                let heuristic_in_file = l
                    .attributes
                    .iter()
                    .any(|attr| matches!(attr, crate::theory::LemmaAttr::Heuristic(_)))
                    .then(|| l.source_file.clone().unwrap_or_else(|| out.in_file.clone()));
                let lem: Lemma = Lemma {
                    name: l.name.clone(),
                    heuristic_in_file,
                    attributes: l.attributes.clone(),
                    trace_quantifier: l.trace_quantifier,
                    formula: item_formula(&l.formula, msig, &preds)?,
                    original_formula: None,
                    proof: match l.proof.as_ref().and_then(|p| p.tree.as_ref()) {
                        Some(t) => {
                            Some(proof_tree_from_parsed(t, msig).map_err(|e| ElabError {
                                message: format!(
                                    "in the proof of lemma `{}`: {}",
                                    l.name, e.message
                                ),
                            })?)
                        }
                        None => None,
                    },
                    plaintext: l.plaintext.clone(),
                };
                out.items
                    .push(TheoryItem::Lemma(apply_macro_in_lemma(&macros, lem)));
            }
            p::TheoryItem::DiffLemma(_dl) => {
                // Unreachable for a non-diff theory: HS only parses
                // `diffLemma` inside `diffTheory`/`addDiffLemma`
                // (Theory/Text/Parser/Lemma.hs), so a regular theory
                // never yields a DiffLemma item. Defensive no-op.
            }
            p::TheoryItem::AccLemma(a) => {
                let heuristic_in_file = a
                    .attributes
                    .iter()
                    .any(|attr| matches!(attr, crate::theory::LemmaAttr::Heuristic(_)))
                    .then(|| a.source_file.clone().unwrap_or_else(|| out.in_file.clone()));
                let acc = AccLemma {
                    name: a.name.clone(),
                    heuristic_in_file,
                    attributes: a.attributes.clone(),
                    formula: crate::formula::from_parser(&a.formula, &out.signature)?,
                    case_test_idents: a.case_test_idents.clone(),
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::AccLemma(acc)));
            }
            p::TheoryItem::CaseTest(c) => {
                let ct = CaseTest {
                    name: c.name.clone(),
                    formula: crate::formula::from_parser(&c.formula, &out.signature)?,
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::CaseTest(ct)));
            }
            p::TheoryItem::TopLevelProcess(proc) => {
                // `toplevelprocess` adds a `ProcessItem`
                // (Theory/Text/Parser/Sapic.hs,
                // Theory/Text/Parser.hs).
                let pp = elaborate_process(proc, &process_defs, &out.signature)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::Process(pp)));
            }
            p::TheoryItem::ProcessDef(d) => {
                // `processDef` stores the body and the declared formals
                // (Theory/Text/Parser/Sapic.hs); `_pVars` is `Nothing`
                // for a `let P = …` written without a parameter list.
                if process_defs.contains_key(&d.name) {
                    return Err(ElabError {
                        message: format!("duplicate process: {}", d.name),
                    });
                }
                let body = elaborate_process(&d.body, &process_defs, &out.signature)?;
                let vars = d
                    .vars
                    .as_ref()
                    .map(|vs| vs.iter().map(varspec_to_sapic).collect());
                let def = ProcessDef {
                    name: d.name.clone(),
                    vars,
                    body,
                };
                process_defs.insert(d.name.clone(), def.clone());
                out.items
                    .push(TheoryItem::Translation(TranslationElement::ProcessDef(def)));
            }
            p::TheoryItem::EquivLemma(p1, p2) => {
                // `equivLemma` (Theory/Text/Parser/Sapic.hs).
                let msig = &out.signature;
                let c1 = elaborate_process(p1, &process_defs, msig)?;
                let c2 = elaborate_process(p2, &process_defs, msig)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::EquivLemma(
                        c1, c2,
                    )));
            }
            p::TheoryItem::DiffEquivLemma(proc) => {
                // `diffEquivLemma` (Theory/Text/Parser/Sapic.hs).
                let pp = elaborate_process(proc, &process_defs, &out.signature)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::DiffEquivLemma(
                        pp,
                    )));
            }
            p::TheoryItem::Export { tag, body } => {
                out.items
                    .push(TheoryItem::Translation(TranslationElement::ExportInfo {
                        tag: tag.clone(),
                        body: body.clone(),
                    }));
            }
            p::TheoryItem::FormalComment { header, body } => {
                out.items
                    .push(TheoryItem::Text((header.clone(), body.clone())));
            }
        }
    }
    Ok(())
}

/// HS `addRestriction` (TheoryObject.hs) as `liftedAddRestriction`
/// (Theory/Text/Parser.hs) throws its failure: a restriction whose name the
/// theory already declares is a `duplicate restriction`.
pub fn add_restriction(thy: &mut Theory, restr: Restriction) -> Result<(), ElabError> {
    if thy.lookup_restriction(&restr.name).is_some() {
        return Err(ElabError {
            message: format!("duplicate restriction: {}", restr.name),
        });
    }
    thy.items.push(TheoryItem::Restriction(restr));
    Ok(())
}

/// HS `liftedAddProtoRule` (Theory/Text/Parser.hs): add one restriction per
/// `_restrict` formula BEFORE the rule, each through [`add_restriction`],
/// append the actions that reach them to the rule, then add the rule through
/// `addOpenProtoRule`'s guard
/// (OpenTheory.hs): a name already bound to a different open rule is a
/// `duplicate rule`, while an identical one is appended again.  The SAPIC
/// translation adds its generated rules through the same function.  A parse
/// through [`parse_theory_checked`] has already run the guard on the parsed
/// rules, with a position; `guard_duplicates` runs it again here, for the
/// generated rules and for theories parsed without the check.
///
/// `closeProtoRule` narrows `applyMacroInRule macros ruE` into the AC half and
/// keeps `ruE` itself as the `cprRuleE` half (lib/theory/src/Rule.hs); a rule
/// whose body calls no macro leaves the two identical.
pub fn lifted_add_proto_rule(
    thy: &mut Theory,
    mut rule: ProtoRuleE,
    rule_ac: Vec<ProtoRuleE>,
    predicates: &[crate::predicate::Predicate],
    macros: &[LNMacro],
    guard_duplicates: bool,
) -> Result<(), ElabError> {
    for restr in crate::rule_restriction::lift_rule_restrictions(&mut rule, predicates)? {
        add_restriction(thy, apply_macro_in_restriction(macros, restr))?;
    }
    let mut opr = OpenProtoRule::new(crate::rule::apply_macro_in_rule(macros, rule.clone()));
    let name = opr.name();
    if guard_duplicates
        && thy
            .rules()
            .find(|prev| prev.name() == name)
            .is_some_and(|prev| prev.rule_e() != &rule || prev.rule_ac != rule_ac)
    {
        return Err(ElabError {
            message: format!("duplicate rule: {name}"),
        });
    }
    if opr.rule != rule {
        opr.rule_e = Some(Box::new(rule));
    }
    opr.rule_ac = rule_ac;
    thy.items.push(TheoryItem::Rule(opr));
    Ok(())
}

/// [`tamarin_parser::RuleConflictCheck`] as [`lifted_add_proto_rule`]'s guard
/// compares: each rule built and lifted under the signature and predicates
/// declared before it, the first rule of each name kept in that form as HS
/// `liftedAddProtoRule` stores it.
///
/// The check costs nothing until a rule name repeats. It logs the
/// declarations and the first rule of each name; a repeated name drains the
/// log in order, applying each declaration to one running scope and lifting
/// each first rule in the scope it was declared in. The check stops for good
/// at the first declaration or rule that does not elaborate, as the load stops
/// there with its error.
///
/// An `[AC]` symbol applied to nothing raises HS's `fAppAC` error, which HS
/// raises only where something forces the term. The check builds it as an
/// inert constant ([`tamarin_term::term::with_empty_ac_as_constant`]) and
/// compares it like any other term, so it never raises; elaboration raises
/// the error when the theory loads. A theory with such a term is therefore
/// rejected, as a duplicate rule or with `fAppAC`, though not always with the
/// error HS reaches first.
pub struct RuleConflicts {
    /// The declarations and first rules the scope below has not taken in,
    /// in source order.
    log: Vec<Logged>,
    thy: Theory,
    preds: Vec<crate::predicate::Predicate>,
    /// The names of the rules declared so far.
    names: BTreeSet<String>,
    /// The first rule of each name the scope has taken in.
    rules: BTreeMap<String, LiftedRule>,
    /// Whether the scope reached an item that does not elaborate.
    stopped: bool,
}

enum Logged {
    Declaration(p::TheoryItem),
    /// The first rule of its name.
    Rule(p::Rule),
}

type LiftedRule = (crate::rule::ProtoRuleE, Vec<crate::rule::ProtoRuleE>);

impl Default for RuleConflicts {
    fn default() -> Self {
        Self {
            log: Vec::new(),
            // The parser runs the check outside diff mode only.
            thy: Theory::new(String::new(), minimal_maude_sig(false)),
            preds: Vec::new(),
            names: BTreeSet::new(),
            rules: BTreeMap::new(),
            stopped: false,
        }
    }
}

impl RuleConflicts {
    fn lifted(&self, r: &p::Rule) -> Option<LiftedRule> {
        let mut e = rule_to_proto_rule_e(r, &self.thy.signature).ok()?;
        let rule_ac = r
            .variants
            .iter()
            .map(|v| rule_to_proto_rule_e(v, &self.thy.signature))
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        crate::rule_restriction::lift_rule_restrictions(&mut e, &self.preds).ok()?;
        Some((e, rule_ac))
    }

    /// Take the log into the scope, stopping for good at the first item that
    /// does not elaborate.
    fn catch_up(&mut self) {
        for entry in std::mem::take(&mut self.log) {
            let elaborated = match entry {
                Logged::Rule(r) => match self.lifted(&r) {
                    Some(lifted) => {
                        self.rules.insert(r.name, lifted);
                        true
                    }
                    None => false,
                },
                Logged::Declaration(p::TheoryItem::Predicates(ps)) => ps.iter().all(|pd| {
                    crate::predicate::from_parser(pd, &self.thy.signature)
                        .map(|pred| self.preds.push(pred))
                        .is_ok()
                }),
                Logged::Declaration(item) => maude_sig_step(&item, &mut self.thy).is_ok(),
            };
            if !elaborated {
                self.stopped = true;
                return;
            }
        }
    }
}

impl tamarin_parser::RuleConflictCheck for RuleConflicts {
    fn declare(&mut self, item: &p::TheoryItem) {
        if self.stopped {
            return;
        }
        match item {
            p::TheoryItem::Rule(r) => {
                if self.names.insert(r.name.clone()) {
                    self.log.push(Logged::Rule(r.clone()));
                }
            }
            _ => self.log.push(Logged::Declaration(item.clone())),
        }
    }

    fn conflicts(&mut self, new: &p::Rule) -> bool {
        if !self.names.contains(&new.name) {
            return false;
        }
        tamarin_term::term::with_empty_ac_as_constant(|| {
            self.catch_up();
            if self.stopped {
                return false;
            }
            let Some(earlier) = self.rules.get(&new.name) else {
                return false;
            };
            self.lifted(new)
                .is_some_and(|new| earlier.0 != new.0 || earlier.1 != new.1)
        })
    }
}

/// [`tamarin_parser::parse_theory_with_rule_check`] with
/// [`RuleConflicts`]: HS's parse-time `duplicate rule` guard, as a
/// positioned diagnostic at the second rule's name.
pub fn parse_theory_checked(
    src: &str,
    flags: &[&str],
    base_dir: Option<std::path::PathBuf>,
) -> Result<p::Theory, tamarin_parser::ParseError> {
    tamarin_parser::parse_theory_with_rule_check(
        src,
        flags,
        base_dir,
        Box::new(RuleConflicts::default()),
    )
}

/// The formula HS's `liftedAddLemma` / `liftedAddRestriction` store: the
/// surface formula closed by [`crate::formula::from_parser`] and stripped of
/// its predicate sugar by `expandLemma` / `expandRestriction`
/// (Theory/Text/Parser.hs, TheoryObject.hs).  The expansion
/// IS the sugar stripper, so a use site with no matching predicate is the
/// only way it fails.
fn item_formula(
    f: &p::Formula,
    sig: &MaudeSig,
    preds: &[crate::predicate::Predicate],
) -> Result<LNFormula, ElabError> {
    let syn = crate::formula::from_parser(f, sig)?;
    crate::predicate::expand_formula(preds, &syn).map_err(|e| ElabError {
        message: format!("predicate expansion failed: {}", e),
    })
}

/// The `PlainProcess` a process-bearing item carries.  HS's parser builds it
/// while it reads the item, so the surface process tree is converted here,
/// against the signature the declarations before the item have built.
fn elaborate_process(
    proc: &p::Process,
    defs: &crate::process_inline::ProcessDefMap,
    sig: &MaudeSig,
) -> Result<crate::sapic::PlainProcess, ElabError> {
    crate::process_inline::convert_process_with_defs(proc, defs, sig).map_err(|e| ElabError {
        message: format!("SAPIC translation: {}", e.message),
    })
}

// =============================================================================
// Rule elaboration
// =============================================================================

/// Fold a parsed rule's attribute list into `RuleAttributes`, mirroring HS
/// `ruleAttributesp = option mempty (fold <$> list ruleAttribute)`
/// (`Theory/Text/Parser/Rule.hs`) and the per-attribute `ruleAttribute`
/// parser (`Theory/Text/Parser/Rule.hs`):
///   * `color=`/`colour=`  → `ruleColor` (`hexToRGB`);
///   * `process=`          → IGNORED (`parseAndIgnore`; the RS parser already
///                           drops it, so `RuleAttr::Process` never reaches here
///                           for user input — SAPIC synthesis aside — but the
///                           arm stays faithful);
///   * `no_derivcheck`     → `ignoreDerivChecks = True`;
///   * `role='...'`        → `role`;
///   * `issapicrule`       → `isSAPiCRule = True`;
///   * `x-<ext>`           → ignored.
///
/// `fold` combines via the `RuleAttributes` `Semigroup` (Theory/Model/Rule.hs):
/// later duplicates win on the `Option` fields (`preferRight`), bools `||`.
///
/// This carries a rule's SAPIC display attributes (role / color /
/// issapicrule) — HS's `toRule` bakes them straight into the `ProtoRuleE`.
/// Display-only: no solver / `--prove`-text path reads these fields (only the
/// web graph renderer does), so populating them is `--prove`-inert.
fn rule_attributes_from_parser(attrs: &[p::RuleAttr]) -> RuleAttributes {
    let mut out = RuleAttributes::empty();
    for a in attrs {
        match a {
            p::RuleAttr::Color(hex) => {
                if let Some(rgb) = tamarin_utils::color::hex_to_rgb(hex) {
                    out.color = Some(rgb);
                }
            }
            p::RuleAttr::NoDerivCheck => out.ignore_deriv_checks = true,
            p::RuleAttr::Role(s) => out.role = Some(s.clone()),
            p::RuleAttr::IsSapicRule => out.is_sapic_rule = true,
            // `process=` (dropped by the parser) and external attributes carry
            // no `RuleAttributes` field — HS `parseAndIgnore` / `parseExternal`.
            p::RuleAttr::Process(_) | p::RuleAttr::External(_, _) => {}
        }
    }
    out
}

pub(crate) fn rule_to_proto_rule_e(r: &p::Rule, sig: &MaudeSig) -> Result<ProtoRuleE, ElabError> {
    let facts = |fs: &[p::Fact]| {
        fs.iter()
            .map(|f| fact_to_lnfact(f, sig))
            .collect::<Result<Vec<_>, _>>()
    };
    let mut prems = facts(&r.premises)?;
    let mut acts = facts(&r.actions)?;
    let mut concs = facts(&r.conclusions)?;
    // HS `modify preRestriction (++ rs) ri` (Theory/Text/Parser/Rule.hs): the
    // rule carries its `_restrict` formulas as parsed — predicate atoms
    // unexpanded, since `liftedAddProtoRule` expands only the copies it lifts
    // (Theory/Text/Parser.hs).
    let mut restrictions = r
        .embedded_restrictions
        .iter()
        .map(|f| crate::formula::from_parser(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    // HS `apply subst (ps0,as0,cs0,rs0)` with `letBlock`'s
    // `foldr1 compose . map (substFromList . return)`
    // (Theory/Text/Parser/Rule.hs, Theory/Text/Parser/Let.hs).  Applying
    // `s1 `compose` ... `compose` sn` is applying sn, then ..., then s1, which
    // costs the rule's size per binding; building the composite rewrites
    // every image so far per binding, cubic in a chain of bindings.  The
    // formulas are locally nameless, so no binder can capture an image.
    for (v, t) in r.lets.iter().rev() {
        let var = varspec_to_lvar(v);
        let used = occurs_free(&var, &prems)
            || occurs_free(&var, &acts)
            || occurs_free(&var, &concs)
            || restrictions
                .iter()
                .any(|f| crate::formula::formula_frees_list(f).contains(&var));
        // HS evaluates an unused binding's image only as far as its outermost
        // symbol, where `substFromList` compares it with the variable once the
        // rule's terms are substituted (Term/Substitution/SubstVFree.hs).  So
        // of an unused image only an `[AC]` symbol applied to nothing raises,
        // and nothing else in it is checked.
        if !used && !matches!(t, p::Term::App(_, args) if args.is_empty()) {
            continue;
        }
        let t = term_to_lnterm(t, sig).ok_or_else(|| ElabError {
            message: format!("could not elaborate the let binding of `{}`", v.name),
        })?;
        if !used {
            continue;
        }
        let subst = LNSubst::from_list([(var, t)]);
        prems = prems.apply(&subst);
        acts = acts.apply(&subst);
        concs = concs.apply(&subst);
        restrictions = restrictions
            .into_iter()
            .map(|f| crate::formula::apply_subst(&subst, f))
            .collect();
    }
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&r.name)),
        attributes: rule_attributes_from_parser(&r.attributes),
        restrictions,
    };
    // HS `newVariables ps $ cs ++ as` (Theory/Text/Parser/Rule.hs).
    let new_vars = crate::fact::new_variables(&prems, &[&concs[..], &acts[..]].concat());

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Fact-tag mapping shared by [`fact_to_lnfact`] and [`fact_to_sapic_fact`].
///
/// Mirrors Haskell's parser in `Theory.Text.Parser.Fact.mkProtoFact`:
///   "OUT" → outFact (Out)
///   "IN"  → inFact  (In)
///   "KU"  → kuFact  (KUFact)
///   "KD"  → kdFact  (KDFact)
///   "DED" → dedLogFact (DedFact)
///   "FR"  → freshFact (Fresh)
///   else  → protoFact (ProtoFact tag with name)
///
/// Critically, `K` is *not* in this list — Haskell's parser falls
/// through to the protoFact case for "K", giving `ProtoFact Linear "K"`.
/// That matches ISend's action `kLogFact = protoFact Linear "K"`,
/// so user lemma `K(t) @ j` correctly matches ISend instances.
/// Do NOT alias "K" → FactTag::Ku: that breaks witness construction
/// for any lemma using K(_) atoms (they can no longer satisfy via
/// ISend; only Coerce/etc. routes would remain available).
pub fn fact_tag_of(f: &p::Fact) -> crate::fact::FactTag {
    use crate::fact::{FactTag, Multiplicity};
    match f.name.as_str() {
        "Fr" => FactTag::Fresh,
        "In" => FactTag::In,
        "Out" => FactTag::Out,
        "KU" => FactTag::Ku,
        "KD" => FactTag::Kd,
        "Ded" => FactTag::Ded,
        _ => FactTag::Proto(
            if f.persistent {
                Multiplicity::Persistent
            } else {
                Multiplicity::Linear
            },
            tamarin_term::intern::intern_str(f.name.as_str()),
            f.args.len(),
        ),
    }
}

/// A parser fact's annotation list as the `S.Set FactAnnotation` a
/// `Theory.Model.Fact` holds (Theory/Model/Fact.hs).
/// Shared by [`fact_to_lnfact`] and [`fact_to_sapic_fact`].
pub(crate) fn copy_fact_annotations(f: &p::Fact) -> BTreeSet<crate::fact::FactAnnotation> {
    f.annotations.iter().copied().collect()
}

pub fn fact_to_lnfact(f: &p::Fact, sig: &MaudeSig) -> Result<crate::fact::LNFact, ElabError> {
    use crate::fact::Fact;
    let tag = fact_tag_of(f);
    let terms: Result<Vec<_>, _> = f
        .args
        .iter()
        .map(|t| {
            term_to_lnterm(t, sig).ok_or_else(|| ElabError {
                message: format!("could not elaborate term in fact `{}`", f.name),
            })
        })
        .collect();
    Ok(Fact::new(tag, terms?).with_annotations(copy_fact_annotations(f)))
}

/// The internal [`Goal`](crate::constraint::constraints::Goal) of a stored
/// `solve( ... )` step.
///
/// HS's proof parser builds the `Goal` value directly (`goal`,
/// Theory/Text/Parser/Proof.hs), and `checkAndExecProofMethod` looks it
/// up in `sGoals` by structural equality (ProofMethod.hs).  The
/// parser AST reaches that value through the same converters the rest of the
/// theory goes through, so a stored goal and a live one are built the same
/// way.
///
/// A disjunct that `formula_to_guarded_parsed` rejects is an error here, as
/// `guardedFormula`'s `fail` is in HS (Theory/Text/Parser/Formula.hs).
pub fn goal_from_parsed(g: &p::GoalSpec, sig: &MaudeSig) -> Result<Goal, ElabError> {
    let term = |t: &p::Term| {
        term_to_lnterm(t, sig).ok_or_else(|| ElabError {
            message: "could not elaborate term in a stored proof goal".to_string(),
        })
    };
    match g {
        p::GoalSpec::Action(i, fa) => {
            Ok(Goal::Action(varspec_to_lvar(i), fact_to_lnfact(fa, sig)?))
        }
        p::GoalSpec::Chain((i, c), (j, v)) => Ok(Goal::Chain(
            (varspec_to_lvar(i), ConcIdx(*c as usize)),
            (varspec_to_lvar(j), PremIdx(*v as usize)),
        )),
        p::GoalSpec::Premise((i, v), fa) => Ok(Goal::Premise(
            (varspec_to_lvar(i), PremIdx(*v as usize)),
            fact_to_lnfact(fa, sig)?,
        )),
        p::GoalSpec::Split(n) => Ok(Goal::Split(SplitId(*n))),
        p::GoalSpec::Subterm(small, big) => Ok(Goal::Subterm((term(small)?, term(big)?))),
        p::GoalSpec::Disj(alts) => {
            let gfs = alts
                .iter()
                .map(|f| {
                    formula_to_guarded_parsed(f, sig).map_err(|e| ElabError {
                        message: format!(
                            "could not convert a disjunct of a stored proof goal: {}",
                            e.message
                        ),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Goal::Disj(Disj::new(gfs)))
        }
    }
}

/// Close and desugar a surface formula at the parser-to-theory boundary,
/// then convert the internal formula to guarded form.
pub fn formula_to_guarded_parsed(
    f: &p::Formula,
    sig: &MaudeSig,
) -> Result<crate::guarded::Guarded, GuardError> {
    let syn = crate::formula::from_parser(f, sig).map_err(|e| crate::guarded::err(e.message))?;
    let plain = crate::formula::to_lnformula(&syn).ok_or_else(|| {
        crate::guarded::err("Syntactic sugar is not allowed, guarded formula expected.")
    })?;
    formula_to_guarded(&plain)
}

/// The internal [`ProofMethod`](crate::constraint::solver::proof_method::ProofMethod)
/// of one stored proof step — the value HS's `proofMethod`
/// (Theory/Text/Parser/Proof.hs) builds directly.
pub fn proof_method_from_parsed(
    m: &p::ParsedMethod,
    sig: &MaudeSig,
) -> Result<crate::constraint::solver::proof_method::ProofMethod, ElabError> {
    use crate::constraint::solver::proof_method::{ProofMethod, Result as MethodResult};
    Ok(match m {
        p::ParsedMethod::Sorry => ProofMethod::Sorry(None),
        p::ParsedMethod::Simplify => ProofMethod::Simplify,
        p::ParsedMethod::SolveGoal(spec) => ProofMethod::SolveGoal(goal_from_parsed(spec, sig)?),
        p::ParsedMethod::Contradiction => ProofMethod::Finished(MethodResult::Contradictory(None)),
        p::ParsedMethod::Induction => ProofMethod::Induction,
        p::ParsedMethod::Invalidated => ProofMethod::Invalidated,
        p::ParsedMethod::Unfinishable => ProofMethod::Finished(MethodResult::Unfinishable),
        p::ParsedMethod::SolvedLeaf => ProofMethod::Finished(MethodResult::Solved),
    })
}

/// A lemma's stored proof as the internal [`ProofTree`], the shape HS's
/// `proofSkeleton` returns (Theory/Text/Parser/Proof.hs).
pub fn proof_tree_from_parsed(
    t: &p::ParsedProofTree,
    sig: &MaudeSig,
) -> Result<ProofTree, ElabError> {
    Ok(ProofTree {
        method: proof_method_from_parsed(&t.method, sig)?,
        cases: t
            .cases
            .iter()
            .map(|(name, sub)| Ok((name.clone(), proof_tree_from_parsed(sub, sig)?)))
            .collect::<Result<_, _>>()?,
    })
}

// =============================================================================
// Term conversion: parser::Term → LNTerm
// =============================================================================

/// A parse-time variable occurrence as the solver's `LVar`: sort, name and
/// index carried over, with the name interned.  The SAPIC-typed variant
/// wraps this in a `SapicLVar` with the `:type` annotation; the
/// `VarSpec.typ` field has no `LVar` counterpart and is dropped here.
pub(crate) fn varspec_to_lvar(v: &p::VarSpec) -> LVar {
    LVar::new(&v.name, v.sort, v.idx)
}

/// Shared structural walker: rebuild a parser-AST fact, mapping `g` over
/// every arg.  The fact arm of [`map_formula_terms`], which supplies its own
/// leaf `&Term -> Term`.
pub(crate) fn map_fact_terms(f: &p::Fact, g: &dyn Fn(&p::Term) -> p::Term) -> p::Fact {
    p::Fact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(g).collect(),
        annotations: f.annotations.clone(),
    }
}

/// Shared structural walker: rebuild an atom, mapping `g` over every term and
/// `map_fact_terms` over embedded facts.  See [`map_fact_terms`].
pub(crate) fn map_atom_terms(a: &p::Atom, g: &dyn Fn(&p::Term) -> p::Term) -> p::Atom {
    use p::Atom::*;
    match a {
        Eq(x, y) => Eq(g(x), g(y)),
        Less(x, y) => Less(g(x), g(y)),
        LessMset(x, y) => LessMset(g(x), g(y)),
        Subterm(x, y) => Subterm(g(x), g(y)),
        Action(f, t) => Action(map_fact_terms(f, g), g(t)),
        Last(t) => Last(g(t)),
        Pred(f) => Pred(map_fact_terms(f, g)),
    }
}

/// Shared structural walker: rebuild a formula, mapping `g` over every leaf
/// term while cloning quantifier `VarSpec`s unchanged.  See [`map_fact_terms`].
/// `pub` (not `pub(crate)`): tamarin-sapic's `formula_unpattern` walks with it
/// too.
pub fn map_formula_terms(f: &p::Formula, g: &dyn Fn(&p::Term) -> p::Term) -> p::Formula {
    use p::Formula::*;
    match f {
        False => False,
        True => True,
        Atom(a) => Atom(map_atom_terms(a, g)),
        Not(x) => Not(Box::new(map_formula_terms(x, g))),
        And(x, y) => And(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Or(x, y) => Or(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Implies(x, y) => Implies(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Iff(x, y) => Iff(
            Box::new(map_formula_terms(x, g)),
            Box::new(map_formula_terms(y, g)),
        ),
        Forall(vs, x) => Forall(vs.clone(), Box::new(map_formula_terms(x, g))),
        Exists(vs, x) => Exists(vs.clone(), Box::new(map_formula_terms(x, g))),
    }
}

/// Right-fold a non-empty term list into a right-associative `pair(..)` chain:
/// `[a, b, c]` → `pair(a, pair(b, c))`; `None` on an empty list.  Mirrors HS's
/// `tupleterm`'s `chainr1 ... (curry fAppPair)` (Theory/Text/Parser/Term.hs)
/// — the shared fold behind the arity-1 surplus-argument tuple and the `<..>`
/// tuple syntax.
fn right_nest_pair<V>(items: Vec<VTerm<Name, V>>) -> Option<VTerm<Name, V>> {
    let mut iter = items.into_iter().rev();
    let mut acc = iter.next()?;
    let sym = tamarin_term::function_symbols::pair_sym();
    for prev in iter {
        acc = f_app_no_eq(sym, vec![prev, acc]);
    }
    Some(acc)
}

/// What an application head resolves to: the free symbol HS `lookupArity`
/// answers with, or the user-defined `[AC]` symbol.
enum HeadSym {
    NoEq(NoEqSym),
    Ac(AcFctSym),
}

/// The symbol a prefix application of `name` at `arity` denotes.
///
/// HS `lookupArity` (Theory/Text/Parser/Term.hs) looks `name` up in
/// `userDefinedFunSyms` — free symbols before user-defined AC symbols — then
/// the macro names, and hands `naryOpApp` / `binaryAlgApp` the privacy,
/// constructability and NDC state of the first match, which those build
/// `fAppNoEq` / `fAppAC` from (Theory/Text/Parser/Term.hs).  A name
/// in both halves is therefore the FREE symbol; [`MaudeSig::fun_sym_named`]
/// preserves that order.
///
/// The arity is the one WRITTEN, not the one declared: HS rejects an
/// application whose two disagree (`naryOpApp`'s arity check), while this
/// parser is arity-unaware and accepts it.  A name the signature does not
/// declare — where HS fails with `unknown operator` — keeps the public
/// constructor default.
fn head_sym(sig: &MaudeSig, name: &str, arity: usize) -> HeadSym {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    match sig.fun_sym_named(name.as_bytes()) {
        Some(FunSym::NoEq(s)) => HeadSym::NoEq(NoEqSym { arity, ..s }),
        Some(FunSym::Ac(AcSym::AcFct(s))) => HeadSym::Ac(s),
        _ => HeadSym::NoEq(NoEqSym::new(
            name.as_bytes().to_vec(),
            arity,
            Privacy::Public,
            Constructability::Constructor,
        )),
    }
}

/// The `[AC]` symbol an infix application of `name` denotes.  HS `acterm`
/// builds `fAppACfct` straight from `stACFunSyms`
/// (Theory/Text/Parser/Term.hs), so a free symbol sharing the name —
/// which claims the prefix spelling in [`head_sym`] — does not claim this
/// one.  The default covers a name the signature has no `[AC]` symbol for,
/// which the parser does not emit: it writes `BinOp::AcFct` only for a name
/// its own signature state carries as an infix operator.
fn ac_fct_sym(sig: &MaudeSig, name: &str) -> AcFctSym {
    sig.ac_fct_sym_named(name.as_bytes()).unwrap_or_else(|| {
        AcFctSym::new(
            name.as_bytes().to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        )
    })
}

/// True when `name` is a free symbol of arity 1, which HS `naryOpApp` reads
/// off `lookupArity` to parse the argument list as ONE tuple term
/// (Theory/Text/Parser/Term.hs), folding `f(a, b, c)` to `f(<a, b, c>)`.
fn is_arity1_no_eq(sig: &MaudeSig, name: &str) -> bool {
    use tamarin_term::function_symbols::FunSym;
    matches!(sig.fun_sym_named(name.as_bytes()), Some(FunSym::NoEq(s)) if s.arity == 1)
}

/// Shared conversion core for [`term_to_lnterm`] and [`term_to_sapic_term`].
///
/// Every arm except the `Var` case is byte-identical between the LNTerm and
/// SAPIC term universes (same function-symbol / arity-1-fold / `em` / pair
/// logic).  `mk_var` reproduces the per-universe `Var` behaviour: LNTerm
/// builds a plain `LVar` literal; SAPIC builds a typed `SapicLVar` literal.
/// Recursion is threaded back through `term_to_vterm` so the whole tree is
/// built in one universe.  `sig` is the theory signature every application
/// head is resolved against, as HS `naryOpApp` / `binaryAlgApp` / `acterm`
/// resolve theirs through `lookupArity` over the parser state's signature
/// (Theory/Text/Parser/Term.hs).
fn term_to_vterm<V, F>(t: &p::Term, sig: &MaudeSig, mk_var: &F) -> Option<VTerm<Name, V>>
where
    V: Clone + Ord,
    F: Fn(&p::VarSpec) -> Option<VTerm<Name, V>>,
{
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::term::{f_app_ac, f_app_acfct};

    match t {
        p::Term::Var(v) => mk_var(v),
        p::Term::PubLit(s) => {
            let n = Name::new(NameTag::Pub, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::FreshLit(s) => {
            let n = Name::new(NameTag::Fresh, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::NatLit(s) => {
            let n = Name::new(NameTag::Nat, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::NumberOne => {
            // HS `fAppOne = fAppNoEq oneSym []` (Term/Term.hs); the
            // `"1"` keyword in the term parser dispatches to this
            // (Theory/Text/Parser/Term.hs).  Mirror exactly — emit
            // a 0-arity NoEq application of `oneSym`, NOT a public
            // constant.  Treating it as `Lit::Con(Pub,"1")` causes
            // source-case enumeration to mismatch HS's `c_one` rule.
            Some(f_app_no_eq(
                tamarin_term::function_symbols::one_sym(),
                vec![],
            ))
        }
        p::Term::DhNeutral => {
            // HS `fAppDHNeutral = fAppNoEq dhNeutralSym []` (Term/Term.hs);
            // dispatched by `symbol "DH_neutral" *> pure fAppDHNeutral`
            // (Theory/Text/Parser/Term.hs).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::dh_neutral_sym(),
                vec![],
            ))
        }
        p::Term::NatOne => {
            // HS `fAppNatOne = fAppNoEq natOneSym []` (Term/Term.hs); the
            // `1:nat` / `%1` keywords dispatch to this
            // (Theory/Text/Parser/Term.hs).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::nat_one_sym(),
                vec![],
            ))
        }
        p::Term::App(name, args) => {
            // HS `naryOpApp` (Theory/Text/Parser/Term.hs) parses the
            // arguments of an arity-1 symbol as one tuple, so `h(a, b, c)`
            // is `h(<a, b, c>)`.
            let unary = is_arity1_no_eq(sig, name);
            let new_args: Option<Vec<_>> =
                args.iter().map(|a| term_to_vterm(a, sig, mk_var)).collect();
            let mut new_args = new_args?;
            if unary && new_args.len() > 1 {
                // Wrap the surplus args into one right-associative pair so the
                // call stays arity-1.
                new_args = vec![right_nest_pair(new_args)?];
            }
            // `em(a, b)` under the bilinear-pairing builtin lowers to a
            // C-symbol application, not NoEq. HS `naryOpApp`
            // (Theory/Text/Parser/Term.hs) selects EMap only when the
            // bilinear-pairing symbol is present in the signature.
            // Classifying `em` as NoEq instead would declare the Maude
            // operator as `op tamem : Msg Msg -> Msg [comm]` (`pp_theory` in
            // maude_print.rs) while rule terms carry the NoEq prefix
            // `tamXCem` (`pp_maude_no_eq_sym_into`); Maude then rejects the
            // unknown operator and `get variants` returns an empty
            // parse-error reply, so variant disjunctions go missing and
            // smartRanking ranks un-narrowed `em` shapes (the RYY_PFS
            // `key_secrecy_PFS` proof-path divergence).
            //
            // Without bilinear pairing, a declared `em` remains an ordinary
            // user function. With the builtin it uses the commutative symbol.
            if name == "em" && new_args.len() == 2 && sig.enable_bp {
                let mut it = new_args.into_iter();
                let a = it.next().unwrap();
                let b = it.next().unwrap();
                return Some(tamarin_term::builtin::emap(a, b));
            }
            // #883 `naryOpApp` IsAC case: a user-declared `[AC]` symbol
            // lowers to an AC application (n-ary — the arity check applies
            // only to non-AC symbols) — unless a `NoEq` symbol shares the
            // name, in which case `lookupArity`'s NoEq-first lookup resolves
            // the spelling to that symbol instead ([`head_sym`]).  The infix
            // spelling is the `BinOp::AcFct` arm below.
            match head_sym(sig, name, new_args.len()) {
                HeadSym::Ac(s) => Some(f_app_acfct(s, new_args)),
                HeadSym::NoEq(s) => Some(f_app_no_eq(s, new_args)),
            }
        }
        p::Term::Pair(items) => {
            let new_items: Option<Vec<_>> = items
                .iter()
                .map(|i| term_to_vterm(i, sig, mk_var))
                .collect();
            // Right-associative pair: <a, b, c> = pair(a, pair(b, c)).
            right_nest_pair(new_items?)
        }
        p::Term::AlgApp(name, a, b) => {
            // `f{a}b` desugars to `f(a, b)` semantically; users typically
            // use this for senc/aenc/sign/mac.
            let aa = term_to_vterm(a, sig, mk_var)?;
            let bb = term_to_vterm(b, sig, mk_var)?;
            // Haskell `binaryAlgApp` also reads `(k,priv,cnstr)` from the
            // signature via `lookupArity` (Theory/Text/Parser/Term.hs),
            // so thread privacy/constructability here too.
            // #883: `[AC]` symbols build an AC application here as well —
            // under the same NoEq-first name resolution as the prefix
            // spelling ([`head_sym`]).
            match head_sym(sig, name, 2) {
                HeadSym::Ac(s) => Some(f_app_acfct(s, vec![aa, bb])),
                HeadSym::NoEq(s) => Some(f_app_no_eq(s, vec![aa, bb])),
            }
        }
        p::Term::Diff(a, b) => {
            let aa = term_to_vterm(a, sig, mk_var)?;
            let bb = term_to_vterm(b, sig, mk_var)?;
            // `diffOp` builds `fAppDiff` (Theory/Text/Parser/Term.hs), i.e.
            // `fAppNoEq diffSym` (Term/Term.hs) — and `diff` is PRIVATE
            // (`diffSym = (diffSymString,(2,Private,Constructor,NotNDC))`,
            // Term/Term/FunctionSymbols.hs).  The privacy is observable:
            // it is the first attribute char of the Maude operator name
            // (`tamPCFUdiff`), and `contains_private` keys off it.
            Some(f_app_no_eq(
                tamarin_term::function_symbols::diff_sym(),
                vec![aa, bb],
            ))
        }
        p::Term::BinOp(op, a, b) => {
            let aa = term_to_vterm(a, sig, mk_var)?;
            let bb = term_to_vterm(b, sig, mk_var)?;
            match op {
                p::BinOp::Mult => Some(f_app_ac(AcSym::Mult, vec![aa, bb])),
                p::BinOp::Union => Some(f_app_ac(AcSym::Union, vec![aa, bb])),
                p::BinOp::Xor => Some(f_app_ac(AcSym::Xor, vec![aa, bb])),
                p::BinOp::NatPlus => Some(f_app_ac(AcSym::NatPlus, vec![aa, bb])),
                // A user-declared `[AC]` symbol applied infix — ALWAYS the AC
                // application (HS `acterm` builds `fAppACfct` straight from
                // `stACFunSyms`, Theory/Text/Parser/Term.hs), even
                // when a `NoEq` symbol shares the name and claims the prefix
                // spelling.  It reads the same user-function signature for
                // the symbol's privacy / constructability / NDC flags.
                p::BinOp::AcFct(name) => Some(f_app_acfct(ac_fct_sym(sig, name), vec![aa, bb])),
                p::BinOp::Exp => Some(f_app_no_eq(
                    tamarin_term::function_symbols::exp_sym(),
                    vec![aa, bb],
                )),
            }
        }
        p::Term::PatMatch(_) => None,
    }
}

pub fn term_to_lnterm(t: &p::Term, sig: &MaudeSig) -> Option<tamarin_term::lterm::LNTerm> {
    let mk_var = |v: &p::VarSpec| -> Option<tamarin_term::lterm::LNTerm> {
        Some(Term::Lit(Lit::Var(varspec_to_lvar(v))))
    };
    term_to_vterm(t, sig, &mk_var)
}

// =============================================================================
// Term conversion: parser::Term → SapicTerm (VTerm<Name, SapicLVar>)
//
// Parallel to `term_to_lnterm`, but the literal/variable case preserves the
// SAPIC type annotation (`VarSpec.typ`) into `SapicLVar.stype`.  Mirrors HS's
// SAPIC term parser (`Theory.Text.Parser.Sapic.sapicterm = msetterm False
// ltypedlit`, Theory/Text/Parser/Sapic.hs), which builds
// `Term (Lit Name SapicLVar)` keeping
// the `name:type` annotation on each typed variable.  Reuses the SAME
// function-symbol / arity-1-fold / em / pair logic as `term_to_lnterm` (via
// `term_to_vterm`) so the resulting term universe matches the protocol-rule
// path exactly.
// =============================================================================

/// `parser::Term` → `SapicTerm`.  Returns `None` on a `PatMatch` term (the
/// surface SAPIC action parser never places one in a plain term position).
pub fn term_to_sapic_term(t: &p::Term, sig: &MaudeSig) -> Option<crate::sapic::SapicTerm> {
    let mk_var = |v: &p::VarSpec| -> Option<crate::sapic::SapicTerm> {
        Some(Term::Lit(Lit::Var(varspec_to_sapic(v))))
    };
    term_to_vterm(t, sig, &mk_var)
}

/// A parse-time variable occurrence as a SAPIC variable: the `LVar` of
/// [`varspec_to_lvar`] carrying the written `name:type` annotation, as HS's
/// `sapicvar` reads one (Token.hs).
pub fn varspec_to_sapic(v: &p::VarSpec) -> crate::sapic::SapicLVar {
    crate::sapic::SapicLVar::new(varspec_to_lvar(v), v.typ.clone())
}

/// `parser::Fact` → `SapicNFact<SapicLVar>` (`Fact<SapicTerm>`).  Mirrors
/// `fact_to_lnfact` but over typed SAPIC terms.  The fact tag mapping is
/// identical (`Fr`/`In`/`Out`/`KU`/`KD`/`Ded` → builtin tags, else ProtoFact).
pub fn fact_to_sapic_fact(
    f: &p::Fact,
    sig: &MaudeSig,
) -> Result<crate::sapic::SapicLNFact, ElabError> {
    use crate::fact::Fact;
    let tag = fact_tag_of(f);
    let terms: Result<Vec<_>, _> = f
        .args
        .iter()
        .map(|t| {
            term_to_sapic_term(t, sig).ok_or_else(|| ElabError {
                message: format!("could not elaborate term in fact `{}`", f.name),
            })
        })
        .collect();
    Ok(Fact::new(tag, terms?).with_annotations(copy_fact_annotations(f)))
}

#[cfg(test)]
#[path = "elaborate_tests.rs"]
mod tests;
