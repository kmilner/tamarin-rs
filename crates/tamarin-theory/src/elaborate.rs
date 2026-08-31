// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
use tamarin_term::lterm::LVar;

use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, hash_maude_sig,
    location_report_maude_sig, minimal_maude_sig, mset_maude_sig, nat_maude_sig,
    pair_dest_maude_sig, reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};
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

/// One diagnostic from `elaborate_with_diagnostics`, mirroring a
/// wellformedness "Formula guardedness" warning.
#[derive(Debug, Clone)]
pub struct GuardDiagnostic {
    pub topic: String,
    pub item: String,
    pub message: String,
}

/// Run elaboration and additionally check that every lemma /
/// restriction formula converts to a guarded formula. Returns the
/// elaborated theory along with any guardedness diagnostics. Mirrors
/// Haskell's `formulaReports.checkGuarded`.
///
/// NOTE: this is an example-only convenience (used by
/// `examples/elaborate_all.rs`), NOT part of the prove pipeline, which
/// produces the byte-exact WF report via
/// [`crate::wellformedness::formulas::formula_reports`].  The two perform the same
/// guardedness scan but format their output differently; keep them in sync
/// if the check itself changes.
pub fn elaborate_with_diagnostics(
    parser_thy: &p::Theory,
) -> Result<(Theory, Vec<GuardDiagnostic>), ElabError> {
    let thy = elaborate(parser_thy)?;
    let mut diags = Vec::new();
    for l in thy.lemmas() {
        if let Err(e) = formula_to_guarded(&l.formula) {
            diags.push(GuardDiagnostic {
                topic: "Formula guardedness".into(),
                item: format!("Lemma `{}'", l.name),
                message: format!("cannot be converted to a guarded formula: {}", e.message),
            });
        }
    }
    for r in thy.restrictions() {
        if let Err(e) = formula_to_guarded(&r.formula) {
            diags.push(GuardDiagnostic {
                topic: "Formula guardedness".into(),
                item: format!("Restriction `{}'", r.name),
                message: format!("cannot be converted to a guarded formula: {}", e.message),
            });
        }
    }
    Ok((thy, diags))
}

/// Collect every `Name` constant of a term in traversal order — HS
/// `universeBi t` at `[Name]`, which both name reports filter by
/// `sortOfName` (Wellformedness.hs:447, :475-478).  Generic over the variable
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
/// theory (`defaultOracleNames`, Theory/Text/Parser.hs:249-250).
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
    // (`heuristic`, Theory/Text/Parser/Signature.hs:305-306) and stores that
    // list (`addHeuristic`, TheoryObject.hs:598-600).
    let mut heuristic_headers = parser_thy.items.iter().filter_map(|item| match item {
        p::TheoryItem::Heuristic(h) => Some(h),
        _ => None,
    });
    if let Some(h) = heuristic_headers.next() {
        thy.heuristic = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            h,
            in_file,
            &thy.tactic,
        );
    }
    if heuristic_headers.next().is_some() {
        return Err(ElabError {
            message: "default heuristic already defined".to_string(),
        });
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

/// The `SapicFunSym` a `functions:` declaration records as its
/// `FunctionTypingInfo` item (HS `function`,
/// Theory/Text/Parser/Signature.hs:183-225): the declared name, arity and
/// attribute flags paired with the declared SAPIC argument and result types.
pub(crate) fn function_decl_typing_info(d: &p::FunctionDecl) -> SapicFunSym {
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
    let sym = if d.ac {
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
    };
    SapicFunSym {
        sym,
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
/// Theory/Text/Parser/Signature.hs:102-135, 200-225) are enforced at parse
/// time (`Parser::enable_builtin` / `Parser::function_decl`) — the single
/// point where theories are ingested — so the declarations reaching here are
/// conflict-free and this step only BUILDS the signature.
fn maude_sig_step(item: &p::TheoryItem, out: &mut Theory) -> Result<Vec<LNMacro>, ElabError> {
    match item {
        p::TheoryItem::Builtins(names) => {
            let mut s = std::mem::take(&mut out.signature);
            for name in names {
                if let Some(sig) = builtin_sig(name) {
                    s = s.merge(sig);
                }
                // NOTE: `diffie-hellman` already arrives with `enable_dh`
                // set (its MaudeSig is `dh_maude_sig`, see
                // builtinsDiffNames in
                // Theory/Text/Parser/Signature.hs:58-76, see line 62),
                // and `merge` ORs `enable_dh`, so no explicit force is
                // needed here.  `diff` is a header/CLI flag handled via
                // the base signature's diff bit, never a `builtins:` entry.
            }
            out.signature = s;
        }
        p::TheoryItem::Functions(decls) => {
            use tamarin_term::function_symbols::UserDefinedSym;
            for d in decls {
                let arity = d.arg_types.len();
                let priv_ = if d.private {
                    Privacy::Private
                } else {
                    Privacy::Public
                };
                let constr = if d.destructor {
                    Constructability::Destructor
                } else {
                    Constructability::Constructor
                };
                let ndc = ndc_state_of(d.ndc, d.ndc_diff);
                // HS `function`'s fst/snd short-circuit (Theory/Text/
                // Parser/Signature.hs:217, name-only by design — it tests
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
                let user_sym = if d.ac {
                    UserDefinedSym::AcFctUser(AcFctSym::new(
                        d.name.as_bytes().to_vec(),
                        priv_,
                        constr,
                        ndc,
                    ))
                } else {
                    UserDefinedSym::NoEqUser(
                        NoEqSym::new(d.name.as_bytes().to_vec(), arity, priv_, constr)
                            .with_ndc(ndc),
                    )
                };
                // `add_fun_sym` consumes `self` by value; move the
                // current sig out via `take` to avoid a per-declaration
                // deep clone of the whole MaudeSig.  Output order and
                // dedup are unchanged (same `add_fun_sym` path).
                let cur = std::mem::take(&mut out.signature);
                out.signature = cur.add_fun_sym(user_sym);
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
                // (Theory/Text/Parser/Signature.hs:245-249, see line 249).  Match
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
                // (Theory/Text/Parser/Macro.hs:39), which has no pattern-match (`=t`)
                // production, so a body that converts to a `PatMatch`
                // here would be a hard parse failure in HS — and
                // `addMacroSym` (Theory/Text/Parser/Macro.hs:46) always runs for any parsed
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
                // (Theory/Text/Parser/Macro.hs:29-47, see line 46) and
                // `macroToFunSym` (Term/Macro.hs:29-30, see line 30).  After parser-
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
    // (Theory/Text/Parser.hs:129-152, TheoryObject.hs:433-449), so an item
    // textually before a `predicates:` block does not see it.
    let mut preds: Vec<crate::predicate::Predicate> = Vec::new();
    // The macros declared so far, read back from the items pushed for them.
    // HS applies `theoryMacros thy0` to every item at close time
    // (`closeTheoryItem`, CloseRule.hs:84-86); a macro call that precedes its
    // `macros:` block is an "unknown operator" parse failure
    // (`lookupArity`, Theory/Text/Parser/Term.hs:62-66), so the two lists
    // agree on every theory that parses.
    let mut macros: Vec<LNMacro> = Vec::new();
    // HS's parser inlines a `P(args)` call against only the definitions the
    // theory holds when the call is read (`checkProcess`,
    // Theory/Text/Parser/Sapic.hs:314-317). The RS parser keeps calls, so this
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
                // declarations (Theory/Text/Parser.hs:259-262,
                // TheoryObject.hs:492-493): one `FunctionTypingInfo` item per
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
                // block (Theory/Text/Parser/Signature.hs:277-283), which
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
            p::TheoryItem::Heuristic(_) => {}
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
                let rule = crate::intruder_variants::intr_rule_from_ast(&out.signature, r)
                    .map_err(|message| ElabError { message })?;
                if !out.intruder_rules.contains(&rule) {
                    out.intruder_rules.push(rule);
                }
            }
            p::TheoryItem::Rule(r) => {
                let mut e = rule_to_proto_rule_e(r, &out.signature)?;
                // HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193) adds
                // one restriction per `_restrict` formula BEFORE the rule and
                // appends the actions that reach them to the rule.
                for restr in crate::rule_restriction::lift_rule_restrictions(&mut e, &preds)? {
                    out.items
                        .push(TheoryItem::Restriction(apply_macro_in_restriction(
                            &macros, restr,
                        )));
                }
                // `closeProtoRule` narrows `applyMacroInRule macros ruE` into
                // the AC half and keeps `ruE` itself as the `cprRuleE` half
                // (lib/theory/src/Rule.hs:82-86).  A theory that declares no
                // macro, or a rule whose body calls none, leaves the two
                // identical.
                let mut opr =
                    OpenProtoRule::new(crate::rule::apply_macro_in_rule(&macros, e.clone()));
                if opr.rule != e {
                    opr.rule_e = Some(Box::new(e));
                }
                // `protoRule`'s `variants` block
                // (Theory/Text/Parser/Rule.hs:126-135, see line 134).
                opr.rule_ac = r
                    .variants
                    .iter()
                    .map(|v| rule_to_proto_rule_e(v, &out.signature))
                    .collect::<Result<Vec<_>, _>>()?;
                out.items.push(TheoryItem::Rule(opr));
            }
            p::TheoryItem::Lemma(l) => {
                let msig = &out.signature;
                let lem: Lemma = Lemma {
                    name: l.name.clone(),
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
                let acc = AccLemma {
                    name: a.name.clone(),
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
                // (Theory/Text/Parser/Sapic.hs:73-78,
                // Theory/Text/Parser.hs:290-291).
                let pp = elaborate_process(proc, &process_defs, &out.signature)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::Process(pp)));
            }
            p::TheoryItem::ProcessDef(d) => {
                // `processDef` stores the body and the declared formals
                // (Theory/Text/Parser/Sapic.hs:64-72); `_pVars` is `Nothing`
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
                // `equivLemma` (Theory/Text/Parser/Sapic.hs:203-209).
                let msig = &out.signature;
                let c1 = elaborate_process(p1, &process_defs, msig)?;
                let c2 = elaborate_process(p2, &process_defs, msig)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::EquivLemma(
                        c1, c2,
                    )));
            }
            p::TheoryItem::DiffEquivLemma(proc) => {
                // `diffEquivLemma` (Theory/Text/Parser/Sapic.hs:211-218).
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
            p::TheoryItem::Define(_) | p::TheoryItem::Include(_) => {
                // Already handled by the parser preprocessor.
            }
        }
    }
    Ok(())
}

/// The formula HS's `liftedAddLemma` / `liftedAddRestriction` store: the
/// surface formula closed by [`crate::formula::from_parser`] and stripped of
/// its predicate sugar by `expandLemma` / `expandRestriction`
/// (Theory/Text/Parser.hs:129-152, TheoryObject.hs:433-449).  The expansion
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
/// (`Theory/Text/Parser/Rule.hs:97-98`) and the per-attribute `ruleAttribute`
/// parser (`Theory/Text/Parser/Rule.hs:70-95`):
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
/// `fold` combines via the `RuleAttributes` `Semigroup` (Theory/Model/Rule.hs:382-396):
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

fn rule_to_proto_rule_e(r: &p::Rule, sig: &MaudeSig) -> Result<ProtoRuleE, ElabError> {
    // HS `modify preRestriction (++ rs) ri` (Theory/Text/Parser/Rule.hs:121,
    // 135): the rule carries its `_restrict` formulas as parsed — predicate
    // atoms unexpanded, since `liftedAddProtoRule` expands only the copies it
    // lifts (Theory/Text/Parser.hs:175-193).
    let restrictions = r
        .embedded_restrictions
        .iter()
        .map(|f| crate::formula::from_parser(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&r.name)),
        attributes: rule_attributes_from_parser(&r.attributes),
        restrictions,
    };
    let prems = r
        .premises
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let acts = r
        .actions
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    let concs = r
        .conclusions
        .iter()
        .map(|f| fact_to_lnfact(f, sig))
        .collect::<Result<Vec<_>, _>>()?;
    // HS `newVariables ps $ cs ++ as` (Theory/Text/Parser/Rule.hs:121-154).
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
/// `Theory.Model.Fact` holds (Theory/Model/Fact.hs:157-162).
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
/// Theory/Text/Parser/Proof.hs:38-72), and `checkAndExecProofMethod` looks it
/// up in `sGoals` by structural equality (ProofMethod.hs:253-258).  The
/// parser AST reaches that value through the same converters the rest of the
/// theory goes through, so a stored goal and a live one are built the same
/// way.
///
/// A disjunct that `formula_to_guarded_parsed` rejects is an error here, as
/// `guardedFormula`'s `fail` is in HS (Theory/Text/Parser/Formula.hs:122-127).
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
/// (Theory/Text/Parser/Proof.hs:75-85) builds directly.
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
/// `proofSkeleton` returns (Theory/Text/Parser/Proof.hs:98-115).
pub fn proof_tree_from_parsed(
    t: &p::ParsedProofTree,
    sig: &MaudeSig,
) -> Result<ProofTree, ElabError> {
    let cases: Result<Vec<_>, _> = t
        .cases
        .iter()
        .map(|(name, sub)| proof_tree_from_parsed(sub, sig).map(|sub| (name.clone(), sub)))
        .collect();
    Ok(ProofTree {
        method: proof_method_from_parsed(&t.method, sig)?,
        cases: cases?,
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
/// `tupleterm`'s `chainr1 ... (curry fAppPair)` (Theory/Text/Parser/Term.hs:210-212)
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
/// HS `lookupArity` (Theory/Text/Parser/Term.hs:60-71) looks `name` up in
/// `userDefinedFunSyms` — free symbols before user-defined AC symbols — then
/// the macro names, and hands `naryOpApp` / `binaryAlgApp` the privacy,
/// constructability and NDC state of the first match, which those build
/// `fAppNoEq` / `fAppAC` from (Theory/Text/Parser/Term.hs:87-121).  A name
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
/// (Theory/Text/Parser/Term.hs:165-172), so a free symbol sharing the name —
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
/// (Theory/Text/Parser/Term.hs:94-96), folding `f(a, b, c)` to `f(<a, b, c>)`.
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
/// (Theory/Text/Parser/Term.hs:60-71,87-121,165-172).
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
            // HS `fAppOne = fAppNoEq oneSym []` (Term/Term.hs:146-148, see line 148); the
            // `"1"` keyword in the term parser dispatches to this
            // (Theory/Text/Parser/Term.hs:138-153, see line 149).  Mirror exactly — emit
            // a 0-arity NoEq application of `oneSym`, NOT a public
            // constant.  Treating it as `Lit::Con(Pub,"1")` causes
            // source-case enumeration to mismatch HS's `c_one` rule.
            Some(f_app_no_eq(
                tamarin_term::function_symbols::one_sym(),
                vec![],
            ))
        }
        p::Term::DhNeutral => {
            // HS `fAppDHNeutral = fAppNoEq dhNeutralSym []` (Term/Term.hs:150-151);
            // dispatched by `symbol "DH_neutral" *> pure fAppDHNeutral`
            // (Theory/Text/Parser/Term.hs:138-153, see line 142).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::dh_neutral_sym(),
                vec![],
            ))
        }
        p::Term::NatOne => {
            // HS `fAppNatOne = fAppNoEq natOneSym []` (Term/Term.hs:156-158); the
            // `1:nat` / `%1` keywords dispatch to this
            // (Theory/Text/Parser/Term.hs:138-153, see line 143).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::nat_one_sym(),
                vec![],
            ))
        }
        p::Term::Number(_) => {
            // Defensive: `p::Term::Number` cannot arise from parsed
            // input. HS has no bare-integer (>=2) term — the parser
            // recognizes only `1`/`%1`/`DH_neutral` (Term.hs), and the
            // Rust parser likewise never constructs `Term::Number`, so
            // this arm is unreachable for real elaboration input.
            let n = Name::new(NameTag::Pub, "n".to_string());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::App(name, args) => {
            // Multi-arg unary builtins: `h(a, b, c)` is parsed as
            // `App("h", [a, b, c])` but Haskell Tamarin folds the
            // surplus args into a right-associative pair so the
            // function stays arity-1: `h(<a, b, c>)`.  Without this,
            // KU source-cases (precomputed using the canonical
            // arity-1 signature) never match the runtime arity-3
            // term, leaving e.g. `c_h` out of the case list.
            // Arity-1 symbols whose surplus comma-separated args fold into
            // a single tuple, mirroring HS's signature-driven `naryOpApp`
            // (`k == 1`, Theory/Text/Parser/Term.hs:94-96).  The listed
            // names cover the builtin unary symbols the signature query
            // does not reach here — `h` / `fst` / `snd` / `inv` / `pk`,
            // plus `getMessage` (revealing-signing) and `get_rep` /
            // `report` (locations-report), Term/Builtin/Signature.hs:38-40.
            // Widening the list to the whole signature regresses the
            // corpus, so it stays written out.
            let unary_builtin = matches!(
                name.as_str(),
                "h" | "fst" | "snd" | "inv" | "pk" | "getMessage" | "get_rep" | "report"
            ) || is_arity1_no_eq(sig, name);
            let new_args: Option<Vec<_>> =
                args.iter().map(|a| term_to_vterm(a, sig, mk_var)).collect();
            let mut new_args = new_args?;
            if unary_builtin && new_args.len() > 1 {
                // Wrap the surplus args into one right-associative pair so the
                // call stays arity-1.
                new_args = vec![right_nest_pair(new_args)?];
            }
            // `em(a, b)` under the bilinear-pairing builtin lowers to a
            // C-symbol application, not NoEq.  Mirrors HS `naryOpApp`
            // (Theory/Text/Parser/Term.hs:87-106, see line 103):
            //   `(o,(_,_,_,_)) | o == emapSymString -> return $ fAppC EMap ts`
            // Classifying `em` as NoEq instead would declare the Maude
            // operator as `op tamem : Msg Msg -> Msg [comm]` (`op_c` in
            // maude_print.rs) while rule terms carry the NoEq prefix
            // `tamXCem` (`pp_maude_no_eq_sym_into`); Maude then rejects the
            // unknown operator and `get variants` returns an empty
            // parse-error reply, so variant disjunctions go missing and
            // smartRanking ranks un-narrowed `em` shapes (the RYY_PFS
            // `key_secrecy_PFS` proof-path divergence).
            //
            // DELIBERATE DIVERGENCE (documented upstream bug):
            // HS's arm is name-keyed with NO builtin gate, so a user
            // `functions: em/2` WITHOUT bilinear-pairing also becomes C EMap —
            // whose Maude operator (`tamem`) is only declared under `enableBP`,
            // so upstream's first `get variants` query over such a term crashes
            // the run.  Mirroring that ungated classification here would leave
            // the port silently wrong instead (empty variant replies swallowed
            // as "no variants"; the intruder's NoEq `c_em` rule never unifying
            // with C-classified protocol terms, flipping exists-trace
            // verdicts), so the arm is gated on the builtin: without it, `em`
            // stays an ordinary user symbol.
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
            // signature via `lookupArity` (Theory/Text/Parser/Term.hs:108-121, see line 114),
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
            // `diffOp` builds `fAppDiff` (Theory/Text/Parser/Term.hs:135), i.e.
            // `fAppNoEq diffSym` (Term/Term.hs:162) — and `diff` is PRIVATE
            // (`diffSym = (diffSymString,(2,Private,Constructor,NotNDC))`,
            // Term/Term/FunctionSymbols.hs:249).  The privacy is observable:
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
                // `stACFunSyms`, Theory/Text/Parser/Term.hs:166-172), even
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
// ltypedlit`, Theory/Text/Parser/Sapic.hs:56-57), which builds
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
/// `sapicvar` reads one (Token.hs:506-510).
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

// =============================================================================
// Builtin → MaudeSig
// =============================================================================

fn builtin_sig(name: &str) -> Option<MaudeSig> {
    match name {
        "diffie-hellman" => Some(dh_maude_sig()),
        "bilinear-pairing" => Some(bp_maude_sig()),
        "multiset" => Some(mset_maude_sig()),
        "natural-numbers" => Some(nat_maude_sig()),
        "xor" => Some(xor_maude_sig()),
        "symmetric-encryption" => Some(sym_enc_maude_sig()),
        "asymmetric-encryption" => Some(asym_enc_maude_sig()),
        "signing" => Some(signature_maude_sig()),
        "revealing-signing" => Some(reveal_signature_maude_sig()),
        "hashing" => Some(hash_maude_sig()),
        "locations-report" => Some(location_report_maude_sig()),
        "dest-symmetric-encryption" => Some(sym_enc_dest_maude_sig()),
        "dest-asymmetric-encryption" => Some(asym_enc_dest_maude_sig()),
        "dest-signing" => Some(signature_dest_maude_sig()),
        "dest-pairing" => Some(pair_dest_maude_sig()), // pair-with-destructors
        _ => None,
    }
}

#[cfg(test)]
#[path = "elaborate_tests.rs"]
mod tests;
