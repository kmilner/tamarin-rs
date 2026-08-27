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
//!   composition is handled by `signature::SignaturePure::empty`)
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
//! It also provides the parser↔typed conversion helpers used above:
//! `term_to_lnterm`, the `lnterm_to_parser` projection the printers read, and
//! the SAPIC term/fact converters (`term_to_sapic_term`/`fact_to_sapic_fact`).
//!
//! Returned errors describe the surface offence (e.g. "duplicate rule
//! `R`"), with no internal panics.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
use tamarin_term::lterm::LVar;

use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, enable_diff_maude_sig,
    hash_maude_sig, location_report_maude_sig, mset_maude_sig, nat_maude_sig, pair_dest_maude_sig,
    reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};
use tamarin_term::term::{f_app_no_eq, Term};
use tamarin_term::vterm::{Lit, VTerm};

use crate::constraint::constraints::{Disj, Goal, SplitId};
use crate::formula::LNFormula;
use crate::guarded::{formula_to_guarded, formula_to_guarded_parsed};
use crate::restriction::{apply_macro_in_restriction, Restriction};
use crate::rule::{
    ConcIdx, PremIdx, ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes,
};
use crate::signature::SignaturePure;
use crate::theory::{
    apply_macro_in_lemma, AccLemma, CaseTest, LNMacro, Lemma, LemmaAttr, OpenProtoRule, ProcessDef,
    ProofTree, SapicFunSym, Theory, TheoryItem, TraceQuantifier, TranslationElement,
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
    crate::sapic::pfold_map(p, &mut |node| {
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
        Vec::<()>::new()
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
    let mut sig = SignaturePure::empty(parser_thy.is_diff);
    if parser_thy.is_diff {
        sig.maude_sig = sig.maude_sig.merge(enable_diff_maude_sig());
    }

    let mut thy: Theory = Theory::new(parser_thy.name.clone(), sig);
    thy.in_file = in_file.to_string();
    // HS sets `_thyIsSapic = True` only for EXACTLY ONE top-level
    // process: `translate` matches on `theoryProcesses th`
    // (= `[i | ProcessItem i <- ...]`, only top-level ProcessItems,
    // not ProcessDefItems), reaching the `True` assignment solely in
    // the single-process `[p]` branch; `[]` leaves the default False
    // and `>=2` throws MoreThanOneProcess (lib/sapic/src/Sapic.hs:48,85,87). Mirror
    // that: count only TopLevelProcess items, true iff exactly one.
    // Read downstream to gate SAPIC translation (run.rs, apply.rs).
    thy.is_sapic = parser_thy
        .items
        .iter()
        .filter(|i| matches!(i, p::TheoryItem::TopLevelProcess(_)))
        .count()
        == 1;

    if let Some(cfg) = &parser_thy.configuration {
        thy.items.push(TheoryItem::ConfigBlock(cfg.clone()));
    }

    elaborate_items(&parser_thy.items, &mut thy)?;
    // The `heuristic:` headers, parsed once the whole item list is known so
    // that a `{name}` ranking finds a `tactic:` declared after it.  HS parses
    // them into `[GoalRanking ProofContext]` in the parser itself
    // (`heuristic`, Theory/Text/Parser/Signature.hs:305-306) and stores that
    // list (`addHeuristic`, TheoryObject.hs:598-600).
    for item in &parser_thy.items {
        if let p::TheoryItem::Heuristic(h) = item {
            thy.heuristic.extend(
                crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
                    h,
                    in_file,
                    &thy.tactic,
                ),
            );
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
/// `out.signature.maude_sig` and `out.options`; every other item kind leaves
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
            let mut s = out.signature.maude_sig.clone();
            for name in names {
                if let Some(sig) = builtin_sig(name) {
                    s = s.merge(sig);
                }
                // HS `builtinsNames` (Theory/Text/Parser/Signature.hs:78-85)
                // maps two builtins to translation options:
                //   `reliable-channel` → `_transReliable`
                //   `locations-report` → `_transReport`
                match name.as_str() {
                    "reliable-channel" => out.options.trans_reliable = true,
                    "locations-report" => out.options.trans_report = true,
                    _ => {}
                }
                // NOTE: `diffie-hellman` already arrives with `enable_dh`
                // set (its MaudeSig is `dh_maude_sig`, see
                // builtinsDiffNames in
                // Theory/Text/Parser/Signature.hs:58-76, see line 62),
                // and `merge` ORs `enable_dh`, so no explicit force is
                // needed here.  `diff` is a header/CLI flag handled via
                // `enable_diff_maude_sig`, never a `builtins:` entry.
            }
            out.signature.maude_sig = s;
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
                        .maude_sig
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
                let cur = std::mem::take(&mut out.signature.maude_sig);
                out.signature.maude_sig = cur.add_fun_sym(user_sym);
            }
        }
        p::TheoryItem::Equations { eqs, convergent } => {
            // Port of Haskell `addEquationsM` (Theory.hs).
            // Convert each LHS=RHS pair to a CtxtStRule via
            // `rrule_to_ctxt_st_rule` and install it on the MaudeSig
            // so Maude sees the rewrite rule in its `fmod MSG ...`
            // module.  Convergent flag is stored as informational.
            out.signature.maude_sig.eq_convergent = *convergent;
            let mut s = out.signature.maude_sig.clone();
            for eq in eqs {
                // Haskell's `equation` parser hard-fails with
                // "Not a correct equation: ..." when an LHS=RHS pair
                // cannot be converted to a CtxtStRule
                // (Theory/Text/Parser/Signature.hs:245-249, see line 249).  Match
                // that failure behaviour rather than silently dropping.
                let (Some(l), Some(r)) = (
                    term_to_lnterm(&eq.lhs, &out.signature.maude_sig),
                    term_to_lnterm(&eq.rhs, &out.signature.maude_sig),
                ) else {
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
            out.signature.maude_sig = s.refresh();
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
                let body = match term_to_lnterm(&m.body, &out.signature.maude_sig) {
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
                let cur = std::mem::take(&mut out.signature.maude_sig);
                out.signature.maude_sig = cur.add_macro_sym(sym);
                ms.push(LNMacro::new(m.name.as_bytes().to_vec(), args, body));
            }
            return Ok(ms);
        }
        _ => {}
    }
    Ok(Vec::new())
}

/// The `MaudeSig` a parsed theory's declarations build, without elaborating
/// the theory: [`maude_sig_step`] folded over `thy`'s items from the empty,
/// diff-seeded signature [`elaborate`] starts from.
///
/// It equals `elaborate(thy)?.signature.maude_sig`: those are the only four
/// item kinds that touch the signature, and `elaborate_items` runs the same
/// step over the same items in the same order.
/// `elaborate_tests::parse_time_signature_matches_elaboration` pins that over
/// the examples tree.
pub fn parse_time_signature(thy: &p::Theory) -> Result<MaudeSig, ElabError> {
    let mut sig = SignaturePure::empty(thy.is_diff);
    if thy.is_diff {
        sig.maude_sig = sig.maude_sig.merge(enable_diff_maude_sig());
    }
    let mut scratch: Theory = Theory::new(thy.name.clone(), sig);
    for item in &thy.items {
        maude_sig_step(item, &mut scratch)?;
    }
    Ok(scratch.signature.maude_sig)
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
    // HS's parser inlines a `P(args)` call against the definitions the theory
    // holds when the call is read (`checkProcess`, Theory/Text/Parser/Sapic.hs:
    // 314-317); the RS parser keeps the call, so the whole item list supplies
    // the definitions here.
    let process_defs = crate::process_inline::collect_process_defs(items);
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
                    let pred = crate::predicate::from_parser(pd, &out.signature.maude_sig)?;
                    preds.push(pred.clone());
                    out.items.push(TheoryItem::Predicate(pred));
                }
            }
            p::TheoryItem::Options(opts) => {
                let mut o = out.options.clone();
                for n in opts {
                    match n.as_str() {
                        "translation-progress" => o.trans_progress = true,
                        "translation-allow-pattern-lookups" => {
                            o.trans_allow_pattern_matching_in_lookup = true
                        }
                        "translation-state-optimisation" => o.state_channel_opt = true,
                        "translation-asynchronous-channels" => o.asynchronous_channels = true,
                        "translation-compress-events" => o.compress_events = true,
                        _ => {}
                    }
                }
                out.options = o;
            }
            // The `heuristic:` header is parsed after the item walk, where
            // the theory's whole tactic list is known.
            p::TheoryItem::Heuristic(_) => {}
            p::TheoryItem::Tactic(t) => {
                out.tactic
                    .push(crate::tactic::Tactic::parse(&t.name, &t.raw));
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                let restr = Restriction {
                    name: r.name.clone(),
                    formula: item_formula(&r.formula, &out.signature.maude_sig, &preds)?,
                    original_formula: None,
                };
                out.items
                    .push(TheoryItem::Restriction(apply_macro_in_restriction(
                        &macros, restr,
                    )));
            }
            // A top-level `rule (modulo AC)` block is an intruder rule: HS's
            // parser routes it into `_thyCache` through `addIntrRuleACs`
            // (`intrRule`, Theory/Text/Parser/Rule.hs:156-161;
            // Theory/Text/Parser.hs:287; OpenTheory.hs:750-751), so it becomes
            // no theory item, reaches neither print (`ppCache = const
            // emptyDoc`, OpenTheory.hs:869-874) and joins no protocol rule
            // set.
            p::TheoryItem::IntrRule(_) => {}
            p::TheoryItem::Rule(r) => {
                let mut e = rule_to_proto_rule_e(r, &out.signature.maude_sig)?;
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
                    .map(|v| rule_to_proto_rule_e(v, &out.signature.maude_sig))
                    .collect::<Result<Vec<_>, _>>()?;
                out.items.push(TheoryItem::Rule(opr));
            }
            p::TheoryItem::Lemma(l) => {
                let msig = &out.signature.maude_sig;
                let lem: Lemma = Lemma {
                    name: l.name.clone(),
                    attributes: l.attributes.iter().map(elaborate_lemma_attr).collect(),
                    trace_quantifier: match l.trace_quantifier {
                        p::TraceQuantifier::AllTraces => TraceQuantifier::AllTraces,
                        p::TraceQuantifier::ExistsTrace => TraceQuantifier::ExistsTrace,
                    },
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
                    attributes: a.attributes.iter().map(elaborate_lemma_attr).collect(),
                    formula: crate::formula::from_parser(&a.formula, &out.signature.maude_sig)?,
                    case_test_idents: a.case_test_idents.clone(),
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::AccLemma(acc)));
            }
            p::TheoryItem::CaseTest(c) => {
                let ct = CaseTest {
                    name: c.name.clone(),
                    formula: crate::formula::from_parser(&c.formula, &out.signature.maude_sig)?,
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::CaseTest(ct)));
            }
            p::TheoryItem::TopLevelProcess(proc) => {
                // `toplevelprocess` adds a `ProcessItem`
                // (Theory/Text/Parser/Sapic.hs:73-78,
                // Theory/Text/Parser.hs:290-291).
                let pp = elaborate_process(proc, &process_defs, &out.signature.maude_sig)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::Process(pp)));
            }
            p::TheoryItem::ProcessDef(d) => {
                // `processDef` stores the body and the declared formals
                // (Theory/Text/Parser/Sapic.hs:64-72); `_pVars` is `Nothing`
                // for a `let P = …` written without a parameter list.
                let body = elaborate_process(&d.body, &process_defs, &out.signature.maude_sig)?;
                let vars = d
                    .vars
                    .as_ref()
                    .map(|vs| vs.iter().map(varspec_to_sapic).collect());
                out.items
                    .push(TheoryItem::Translation(TranslationElement::ProcessDef(
                        ProcessDef {
                            name: d.name.clone(),
                            vars,
                            body,
                        },
                    )));
            }
            p::TheoryItem::EquivLemma(p1, p2) => {
                // `equivLemma` (Theory/Text/Parser/Sapic.hs:203-209).
                let msig = &out.signature.maude_sig;
                let c1 = elaborate_process(p1, &process_defs, msig)?;
                let c2 = elaborate_process(p2, &process_defs, msig)?;
                out.items
                    .push(TheoryItem::Translation(TranslationElement::EquivLemma(
                        c1, c2,
                    )));
            }
            p::TheoryItem::DiffEquivLemma(proc) => {
                // `diffEquivLemma` (Theory/Text/Parser/Sapic.hs:211-218).
                let pp = elaborate_process(proc, &process_defs, &out.signature.maude_sig)?;
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
    defs: &crate::process_inline::ProcessDefMap<'_>,
    sig: &MaudeSig,
) -> Result<crate::sapic::PlainProcess, ElabError> {
    crate::process_inline::convert_process_with_defs(proc, defs, sig).map_err(|e| ElabError {
        message: format!("SAPIC translation: {}", e.message),
    })
}

/// Map a parser-AST lemma attribute to the elaborated form (the two enums
/// are 1:1).  `pub` for `tamarin-accountability`'s lemma injection.
pub fn elaborate_lemma_attr(a: &p::LemmaAttr) -> LemmaAttr {
    match a {
        p::LemmaAttr::Sources => LemmaAttr::Sources,
        p::LemmaAttr::Reuse => LemmaAttr::Reuse,
        p::LemmaAttr::DiffReuse => LemmaAttr::DiffReuse,
        p::LemmaAttr::UseInduction => LemmaAttr::UseInduction,
        p::LemmaAttr::HideLemma(s) => LemmaAttr::HideLemma(s.clone()),
        p::LemmaAttr::Heuristic(s) => LemmaAttr::Heuristic(s.clone()),
        p::LemmaAttr::Output(v) => LemmaAttr::Output(v.clone()),
        p::LemmaAttr::Left => LemmaAttr::Left,
        p::LemmaAttr::Right => LemmaAttr::Right,
        p::LemmaAttr::Hint(s) => LemmaAttr::Hint(s.clone()),
    }
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

/// Copy a parser fact's annotations into the typed `FactAnnotation` set.
/// Shared by [`fact_to_lnfact`] and [`fact_to_sapic_fact`].
pub(crate) fn copy_fact_annotations(f: &p::Fact) -> BTreeSet<crate::fact::FactAnnotation> {
    let mut anns: BTreeSet<crate::fact::FactAnnotation> = BTreeSet::new();
    for ann in &f.annotations {
        anns.insert(match ann {
            p::FactAnnotation::SolveFirst => crate::fact::FactAnnotation::SolveFirst,
            p::FactAnnotation::SolveLast => crate::fact::FactAnnotation::SolveLast,
            p::FactAnnotation::NoSources => crate::fact::FactAnnotation::NoSources,
        });
    }
    anns
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

// =============================================================================
// Projection: internal values → parser AST
// =============================================================================

/// `LNFact` → parser-AST `Fact`: the tag's name and multiplicity, the terms
/// through [`lnterm_to_parser`] and the annotation set.
pub fn lnfact_to_parser(fa: &crate::fact::LNFact) -> p::Fact {
    let (name, persistent) = fact_tag_to_parser(&fa.tag);
    p::Fact {
        persistent,
        name,
        args: fa.terms.iter().map(lnterm_to_parser).collect(),
        annotations: fact_annotations_to_parser(&fa.annotations),
    }
}

/// The parser AST's spelling of a fact tag: `factTagName`
/// (Theory/Model/Fact.hs:536-545) with the persistence `factTagMultiplicity`
/// gives it (Theory/Model/Fact.hs:383-388).  The inverse of [`fact_tag_of`] on
/// every tag that function builds.
pub(crate) fn fact_tag_to_parser(tag: &crate::fact::FactTag) -> (String, bool) {
    (
        crate::fact::fact_tag_name(tag),
        crate::fact::fact_tag_multiplicity(tag) == crate::fact::Multiplicity::Persistent,
    )
}

/// A fact's annotations in the parser AST's own constructors — the inverse of
/// [`copy_fact_annotations`].  HS `prettyFact` appends `ppAnn an` to every fact
/// (Theory/Model/Fact.hs:567-574), so the annotations must survive the
/// projection; the `BTreeSet`'s iteration order IS the HS `S.toList` (Ord)
/// order the renderer expects.
pub(crate) fn fact_annotations_to_parser(
    anns: &BTreeSet<crate::fact::FactAnnotation>,
) -> Vec<p::FactAnnotation> {
    anns.iter()
        .map(|a| match a {
            crate::fact::FactAnnotation::SolveFirst => p::FactAnnotation::SolveFirst,
            crate::fact::FactAnnotation::SolveLast => p::FactAnnotation::SolveLast,
            crate::fact::FactAnnotation::NoSources => p::FactAnnotation::NoSources,
        })
        .collect()
}

/// The parser-AST atom a syntactic-sugar variant closes back into — the
/// `ppS` argument of HS `prettyProtoAtom` (Atom.hs:212-224) in the closing
/// direction, and the projection counterpart of [`crate::atom::MapSugar`].
pub(crate) trait SugarToParser {
    fn sugar_to_parser(&self) -> p::Atom;
}

impl SugarToParser for crate::atom::SyntacticSugar<tamarin_term::lterm::LNTerm> {
    /// The `Pred` sugar (Atom.hs:86-87) closes back into `blatom`'s predicate
    /// alternative (Theory/Text/Parser/Formula.hs:52).  The multiset `(<)` is
    /// parsed into the `Smaller` predicate (`smallerp`,
    /// Theory/Text/Parser/Formula.hs:30-38) and has no closed form of its own.
    fn sugar_to_parser(&self) -> p::Atom {
        let crate::atom::SyntacticSugar::Pred(fa) = self;
        p::Atom::Pred(lnfact_to_parser(fa))
    }
}

impl SugarToParser for crate::atom::Unit2 {
    /// HS `prettyAtom = prettyProtoAtom (const emptyDoc)` (Atom.hs:226-229):
    /// `Unit2` holds no term, and the parser grammar has no production for it.
    /// `predicate::expand_formula` replaces every `Pred` atom by a formula
    /// (Theory/Syntactic/Predicate.hs:82-105), so an `LNFormula` reaches this
    /// projection with the sugar gone.
    fn sugar_to_parser(&self) -> p::Atom {
        panic!("proto_atom_to_parser: Unit2 sugar has no parser-AST atom")
    }
}

/// `ProtoAtom<S, LNTerm>` → parser-AST `Atom`: [`lnterm_to_parser`] and
/// [`lnfact_to_parser`] over the arms of HS `ProtoAtom` (Atom.hs:78-84,100),
/// with the sugar closed by its own [`SugarToParser`] impl.
pub(crate) fn proto_atom_to_parser<S: SugarToParser>(
    a: &crate::atom::ProtoAtom<S, tamarin_term::lterm::LNTerm>,
) -> p::Atom {
    use crate::atom::ProtoAtom;
    match a {
        ProtoAtom::Action(t, fa) => p::Atom::Action(lnfact_to_parser(fa), lnterm_to_parser(t)),
        ProtoAtom::EqE(l, r) => p::Atom::Eq(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Subterm(l, r) => p::Atom::Subterm(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Less(l, r) => p::Atom::Less(lnterm_to_parser(l), lnterm_to_parser(r)),
        ProtoAtom::Last(t) => p::Atom::Last(lnterm_to_parser(t)),
        ProtoAtom::Syntactic(s) => s.sugar_to_parser(),
    }
}

/// `LNTerm` → parser-AST `Term`: the projection every printer of an `LNTerm`
/// goes through, and the term-level twin of [`lnfact_to_parser`].
///
/// The parser AST is the universe HS `prettyTerm` (Term/Term.hs:299-317) prints
/// from, so the shapes that function special-cases must be materialised here:
/// `exp` as the infix `^` (line 310), a `pair` chain as the n-ary tuple its
/// `split` walks out of the RIGHT spine (lines 313,323-324), an AC symbol as
/// the infix chain of its `ppTerms` arms (lines 305-309), a nullary user-`[AC]`
/// symbol as its bare name (line 304) and `List` as `LIST(…)` (line 317).
///
/// `tamarin-sapic` lowers through this same function (its restriction and
/// `if`-predicate bodies are parser-AST formulas), so the two surfaces cannot
/// disagree about any of those shapes.
pub fn lnterm_to_parser(t: &tamarin_term::lterm::LNTerm) -> p::Term {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => p::Term::Var(p::VarSpec {
            name: v.name.to_string(),
            idx: v.idx,
            sort: v.sort,
            typ: None,
        }),
        Term::Lit(Lit::Con(n)) => {
            use tamarin_term::lterm::NameTag;
            match n.tag {
                NameTag::Pub => p::Term::PubLit(n.id.0.to_string()),
                NameTag::Fresh => p::Term::FreshLit(n.id.0.to_string()),
                NameTag::Nat => p::Term::NatLit(n.id.0.to_string()),
                NameTag::Node => p::Term::PubLit(n.id.0.to_string()),
                // `prettyTerm`'s literal case is `text . show`, and `show
                // (Name AbbrevName n) = show n` (LTerm.hs:240) is the bare id;
                // a nullary `App` is the parser-AST term `term_to_doc` renders
                // that way.  Reached from `prettyLNFact` on the facts
                // `Web.Utils.abbrev` rewrote.
                NameTag::Abbrev => p::Term::App(n.id.0.to_string(), Vec::new()),
            }
        }
        Term::App(FunSym::NoEq(sym), args) => {
            let name = String::from_utf8_lossy(sym.name).to_string();
            // HS `prettyTerm`'s `diff` arm (Term/Term.hs:311) is a chain of
            // `<>`, so the application never breaks at its comma — a wide
            // `diff` wraps inside its second operand instead.
            // `p::Term::Diff` is the parser-AST shape `term_to_doc` renders
            // that way; a `NoEq` application of the same NAME is a different
            // symbol and renders through `ppFun`, whose `fsep` does break.
            if *sym == tamarin_term::function_symbols::diff_sym() && args.len() == 2 {
                return p::Term::Diff(
                    Box::new(lnterm_to_parser(&args[0])),
                    Box::new(lnterm_to_parser(&args[1])),
                );
            }
            // `exp` is the DH exponentiation infix operator — HS
            // `prettyTerm` (Term/Term.hs:310) renders `exp(a, b)` as `a^b`.
            // Surface as `p::Term::BinOp(Exp, ..)` so `term_to_doc`'s special
            // case applies.
            if name == "exp" && args.len() == 2 {
                return p::Term::BinOp(
                    p::BinOp::Exp,
                    Box::new(lnterm_to_parser(&args[0])),
                    Box::new(lnterm_to_parser(&args[1])),
                );
            }
            // A `pair` chain flattens to the n-ary tuple HS `prettyTerm`'s
            // `split` produces (Term/Term.hs:313,323-324): `split` consumes the
            // RIGHT child while it is itself a pair, so a left-nested
            // `pair(pair(a,b),c)` stays the 2-tuple `<<a, b>, c>`.
            if name == "pair" && args.len() == 2 {
                let mut items: Vec<p::Term> = Vec::new();
                items.push(lnterm_to_parser(&args[0]));
                let mut tail = &args[1];
                loop {
                    match tail {
                        Term::App(FunSym::NoEq(s2), a2)
                            if a2.len() == 2 && String::from_utf8_lossy(s2.name) == "pair" =>
                        {
                            items.push(lnterm_to_parser(&a2[0]));
                            tail = &a2[1];
                        }
                        _ => {
                            items.push(lnterm_to_parser(tail));
                            break;
                        }
                    }
                }
                return p::Term::Pair(items);
            }
            p::Term::App(name, args.iter().map(lnterm_to_parser).collect())
        }
        // HS `FApp (C EMap) ts -> ppFun emapSymString ts` (Term/Term.hs:316).
        Term::App(FunSym::C(_), args) => p::Term::App(
            "em".to_string(),
            args.iter().map(lnterm_to_parser).collect(),
        ),
        // HS `prettyTerm` (Term/Term.hs:304): `FApp (AC (ACfct (f,_))) [] ->
        // text (BC.unpack f)` — a nullary user-AC symbol is the bare name,
        // which `term_to_doc` renders for a nullary `App`.
        Term::App(FunSym::Ac(AcSym::AcFct(s)), args) if args.is_empty() => {
            p::Term::App(String::from_utf8_lossy(s.name).into_owned(), vec![])
        }
        Term::App(FunSym::Ac(ac), args) => {
            // Render AC as left-assoc binops to preserve display.
            let op = match ac {
                AcSym::Mult => p::BinOp::Mult,
                AcSym::Union => p::BinOp::Union,
                AcSym::NatPlus => p::BinOp::NatPlus,
                AcSym::Xor => p::BinOp::Xor,
                // HS renders a user-declared `[AC]` symbol INFIX too
                // (Term/Term.hs:305): `ppTerms (" " ++ BC.unpack f ++ " ") 1
                // "(" ")" ts`, i.e. `(x add y)`.
                AcSym::AcFct(s) => p::BinOp::AcFct(tamarin_term::intern::intern_str(
                    &String::from_utf8_lossy(s.name),
                )),
            };
            let mut it = args.iter();
            let first = lnterm_to_parser(it.next().expect("AC needs at least one arg"));
            it.fold(first, |acc, next| {
                p::Term::BinOp(op, Box::new(acc), Box::new(lnterm_to_parser(next)))
            })
        }
        // HS `FApp List ts -> ppFun "LIST" ts` (Term/Term.hs:317).
        Term::App(FunSym::List, args) => p::Term::App(
            "LIST".to_string(),
            args.iter().map(lnterm_to_parser).collect(),
        ),
    }
}

// =============================================================================
// HS-faithful Ord for a parser-AST term
// =============================================================================
//
// [`canonicalize_ac_in_pterm`] reproduces on the parser AST the argument sort
// HS's `fAppAC` and `fAppC` smart constructors perform when they build an
// `LNTerm` (Term/Term/Raw.hs:118-134).  That sort is HS's derived
// `Ord (Term a)` (Term/Term/Raw.hs:71-75, see line 74), so the comparator
// below reads that order off the parser-AST spelling of the same term.

/// HS list Ord: element by element, shorter first.  `T` is `p::Term` for a
/// stored argument vector and `&p::Term` for the borrowed operand list the
/// AC branch of [`cmp_pterm`] flattens.
fn cmp_pterm_list<T: std::borrow::Borrow<p::Term>>(a: &[T], b: &[T]) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let c = cmp_pterm(x.borrow(), y.borrow());
        if c != std::cmp::Ordering::Equal {
            return c;
        }
    }
    a.len().cmp(&b.len())
}

/// HS Term Ord: `LIT _ < FAPP _ _` (Term/Term/Raw.hs:71-75, see line 74),
/// walked over the parser AST, whose variables are all free.
fn cmp_pterm(a: &p::Term, b: &p::Term) -> std::cmp::Ordering {
    use p::Term::*;
    let (ca, sa) = term_class(a);
    let (cb, sb) = term_class(b);
    if ca != cb {
        return ca.cmp(&cb);
    }
    // FApp class (ca == cb == 1): HS `Ord (Term a)` compares `FAPP fsym ts`
    // by `compare fsym` THEN `compare ts` (derived Ord on
    // `Term a = LIT a | FAPP FunSym [Term a]`, Term/Term/Raw.hs:71-75, see line 74).  The
    // `FunSym` Ord is `NoEq < AC < C < List`, and within `NoEq` it is
    // `Ord NoEqSym = (name, (arity, privacy, constructability, ndc))`
    // (FunctionSymbols.hs:131-132) — i.e. compared by NAME first.
    //
    // The parser AST spells several HS `FAPP (NoEq sym)` terms as dedicated
    // variants (`Pair`=pair, `BinOp Exp`=exp, `Diff`=diff, `NumberOne`=one,
    // `NatOne`=tone, `DhNeutral`=DH_neutral) and the AC ops as
    // `BinOp Mult/Union/Xor/NatPlus`.  These must NOT be ordered by RUST
    // VARIANT: HS's `FunSym` Ord is name-based (e.g. HS sorts `exp(...)`
    // BEFORE `pair(...)` because `"exp" < "pair"`), and this order decides
    // the operand sequence [`canonicalize_ac_in_pterm`] stores — hence every
    // AC list the theory echo prints.
    //
    // Faithful: compare two FApp-class terms by their HS `FunSym` key
    // (`funsym_key`), then by the argument list (flattened+sorted for AC,
    // matching `fAppAC`'s `sort (...)`, Term/Term/Raw.hs:118-129, see line 123).
    if ca == 1 {
        // Borrowed FunSym key (no per-comparison allocation): compare
        // (outer, name-bytes, arity) in HS order without materialising a
        // `Vec`.  The name is compared as a `&[u8]` slice.
        let (oa, na, aa) = funsym_key(a);
        let (ob, nb, ab) = funsym_key(b);
        let kc = oa
            .cmp(&ob)
            .then_with(|| na.cmp(nb))
            .then_with(|| aa.cmp(&ab));
        if kc != std::cmp::Ordering::Equal {
            return kc;
        }
        // Same FunSym: compare argument lists in HS `[Term a]` order.
        // AC ops compare a sorted, flattened multiset (HS stores args
        // pre-sorted by `fAppAC`); everything else compares positionally.
        if let (BinOp(o1, _, _), BinOp(o2, _, _)) = (a, b) {
            if is_ac_binop(o1) && is_ac_binop(o2) {
                let mut args_a = Vec::new();
                let mut args_b = Vec::new();
                flatten_ac_binop(o1, a, &mut args_a);
                flatten_ac_binop(o2, b, &mut args_b);
                args_a.sort_by(|x, y| cmp_pterm(x, y));
                args_b.sort_by(|x, y| cmp_pterm(x, y));
                return cmp_pterm_list(&args_a, &args_b);
            }
        }
        return cmp_fapp_args(a, b);
    }
    match (a, b) {
        // Lit class:
        (Var(v1), Var(v2)) => cmp_varspec(v1, v2),
        (PubLit(s1), PubLit(s2)) => s1.cmp(s2),
        (FreshLit(s1), FreshLit(s2)) => s1.cmp(s2),
        (NatLit(s1), NatLit(s2)) => s1.cmp(s2),
        (Number(n1), Number(n2)) => n1.cmp(n2),
        _ => {
            // Lit-class sub-discriminator (Con < Var; among Con by NameTag
            // then name) — handled by `term_class`'s sub_tag.
            sa.cmp(&sb)
        }
    }
}

/// HS `FunSym` Ord key for a FApp-class `p::Term`.  Returns
/// `(outer, name, arity)` where `outer` mirrors HS's `FunSym` constructor
/// order `NoEq(0) < AC(1) < C(2) < List(3)` (FunctionSymbols.hs:150-154)
/// and, within `NoEq`, `(name, arity)` mirrors `Ord NoEqSym` (compared by
/// name then arity — privacy/constructability never disambiguate two
/// distinct symbols sharing a name+arity).  The builtin AC ops carry no name;
/// their `ACSym` order is `Union < Mult < Xor < NatPlus < ACfct`
/// (FunctionSymbols.hs:138-139), encoded in the third (`arity`) field as an
/// index so AC terms sort among themselves by ACSym and after every NoEq
/// term.  A user-defined `ACfct` carries its name, which sorts after the
/// builtin ops' empty name and orders two `ACfct`s by name — mirroring
/// `Ord ACfctSym`, whose first tuple component is the name.
///
/// `em/2` is HS's sole `C` symbol.  `CSym` is a single nullary constructor
/// (`data CSym = EMap`, FunctionSymbols.hs:142-143), so a `C` key carries
/// neither name nor arity and every `C` term ties on those two fields.
/// The classification is by NAME ALONE: the parser's `naryOpApp` builds
/// `fAppC EMap` for any application written `em(…)`, whether `em` comes from
/// the `bilinear-pairing` builtin or from a user `functions:` declaration
/// (Theory/Text/Parser/Term.hs:103) — so a `p::Term`, which carries only the
/// name, has everything the decision needs.  The `op{t1}t2` spelling is NOT
/// covered: `binaryAlgApp` has no `em` case and builds `fAppNoEq`
/// (Theory/Text/Parser/Term.hs:119-121), matching `AlgApp`'s `NoEq` key below.
/// Arity is pinned to 2 because a `C` term of any other arity is rejected
/// downstream (`viewTerm2`, Term/Term/Raw.hs:190).
fn funsym_key(t: &p::Term) -> (u8, &[u8], usize) {
    use p::Term::*;
    // NoEq syms: outer = 0, key by (name-bytes, arity).  Static byte-string
    // literals (`b"pair"` etc.) are `&'static [u8]` and coerce to the
    // elided output lifetime; `n.as_bytes()` borrows from `t`.  No alloc.
    match t {
        // Parser-AST spellings of HS `FAPP (NoEq sym)` terms:
        Pair(_) => (0, b"pair", 2),
        BinOp(p::BinOp::Exp, _, _) => (0, b"exp", 2),
        Diff(_, _) => (0, b"diff", 2),
        NumberOne => (0, b"one", 0),
        NatOne => (0, b"tone", 0),
        DhNeutral => (0, b"DH_neutral", 0),
        // C sym: outer = 2, above every NoEq and AC term whatever its name.
        App(n, args) if n == "em" && args.len() == 2 => (2, b"", 0),
        App(n, args) => (0, n.as_bytes(), args.len()),
        AlgApp(n, _, _) => (0, n.as_bytes(), 2),
        // AC ops: outer = 1, ACSym order Union<Mult<Xor<NatPlus> in field 3.
        BinOp(p::BinOp::Union, _, _) => (1, b"", 0),
        BinOp(p::BinOp::Mult, _, _) => (1, b"", 1),
        BinOp(p::BinOp::Xor, _, _) => (1, b"", 2),
        BinOp(p::BinOp::NatPlus, _, _) => (1, b"", 3),
        BinOp(p::BinOp::AcFct(n), _, _) => (1, n.as_bytes(), 4),
        // PatMatch is SAPIC surface syntax with no HS term — sort after all.
        PatMatch(_) => (255, b"", 0),
        // Lit-class terms never reach here (ca != 1).
        _ => (254, b"", 0),
    }
}

/// The HS argument pair `[t1, t2]` of a `pairSym`-headed term, as
/// `(t1, spine)` where `spine` is the operand list of `t2` in the same
/// flattened spelling — so `t2` is `Pair(spine)` when `spine` has two or more
/// elements and `spine[0]` when it has one.
///
/// HS builds nested pairs (`fAppPair (x, y) = fAppNoEq pairSym [x, y]`,
/// Term/Term.hs:163), so `<a, b, c>` is `pair(a, pair(b, c))` and its arity-2
/// argument list is `[a, pair(b, c)]`.  The parser stores that spine FLAT in
/// `Pair`, and also carries the source prefix spelling `pair(a, b)` as
/// `App("pair", [a, b])` — both key `(0, "pair", 2)` in [`funsym_key`], so
/// both must expose the same nested argument list to `Ord`.
fn pair_spine(t: &p::Term) -> Option<(&p::Term, &[p::Term])> {
    match t {
        p::Term::Pair(x) if x.len() >= 2 => Some((&x[0], &x[1..])),
        p::Term::App(n, x) if n == "pair" && x.len() == 2 => Some((&x[0], &x[1..])),
        p::Term::AlgApp(n, l, r) if n == "pair" => Some((l, std::slice::from_ref(&**r))),
        _ => None,
    }
}

/// Compare two pair spines: `x` and `y` each stand for the term
/// `Pair(x)`/`Pair(y)` when they hold two or more elements and for their sole
/// element otherwise.  Recurses down the spine so that, at the position where
/// one side's spine ends and the other's continues, HS's `Ord` pits a plain
/// term against a `pairSym` FAPP — which is why `<a, z>` sorts BEFORE
/// `<a, b, c>` (`z` is a LIT, `pair(b, c)` a FAPP, and `LIT _ < FAPP _ _`,
/// Term/Term/Raw.hs:72-74).
fn cmp_pair_spine(x: &[p::Term], y: &[p::Term]) -> std::cmp::Ordering {
    if x.is_empty() || y.is_empty() {
        return x.len().cmp(&y.len());
    }
    match (x.len(), y.len()) {
        (1, 1) => cmp_pterm(&x[0], &y[0]),
        (1, _) => cmp_pterm_vs_pair_spine(&x[0], y),
        (_, 1) => cmp_pterm_vs_pair_spine(&y[0], x).reverse(),
        _ => cmp_pterm(&x[0], &y[0]).then_with(|| cmp_pair_spine(&x[1..], &y[1..])),
    }
}

/// Compare a term `t` against the pair `Pair(y)` that spine `y` (two or more
/// elements) stands for, without materialising that `Pair`.  Mirrors
/// [`cmp_pterm`]'s dispatch: LIT class first, then the `FunSym` key against
/// `pairSym`, then the argument lists.
fn cmp_pterm_vs_pair_spine(t: &p::Term, y: &[p::Term]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    if term_class(t).0 != 1 {
        return Ordering::Less;
    }
    let (o, n, a) = funsym_key(t);
    let key = o
        .cmp(&0)
        .then_with(|| n.cmp(b"pair".as_slice()))
        .then_with(|| a.cmp(&2));
    if key != Ordering::Equal {
        return key;
    }
    match pair_spine(t) {
        Some((h, tail)) => cmp_pterm(h, &y[0]).then_with(|| cmp_pair_spine(tail, &y[1..])),
        None => Ordering::Equal,
    }
}

/// Compare the argument lists of two same-FunSym, non-AC FApp terms,
/// mirroring HS's positional `compare ts` on `[Term a]`.
fn cmp_fapp_args(a: &p::Term, b: &p::Term) -> std::cmp::Ordering {
    use p::Term::*;
    // A `pairSym` key ties every pair spelling, whose HS argument list is the
    // arity-2 `[t1, t2]` of the RIGHT-NESTED spine rather than the parser's
    // flat operand vector — see [`pair_spine`].
    if let (Some((ha, ta)), Some((hb, tb))) = (pair_spine(a), pair_spine(b)) {
        return cmp_pterm(ha, hb).then_with(|| cmp_pair_spine(ta, tb));
    }
    match (a, b) {
        (App(_, x), App(_, y)) => cmp_pterm_list(x, y),
        (AlgApp(_, l1, r1), AlgApp(_, l2, r2)) => cmp_pterm(l1, l2).then_with(|| cmp_pterm(r1, r2)),
        (Diff(l1, r1), Diff(l2, r2)) => cmp_pterm(l1, l2).then_with(|| cmp_pterm(r1, r2)),
        (BinOp(_, l1, r1), BinOp(_, l2, r2)) => cmp_pterm(l1, l2).then_with(|| cmp_pterm(r1, r2)),
        (PatMatch(x), PatMatch(y)) => cmp_pterm(x, y),
        // 0-arity builtins (one/tone/DH_neutral): no args.
        (NumberOne, NumberOne) | (NatOne, NatOne) | (DhNeutral, DhNeutral) => {
            std::cmp::Ordering::Equal
        }
        // Cross-variant operands only reach here when funsym_key tied them
        // (e.g. App("exp",[..]) vs BinOp(Exp,..) — both key (0,"exp",2));
        // compare their argument lists positionally.
        _ => cmp_pterm_list(&fapp_args(a), &fapp_args(b)),
    }
}

/// Collect the positional argument list of a FApp-class term (for
/// cross-representation comparison when two terms share a FunSym key).
fn fapp_args(t: &p::Term) -> Vec<p::Term> {
    use p::Term::*;
    match t {
        App(_, x) => x.clone(),
        Pair(x) => x.clone(),
        AlgApp(_, l, r) | Diff(l, r) | BinOp(_, l, r) => vec![(**l).clone(), (**r).clone()],
        PatMatch(x) => vec![(**x).clone()],
        _ => Vec::new(),
    }
}

/// Returns `(class, sub_tag)` where class=0 for Lit-like, 1 for FApp-like.
///
/// HS-faithful: a free-variable `p::Term` corresponds to `Term (Lit Name LVar)`,
/// whose derived `Ord` is `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74), and within
/// `LIT`, `Lit c v = Con c | Var v` derives `Con < Var` (VTerm.hs:56-57).
/// Therefore ALL constant literals (Pub/Fresh/Nat names) sort BEFORE any
/// variable.  Among constants, `Ord Name` compares the `NameTag` first
/// (`FreshName | PubName | NodeName | NatName`, LTerm.hs:219-220) so the literal
/// order is Fresh < Pub < Nat, then by name string.  Variables come last in
/// the `LIT` class.
///
/// The 0-arity builtins `NumberOne`/`NatOne`/`DhNeutral` are NOT literals in
/// HS — they are `fAppNoEq oneSym []` / `fAppNoEq natOneSym []` /
/// `fAppNoEq dhNeutralSym []` (Term/Term.hs:127-130), i.e. nullary function
/// applications, so they belong to the FApp class.
fn term_class(t: &p::Term) -> (u8, u8) {
    use p::Term::*;
    match t {
        // LIT (Con name): constants, ordered by Name's NameTag (Fresh<Pub<Nat).
        FreshLit(_) => (0, 0),
        PubLit(_) => (0, 1),
        NatLit(_) => (0, 2),
        Number(_) => (0, 3),
        // LIT (Var v): variables sort after all constants.
        Var(_) => (0, 4),
        // FAPP: nullary builtins are NoEq function applications, not literals.
        // NB: the second field below is a tie-breaker ONLY within the Lit
        // class (sub-tags 0..4); the FApp sub-tags (1,0)..(1,8) are never
        // consulted for ordering, because [`cmp_pterm`] dispatches every
        // FApp-class term through `funsym_key`/`cmp_fapp_args` (the `ca == 1`
        // branch) and returns before the `sa.cmp(&sb)` sub-tag fallthrough.
        NumberOne => (1, 0),
        NatOne => (1, 1),
        DhNeutral => (1, 2),
        App(_, _) => (1, 3),
        AlgApp(_, _, _) => (1, 4),
        Pair(_) => (1, 5),
        Diff(_, _) => (1, 6),
        BinOp(_, _, _) => (1, 7),
        PatMatch(_) => (1, 8),
    }
}

/// HS-faithful: which `BinOp`s are AC (associative-commutative)?
/// Mirrors HS's `MaudeSig`-attribute classification: Mult, Union, Xor,
/// NatPlus and the user-declared `[AC]` symbols are AC; Exp is NOT
/// (right-associative algebraic).
fn is_ac_binop(o: &p::BinOp) -> bool {
    use p::BinOp::*;
    matches!(o, Mult | Union | Xor | NatPlus | AcFct(_))
}

/// Flatten an AC-BinOp chain into a flat operand list, BORROWING the operands.
/// E.g. `BinOp(Union, BinOp(Union, a, b), c)` flattens to `[&a, &b, &c]`.
/// Non-matching outer terms are pushed verbatim (no recursion into
/// nested non-Union/non-same-op subtrees).
fn flatten_ac_binop<'a>(op: &p::BinOp, t: &'a p::Term, out: &mut Vec<&'a p::Term>) {
    match t {
        p::Term::BinOp(inner_op, l, r) if inner_op == op => {
            flatten_ac_binop(op, l, out);
            flatten_ac_binop(op, r, out);
        }
        _ => out.push(t),
    }
}

/// HS-faithful Ord for free `LVar`: `(idx, sort, name)` lexicographic
/// (Term/LTerm.hs:545-548).  Rust's `p::VarSpec` has the same fields
/// in a different declaration order — we compare in HS's order.
fn cmp_varspec(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx
        .cmp(&b.idx)
        .then_with(|| a.sort.cmp(&b.sort))
        .then_with(|| a.name.cmp(&b.name))
}

/// AC-canonicalise a parser-AST term: for every `BinOp(op, l, r)` where op
/// is AC (Mult/Union/Xor/NatPlus, or a user-declared `[AC]` symbol),
/// flatten the chain into the full multiset, sort it with [`cmp_pterm`],
/// then re-fold right-leaning so the canonical form matches HS's flat-sorted
/// `FApp (AC op) args`.
///
/// Without this, parser-AST `BinOp` stays in the order the parser
/// produced (left-associative left-to-right), so e.g.
/// `na XOR ~k XOR ~nb` parses as `BinOp(Xor, BinOp(Xor, na, k), nb)`
/// and pretty-prints as `((na⊕~k)⊕~nb)` — but HS prints the same source
/// as `(~k⊕~nb⊕na)` because HS's `fAppAC` smart constructor flattens
/// and sorts at parse time.  `term_to_lnterm` does call `f_app_ac` so
/// LNTerm-side is already canonical; this fixes the parser-AST side
/// for downstream consumers (rule body pretty-printing,
/// guardedness checks, etc.) that operate on parser-AST directly.
///
/// Also canonicalises `C`-symbol applications: `em(a, b)` is
/// commutative (not associative), so HS's `fAppC EMap [a, b]` sorts the
/// two arguments (Term/Term/Raw.hs:133-134).  Mirror that here so the parser-AST
/// display path matches HS — `em` args arrive in source order, which can
/// differ from canonical order.
/// HS site: `Theory/Text/Parser/Term.hs:87-106, see line 103` / `Term/Term/Raw.hs:133-134`:
///   `fAppC nacsym as = FAPP (C nacsym) (sort as)`
pub fn canonicalize_ac_in_pterm(t: &p::Term) -> p::Term {
    use p::BinOp;
    /// Sort a flattened AC operand list and re-fold it right-leaning into
    /// `BinOp(op, x_0, BinOp(op, x_1, ...))` — the parser-AST spelling of
    /// HS's flat, sorted `FApp (AC op) args` (`fAppAC`,
    /// Term/Term/Raw.hs:118-122).  A one-element list collapses to that
    /// element, mirroring `fAppAC _ [a] = a`.
    fn sort_and_fold(op: BinOp, mut flat: Vec<p::Term>) -> p::Term {
        flat.sort_by(cmp_pterm);
        let mut iter = flat.into_iter().rev();
        let mut acc = iter.next().expect("AC chain has at least one element");
        for prev in iter {
            acc = p::Term::BinOp(op, Box::new(prev), Box::new(acc));
        }
        acc
    }
    match t {
        p::Term::Var(_)
        | p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => t.clone(),
        // `em(a, b)` — commutative C-symbol: sort the two args to match
        // HS `fAppC EMap [a,b] = FAPP (C EMap) (sort [a,b])`
        // (Term/Term/Raw.hs:133-134).  Name-keyed with NO builtin gate, exactly
        // like HS's `naryOpApp` arm (Theory/Text/Parser/Term.hs:103) and its
        // `lookupArity` table, which always carries `emapSymString`
        // (Theory/Text/Parser/Term.hs:65) — so a user `functions: em/2` sorts
        // here too.  `term_to_vterm`'s `em` arm IS builtin-gated; see the
        // DELIBERATE DIVERGENCE note there for why the two differ.
        p::Term::App(n, args) if n == "em" && args.len() == 2 => {
            let a2 = canonicalize_ac_in_pterm(&args[0]);
            let b2 = canonicalize_ac_in_pterm(&args[1]);
            let (first, second) = if cmp_pterm(&a2, &b2) != std::cmp::Ordering::Greater {
                (a2, b2)
            } else {
                (b2, a2)
            };
            p::Term::App(n.clone(), vec![first, second])
        }
        p::Term::App(n, args) => p::Term::App(
            n.clone(),
            args.iter().map(canonicalize_ac_in_pterm).collect(),
        ),
        // `op{t1}t2` is a head of its own: HS `binaryAlgApp` has no `em` case
        // and builds `fAppNoEq` (Theory/Text/Parser/Term.hs:109-121) where
        // `naryOpApp` builds `fAppC EMap` for `em(a, b)`
        // (Theory/Text/Parser/Term.hs:103), so the braced spelling of a
        // commutative symbol keeps its arguments in source order.
        p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
            n.clone(),
            Box::new(canonicalize_ac_in_pterm(a)),
            Box::new(canonicalize_ac_in_pterm(b)),
        ),
        p::Term::Pair(items) => p::Term::Pair(items.iter().map(canonicalize_ac_in_pterm).collect()),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(canonicalize_ac_in_pterm(a)),
            Box::new(canonicalize_ac_in_pterm(b)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(canonicalize_ac_in_pterm(inner))),
        p::Term::BinOp(op, l, r) => {
            let l2 = canonicalize_ac_in_pterm(l);
            let r2 = canonicalize_ac_in_pterm(r);
            if !is_ac_binop(op) {
                return p::Term::BinOp(*op, Box::new(l2), Box::new(r2));
            }
            // Flatten the WHOLE AC chain rooted at this BinOp, then sort.
            let mut operands: Vec<&p::Term> = Vec::new();
            flatten_ac_binop(op, &l2, &mut operands);
            flatten_ac_binop(op, &r2, &mut operands);
            let flat: Vec<p::Term> = operands.into_iter().cloned().collect();
            sort_and_fold(*op, flat)
        }
    }
}

/// Shared structural walker: rebuild a parser-AST fact, mapping `g` over
/// every arg.  The traversal shape behind [`canonicalize_ac_in_pfact`], which
/// supplies its own leaf `&Term -> Term`.
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

/// Apply `canonicalize_ac_in_pterm` to every term in a fact.
pub fn canonicalize_ac_in_pfact(f: &p::Fact) -> p::Fact {
    map_fact_terms(f, &canonicalize_ac_in_pterm)
}

/// Apply `canonicalize_ac_in_pterm` to every term in a parser-AST formula.
///
/// HS sorts AC arguments at parse time when building LNTerm via `fAppAC`
/// (Term/Term/Raw.hs:118-129) over the *free* logical variables, using
/// `Ord LVar` = (idx, sort, name) (LTerm.hs:545-548).  The parser keeps
/// `BinOp` trees in written order; this walk re-establishes the canonical AC
/// order on the free-variable parser AST.  Test-only: the formula printers
/// consume internal formulas, whose terms are AC-canonical by construction,
/// and the printer parity tests use this walk to put their parser-AST side
/// into the same order.
#[cfg(test)]
pub(crate) fn canonicalize_ac_in_formula(f: &p::Formula) -> p::Formula {
    map_formula_terms(f, &canonicalize_ac_in_pterm)
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
                p::BinOp::Exp => {
                    let sym = NoEqSym::new(
                        b"exp".to_vec(),
                        2,
                        Privacy::Public,
                        Constructability::Constructor,
                    );
                    Some(f_app_no_eq(sym, vec![aa, bb]))
                }
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
