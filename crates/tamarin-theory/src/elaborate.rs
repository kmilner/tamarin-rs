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
//!   (`st_fun_syms`, `CtxtStRule`s when convertible, macro definitions)
//! - Parser-AST macro expansion (`macro_expand::expand_theory_macros`)
//!   and predicate expansion (`predicate_expand::expand_theory_formulas`)
//!   before any typed conversion
//! - Rules — `parser::Rule` → `OpenProtoRule(ProtoRuleE, [])`
//! - Lemmas / restrictions — the formula is intentionally retained as
//!   parser AST (guarded conversion done lazily via `formula_to_guarded`),
//!   after arity-1 tuple folding (`rewrite_arity1_*`) and AC/C
//!   canonicalization (`canonicalize_ac_in_p*`)
//!
//! It also provides the parser↔typed conversion helpers used above:
//! `term_to_lnterm`/`lnterm_to_term` (LNTerm round-tripping) and the
//! SAPIC term/fact converters (`term_to_sapic_term`/`fact_to_sapic_fact`).
//!
//! Returned errors describe the surface offence (e.g. "duplicate rule
//! `R`"), with no internal panics.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
use tamarin_term::lterm::LSort;
use tamarin_term::lterm::LVar;

thread_local! {
    /// The user-declared function-name sets of the theory currently being
    /// elaborated or proved, held as one shared bundle.  Installed by
    /// [`set_user_funs_for_theory`] / [`set_user_funs_from_collected`] /
    /// [`MaudeSigNullaryGuard`], each of which returns an RAII guard that
    /// restores the previous bundle on drop, so nested or sequential
    /// elaborations on one thread cannot bleed each other's sets.  Read by
    /// `term_to_vterm` (through the [`with_user_fun_sets`] snapshot), by
    /// `canonicalize_ac_in_pterm` and by the guarded-formula conversion.
    /// [`CollectedUserFuns`] documents what each set drives.
    ///
    /// A freshly spawned thread starts with every set EMPTY, so a rayon
    /// worker that converts terms must install a [`snapshot_user_funs`]
    /// bundle of the spawning thread's sets first.
    static USER_FUNS: RefCell<Arc<CollectedUserFuns>>
        = RefCell::new(Arc::new(CollectedUserFuns::default()));
}
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig, enable_diff_maude_sig,
    hash_maude_sig, location_report_maude_sig, mset_maude_sig, nat_maude_sig, pair_dest_maude_sig,
    reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};
use tamarin_term::term::{f_app_no_eq, Term};
use tamarin_term::vterm::{Lit, VTerm};

use crate::guarded::formula_to_guarded;
use crate::rule::{ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};
use crate::signature::SignaturePure;
use crate::theory::{
    AccLemma, CaseTest, LNMacro, Lemma, LemmaAttr, OpenProtoRule, OpenRestriction, ProofSkeleton,
    Theory, TheoryItem, TraceQuantifier, TranslationElement,
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
/// [`crate::formula_reports::formula_reports`].  The two perform the same
/// `formula_to_guarded` scan but format their output differently; keep them
/// in sync if the guardedness check itself changes.
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

/// Port of HS `checkGuarded` called inside `formulaReports`
/// (Wellformedness.hs:988-1004).
///
/// For each lemma/restriction formula that fails `formulaToGuarded`,
/// produce a `WfError` with:
///   - topic `" Formula guardedness"` (leading space, matching HS
///     `underlineTopic " Formula guardedness"` at Wellformedness.hs:999-1014, see line 1004)
///   - message layout matching HS's `prettyWfErrorReport` + `checkGuarded`:
///
/// ```text
///  Formula guardedness
/// ====================
///
///   {header} cannot be converted to a guarded formula:
///     {error_text}
///       "{sub_formula}"
///     in the formula
///       "{full_formula}"
/// ```
///
/// Indentation: 2 (prettyWfErrorReport nest 2) + 2 (checkGuarded nest 2
/// err) + 2 (ppFormula nest 2) = 6 spaces for formula text.
///
/// HS `msum` semantics: in `formulaReports` the check order is
/// `checkQuantifiers`, `checkTerms`, `checkGuarded` (Wellformedness.hs:1002-1004).
/// Because `WfErrorReport = [WfError]`, the list monad's `msum` is
/// `concat`, so all three checks run and their results are
/// concatenated — there is NO "first wins" short-circuit, and
/// `checkGuarded` always runs unconditionally for every
/// lemma/restriction.  This function does the same: it runs the
/// guardedness check unconditionally on every lemma/restriction.
///
/// The batch / web load pipelines instead go through
/// [`crate::formula_reports::formula_reports`], which interleaves this arm
/// with the other two per formula as HS's `msum` does; this entry point
/// serves callers that want the `checkGuarded` findings alone.
pub fn check_guarded_wf(parser_thy: &p::Theory) -> Vec<tamarin_parser::wf::WfError> {
    // Apply macros so the WF check sees the expanded formulas, just as
    // HS's `formulaReports` applies `applyMacroInFormula` before checking.
    let mut thy_clone = parser_thy.clone();
    crate::macro_expand::expand_theory_macros(&mut thy_clone);

    // Expand `predicates:` use-sites BEFORE the guardedness check, mirroring
    // HS: there the lemma/restriction formula is predicate-expanded at PARSE
    // time (`liftedAddLemma`→`expandLemma`→`expandFormula`,
    // Theory/Text/Parser.hs:145-147; `liftedAddRestriction`→`expandRestriction`,
    // lines 132-134), so by the time `formulaReports.checkGuarded`
    // (Wellformedness.hs:999-1014, see line 1004) reads `get lFormula l` / `get rstrFormula rstr`
    // the `Pred` sugar is already gone and the formula is the inlined body.
    // The guardedness conversion can only guard a quantified var that appears
    // in an `Action`/`Eq`/`Less`/… atom — never one buried inside an opaque
    // `Pred(...)` atom.  A predicate like `Exists(#time) <=> ∃ val. Action(val)
    // @ time` means `∃ #t. Exists(#t)` expands to `∃ #t. ∃ val. Action(val) @
    // #t`, where `#t` IS guarded by the action's timepoint.  Without this
    // expansion the check sees the un-expanded `∃ #t. Exists(#t)` and falsely
    // reports `#t` as unguarded.  Order matches `elaborate` (macros → predicates).
    // An expansion error here (e.g. an undefined predicate) is surfaced
    // elsewhere by the elaborate path; here we keep the macro-only form so the
    // guardedness check still runs on what it can.
    let _ = crate::predicate_expand::expand_theory_formulas(&mut thy_clone);

    // Iterate lemmas and restrictions in HS `annFormulas` order — all lemmas
    // in theory order, then all restrictions (`formulaReports`,
    // Wellformedness.hs:1007-1014).
    crate::formula_reports::ann_formulas(&thy_clone)
        .into_iter()
        .filter_map(|(header, formula)| check_guarded_entry(&header, formula))
        .collect()
}

/// The `checkGuarded` finding for one annotated formula, if it fails
/// `formulaToGuarded`.  `header` is HS's `"Lemma `n'"` / `"Restriction `n'"`;
/// the formula must already be macro- and predicate-expanded (see
/// [`check_guarded_wf`], which does both before calling this).  Split out so
/// the combined per-formula pass in [`crate::formula_reports`] can interleave
/// this arm with `checkQuantifiers` / `checkTerms` as HS's `msum` does.
pub fn check_guarded_entry(
    header: &str,
    formula: &p::Formula,
) -> Option<tamarin_parser::wf::WfError> {
    use crate::pretty_formula::pretty_formula;
    use tamarin_parser::wf::underline_topic;

    let e = match formula_to_guarded(formula) {
        Ok(_) => return None, // guard check passed
        Err(e) => e,
    };

    // Render the formula text (the full formula).
    let full_formula_text = pretty_formula(formula);

    // Render the sub-formula text (the innermost failing quantifier,
    // or the full formula if no sub-formula was tracked — which
    // matches HS's `ppFormula fmOrig` for the top-level case).
    let sub_formula_text = e
        .subject_formula
        .as_ref()
        .map(pretty_formula)
        .unwrap_or_else(|| full_formula_text.clone());

    // Build the HS-faithful message block.
    // Layout (indent levels):
    //   2:  "{header} cannot be converted to a guarded formula:"
    //   4:  "{error_text}"
    //   6:  '"{sub_formula}"'     (if sub_formula != full_formula)
    //   4:  "in the formula"
    //   6:  '"{full_formula}"'
    //
    // The `underlineTopic` of " Formula guardedness" includes the
    // trailing newline; we add one blank line before the body (from
    // `$-$` in `ppTopic` of `prettyWfErrorReport`).
    let topic = " Formula guardedness";
    let mut msg = String::new();
    msg.push_str(&underline_topic(topic));
    msg.push('\n'); // blank line between header and body
    msg.push_str("  "); // nest 2 (prettyWfErrorReport)
    msg.push_str(header);
    msg.push_str(" cannot be converted to a guarded formula:\n");

    // Indent the error body by 4 spaces (nest 2 inside checkGuarded).
    for line in e.message.lines() {
        msg.push_str("    ");
        msg.push_str(line);
        msg.push('\n');
    }

    // If the sub-formula is different from the full formula (nested
    // quantifier case), emit the sub-formula line (6 spaces).
    // This mirrors HS's `noUnguardedVars` which includes `ppFormula f0`
    // (the sub-formula) as part of the `d` doc, then `ppError` appends
    // "in the formula" + full formula.
    // When sub == full (top-level quantifier failure), HS still emits
    // the formula once under the error text and once under "in the formula"
    // — the same text appears twice.
    msg.push_str("      "); // 6 spaces
    msg.push('"');
    msg.push_str(&sub_formula_text);
    msg.push_str("\"\n");
    msg.push_str("    in the formula\n");
    msg.push_str("      "); // 6 spaces
    msg.push('"');
    msg.push_str(&full_formula_text);
    msg.push_str("\"\n");

    Some(tamarin_parser::wf::WfError::new(topic, msg))
}

/// Post-translation port of HS `publicNamesReport'` (Wellformedness.hs:463-484)
/// for SAPIC theories.  HS runs the FULL `checkWellformedness` on the TRANSLATED
/// theory, so `publicNames = universeBi ru` walks each generated rule INCLUDING
/// the source subprocess HS attaches to it.  The parser-level
/// `wf::public_names_report` runs BEFORE translation (on the process-only
/// theory, no generated rules) and — even post-translation — the parser AST
/// stores the process only as a rendered `process="…"` string, so a constant
/// appearing solely inside the process (the `'C'` in `insert <'roles', x, 'C'>`)
/// is invisible to it.  Walk the ELABORATED rules' facts AND their `process`
/// attribute here to recover those constants.
///
/// The root `Init` rule carries the WHOLE process (`base_init` in
/// tamarin-sapic's base_translation.rs; HS `baseInit`,
/// Basetranslation.hs:312-317, see line 313 — the rule's annotation is `anP`, the full
/// process) and is emitted first, so under `clashesOn`'s
/// first-occurrence dedup it wins every public name — reproducing HS's
/// `rule "Init":  name 'C', 'c'` attribution.
pub fn sapic_public_names_report(thy: &Theory) -> Vec<tamarin_parser::wf::WfError> {
    let mut pairs: Vec<(String, String)> = Vec::new();
    for r in thy.items.iter().filter_map(|it| match it {
        TheoryItem::Rule(r) => Some(r),
        _ => None,
    }) {
        // HS `showRuleCaseName ru = prettyProtoRuleName (ruleName ru)`
        // (Rule.hs:1225-1227) = `prefixIfReserved n` for a `StandRule n`.
        let case_name = crate::rule::prefix_if_reserved(r.name());
        let mut names: Vec<String> = Vec::new();
        for f in r
            .rule
            .premises
            .iter()
            .chain(&r.rule.actions)
            .chain(&r.rule.conclusions)
        {
            for t in f.terms.iter() {
                collect_pub_names(t, &mut names);
            }
        }
        if let Some(proc) = &r.rule.info.attributes.process {
            collect_process_pub_names(proc, &mut names);
        }
        for n in names {
            pairs.push((case_name.clone(), n));
        }
    }
    tamarin_parser::wf::public_names_report_from_pairs(pairs)
}

/// Collect the id of every public-sorted `Name` constant in a term, in
/// traversal order (HS `filter ((LSortPub ==) . sortOfName) (universeBi t)`).
/// Generic over the variable type so it serves both `LNTerm` (rule facts) and
/// `SapicTerm` (process terms).
fn collect_pub_names<V>(t: &VTerm<Name, V>, out: &mut Vec<String>) {
    match t {
        Term::Lit(Lit::Con(n)) => {
            if tamarin_term::lterm::sort_of_name(n) == LSort::Pub {
                out.push(n.id.0.to_string());
            }
        }
        Term::Lit(Lit::Var(_)) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                collect_pub_names(a, out);
            }
        }
    }
}

/// Walk every node of a SAPIC process (`pfoldMap`), collecting public-name
/// constants from each node's terms — the `universeBi` reach over the source
/// subprocess HS attaches to a generated rule.  HS's `universeBi` is
/// field-exhaustive: it also descends into each node's
/// `ProcessParsedAnnotation.location` term and into a `Cond` combinator's
/// condition formula (both `Data` in HS), so those are harvested here too.
/// Collection order within a rule differs from HS's (HS walks `rInfo` first,
/// facts after) but is immaterial: `clashesOn` dedups by (spelling) with the
/// surviving pair keyed only on (rule name, spelling), which is identical for
/// every occurrence inside one rule.
fn collect_process_pub_names(p: &crate::sapic::PlainProcess, out: &mut Vec<String>) {
    use crate::sapic::{Process, ProcessCombinator as PC, SapicAction as SA};
    crate::sapic::pfold_map(p, &mut |node| {
        let ann = match node {
            Process::Null(a) => a,
            Process::Action(_, a, _) => a,
            Process::Comb(_, a, _, _) => a,
        };
        if let Some(loc) = &ann.location {
            collect_pub_names(loc, out);
        }
        match node {
            Process::Null(_) => {}
            Process::Action(ac, _, _) => match ac {
                SA::ChIn { chan, msg, .. } => {
                    if let Some(c) = chan {
                        collect_pub_names(c, out);
                    }
                    collect_pub_names(msg, out);
                }
                SA::ChOut { chan, msg } => {
                    if let Some(c) = chan {
                        collect_pub_names(c, out);
                    }
                    collect_pub_names(msg, out);
                }
                SA::Insert(a, b) => {
                    collect_pub_names(a, out);
                    collect_pub_names(b, out);
                }
                SA::Delete(a) | SA::Lock(a) | SA::Unlock(a) => collect_pub_names(a, out),
                SA::Event(fa) => {
                    for t in fa.terms.iter() {
                        collect_pub_names(t, out);
                    }
                }
                SA::ProcessCall(_, args) => {
                    for t in args {
                        collect_pub_names(t, out);
                    }
                }
                SA::Msr {
                    prems, acts, concs, ..
                } => {
                    for fa in prems.iter().chain(acts).chain(concs) {
                        for t in fa.terms.iter() {
                            collect_pub_names(t, out);
                        }
                    }
                }
                SA::Rep | SA::New(_) => {}
            },
            Process::Comb(c, _, _, _) => match c {
                PC::CondEq(a, b) => {
                    collect_pub_names(a, out);
                    collect_pub_names(b, out);
                }
                PC::Lookup(t, _) => collect_pub_names(t, out),
                PC::Let { left, right, .. } => {
                    collect_pub_names(left, out);
                    collect_pub_names(right, out);
                }
                // `Cond` stores its condition as an UN-elaborated parser-AST
                // formula (see `ProcessCombinator::Cond`); HS stores an
                // elaborated `SapicNFormula` whose `'c'` literals are `Name`s
                // that `universeBi` collects.  Harvest the parser `PubLit`s —
                // bare nullary-constant tokens stay `Var`/`App` in the parser
                // AST and are correctly NOT collected (in HS they are `FApp`s,
                // not `Name`s).
                PC::Cond(f) => collect_parser_formula_pub_names(f, out),
                PC::Parallel | PC::Ndc => {}
            },
        }
        Vec::<()>::new()
    });
}

/// Collect public-name constants (parser `PubLit`, HS `Name PubName`) from a
/// parser-AST formula, in traversal order.  Serves `collect_process_pub_names`
/// for the `Cond` combinator, whose condition never leaves the parser AST.
fn collect_parser_formula_pub_names(f: &p::Formula, out: &mut Vec<String>) {
    use tamarin_parser::ast::{Atom, Formula};
    match f {
        Formula::False | Formula::True => {}
        Formula::Atom(a) => match a {
            Atom::Eq(x, y) | Atom::Less(x, y) | Atom::LessMset(x, y) | Atom::Subterm(x, y) => {
                collect_parser_term_pub_names(x, out);
                collect_parser_term_pub_names(y, out);
            }
            Atom::Action(fa, t) => {
                for x in &fa.args {
                    collect_parser_term_pub_names(x, out);
                }
                collect_parser_term_pub_names(t, out);
            }
            Atom::Last(t) => collect_parser_term_pub_names(t, out),
            Atom::Pred(fa) => {
                for x in &fa.args {
                    collect_parser_term_pub_names(x, out);
                }
            }
        },
        Formula::Not(x) => collect_parser_formula_pub_names(x, out),
        Formula::And(x, y) | Formula::Or(x, y) | Formula::Implies(x, y) | Formula::Iff(x, y) => {
            collect_parser_formula_pub_names(x, out);
            collect_parser_formula_pub_names(y, out);
        }
        Formula::Forall(_, x) | Formula::Exists(_, x) => {
            collect_parser_formula_pub_names(x, out);
        }
    }
}

/// Collect public-name constants from a parser-AST term (the `PubLit`
/// variant), recursively.
fn collect_parser_term_pub_names(t: &p::Term, out: &mut Vec<String>) {
    use tamarin_parser::ast::Term as PT;
    match t {
        PT::PubLit(n) => out.push(n.clone()),
        PT::Var(_)
        | PT::FreshLit(_)
        | PT::NatLit(_)
        | PT::Number(_)
        | PT::NumberOne
        | PT::NatOne
        | PT::DhNeutral => {}
        PT::App(_, args) | PT::Pair(args) => {
            for a in args {
                collect_parser_term_pub_names(a, out);
            }
        }
        PT::AlgApp(_, a, b) | PT::Diff(a, b) | PT::BinOp(_, a, b) => {
            collect_parser_term_pub_names(a, out);
            collect_parser_term_pub_names(b, out);
        }
        PT::PatMatch(inner) => collect_parser_term_pub_names(inner, out),
    }
}

/// Elaborate a parser theory into a typed `Theory`. The signature
/// is initialised from the union of `builtins:` declarations. Before
/// the structural conversion runs, predicate atoms are expanded
/// in-place against any `predicates:` declarations.
pub fn elaborate(parser_thy: &p::Theory) -> Result<Theory, ElabError> {
    let mut thy_clone = parser_thy.clone();
    // Apply macros at parser-AST level BEFORE predicate expansion.
    // Mirrors HS's parse-time application: lemmas are expanded by
    // `parseLemmaWithMacros` (Theory/Text/Parser.hs:97-105); rules by
    // `closeProtoRule` (lib/theory/src/Rule.hs:96-98) before
    // variantsProtoRule runs; restrictions by `applyMacroInRestriction`
    // (Theory/Model/Restriction.hs:163-165).  We apply at the parser-AST
    // level so a single pass handles every term-bearing item before any
    // typed conversion (`term_to_lnterm` / `formula_to_guarded`) sees a
    // macro call.  Predicate-expand may itself substitute the inlined
    // predicate body into use sites, and the body could contain macro
    // calls — so expand macros first.
    crate::macro_expand::expand_theory_macros(&mut thy_clone);
    if let Err(e) = crate::predicate_expand::expand_theory_formulas(&mut thy_clone) {
        return Err(ElabError {
            message: format!("predicate expansion failed: {}", e.message),
        });
    }
    // Collect the user-declared unary / nullary / private / destructor / AC /
    // NDC / NDC-diff function-name sets that drive `term_to_lnterm`.  The
    // bundle is installed via an RAII guard, scoped so concurrent /
    // sequential elaborations on the same thread can't bleed stale state.
    let _guard = UserFunsForTheoryGuard::set(Arc::new(collect_user_funs(&thy_clone.items)));
    let mut thy = elaborate_already_expanded(&thy_clone)?;

    // HS folds surplus arguments of arity-1 function applications into a
    // single right-associative pair at PARSE time (`naryOpApp` `k == 1`,
    // Theory/Text/Parser/Term.hs:94-96 + `tupleterm` line 211-212:
    // `chainr1 (msetterm ...) (curry fAppPair <$ comma)`), so the surface
    // `h(a, b, c)` parses to `h(<a, b, c>)` = `h(fAppPair a (fAppPair b c))`.
    // Because the fold happens at parse time, the lemma/restriction formula
    // stored in HS's theory is ALREADY folded, and every downstream consumer
    // (in particular `formulaToGuarded`, which builds the prover's initial
    // constraint-system goal and thus the `solve( ... )` text printed in the
    // proof body) sees the folded form.
    //
    // RS's term parser is arity-unaware and keeps `App("h", [a, b, c])`, so we
    // re-establish the fold here, once, on the elaborated theory's
    // lemma/restriction formulas — after the signature is final so
    // `arity1_noeq_names` covers both user `functions: f/1` and builtin
    // arity-1 NoEq symbols.  This makes `prove.rs`'s `formula_to_guarded`
    // calls (lemma + reuse-lemma + restriction) carry the folded `h(<…>)`
    // shape into the goal, matching HS.  The display path folds the parser-AST
    // separately (pretty_theory.rs), and the fold is idempotent (an arity-1
    // application with exactly one — already-paired — argument is left
    // unchanged), so applying it on both sides is safe.
    let arity1 = arity1_noeq_names(thy.signature.maude_sig());
    if !arity1.is_empty() {
        for item in &mut thy.items {
            match item {
                TheoryItem::Lemma(l) => {
                    l.formula = rewrite_arity1_formula(&l.formula, &arity1);
                }
                TheoryItem::Restriction(r) => {
                    r.formula = rewrite_arity1_formula(&r.formula, &arity1);
                    if let Some(of) = &r.original_formula {
                        r.original_formula = Some(rewrite_arity1_formula(of, &arity1));
                    }
                }
                _ => {}
            }
        }
    }
    Ok(thy)
}

/// The user-declared function-name sets read by `term_to_lnterm`.
///
/// One bundle serves as both the value installed in the `USER_FUNS`
/// thread-local and the snapshot handed around for re-installation on
/// another thread.
#[derive(Clone, Default)]
pub struct CollectedUserFuns {
    /// Arity-1 user `functions:` names (drives the auto-tuple fold, like
    /// the built-in unary names h / fst / snd / ...).  In Tamarin's surface
    /// syntax `f(a, b, c)` for a function declared `f/1` is sugar for
    /// `f(<a, b, c>)`.  Without this set, `PRF(pms, nc, ns)` for
    /// `functions: PRF/1` would reach Maude as a 3-arg call, which Maude
    /// silently rejects, and our `reduce` loop spins forever.
    unary: BTreeSet<String>,
    /// 0-arity names from user `functions:` plus any enabled builtin's
    /// 0-arity constants (`signing`/`dest-signing`/`revealing-signing` add
    /// `true`; `xor` adds `zero`; etc.), mirroring HS's parser-state
    /// `nullaryApp` lookup.  Read by `term_to_lnterm`'s `Var` branch so a
    /// bare `true` (which the lexer-level surface parser renders as
    /// `Var("true",Untagged)` for lack of a signature lookup) becomes a
    /// 0-arity `f_app_no_eq` constant instead of a free variable.  Without
    /// it, `Eq(verify(...), true)` in a rule's actions becomes an `Eq` over
    /// `verify(...)` and a Msg-sort variable, which the `Eq_check_succeed`
    /// restriction trivially satisfies via the eq-store — undermining the
    /// signing builtin's semantics and causing TLS_Handshake-class lemmas
    /// to be wrong-falsified.
    nullary: BTreeSet<String>,
    /// NON-`[AC]` user `functions:` names marked `private` (any arity), plus
    /// the private symbols of each enabled builtin; threads
    /// `Privacy::Private` through synthesized NoEqSyms.  Without it, `KU(f)`
    /// for a private nullary `f` is filtered by
    /// `is_nullary_public_function` (because we say Public), causing
    /// `is_finished` to incorrectly report Solved.
    ///
    /// `[AC]` declarations are excluded here (and from `destructor` / `ndc` /
    /// `ndc_diff`): their options live on the `AcFctSym` stored in `ac`.  See
    /// that field for why the two must not share one name-keyed set.
    private: BTreeSet<String>,
    /// NON-`[AC]` user `functions:` names marked `[destructor]` (any arity),
    /// plus the destructor symbols of each enabled builtin; threads
    /// `Constructability::Destructor` through synthesized NoEqSyms,
    /// mirroring Haskell's `naryOpApp`/`lookupArity`, which reads
    /// `(k,priv,cnstr)` from the signature
    /// (Theory/Text/Parser/Term.hs:62-71,93).  `NoEqSym` derives
    /// Eq/Ord/Hash over `constructability`, and the constructor/destructor
    /// tag is encoded into the Maude operator name (`XC` vs `XD`), so a
    /// Constructor-tagged term for a `[destructor]` symbol would print as
    /// an operator Maude never declared.
    destructor: BTreeSet<String>,
    /// The user-declared `[AC]` symbols, keyed by name and carrying THAT
    /// declaration's own privacy / constructability / NDC options.  A prefix
    /// application of such a name lowers to `f_app_ac(AcFct ..)` (n-ary, no
    /// arity check) instead of `f_app_no_eq` — unless the name is also in
    /// `noeq_names`, see
    /// [`CollectedUserFuns::prefix_resolves_to_user_ac`].
    ///
    /// The options ride on the symbol rather than in the name-keyed
    /// `private` / `destructor` / `ndc` / `ndc_diff` sets because HS keeps a
    /// dual-declared name's two symbols in two different places — the NoEq
    /// one in `stFunSyms`, the AC one in `stACFunSyms`
    /// (Term/Maude/Signature.hs:97-98) — each with its own options tuple.
    /// `functions: f/2 [AC, destructor], f/2` declares a DESTRUCTOR AC `f`
    /// and a CONSTRUCTOR NoEq `f`; conflating them encodes the NoEq `f` as
    /// the Maude operator `tamXDFUf`, which the theory module never declares,
    /// so `get variants` comes back empty and the rule reports "has no
    /// variants".
    ///
    /// A name declared `[AC]` twice with differing options keeps the least
    /// symbol by `Ord AcFctSym`, mirroring HS `lookupArity`'s `lookup` over
    /// the ascending `S.toList (userDefinedFunSyms maudeSig)`
    /// (Theory/Text/Parser/Term.hs:62-72).
    ac: BTreeMap<String, AcFctSym>,
    /// Names (any arity) of every `NoEq` symbol of the full signature — the
    /// non-`[AC]` user `functions:` declarations, each enabled builtin's
    /// `NoEq` contribution to `funSyms`, and the always-present pair
    /// signature (`minimalMaudeSig` is `pairFunSig` — `pair`/`fst`/`snd` —
    /// Term/Maude/Signature.hs:224-226).  Mirrors HS
    /// `noEqFunSyms maudeSig` (Signature.hs:157-158); read by
    /// [`CollectedUserFuns::prefix_resolves_to_user_ac`].
    noeq_names: BTreeSet<String>,
    /// NON-`[AC]` user `functions:` names marked `[NDC]`.
    ndc: BTreeSet<String>,
    /// NON-`[AC]` user `functions:` names marked `[NDC-diff]`.
    ndc_diff: BTreeSet<String>,
    /// Whether the `bilinear-pairing` builtin is enabled.  Gates the
    /// name-keyed `em` → C-symbol lowering in `term_to_vterm`.
    bp: bool,
}

/// Single source of truth for collecting the user-declared function-name
/// sets from a theory's items (shared by `elaborate` and
/// `set_user_funs_for_theory`).
fn collect_user_funs(items: &[p::TheoryItem]) -> CollectedUserFuns {
    // HS `function` (Theory/Text/Parser/Signature.hs): a re-declaration of
    // `fst`/`snd` at arity 1 with public visibility resolves to the EXISTING
    // builtin pair-projection symbol (`return (NoEqUser (f,kp'), ...)` with
    // `kp'` the builtin's `(1, Public, Constructor, NotNDC)`) — every
    // requested attribute is discarded and no symbol is added.  Mirror that
    // here: such declarations must not contribute to the attribute sets,
    // otherwise `term_to_lnterm` resolves the theory's own
    // `fst(<x,y>) = x` equations with a Destructor-flagged symbol whose
    // Maude encoding (`tamXDFUfst`) does not match the declared op
    // (`tamXCFUfst`), killing the rewrite rule and with it the narrowed
    // `_0_fst`/`_0_snd` intruder destructors (noise theories).
    let is_builtin_pair_proj = |d: &p::FunctionDecl| -> bool {
        (d.name == "fst" || d.name == "snd") && d.arg_types.len() == 1 && !d.private
    };
    let mut unary: BTreeSet<String> = BTreeSet::new();
    let mut nullary: BTreeSet<String> = BTreeSet::new();
    let mut private: BTreeSet<String> = BTreeSet::new();
    let mut destructor: BTreeSet<String> = BTreeSet::new();
    let mut ac: BTreeMap<String, AcFctSym> = BTreeMap::new();
    let mut ndc: BTreeSet<String> = BTreeSet::new();
    let mut ndc_diff: BTreeSet<String> = BTreeSet::new();
    // `pairFunSig` is in every signature (`minimalMaudeSig`,
    // Term/Maude/Signature.hs:224-226).
    let mut noeq_names: BTreeSet<String> = ["pair", "fst", "snd"]
        .into_iter()
        .map(String::from)
        .collect();
    for it in items {
        let p::TheoryItem::Functions(decls) = it else {
            continue;
        };
        for d in decls {
            if d.arg_types.len() == 1 {
                unary.insert(d.name.clone());
            }
            if d.arg_types.is_empty() {
                nullary.insert(d.name.clone());
            }
            if !d.ac {
                noeq_names.insert(d.name.clone());
            }
            // The exemption gates the ATTRIBUTE sets only; arity resolution
            // via `unary` / `nullary` is unaffected, since the builtin
            // symbol has the same name and arity.
            if is_builtin_pair_proj(d) {
                continue;
            }
            // An `[AC]` declaration contributes an `ACfctUser` symbol to
            // `stACFunSyms` and NOTHING to `stFunSyms` (HS `function`,
            // Theory/Text/Parser/Signature.hs:220-222), so its options must
            // stay on that symbol instead of joining the NoEq-keyed sets
            // below — a same-named `NoEqUser` declaration keeps its own
            // (see the `ac` field).
            if d.ac {
                let sym = AcFctSym::new(
                    d.name.as_bytes().to_vec(),
                    if d.private {
                        Privacy::Private
                    } else {
                        Privacy::Public
                    },
                    if d.destructor {
                        Constructability::Destructor
                    } else {
                        Constructability::Constructor
                    },
                    ndc_state_of(d.ndc, d.ndc_diff),
                );
                ac.entry(d.name.clone())
                    .and_modify(|cur| {
                        if sym < *cur {
                            *cur = sym;
                        }
                    })
                    .or_insert(sym);
                continue;
            }
            if d.private {
                private.insert(d.name.clone());
            }
            if d.destructor {
                destructor.insert(d.name.clone());
            }
            if d.ndc {
                ndc.insert(d.name.clone());
            }
            if d.ndc_diff {
                ndc_diff.insert(d.name.clone());
            }
        }
    }
    let mut bp = false;
    for it in items {
        if let p::TheoryItem::Builtins(names) = it {
            for n in names {
                if n == "bilinear-pairing" {
                    bp = true;
                }
                for c in builtin_nullary_constants(n) {
                    nullary.insert(c.to_string());
                }
                // Every `NoEq` name the builtin folds into `funSyms` — the
                // set `lookupArity` ranks ahead of the `ACfctUser` entries
                // (Theory/Text/Parser/Term.hs:62-72), e.g. `exp` under
                // `builtins: diffie-hellman`.
                for c in builtin_noeq_fun_names(n) {
                    noeq_names.insert(c);
                }
                // HS `naryOpApp` / `lookupArity` (Theory/Text/Parser/Term.hs:63-65,93)
                // reads `(k, priv, cnstr)` straight from the per-theory
                // signature, which includes the BUILTIN symbols.  Mirror that by
                // merging the privacy / constructability of each builtin's
                // function symbols (most are public constructors, so this only
                // matters for `locations-report` — `rep` private, `check_rep` /
                // `get_rep` destructors — and the `dest-*` builtins' destructors).
                // Without this, a user/translation `rep(..)` / `check_rep(..)`
                // term serialises with the default `tamXC..` prefix and Maude
                // rejects it (`bad token`), so `get variants` returns empty and
                // the rule wrongly reports "has no variants".
                for (name, priv_, constr) in builtin_fun_attrs(n) {
                    if priv_ == Privacy::Private {
                        private.insert(name.clone());
                    }
                    if constr == Constructability::Destructor {
                        destructor.insert(name);
                    }
                }
            }
        }
    }
    CollectedUserFuns {
        unary,
        nullary,
        private,
        destructor,
        ac,
        noeq_names,
        ndc,
        ndc_diff,
        bp,
    }
}

/// The set of 0-arity function-symbol names for a theory: every user
/// `functions: f/0` declaration plus each enabled builtin's nullary constants.
/// Mirrors HS's parser-state `nullaryApp` lookup (Theory/Text/Parser/Term.hs:
/// 139-143), which resolves a bare `<name>` token to `FApp (NoEq <sym>) []`
/// rather than `Var <name>` when `<name>` is 0-arity in the signature.  The
/// `_restrict` / SAPIC-`Cond` restriction lift (`rule_restriction`) needs this
/// set to keep such constants inlined in the generated restriction formula
/// (HS `rewrite` treats a `FApp` as a non-variable and never abstracts it,
/// whereas the un-resolved parser-AST `Var` would be abstracted into a fresh
/// fact argument).
pub fn nullary_fun_names(items: &[p::TheoryItem]) -> BTreeSet<String> {
    collect_user_funs(items).nullary
}

/// The `(name, privacy, constructability)` of every NoEq function symbol a
/// builtin contributes, read from its `MaudeSig` (the same signature the Maude
/// theory module is generated from).  Used to thread builtin privacy /
/// destructor flags into `term_to_lnterm`'s symbol resolution — HS reads these
/// from the per-theory signature via `lookupArity`.
fn builtin_fun_attrs(name: &str) -> Vec<(String, Privacy, Constructability)> {
    let Some(msig) = builtin_sig(name) else {
        return Vec::new();
    };
    msig.st_fun_syms
        .iter()
        .filter_map(|s| {
            String::from_utf8(s.name.to_vec())
                .ok()
                .map(|n| (n, s.privacy, s.constructability))
        })
        .collect()
}

/// Extracts the 0-arity NoEq function-symbol names from a `MaudeSig`.
/// Mirrors HS `nullaryApp` (Theory/Text/Parser/Term.hs:158-163):
///
/// ```haskell
/// nullaryApp = do
///   maudeSig <- sig <$> getState
///   asum [ try (symbol (BC.unpack sym)) $> fApp fs []
///        | fs@(NoEq (sym,(0,_,_,_))) <- S.toList $
///            funSyms maudeSig `S.union` S.map NoEq (macroNames maudeSig) ]
/// ```
///
/// HS's parser consults `funSyms maudeSig` when disambiguating a bare
/// identifier from a free variable.  Our parser is too lexer-driven to
/// thread the MaudeSig through the parser-state, so we populate the
/// installed bundle's `nullary` set with the same names instead.  By
/// asking the MaudeSig directly here (rather than maintaining a parallel
/// hand-curated table) we guarantee the set we recognise matches HS's
/// `funSyms`, e.g. `oneSymString = "one"` and
/// `dhNeutralSymString = "DH_neutral"` for `dhFunSig`
/// (lib/term/src/Term/Term/FunctionSymbols.hs:134-134,137,153,163,192).
fn builtin_nullary_names_from_msig(msig: &MaudeSig) -> Vec<String> {
    msig.fun_syms
        .iter()
        .filter_map(|fs| match fs {
            tamarin_term::function_symbols::FunSym::NoEq(s) if s.arity == 0 => {
                String::from_utf8(s.name.to_vec()).ok()
            }
            _ => None,
        })
        .collect()
}

/// Returns the 0-arity function symbol names introduced by a given
/// `builtins:` declaration name.  Resolves the name to its MaudeSig via
/// `builtin_sig` and then extracts the 0-arity NoEq names via
/// [`builtin_nullary_names_from_msig`].  This mirrors HS exactly: a
/// `builtins: foo` declaration triggers `enableBuiltin foo` which
/// installs the corresponding `*FunSig` into the parser-state MaudeSig,
/// and `nullaryApp` then consults that signature.
///
/// Returns an empty vector for unknown builtin names (HS would never
/// reach this point: `enableBuiltin` is exhaustive over the parsed
/// keywords; unknowns fail at the parser).
pub fn builtin_nullary_constants(name: &str) -> Vec<String> {
    match builtin_sig(name) {
        Some(msig) => builtin_nullary_names_from_msig(&msig),
        None => Vec::new(),
    }
}

/// The names (any arity) of every `NoEq` function symbol a given `builtins:`
/// declaration folds into `funSyms` — both its `stFunSyms` (`h`, `aenc`, …)
/// and its enable flags' theory-level contributions (`exp`/`inv`/`one`/
/// `DH_neutral` for `diffie-hellman`, Term/Maude/Signature.hs:110-125) —
/// read off the same `MaudeSig` as [`builtin_nullary_constants`].  These are
/// the names `lookupArity` resolves as `NoEqUser` ahead of any `ACfctUser`
/// entry (Theory/Text/Parser/Term.hs:62-72).  Empty for unknown names, as
/// with [`builtin_nullary_constants`].
fn builtin_noeq_fun_names(name: &str) -> Vec<String> {
    let Some(msig) = builtin_sig(name) else {
        return Vec::new();
    };
    msig.fun_syms
        .iter()
        .filter_map(|fs| match fs {
            tamarin_term::function_symbols::FunSym::NoEq(s) => {
                String::from_utf8(s.name.to_vec()).ok()
            }
            _ => None,
        })
        .collect()
}

/// The bundle currently installed in [`USER_FUNS`] on this thread, as an
/// `Arc` clone.  The thread-local borrow ends inside this call, so the
/// caller may install or drop guards while holding the returned snapshot.
fn current_user_funs() -> Arc<CollectedUserFuns> {
    USER_FUNS.with(|c| c.borrow().clone())
}

/// True if `name` is registered as a 0-arity function for the current
/// elaboration.  See `CollectedUserFuns::nullary` for the populating logic.
pub(crate) fn is_user_nullary_fun(name: &str) -> bool {
    USER_FUNS.with(|c| c.borrow().nullary.contains(name))
}

/// The user-declared `[AC]` symbol names of the current elaboration,
/// ascending by name — HS's `S.toList (stACFunSyms sig)`
/// (Term/Maude/Signature.hs:98).  Callers that re-parse rendered term text
/// hand this to `parse_term_str` so `acterm`
/// (Theory/Text/Parser/Term.hs:165-174) recognises the INFIX spelling of
/// those symbols; without it `(z add h(y))` is a parse error.
pub(crate) fn current_user_ac_names() -> Vec<String> {
    USER_FUNS.with(|c| c.borrow().ac.keys().cloned().collect())
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

/// The symbol-resolution reads `term_to_vterm` performs against the
/// user-declared name sets.  The recursion carries one `Arc` snapshot of the
/// installed bundle, taken once at the entry point by `with_user_fun_sets`,
/// so a term tree costs one thread-local access rather than one per node.
impl CollectedUserFuns {
    /// True if `name` is registered as a user-declared arity-1 function for
    /// the current elaboration.  Read from the `unary` set.
    fn is_user_unary_fun(&self, name: &str) -> bool {
        self.unary.contains(name)
    }

    /// True if `name` is registered as a 0-arity function for the current
    /// elaboration.  See the `nullary` field for the populating logic.
    fn is_user_nullary_fun(&self, name: &str) -> bool {
        self.nullary.contains(name)
    }

    /// True if `name` is a user-declared `[AC]` function symbol — the raw
    /// declaration-set probe the `USER_FUNS` install/restore tests key on.
    /// Term resolution goes through
    /// [`CollectedUserFuns::prefix_resolves_to_user_ac`] instead.
    #[cfg(test)]
    fn is_user_ac_fun(&self, name: &str) -> bool {
        self.ac.contains_key(name)
    }

    /// True if a PREFIX (or `op{a}b`) application of `name` denotes the
    /// user-declared `[AC]` symbol.  HS `lookupArity` resolves those
    /// spellings by a list lookup over `S.toList (userDefinedFunSyms
    /// maudeSig)` in which every `NoEqUser` sorts before every `ACfctUser`
    /// (Theory/Text/Parser/Term.hs:62-72, constructor order of
    /// `UserDefinedSym`, Term/Term/FunctionSymbols.hs:146-147), so a name
    /// that is ALSO a `NoEq` symbol of the full signature resolves to that
    /// `NoEq` symbol, never the AC one.  The infix spelling bypasses
    /// `lookupArity` (`acterm`, Term.hs:163-168): `BinOp::AcFct` readers do
    /// not consult this.
    fn prefix_resolves_to_user_ac(&self, name: &str) -> bool {
        self.ac.contains_key(name) && !self.noeq_names.contains(name)
    }

    /// True when a PREFIX `exp(a, b)` resolves to THE DH exponentiation
    /// symbol, which HS `prettyTerm` renders infix: `FApp (NoEq s) [t1,t2] |
    /// s == expSym -> ppTerm t1 <> text "^" <> ppTerm t2` (Term/Term.hs:310)
    /// with `expSym = ("exp",(2,Public,Constructor,NotNDC))`
    /// (Term/Term/FunctionSymbols.hs:251).  The guard is on the WHOLE symbol:
    /// the name must resolve NoEq (so a lone `exp/2 [AC]` declaration stays
    /// the infix AC symbol) at arity 2 with default attributes — a
    /// `functions: exp/2 [private]` re-declaration is a different symbol and
    /// keeps the prefix rendering.
    fn prefix_exp_is_dh_exp(&self) -> bool {
        self.noeq_names.contains("exp")
            && !self.unary.contains("exp")
            && !self.nullary.contains("exp")
            && self.user_fun_privacy("exp") == Privacy::Public
            && self.user_fun_constructability("exp") == Constructability::Constructor
            && self.user_fun_ndc("exp") == NdcState::NotNdc
    }

    /// True if the theory enables the `bilinear-pairing` builtin.
    fn is_bp_enabled(&self) -> bool {
        self.bp
    }

    /// Returns `Privacy::Private` if the NoEq symbol called `name` is
    /// private; otherwise `Privacy::Public`.  Mirrors Haskell's `signature`
    /// lookup against the per-theory funSig.  A same-named `[AC]`
    /// declaration's privacy is NOT read here — see the `ac` field.
    fn user_fun_privacy(&self, name: &str) -> Privacy {
        if self.private.contains(name) {
            Privacy::Private
        } else {
            Privacy::Public
        }
    }

    /// Returns `Constructability::Destructor` if the NoEq symbol called
    /// `name` is a `[destructor]`; otherwise
    /// `Constructability::Constructor`.  Mirrors Haskell's `lookupArity`,
    /// which reads `(k,priv,cnstr)` straight from the signature
    /// (Theory/Text/Parser/Term.hs:62-71).  A same-named `[AC]`
    /// declaration's constructability is NOT read here — see the `ac` field.
    fn user_fun_constructability(&self, name: &str) -> Constructability {
        if self.destructor.contains(name) {
            Constructability::Destructor
        } else {
            Constructability::Constructor
        }
    }

    /// The NDC state of the NoEq symbol called `name`, read from the `[NDC]`
    /// / `[NDC-diff]` name sets.  A same-named `[AC]` declaration's NDC state
    /// is NOT read here — see the `ac` field.
    fn user_fun_ndc(&self, name: &str) -> NdcState {
        ndc_state_of(self.ndc.contains(name), self.ndc_diff.contains(name))
    }

    /// The `NoEqSym` for a user-declared name applied at `arity`, carrying
    /// the privacy / constructability / NDC flags read off its declaration
    /// (HS `lookupArity`).  The 0-arity `nullaryApp` recovery does not use
    /// this: a bare constant is always a constructor there.
    fn user_no_eq_sym(&self, name: &str, arity: usize) -> NoEqSym {
        NoEqSym::new(
            name.as_bytes().to_vec(),
            arity,
            self.user_fun_privacy(name),
            self.user_fun_constructability(name),
        )
        .with_ndc(self.user_fun_ndc(name))
    }

    /// The `AcFctSym` for a user-declared `[AC]` name, carrying the privacy /
    /// constructability / NDC flags read off ITS OWN declaration (HS
    /// `lookupArity` / `acterm` both hand back the whole `ACfctUser` tuple
    /// stored in `stACFunSyms`, Theory/Text/Parser/Term.hs:62-72,163-168) —
    /// never the flags of a same-named `NoEq` declaration.
    ///
    /// The default-attribute fallback covers a name the bundle has no `[AC]`
    /// declaration for, which the callers cannot produce: both prefix arms
    /// are gated on [`Self::prefix_resolves_to_user_ac`], and the parser only
    /// emits `BinOp::AcFct` for a name it saw declared `[AC]`.
    fn user_ac_fct_sym(&self, name: &str) -> AcFctSym {
        self.ac.get(name).copied().unwrap_or_else(|| {
            AcFctSym::new(
                name.as_bytes().to_vec(),
                Privacy::Public,
                Constructability::Constructor,
                NdcState::NotNdc,
            )
        })
    }
}

/// Snapshots the installed user-declared function-name bundle (one `Arc`
/// clone) and hands it to `f`.  The thread-local borrow ends before `f`
/// runs, so nothing `f` does — including installing or dropping a guard —
/// can conflict with the snapshot.
fn with_user_fun_sets<R>(f: impl FnOnce(&CollectedUserFuns) -> R) -> R {
    let sets = current_user_funs();
    f(&sets)
}

/// RAII guard that installs a user-declared function-name bundle into
/// `USER_FUNS` for the guard's lifetime, scoped to an outer call
/// (typically `prove_lemma`), and restores the previous bundle on drop.
///
/// Guards nest: the server installs one per renderer inside the per-theory
/// one (`TheoryEntry::install_user_funs`).  Restoration is by saved value,
/// so nesting behaves as a stack as long as the guards are dropped in
/// reverse installation order — which holding them in `let` bindings (or in
/// a struct that outlives the inner scopes, as `prove.rs`'s session does)
/// guarantees.
#[must_use = "dropping this guard immediately ends the scope it protects"]
pub struct UserFunsForTheoryGuard {
    previous: Arc<CollectedUserFuns>,
}

impl UserFunsForTheoryGuard {
    /// Make `funs` the current bundle, saving the one it displaces.
    fn set(funs: Arc<CollectedUserFuns>) -> Self {
        let previous = USER_FUNS.with(|c| {
            let mut b = c.borrow_mut();
            std::mem::replace(&mut *b, funs)
        });
        UserFunsForTheoryGuard { previous }
    }
}

impl Drop for UserFunsForTheoryGuard {
    fn drop(&mut self) {
        USER_FUNS.with(|c| {
            *c.borrow_mut() = std::mem::take(&mut self.previous);
        });
    }
}

/// RAII guard that swaps in the 0-arity NoEq function-symbol names from
/// a `MaudeSig` for the duration of a parse, then restores the previous
/// bundle on drop.  Only the nullary set is replaced — the other sets are
/// carried over from the bundle installed at construction.  Use this around
/// any call that builds LNTerms via [`term_to_lnterm`] from a string the
/// user/HS wrote against a specific MaudeSig (e.g. the cached
/// intruder-variant files in `data/`).
///
/// HS analogue: the parser-state MaudeSig consulted by `nullaryApp`
/// (Theory/Text/Parser/Term.hs:139-143).  HS sets it via
/// `setState (mkStateSig msig)` at the top of `parseIntruderRules`
/// (Theory/Text/Parser/Rule.hs:200-204).
pub struct MaudeSigNullaryGuard {
    _funs: UserFunsForTheoryGuard,
}

impl MaudeSigNullaryGuard {
    /// Push the 0-arity NoEq names from `msig` into the nullary set.
    pub fn set(msig: &MaudeSig) -> Self {
        let mut funs = current_user_funs().as_ref().clone();
        funs.nullary = builtin_nullary_names_from_msig(msig).into_iter().collect();
        MaudeSigNullaryGuard {
            _funs: UserFunsForTheoryGuard::set(Arc::new(funs)),
        }
    }
}

/// Re-collects the user-declared function-name sets from `parser_theory`
/// and installs them as the current bundle read by `term_to_lnterm`.
/// Returns an RAII guard whose drop restores the previous bundle.  Use
/// from `prove_lemma` so search-time term conversions see the right
/// per-theory signature info.
pub fn set_user_funs_for_theory(parser_theory: &p::Theory) -> UserFunsForTheoryGuard {
    UserFunsForTheoryGuard::set(Arc::new(collect_user_funs(&parser_theory.items)))
}

/// Collect the user-declared function-name sets from a parser theory, to
/// be cached and re-installed later (e.g. per-lemma on a rayon worker
/// thread under lemma-level parallelism, where the file-level guard set
/// on the main thread is not visible).
pub fn collect_user_funs_for_theory(parser_theory: &p::Theory) -> CollectedUserFuns {
    collect_user_funs(&parser_theory.items)
}

/// Install the cached user-fn sets as the current thread's bundle,
/// returning an RAII guard that restores the previous one on drop.
/// `term_to_lnterm` / `term_to_gterm` read the bundle, so any thread that
/// performs search-time term conversion must have it set — including rayon
/// worker threads proving lemmas in parallel.
pub fn set_user_funs_from_collected(funs: &CollectedUserFuns) -> UserFunsForTheoryGuard {
    UserFunsForTheoryGuard::set(Arc::new(funs.clone()))
}

/// Snapshot the calling thread's user-fun bundle so a rayon fan-out can
/// replicate it onto its worker threads (which spawn with EMPTY sets).
/// Capture this BEFORE `par_iter`, then install per worker with
/// [`set_user_funs_from_collected`]; a worker that converts terms without
/// it mis-classifies user nullary/unary symbols (e.g. a declared `true/0`
/// lifts to a free variable), silently changing term identity relative to
/// the calling thread.
pub fn snapshot_user_funs() -> CollectedUserFuns {
    current_user_funs().as_ref().clone()
}

fn elaborate_already_expanded(parser_thy: &p::Theory) -> Result<Theory, ElabError> {
    let mut sig = SignaturePure::empty(parser_thy.is_diff);
    if parser_thy.is_diff {
        sig.maude_sig = sig.maude_sig.merge(enable_diff_maude_sig());
    }

    let mut thy: Theory = Theory::new(parser_thy.name.clone(), sig);
    thy.in_file = String::new();
    // HS sets `_thyIsSapic = True` only for EXACTLY ONE top-level
    // process: `translate` matches on `theoryProcesses th`
    // (= `[i | ProcessItem i <- ...]`, only top-level ProcessItems,
    // not ProcessDefItems), reaching the `True` assignment solely in
    // the single-process `[p]` branch; `[]` leaves the default False
    // and `>=2` throws MoreThanOneProcess (Sapic.hs:48,85,87). Mirror
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
    Ok(thy)
}

fn elaborate_items(items: &[p::TheoryItem], out: &mut Theory) -> Result<(), ElabError> {
    // Signature-conflict rules (HS `extendSig` / `function`,
    // Theory/Text/Parser/Signature.hs:102-135, 200-222) are enforced at
    // parse time (`Parser::enable_builtin` / `Parser::function_decl`) — the
    // single point where theories are ingested — so the declarations
    // reaching here are conflict-free and the arms below only BUILD the
    // signature.
    for item in items {
        match item {
            p::TheoryItem::Builtins(names) => {
                let mut s = out.signature.maude_sig.clone();
                for name in names {
                    if let Some(sig) = builtin_sig(name) {
                        s = s.merge(sig);
                    }
                    // HS `builtinsNames` (Theory/Text/Parser/Signature.hs:78-83)
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
                    // builtinsNames in Theory/Text/Parser/Signature.hs:57-74, see line 60),
                    // and `merge` ORs `enable_dh`, so no explicit force is
                    // needed here.  `diff` is a header/CLI flag handled via
                    // `enable_diff_maude_sig`, never a `builtins:` entry.
                    out.items.push(TheoryItem::Translation(
                        TranslationElement::SignatureBuiltin(name.clone()),
                    ));
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
                    // (Theory/Text/Parser/Signature.hs:232-234).  Match
                    // that failure behaviour rather than silently dropping.
                    let (Some(l), Some(r)) = (term_to_lnterm(&eq.lhs), term_to_lnterm(&eq.rhs))
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
                out.signature.maude_sig = s.refresh();
            }
            p::TheoryItem::Macros(macros) => {
                let mut ms = Vec::new();
                for m in macros {
                    let args: Vec<LVar> = m.args.iter().map(varspec_to_lvar).collect();
                    // HS `macro` parses the body with `msetterm False llit`
                    // (Macro.hs:41), which has no pattern-match (`=t`)
                    // production, so a body that converts to a `PatMatch`
                    // here would be a hard parse failure in HS — and
                    // `addMacroSym` (Macro.hs:48) always runs for any parsed
                    // macro.  Returning an error therefore matches HS's
                    // parse-fail semantics: silently skipping would drop both
                    // the `LNMacro` push and the fun-sym registration.
                    // `term_to_lnterm` returns None only on `PatMatch`, which
                    // the surface macro parser never places in a body.
                    let body = match term_to_lnterm(&m.body) {
                        Some(t) => t,
                        None => {
                            return Err(ElabError {
                                message: format!("could not elaborate macro body for `{}`", m.name),
                            });
                        }
                    };
                    // Register macro fun-sym in MaudeSig — mirrors HS
                    // `addMacroSym (op,(k,Private,Destructor))`
                    // (Theory/Text/Parser/Macro.hs:29-49, see line 48) and
                    // `macroToFunSym` (Term/Macro.hs:29-30, see line 30).  After parser-
                    // AST macro expansion (run in `elaborate()` above)
                    // call sites no longer reference the macro name, but
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
                    ms.push(LNMacro {
                        name: m.name.clone(),
                        args,
                        body,
                    });
                }
                if !ms.is_empty() {
                    out.items.push(TheoryItem::Macros(ms));
                }
            }
            p::TheoryItem::Predicates(_predicates) => {
                // Predicates render via the PARSER-AST path
                // (`render_parsed_item` → HS `prettyPredicate`,
                // pretty_theory.rs) since the pretty-printer iterates the
                // parser theory, not this elaborated one.  Their `_restrict`
                // / lemma / restriction USES are already inlined upstream:
                // `predicate_expand::expand_theory_formulas` (called below)
                // substitutes predicate atoms in lemmas/restrictions, and
                // `rule_restriction::lift_rule_restrictions` (run in run.rs
                // right after parse, mirroring HS `liftedAddProtoRule`)
                // expands them inside `_restrict` formulas.  Building a typed
                // `theory::Predicate` here would need a parser-Formula →
                // LNFormula converter that nothing consumes (the typed
                // predicate item is read nowhere), so we do not synthesise
                // dead state — HS keeps a `PredicateItem` only to feed its
                // own closed-theory renderer, a role the RS parser-AST
                // renderer already fills.
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
            p::TheoryItem::Heuristic(h) => {
                out.heuristic.push(h.clone());
            }
            p::TheoryItem::Tactic(t) => {
                out.tactic
                    .push(crate::tactic::Tactic::parse(&t.name, &t.raw));
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                let or = OpenRestriction::new(r.name.clone(), r.formula.clone());
                out.items.push(TheoryItem::Restriction(or));
            }
            p::TheoryItem::Rule(r) | p::TheoryItem::IntrRule(r) => {
                let elab = rule_to_proto_rule_e(r)?;
                out.items.push(TheoryItem::Rule(OpenProtoRule::new(elab)));
            }
            p::TheoryItem::Lemma(l) => {
                let lem: Lemma = Lemma {
                    name: l.name.clone(),
                    modulo: l.modulo.clone(),
                    attributes: l.attributes.iter().map(elaborate_lemma_attr).collect(),
                    trace_quantifier: match l.trace_quantifier {
                        p::TraceQuantifier::AllTraces => TraceQuantifier::AllTraces,
                        p::TraceQuantifier::ExistsTrace => TraceQuantifier::ExistsTrace,
                    },
                    formula: l.formula.clone(),
                    proof: ProofSkeleton {
                        raw: l.proof.as_ref().map(|p| p.raw.clone()).unwrap_or_default(),
                        tree: l.proof.as_ref().and_then(|p| p.tree.clone()),
                    },
                    plaintext: l.plaintext.clone(),
                };
                out.items.push(TheoryItem::Lemma(lem));
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
                    formula: a.formula.clone(),
                    case_test_idents: a.case_test_idents.clone(),
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::AccLemma(acc)));
            }
            p::TheoryItem::CaseTest(c) => {
                let ct = CaseTest {
                    name: c.name.clone(),
                    formula: c.formula.clone(),
                };
                out.items
                    .push(TheoryItem::Translation(TranslationElement::CaseTest(ct)));
            }
            p::TheoryItem::ProcessDef(_)
            | p::TheoryItem::TopLevelProcess(_)
            | p::TheoryItem::EquivLemma(_, _)
            | p::TheoryItem::DiffEquivLemma(_) => {
                // Process/equiv items are intentionally not lowered here.
                // SAPIC translation is a dedicated pass
                // (`tamarin_sapic::apply::apply_sapic`) that consumes the
                // parser AST directly and injects the generated MSR rules
                // into the elaborated theory, so this arm deliberately
                // drops them.
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
/// (`Theory/Text/Parser/Rule.hs:95-96`) and the per-attribute `ruleAttribute`
/// parser (`Rule.hs:68-93`):
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
/// `fold` combines via the `RuleAttributes` `Semigroup` (Rule.hs:370-384):
/// later duplicates win on the `Option` fields (`preferRight`), bools `||`.
///
/// This restores the SAPIC display attributes (role / color / issapicrule) onto
/// the re-elaborated proving rules — HS's `toRule` bakes them straight into the
/// `ProtoRuleE`, but the RS pipeline round-trips SAPIC rules through the parser
/// AST (`apply_sapic`'s `proto_rule_to_parsed`) and re-elaborates the parser theory
/// for proving (`prove.rs`), so they must be re-read here.  Display-only: no
/// solver / `--prove`-text path reads these fields (only the web graph renderer
/// does), so populating them is `--prove`-inert.
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

fn rule_to_proto_rule_e(r: &p::Rule) -> Result<ProtoRuleE, ElabError> {
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&r.name)),
        attributes: rule_attributes_from_parser(&r.attributes),
        restrictions: Vec::new(),
    };
    // Desugar let-bindings before fact conversion: each `let x = t in ...`
    // binding substitutes `x` with `t` in the rule body.
    let r_owned: p::Rule;
    let r_eff = if r.let_block.is_empty() {
        r
    } else {
        r_owned = apply_let_block(r);
        &r_owned
    };
    let prems = r_eff
        .premises
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let acts = r_eff
        .actions
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let concs = r_eff
        .conclusions
        .iter()
        .map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let new_vars = compute_new_vars(&prems, &concs, &acts);

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Desugar a rule's `let x_1 = t_1 ... x_n = t_n in body` block by
/// substituting each binding's RHS for occurrences of the LHS in the
/// body (premises, actions, conclusions, embedded restrictions).
///
/// HS `letBlock` (Parser/Let.hs): `toSubst = foldr1 compose . map
/// (substFromList . return)` with `compose s1 s2` = "apply s2 first,
/// then s1" (SubstVFree.hs).  `foldr1 compose [b1..bn]` is
/// therefore equivalent to applying each binding as a SINGLETON
/// substitution sequentially in REVERSE binding order ("bottom-up
/// application semantics", Let.hs:22).  Consequences:
///   * backward references expand: binding i's RHS, once introduced
///     into the body at step i, is rewritten by the later-applied
///     steps j < i;
///   * FORWARD references survive as free variables: by the time an
///     early binding introduces a later binding's name into the body,
///     that later binding has already been applied (spdm's `cipher_in
///     = senc(message_in, resp_master_secret)` with
///     `resp_master_secret` defined 20 lines below keeps it as a free
///     Msg-var in the rule — semantically MORE GENERAL than the
///     expanded term, affecting unification and proof search).
pub fn apply_let_block(r: &p::Rule) -> p::Rule {
    let mut out = r.clone();
    let bindings = std::mem::take(&mut out.let_block);

    for b in bindings.iter().rev() {
        for f in &mut out.premises {
            subst_fact_in_place(f, &b.var, &b.value);
        }
        for f in &mut out.actions {
            subst_fact_in_place(f, &b.var, &b.value);
        }
        for f in &mut out.conclusions {
            subst_fact_in_place(f, &b.var, &b.value);
        }
        for phi in &mut out.embedded_restrictions {
            subst_formula_in_place(phi, &b.var, &b.value);
        }
    }
    out
}

fn subst_term(t: &p::Term, key: &p::Term, val: &p::Term) -> p::Term {
    if t == key {
        return val.clone();
    }
    match t {
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| subst_term(a, key, val)).collect(),
        ),
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::Pair(args) => {
            p::Term::Pair(args.iter().map(|a| subst_term(a, key, val)).collect())
        }
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::PatMatch(a) => p::Term::PatMatch(Box::new(subst_term(a, key, val))),
        // Atoms and literals: no recursion.
        p::Term::Var(_)
        | p::Term::PubLit(_)
        | p::Term::FreshLit(_)
        | p::Term::NatLit(_)
        | p::Term::Number(_)
        | p::Term::NumberOne
        | p::Term::NatOne
        | p::Term::DhNeutral => t.clone(),
    }
}

fn subst_fact_in_place(f: &mut p::Fact, key: &p::Term, val: &p::Term) {
    for a in &mut f.args {
        *a = subst_term(a, key, val);
    }
}

fn subst_formula_in_place(phi: &mut p::Formula, key: &p::Term, val: &p::Term) {
    use p::Formula::*;
    match phi {
        False | True => {}
        Atom(a) => subst_atom_in_place(a, key, val),
        Not(p) => subst_formula_in_place(p, key, val),
        And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
            subst_formula_in_place(a, key, val);
            subst_formula_in_place(b, key, val);
        }
        Forall(_, body) | Exists(_, body) => {
            subst_formula_in_place(body, key, val);
        }
    }
}

fn subst_atom_in_place(a: &mut p::Atom, key: &p::Term, val: &p::Term) {
    use p::Atom::*;
    match a {
        Eq(x, y) | Less(x, y) | LessMset(x, y) | Subterm(x, y) => {
            *x = subst_term(x, key, val);
            *y = subst_term(y, key, val);
        }
        Action(f, t) => {
            subst_fact_in_place(f, key, val);
            *t = subst_term(t, key, val);
        }
        Last(t) => {
            *t = subst_term(t, key, val);
        }
        Pred(f) => subst_fact_in_place(f, key, val),
    }
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
fn fact_tag_of(f: &p::Fact) -> crate::fact::FactTag {
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
fn copy_fact_annotations(f: &p::Fact) -> BTreeSet<crate::fact::FactAnnotation> {
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

pub fn fact_to_lnfact(f: &p::Fact) -> Result<crate::fact::LNFact, ElabError> {
    use crate::fact::Fact;
    let tag = fact_tag_of(f);
    let terms: Result<Vec<_>, _> = f
        .args
        .iter()
        .map(|t| {
            term_to_lnterm(t).ok_or_else(|| ElabError {
                message: format!("could not elaborate term in fact `{}`", f.name),
            })
        })
        .collect();
    Ok(Fact::new(tag, terms?).with_annotations(copy_fact_annotations(f)))
}

fn compute_new_vars(
    prems: &[crate::fact::LNFact],
    concs: &[crate::fact::LNFact],
    acts: &[crate::fact::LNFact],
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in f.terms.iter() {
            collect_vars(t, &mut prem_vars);
        }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs.iter().chain(acts) {
        for t in f.terms.iter() {
            let mut here = BTreeSet::new();
            collect_vars(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) {
                    new_set.insert(v);
                }
            }
        }
    }
    new_set
        .into_iter()
        .map(|v| Term::Lit(Lit::Var(v)))
        .collect()
}

fn collect_vars(t: &tamarin_term::lterm::LNTerm, out: &mut BTreeSet<LVar>) {
    match t {
        Term::Lit(Lit::Var(v)) => {
            out.insert(*v);
        }
        Term::Lit(_) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                collect_vars(a, out);
            }
        }
    }
}

// =============================================================================
// Term conversion: parser::Term → LNTerm
// =============================================================================

fn sort_of(s: &p::SortHint) -> LSort {
    match s {
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => LSort::Fresh,
        p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => LSort::Pub,
        p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => LSort::Node,
        p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => LSort::Nat,
        p::SortHint::Msg | p::SortHint::Suffix(p::SuffixSort::Msg) | p::SortHint::Untagged => {
            LSort::Msg
        }
    }
}

/// A parse-time variable occurrence as the solver's `LVar`: the surface sort
/// hint resolved through [`sort_of`], name and index carried over.  The
/// SAPIC-typed variant wraps this in a `SapicLVar` with the `:type`
/// annotation; the `VarSpec.typ` field has no `LVar` counterpart and is
/// dropped here.
pub(crate) fn varspec_to_lvar(v: &p::VarSpec) -> LVar {
    LVar::new(&v.name, sort_of(&v.sort), v.idx)
}

/// Convert an `LNTerm` back to a parser-AST term. Used when we
/// need to translate Maude-produced substitutions back into the
/// parser-AST world (e.g. for `insert_implied_formulas`).
pub fn lnterm_to_term(t: &tamarin_term::lterm::LNTerm) -> p::Term {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::lterm::LSort;
    use tamarin_term::vterm::Lit;
    match t {
        tamarin_term::term::Term::Lit(Lit::Var(v)) => {
            let sort = match v.sort {
                LSort::Msg => p::SortHint::Msg,
                LSort::Pub => p::SortHint::Pub,
                LSort::Fresh => p::SortHint::Fresh,
                LSort::Node => p::SortHint::Node,
                LSort::Nat => p::SortHint::Nat,
            };
            p::Term::Var(p::VarSpec {
                name: v.name.to_string(),
                idx: v.idx,
                sort,
                typ: None,
            })
        }
        tamarin_term::term::Term::Lit(Lit::Con(name)) => {
            // Encode as the right literal kind based on the sort hint
            // attached to the name's tag.
            match name.tag {
                tamarin_term::lterm::NameTag::Pub => p::Term::PubLit(name.id.0.to_string()),
                tamarin_term::lterm::NameTag::Fresh => p::Term::FreshLit(name.id.0.to_string()),
                tamarin_term::lterm::NameTag::Nat => p::Term::NatLit(name.id.0.to_string()),
                tamarin_term::lterm::NameTag::Node => p::Term::PubLit(name.id.0.to_string()),
                // `show (Name AbbrevName n) = show n` (LTerm.hs:240) is the
                // bare id, and a nullary `App` is the parser-AST term that
                // renders that way.
                tamarin_term::lterm::NameTag::Abbrev => {
                    p::Term::App(name.id.0.to_string(), Vec::new())
                }
            }
        }
        tamarin_term::term::Term::App(funsym, args) => {
            let parser_args: Vec<p::Term> = args.iter().map(lnterm_to_term).collect();
            match funsym {
                FunSym::NoEq(s) => {
                    let name = String::from_utf8(s.name.to_vec()).unwrap_or_default();
                    if name == "pair" && parser_args.len() == 2 {
                        // Re-pair into a flat Pair term where possible.
                        // Right-assoc: pair(a, pair(b, c)) → Pair([a, b, c]).
                        let mut flat = vec![parser_args[0].clone()];
                        match &parser_args[1] {
                            p::Term::Pair(rest) => flat.extend(rest.clone()),
                            other => flat.push(other.clone()),
                        }
                        p::Term::Pair(flat)
                    } else if name == "exp" && parser_args.len() == 2 {
                        // Round-trip the `exp` NoEq head back to parser
                        // `BinOp(Exp, ..)` (the inverse of the
                        // `p::BinOp::Exp` arm in `term_to_vterm` below).
                        // HS `viewTerm` exposes `exp(b,e)` as
                        // `FApp (NoEq s) [t1,t2] | s == expSym`, and
                        // `prettyTerm` (Term/Term.hs:272-300, see line 274) renders that arm as
                        // `ppTerm t1 <> text "^" <> ppTerm t2` — infix `b^e`,
                        // uniformly at every nesting depth (the printer is
                        // recursive).  Without this round-trip the runtime
                        // exp term reaches the formula/guard term path as a
                        // generic `App("exp", [..])`, which `term_to_doc`/
                        // `pp_term` render PREFIX `exp(b, e)` — diverging from
                        // HS for every exp nested inside a multiset/pair/
                        // equation in a guard or contradiction (e.g.
                        // DHKEA_NAXOS `eCK_key_secrecy`).  Same NoEq
                        // round-trip rationale as the AC/`em` arms above.
                        let mut iter = parser_args.into_iter();
                        let base = iter.next().unwrap();
                        let exponent = iter.next().unwrap();
                        p::Term::BinOp(p::BinOp::Exp, Box::new(base), Box::new(exponent))
                    } else {
                        p::Term::App(name, parser_args)
                    }
                }
                FunSym::Ac(ac) => {
                    // Round-trip AC heads back to parser BinOp so that a
                    // later `term_to_lnterm` call rebuilds them as the
                    // proper `FunSym::Ac` head (not as `NoEqSym("?")`).
                    // Without this, `insert_implied_formulas_pass`'s
                    // Maude-backed matcher (`match_atom_via_maude`) sees
                    // a NoEq-headed pattern against an Ac-headed
                    // subject, and AC matching fails — observed on
                    // MTI_C0::Secrecy_..._Initiator where the lemma's
                    // `AcceptedR(... exp(g, ~tid*~x.5) ...)` universal
                    // pattern arrives at the matcher as
                    // `exp(g, NoEq("?", 2, ekI, x))` and never matches
                    // the system's `exp(g, Mult(x, ekI))`.
                    // Mirrors HS's `viewTerm` round-trip via `FApp (AC m)`
                    // (Term/Term.hs: viewTerm).
                    use tamarin_term::function_symbols::AcSym;
                    // AC terms are flattened by `f_app_ac` to 2+ args.
                    // Round-trip via parser BinOp (left-fold), which
                    // term_to_lnterm later rebuilds as a flat AC App.
                    // Must fire on ALL arity>=2 AC terms: a flat 3+-arg AC
                    // term (common with multiset: `a + b + c`) must NOT fall
                    // through to the `?Union` placeholder branch, or a
                    // downstream `term_to_lnterm` re-parse rebuilds it as an
                    // opaque non-AC functor `App(NoEq("?Union"), [a,b,c])`,
                    // breaking Maude unification on multiset equations (e.g.
                    // the `1+x+z` → false simplification chain for
                    // `counters_linear_order`).
                    if parser_args.len() >= 2 {
                        let op = match ac {
                            AcSym::Mult => p::BinOp::Mult,
                            AcSym::Union => p::BinOp::Union,
                            AcSym::Xor => p::BinOp::Xor,
                            AcSym::NatPlus => p::BinOp::NatPlus,
                            // A user-declared `[AC]` symbol is infix in HS's
                            // `prettyTerm` as well (Term/Term.hs:305:
                            // `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")"
                            // ts`), so it round-trips through the same parser
                            // `BinOp` node as the builtin AC operators.
                            AcSym::AcFct(s) => p::BinOp::AcFct(tamarin_term::intern::intern_str(
                                &String::from_utf8_lossy(s.name),
                            )),
                        };
                        // Left-fold: a parser BinOp is strictly arity-2,
                        // so fold left-to-right when more than 2 args.
                        let mut iter = parser_args.into_iter();
                        let first = iter.next().unwrap();
                        let second = iter.next().unwrap();
                        let mut acc = p::Term::BinOp(op, Box::new(first), Box::new(second));
                        for next in iter {
                            acc = p::Term::BinOp(op, Box::new(acc), Box::new(next));
                        }
                        acc
                    } else if let AcSym::AcFct(s) = ac {
                        // HS `prettyTerm` renders a NULLARY user-AC symbol as
                        // its bare name (Term/Term.hs:304), and `fAppAC`
                        // collapses a one-element operand list to that operand
                        // (Term/Term/Raw.hs:118-122) — neither shape carries an
                        // infix operator, so both stay a named application.
                        p::Term::App(String::from_utf8_lossy(s.name).into_owned(), parser_args)
                    } else {
                        // Defensive: 0- or 1-arg AC term shouldn't occur
                        // (AC operators are arity-2), but emit a
                        // recognisable placeholder if it does.
                        let name = match ac {
                            AcSym::Mult => "?Mult",
                            AcSym::Union => "?Union",
                            AcSym::Xor => "?Xor",
                            AcSym::NatPlus => "?NatPlus",
                            AcSym::AcFct(_) => unreachable!("handled above"),
                        };
                        p::Term::App(name.to_string(), parser_args)
                    }
                }
                FunSym::C(c) => {
                    // HS-faithful: round-trip a C-symbol (bilinear-pairing
                    // `em`) back through the parser AST under its proper
                    // builtin name so a later `term_to_lnterm` rebuilds it
                    // as `FunSym::C(EMap)` (via the `em` arm of
                    // `term_to_vterm`).  Without this, `lnterm_to_term`
                    // emits `App("?", [a,b])` which `term_to_lnterm` rebuilds
                    // as `NoEqSym(name="?", arity=2, Public, Constructor)` —
                    // Maude rejects `tamXC?` as a bad token, returns empty
                    // for every `match in MSG` over a guard that mentions
                    // `em`, and `insert_implied_formulas_pass` silently
                    // fails to instantiate the implications.  Symptom on
                    // Scott::key_secrecy: lemma verifies in HS but RS
                    // terminates `SOLVED // trace found` (wrong verdict).
                    // Mirrors HS's `viewTerm` round-trip via `FApp (C EMap)`
                    // followed by `naryOpApp` at Theory/Text/Parser/Term.hs:87-106, see line 103.
                    use tamarin_term::function_symbols::CSym;
                    let name = match c {
                        CSym::EMap => String::from_utf8(
                            tamarin_term::function_symbols::EMAP_SYM_STRING.to_vec(),
                        )
                        .unwrap(),
                    };
                    p::Term::App(name, parser_args)
                }
                FunSym::List => {
                    let name = "?".to_string();
                    p::Term::App(name, parser_args)
                }
            }
        }
    }
}

/// AC-canonicalise a parser-AST term: for every `BinOp(op, l, r)` where op
/// is AC (Mult/Union/Xor/NatPlus, or a user-declared `[AC]` symbol),
/// flatten the chain into the full multiset, sort it (via the existing
/// `cmp_term` for GTerm — we convert through GTerm transiently), then
/// re-fold right-leaning so the canonical form matches HS's flat-sorted
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
/// two arguments (Raw.hs:132-133).  Mirror that here so the parser-AST
/// display path matches HS — `em` args from let-block desugaring may
/// arrive in source order, which can differ from canonical order.
/// HS site: `Theory/Text/Parser/Term.hs:87-106, see line 103` / `Term/Term/Raw.hs:132-133`:
///   `fAppC nacsym as = FAPP (C nacsym) (sort as)`
pub fn canonicalize_ac_in_pterm(t: &p::Term) -> p::Term {
    with_user_fun_sets(|funs| canonicalize_ac_in_pterm_with(t, funs))
}

/// [`canonicalize_ac_in_pterm`] against an already-snapshotted bundle: the
/// user-`[AC]` name set is read from `funs`, so a whole term tree — and, via
/// the fact / atom / formula wrappers below, a whole item — costs one
/// thread-local access instead of one per `App` node.
fn canonicalize_ac_in_pterm_with(t: &p::Term, funs: &CollectedUserFuns) -> p::Term {
    use p::BinOp;
    fn is_ac(op: BinOp) -> bool {
        matches!(
            op,
            BinOp::Mult | BinOp::Union | BinOp::Xor | BinOp::NatPlus | BinOp::AcFct(_)
        )
    }
    fn flatten(op: BinOp, t: &p::Term, out: &mut Vec<p::Term>) {
        match t {
            p::Term::BinOp(inner, l, r) if *inner == op => {
                flatten(op, l, out);
                flatten(op, r, out);
            }
            _ => out.push(t.clone()),
        }
    }
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
    fn cmp_pterm(a: &p::Term, b: &p::Term) -> std::cmp::Ordering {
        // Convert to GTerm transiently for the canonical `cmp_term`
        // ordering.  GTerm and p::Term are structurally identical for
        // Free-only inputs, so the comparison is faithful.
        let ga = crate::guarded_types::term_to_gterm_free(a);
        let gb = crate::guarded_types::term_to_gterm_free(b);
        crate::guarded::cmp_term(&ga, &gb)
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
        // HS `fAppC EMap [a,b] = FAPP (C EMap) (sort [a,b])` (Raw.hs:132-133).
        p::Term::App(n, args) if n == "em" && args.len() == 2 => {
            let a2 = canonicalize_ac_in_pterm_with(&args[0], funs);
            let b2 = canonicalize_ac_in_pterm_with(&args[1], funs);
            let (first, second) = if cmp_pterm(&a2, &b2) != std::cmp::Ordering::Greater {
                (a2, b2)
            } else {
                (b2, a2)
            };
            p::Term::App(n.clone(), vec![first, second])
        }
        // A user-declared `[AC]` symbol written in PREFIX form — when no
        // `NoEq` symbol shares the name (`lookupArity`'s NoEq-first lookup,
        // see [`CollectedUserFuns::prefix_resolves_to_user_ac`]).  HS's
        // `naryOpApp` builds `fAppAC (ACfct …) ts` for it whatever the
        // written arity (Theory/Text/Parser/Term.hs:88-105), so the operands
        // are flattened and sorted into the same AC node the infix spelling
        // yields — and `prettyTerm` then renders that node infix
        // (Term/Term.hs:305).
        p::Term::App(n, args) if !args.is_empty() && funs.prefix_resolves_to_user_ac(n) => {
            let op = BinOp::AcFct(tamarin_term::intern::intern_str(n));
            let mut flat: Vec<p::Term> = Vec::new();
            for a in args {
                flatten(op, &canonicalize_ac_in_pterm_with(a, funs), &mut flat);
            }
            sort_and_fold(op, flat)
        }
        // `exp(a, b)` written prefix, resolving to the DH exponentiation
        // symbol ([`CollectedUserFuns::prefix_exp_is_dh_exp`]): surface the
        // same `BinOp::Exp` node the `^` spelling parses to, so the printers
        // render HS `prettyTerm`'s `t1^t2` (Term/Term.hs:310).
        p::Term::App(n, args) if n == "exp" && args.len() == 2 && funs.prefix_exp_is_dh_exp() => {
            p::Term::BinOp(
                BinOp::Exp,
                Box::new(canonicalize_ac_in_pterm_with(&args[0], funs)),
                Box::new(canonicalize_ac_in_pterm_with(&args[1], funs)),
            )
        }
        p::Term::App(n, args) => p::Term::App(
            n.clone(),
            args.iter()
                .map(|a| canonicalize_ac_in_pterm_with(a, funs))
                .collect(),
        ),
        // `op{a}b` resolves through the same `lookupArity` NoEq-first lookup
        // (HS `binaryAlgApp`, Theory/Text/Parser/Term.hs:108-121), so a name
        // it resolves to the `[AC]` symbol builds the flattened, sorted AC
        // node `prettyTerm` renders infix — `f{'a'}'b'` prints `('a' f 'b')`.
        p::Term::AlgApp(n, a, b) if funs.prefix_resolves_to_user_ac(n) => {
            let op = BinOp::AcFct(tamarin_term::intern::intern_str(n));
            let mut flat: Vec<p::Term> = Vec::new();
            flatten(op, &canonicalize_ac_in_pterm_with(a, funs), &mut flat);
            flatten(op, &canonicalize_ac_in_pterm_with(b, funs), &mut flat);
            sort_and_fold(op, flat)
        }
        p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
            n.clone(),
            Box::new(canonicalize_ac_in_pterm_with(a, funs)),
            Box::new(canonicalize_ac_in_pterm_with(b, funs)),
        ),
        p::Term::Pair(items) => p::Term::Pair(
            items
                .iter()
                .map(|i| canonicalize_ac_in_pterm_with(i, funs))
                .collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(canonicalize_ac_in_pterm_with(a, funs)),
            Box::new(canonicalize_ac_in_pterm_with(b, funs)),
        ),
        p::Term::PatMatch(inner) => {
            p::Term::PatMatch(Box::new(canonicalize_ac_in_pterm_with(inner, funs)))
        }
        p::Term::BinOp(op, l, r) => {
            let l2 = canonicalize_ac_in_pterm_with(l, funs);
            let r2 = canonicalize_ac_in_pterm_with(r, funs);
            if !is_ac(*op) {
                return p::Term::BinOp(*op, Box::new(l2), Box::new(r2));
            }
            // Flatten the WHOLE AC chain rooted at this BinOp, then sort.
            let mut flat: Vec<p::Term> = Vec::new();
            flatten(*op, &l2, &mut flat);
            flatten(*op, &r2, &mut flat);
            sort_and_fold(*op, flat)
        }
    }
}

/// Apply `canonicalize_ac_in_pterm` to every term in a fact.
pub fn canonicalize_ac_in_pfact(f: &p::Fact) -> p::Fact {
    with_user_fun_sets(|funs| {
        crate::macro_expand::map_fact_terms(f, &|t| canonicalize_ac_in_pterm_with(t, funs))
    })
}

/// Apply `canonicalize_ac_in_pterm` to every term in a parser-AST atom.
pub fn canonicalize_ac_in_atom(a: &p::Atom) -> p::Atom {
    with_user_fun_sets(|funs| {
        crate::macro_expand::map_atom_terms(a, &|t| canonicalize_ac_in_pterm_with(t, funs))
    })
}

/// Apply `canonicalize_ac_in_pterm` to every term in a parser-AST formula.
///
/// HS-faithful: HS sorts AC arguments at parse time when building LNTerm via
/// `fAppAC` (Term/Term/Raw.hs:118-122) over the *free* logical variables,
/// using `Ord LVar` = (idx, sort, name) (LTerm.hs:522-524).  Our parser keeps
/// `BinOp` trees in written order; this walk re-establishes the canonical AC
/// order on the free-variable parser AST so the subsequent guarded conversion
/// (Free→Bound abstraction) preserves exactly what HS would have produced.
pub fn canonicalize_ac_in_formula(f: &p::Formula) -> p::Formula {
    with_user_fun_sets(|funs| {
        crate::macro_expand::map_formula_terms(f, &|t| canonicalize_ac_in_pterm_with(t, funs))
    })
}

/// Names of arity-1 NoEq function symbols in the (closed-theory) signature.
/// Mirrors HS `lookupArity` reading the parser-state signature for
/// `naryOpApp`'s `k == 1` tuple-folding (Theory/Text/Parser/Term.hs:58-93).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn arity1_noeq_names(
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> std::collections::HashSet<String> {
    sig.no_eq_fun_syms()
        .iter()
        .filter(|s| s.arity == 1)
        .map(|s| String::from_utf8_lossy(s.name).to_string())
        .collect()
}

/// Re-fold surplus arguments of an arity-1 function application into a
/// single right-associative pair, mirroring HS `naryOpApp` for `k == 1`
/// (Theory/Text/Parser/Term.hs:94-96):
///   `ts <- parens $ if k == 1 then return <$> tupleterm ... else commaSep ...`
/// where `tupleterm = chainr1 (...) (fAppPair <$ comma)`.  So for an arity-1
/// symbol `f`, the surface `f(a, b, c)` parses to `f(<a, b, c>)` — a single
/// argument which is the right-associative pair `<a, b, c>`.
///
/// HS performs this fold at PARSE time, so every downstream consumer (the
/// lemma/restriction pretty-printer, the guarded-formula conversion, and the
/// "Formula terms" wellformedness check) sees the already-folded form.  RS's
/// term parser performs the same fold (its `lookup_arity`-resolved `k == 1`
/// branch parses one tuple), so on theory ASTs this pass is a no-op; it is
/// kept as belt-and-braces for ASTs from other producers (e.g. the parser's
/// structural mode, which is arity-unaware and keeps `App("f", [a, b, c])`).
/// Historically this was the shared root behind the alethea `h(<a,b>)`
/// formula-rendering divergence AND the spurious "reducible function symbols
/// are disallowed" wf warning (a unary `h` applied with surplus args looks
/// to the wf check like an unknown reducible `h/n`).
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn rewrite_arity1_term(t: &p::Term, arity1: &std::collections::HashSet<String>) -> p::Term {
    use p::Term::*;
    match t {
        App(name, args) => {
            let new_args: Vec<p::Term> = args
                .iter()
                .map(|a| rewrite_arity1_term(a, arity1))
                .collect();
            if arity1.contains(name) && new_args.len() > 1 {
                App(name.clone(), vec![Pair(new_args)])
            } else {
                App(name.clone(), new_args)
            }
        }
        Pair(items) => Pair(
            items
                .iter()
                .map(|i| rewrite_arity1_term(i, arity1))
                .collect(),
        ),
        AlgApp(name, l, r) => AlgApp(
            name.clone(),
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        Diff(l, r) => Diff(
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        BinOp(op, l, r) => BinOp(
            *op,
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        PatMatch(inner) => PatMatch(Box::new(rewrite_arity1_term(inner, arity1))),
        other => other.clone(),
    }
}

/// Apply [`rewrite_arity1_term`] to every term in a parser-AST fact.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn rewrite_arity1_fact(fa: &p::Fact, arity1: &std::collections::HashSet<String>) -> p::Fact {
    crate::macro_expand::map_fact_terms(fa, &|t| rewrite_arity1_term(t, arity1))
}

/// Apply [`rewrite_arity1_term`] to every term in a parser-AST atom.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn rewrite_arity1_atom(a: &p::Atom, arity1: &std::collections::HashSet<String>) -> p::Atom {
    crate::macro_expand::map_atom_terms(a, &|t| rewrite_arity1_term(t, arity1))
}

/// Apply [`rewrite_arity1_term`] to every term in a parser-AST formula.
/// See [`rewrite_arity1_term`] for the HS-faithfulness rationale.
// arity-1 no-eq function-name set; membership-only (.contains), never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
pub fn rewrite_arity1_formula(
    f: &p::Formula,
    arity1: &std::collections::HashSet<String>,
) -> p::Formula {
    crate::macro_expand::map_formula_terms(f, &|t| rewrite_arity1_term(t, arity1))
}

/// Right-fold a non-empty term list into a right-associative `pair(..)` chain:
/// `[a, b, c]` → `pair(a, pair(b, c))`; `None` on an empty list.  Mirrors HS's
/// `tupleterm`'s `chainr1 ... (curry fAppPair)` (Theory/Text/Parser/Term.hs:187-188)
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

/// Shared conversion core for [`term_to_lnterm`] and [`term_to_sapic_term`].
///
/// Every arm except the `Var` case is byte-identical between the LNTerm and
/// SAPIC term universes (same function-symbol / arity-1-fold / `em` / pair
/// logic).  `mk_var` reproduces the per-universe `Var` behaviour: LNTerm
/// builds a plain `LVar` literal (with `nullaryApp` 0-arity recovery); SAPIC
/// builds a typed `SapicLVar` literal (same recovery, additionally gated on an
/// un-annotated variable).  Recursion is threaded back through `term_to_vterm`
/// so the whole tree is built in one universe.  `funs` carries the
/// user-declared function-name sets, snapshotted once at the entry point by
/// [`with_user_fun_sets`] and handed to every node (`mk_var` included).
fn term_to_vterm<V, F>(t: &p::Term, mk_var: &F, funs: &CollectedUserFuns) -> Option<VTerm<Name, V>>
where
    V: Clone + Ord,
    F: Fn(&p::VarSpec, &CollectedUserFuns) -> Option<VTerm<Name, V>>,
{
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::term::{f_app_ac, f_app_acfct};

    match t {
        p::Term::Var(v) => mk_var(v, funs),
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
            // HS `fAppOne = fAppNoEq oneSym []` (Term/Term.hs:126-127, see line 127); the
            // `"1"` keyword in the term parser dispatches to this
            // (Theory/Text/Parser/Term.hs:123-148, see line 134).  Mirror exactly — emit
            // a 0-arity NoEq application of `oneSym`, NOT a public
            // constant.  Treating it as `Lit::Con(Pub,"1")` causes
            // source-case enumeration to mismatch HS's `c_one` rule.
            Some(f_app_no_eq(
                tamarin_term::function_symbols::one_sym(),
                vec![],
            ))
        }
        p::Term::DhNeutral => {
            // HS `fAppDHNeutral = fAppNoEq dhNeutralSym []` (Term/Term.hs:129-130, see line 130);
            // dispatched by `symbol "DH_neutral" *> pure fAppDHNeutral`
            // (Theory/Text/Parser/Term.hs:123-148, see line 127).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::dh_neutral_sym(),
                vec![],
            ))
        }
        p::Term::NatOne => {
            // HS `fAppNatOne = fAppNoEq natOneSym []` (Term/Term.hs); the
            // `1:nat` / `%1` keywords dispatch to this
            // (Theory/Text/Parser/Term.hs:128-129).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::nat_one_sym(),
                vec![],
            ))
        }
        p::Term::Number(_) => {
            // Defensive: `p::Term::Number` cannot arise from parsed
            // input. HS has no bare-integer (>=2) term — the parser
            // recognizes only `1`/`%1`/`DH_neutral` (Term.hs), and the
            // Rust parser likewise never constructs `Term::Number`. This
            // variant only appears via GTerm round-trip converters, so
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
            // Builtin arity-1 NoEq symbols whose surplus comma-separated
            // args must be folded into a single tuple, mirroring HS's
            // signature-driven `naryOpApp` (`k == 1`) over `noEqFunSyms`
            // (Theory/Text/Parser/Term.hs:94-96).  In addition to the
            // common ones (h / fst / snd / inv / pk), this covers the
            // less-common builtin unary symbols: `getMessage`
            // (revealing-signing) and `get_rep` / `report`
            // (locations-report) — see Term/Builtin/Signature.hs:38-40.
            // Other multi-arg builtins (senc/aenc/sign/...) are
            // genuinely multi-arg and are excluded.
            let unary_builtin = matches!(
                name.as_str(),
                "h" | "fst" | "snd" | "inv" | "pk" | "getMessage" | "get_rep" | "report"
            ) || funs.is_user_unary_fun(name.as_str());
            let new_args: Option<Vec<_>> = args
                .iter()
                .map(|a| term_to_vterm(a, mk_var, funs))
                .collect();
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
            if name == "em" && new_args.len() == 2 && funs.is_bp_enabled() {
                let mut it = new_args.into_iter();
                let a = it.next().unwrap();
                let b = it.next().unwrap();
                return Some(tamarin_term::builtin::emap(a, b));
            }
            // #883 `naryOpApp` IsAC case: a user-declared `[AC]` symbol
            // lowers to an AC application (n-ary — the arity check applies
            // only to non-AC symbols) — unless a `NoEq` symbol shares the
            // name, in which case `lookupArity`'s NoEq-first lookup resolves
            // the prefix spelling to that symbol instead
            // ([`CollectedUserFuns::prefix_resolves_to_user_ac`]).  The infix
            // spelling is the `BinOp::AcFct` arm below.
            if funs.prefix_resolves_to_user_ac(name.as_str()) {
                return Some(f_app_acfct(funs.user_ac_fct_sym(name), new_args));
            }
            let sym = funs.user_no_eq_sym(name, new_args.len());
            Some(f_app_no_eq(sym, new_args))
        }
        p::Term::Pair(items) => {
            let new_items: Option<Vec<_>> = items
                .iter()
                .map(|i| term_to_vterm(i, mk_var, funs))
                .collect();
            // Right-associative pair: <a, b, c> = pair(a, pair(b, c)).
            right_nest_pair(new_items?)
        }
        p::Term::AlgApp(name, a, b) => {
            // `f{a}b` desugars to `f(a, b)` semantically; users typically
            // use this for senc/aenc/sign/mac.
            let aa = term_to_vterm(a, mk_var, funs)?;
            let bb = term_to_vterm(b, mk_var, funs)?;
            // Haskell `binaryAlgApp` also reads `(k,priv,cnstr)` from the
            // signature via `lookupArity` (Theory/Text/Parser/Term.hs:108-121, see line 114),
            // so thread user privacy/constructability here too.
            // #883: `[AC]` symbols build an AC application here as well —
            // under the same NoEq-first name resolution as the prefix
            // spelling ([`CollectedUserFuns::prefix_resolves_to_user_ac`]).
            if funs.prefix_resolves_to_user_ac(name.as_str()) {
                return Some(f_app_acfct(funs.user_ac_fct_sym(name), vec![aa, bb]));
            }
            let sym = funs.user_no_eq_sym(name, 2);
            Some(f_app_no_eq(sym, vec![aa, bb]))
        }
        p::Term::Diff(a, b) => {
            let aa = term_to_vterm(a, mk_var, funs)?;
            let bb = term_to_vterm(b, mk_var, funs)?;
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
            let aa = term_to_vterm(a, mk_var, funs)?;
            let bb = term_to_vterm(b, mk_var, funs)?;
            match op {
                p::BinOp::Mult => Some(f_app_ac(AcSym::Mult, vec![aa, bb])),
                p::BinOp::Union => Some(f_app_ac(AcSym::Union, vec![aa, bb])),
                p::BinOp::Xor => Some(f_app_ac(AcSym::Xor, vec![aa, bb])),
                p::BinOp::NatPlus => Some(f_app_ac(AcSym::NatPlus, vec![aa, bb])),
                // A user-declared `[AC]` symbol applied infix — ALWAYS the AC
                // application (HS `acterm` builds `fAppACfct` straight from
                // `stACFunSyms`, Theory/Text/Parser/Term.hs:163-168), even
                // when a `NoEq` symbol shares the name and claims the prefix
                // spelling.  It reads the same user-function signature for
                // the symbol's privacy / constructability / NDC flags.
                p::BinOp::AcFct(name) => {
                    Some(f_app_acfct(funs.user_ac_fct_sym(name), vec![aa, bb]))
                }
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

pub fn term_to_lnterm(t: &p::Term) -> Option<tamarin_term::lterm::LNTerm> {
    // LNTerm `Var` case: a bare identifier in surface syntax may denote a
    // 0-arity function symbol (e.g. `true` when `builtins: signing` is
    // enabled).  Haskell's `term` parser disambiguates this via `nullaryApp`
    // against the maudeSig in parser state; our parser doesn't, so the lexer
    // leaves it as `Var{name, sort: Untagged}`.  We recover the constant
    // here.  Only fires for `Untagged` sort + idx 0 — a user can still bind a
    // Msg-sort var named `true` if they explicitly annotate it (e.g.
    // `true:msg`), and the parser would emit `Untagged` only for the bare
    // form anyway.
    let mk_var =
        |v: &p::VarSpec, funs: &CollectedUserFuns| -> Option<tamarin_term::lterm::LNTerm> {
            if matches!(v.sort, p::SortHint::Untagged)
                && v.idx == 0
                && funs.is_user_nullary_fun(&v.name)
            {
                let sym = NoEqSym::new(
                    v.name.as_bytes().to_vec(),
                    0,
                    funs.user_fun_privacy(&v.name),
                    Constructability::Constructor,
                )
                .with_ndc(funs.user_fun_ndc(&v.name));
                return Some(f_app_no_eq(sym, vec![]));
            }
            Some(Term::Lit(Lit::Var(varspec_to_lvar(v))))
        };
    with_user_fun_sets(|funs| term_to_vterm(t, &mk_var, funs))
}

// =============================================================================
// Term conversion: parser::Term → SapicTerm (VTerm<Name, SapicLVar>)
//
// Parallel to `term_to_lnterm`, but the literal/variable case preserves the
// SAPIC type annotation (`VarSpec.typ`) into `SapicLVar.stype`.  Mirrors HS's
// SAPIC term parser (`Theory.Text.Parser.Sapic.sapicterm = msetterm False
// ltypedlit`, Sapic.hs:56), which builds `Term (Lit Name SapicLVar)` keeping
// the `name:type` annotation on each typed variable.  Reuses the SAME
// function-symbol / arity-1-fold / em / pair logic as `term_to_lnterm` (via
// `term_to_vterm`) so the resulting term universe matches the protocol-rule
// path exactly.
// =============================================================================

/// `parser::Term` → `SapicTerm`.  Returns `None` on a `PatMatch` term (the
/// surface SAPIC action parser never places one in a plain term position).
pub fn term_to_sapic_term(t: &p::Term) -> Option<crate::sapic::SapicTerm> {
    use crate::sapic::SapicLVar;

    // SAPIC `Var` case: a bare untagged idx-0 identifier may be a 0-arity NoEq
    // fun symbol (mirrors `term_to_lnterm`'s `nullaryApp` recovery, additionally
    // gated on an un-annotated variable); otherwise a typed `SapicLVar`.
    let mk_var = |v: &p::VarSpec, funs: &CollectedUserFuns| -> Option<crate::sapic::SapicTerm> {
        if matches!(v.sort, p::SortHint::Untagged)
            && v.idx == 0
            && v.typ.is_none()
            && funs.is_user_nullary_fun(&v.name)
        {
            let sym = NoEqSym::new(
                v.name.as_bytes().to_vec(),
                0,
                funs.user_fun_privacy(&v.name),
                Constructability::Constructor,
            )
            .with_ndc(funs.user_fun_ndc(&v.name));
            return Some(f_app_no_eq(sym, vec![]));
        }
        Some(Term::Lit(Lit::Var(SapicLVar::new(
            varspec_to_lvar(v),
            v.typ.clone(),
        ))))
    };
    with_user_fun_sets(|funs| term_to_vterm(t, &mk_var, funs))
}

/// `parser::Fact` → `SapicNFact<SapicLVar>` (`Fact<SapicTerm>`).  Mirrors
/// `fact_to_lnfact` but over typed SAPIC terms.  The fact tag mapping is
/// identical (`Fr`/`In`/`Out`/`KU`/`KD`/`Ded` → builtin tags, else ProtoFact).
pub fn fact_to_sapic_fact(f: &p::Fact) -> Result<crate::sapic::SapicLNFact, ElabError> {
    use crate::fact::Fact;
    let tag = fact_tag_of(f);
    let terms: Result<Vec<_>, _> = f
        .args
        .iter()
        .map(|t| {
            term_to_sapic_term(t).ok_or_else(|| ElabError {
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
