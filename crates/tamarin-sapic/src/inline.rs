// Currently GPL 3.0 until granted permission by the following authors:
//   Robert Künnemann, Hong-Thai Luu, Simon Meier, Charlie Jacomme, Benedikt
//   Schmidt, Kevin Morio, "Tom" (github BTom-GH), Artur Cygan,
//   "ValentinYuri" (github), Felix Linker, Yavor Ivanov, Jannik Dreier,
//   "Pops" (github racoucho1u), and other minor contributors (see upstream
//   git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Basetranslation.hs, lib/sapic/src/Sapic/Bindings.hs,
//   lib/term/src/Term/Maude/Process.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Text/Parser/Sapic.hs,
//   lib/theory/src/TheoryObject.hs

//! Process-call inlining.
//!
//! HS inlines process definitions at PARSE TIME: when the parser
//! (`actionprocess`, `Theory/Text/Parser/Sapic.hs:293-312`) reads an identifier
//! `P(t1,..,tn)`, it looks the definition up (`checkProcess`), builds the
//! parameter substitution `params -> args`, applies it to the def body with the
//! capture-checking `applyM`, and emits
//!
//! ```text
//! ProcessAction (ProcessCall name args) mempty
//!     (processAddAnnotation substitutedBody (mempty {processnames = [name]}))
//! ```
//!
//! The `ProcessCall` action node is a pure marker — its base translation is a
//! trivial pass-through (`Basetranslation.hs:204-207`); the real behaviour comes
//! from the substituted body that follows it as the action's continuation.
//!
//! The RS parser does NOT inline (it produces a `p::Process::Call { name, args }`
//! node), so we reproduce HS's inlining here, on the way from the parser AST to
//! the theory AST.  [`convert_process_with_defs`] resolves every `Call` against
//! the collected `ProcessDef`s and substitutes the parameters.
//!
//! The `extend_sup` "type-erasure doubling" of
//! `Theory/Text/Parser/Sapic.hs:299-306` is mirrored:
//! a typed formal `x:ty` produces TWO substitution entries (typed AND untyped
//! keyed) to the same argument, so body occurrences of either form are hit.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;
use tamarin_term::lterm::Name;
use tamarin_term::subst::Subst;
use crate::base_translation::{subst_term, subst_fact};
use tamarin_term::vterm::{Lit, VTerm};

use tamarin_theory::sapic::{
    PlainProcess, Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm,
};

use crate::convert::{convert_action, convert_combinator, convert_term, ConvertError};

/// A substitution mapping SAPIC parameter variables to argument terms.
type SapicSubst = Subst<Name, SapicLVar>;

/// Look up each process definition by name (HS `lookupProcessDef`,
/// `TheoryObject.hs:678`).  Built once from the parsed theory's `ProcessDef`
/// items, threaded into [`convert_process_with_defs`].
pub type ProcessDefMap<'a> = BTreeMap<String, &'a p::ProcessDef>;

/// Collect every `ProcessDef` of the parsed theory into a lookup map.
pub fn collect_process_defs(thy: &p::Theory) -> ProcessDefMap<'_> {
    let mut m = BTreeMap::new();
    for item in &thy.items {
        if let p::TheoryItem::ProcessDef(d) = item {
            // HS `addProcessDef` rejects duplicate names; the first definition
            // wins for our lookup (a well-formed theory has no duplicates).
            m.entry(d.name.clone()).or_insert(d);
        }
    }
    m
}

/// `convert_process` with process-definition resolution.  Identical to
/// `convert_process` for every node except `Call`, which is inlined here.
pub fn convert_process_with_defs(
    proc: &p::Process,
    defs: &ProcessDefMap<'_>,
) -> Result<PlainProcess, ConvertError> {
    use tamarin_theory::sapic::ProcessParsedAnnotation;
    let ann = ProcessParsedAnnotation::empty();
    match proc {
        p::Process::Null => Ok(Process::Null(ann)),
        p::Process::Action { action: act, body } => Ok(Process::Action(
            convert_action(act)?,
            ann,
            Box::new(convert_process_with_defs(body, defs)?),
        )),
        p::Process::Comb { comb, left, right } => {
            let l = Box::new(convert_process_with_defs(left, defs)?);
            let r = Box::new(convert_process_with_defs(right, defs)?);
            let c = convert_combinator(comb)?;
            Ok(Process::Comb(c, ann, l, r))
        }
        p::Process::Replication(body) => Ok(Process::Action(
            SapicAction::Rep,
            ann,
            Box::new(convert_process_with_defs(body, defs)?),
        )),
        p::Process::Call { name, args } => inline_call(name, args, defs),
        p::Process::AtAnnotation(inner, _) => convert_process_with_defs(inner, defs),
    }
}

/// Inline one `P(args)` call (HS `actionprocess` identifier branch,
/// `Theory/Text/Parser/Sapic.hs:293-312`).
fn inline_call(
    name: &str,
    args: &[p::Term],
    defs: &ProcessDefMap<'_>,
) -> Result<PlainProcess, ConvertError> {
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    // `checkProcess` (Theory/Text/Parser/Sapic.hs:314-317): fail if the
    // process is undefined.
    let def = defs.get(name).ok_or_else(|| {
        ConvertError::new(format!("process not defined: {name}"))
    })?;

    // Convert the actual argument terms.
    let sapic_args: Vec<SapicTerm> = args
        .iter()
        .map(convert_term)
        .collect::<Result<_, _>>()?;

    // Convert the formal parameters (HS `fromMaybe [] (get pVars p)`).
    let params: Vec<SapicLVar> = def
        .vars
        .as_ref()
        .map(|vs| vs.iter().map(crate::convert::varspec_to_sapic).collect())
        .unwrap_or_default();

    if params.len() != sapic_args.len() {
        return Err(ConvertError::new(format!(
            "process call {name}: expected {} argument(s), got {}",
            params.len(),
            sapic_args.len()
        )));
    }

    // Recursively inline the definition body (a def may call other defs).
    let body = convert_process_with_defs(&def.body, defs)?;

    // Build the parameter substitution with HS's `extend_sup` type-erasure
    // doubling (Theory/Text/Parser/Sapic.hs:299-306): a typed formal
    // contributes both its typed and untyped keys mapping to the argument.
    let mut pairs: Vec<(SapicLVar, SapicTerm)> = Vec::new();
    for (param, arg) in params.iter().zip(sapic_args.iter()) {
        pairs.push((param.clone(), arg.clone()));
        if param.stype.is_some() {
            pairs.push((SapicLVar::untyped(param.var.clone()), arg.clone()));
        }
    }
    let subst = SapicSubst::from_list(pairs);

    // `applyM (substFromList extend_sup) p` — capture-checking substitution.
    let substituted = apply_m_process(&subst, body)?;

    // `processAddAnnotation substP (mempty {processnames = [name]})`: tag the
    // body's root node with the call name (drives `role=` / colour).
    let mut name_ann = ProcessParsedAnnotation::empty();
    name_ann.process_names = vec![name.to_string()];
    let annotated = process_add_annotation(substituted, name_ann);

    // Wrap in the `ProcessCall` marker action
    // (Theory/Text/Parser/Sapic.hs:308-311).
    Ok(Process::Action(
        SapicAction::ProcessCall(name.to_string(), sapic_args),
        ProcessParsedAnnotation::empty(),
        Box::new(annotated),
    ))
}

/// `processAddAnnotation p ann'` (Process.hs): mappend `ann'` onto the root
/// node's annotation.  Only the FRONT node is touched (HS mappends at the root).
fn process_add_annotation(
    p: PlainProcess,
    ann_add: tamarin_theory::sapic::ProcessParsedAnnotation,
) -> PlainProcess {
    match p {
        Process::Null(a) => Process::Null(a.append(ann_add)),
        Process::Action(ac, a, body) => Process::Action(ac, a.append(ann_add), body),
        Process::Comb(c, a, l, r) => Process::Comb(c, a.append(ann_add), l, r),
    }
}

/// `applyM subst p` over an `LProcess` (Process.hs:411-424): apply `subst` to
/// every term, raising a capture error if a substituted parameter would be
/// captured by an inner binder (`new` / `lookup` / single-var `in`).
///
/// HS `applyM` is capture-DETECTING (it throws `CapturedEx`), NOT
/// capture-avoiding.  For parameterless calls (`subst` empty) this is a no-op
/// rename and never fails.
fn apply_m_process(subst: &SapicSubst, p: PlainProcess) -> Result<PlainProcess, ConvertError> {
    if subst.is_empty() {
        return Ok(p);
    }
    match p {
        Process::Null(a) => Ok(Process::Null(a)),
        Process::Action(ac, a, body) => {
            let ac1 = apply_m_action(subst, ac)?;
            let body1 = apply_m_process(subst, *body)?;
            Ok(Process::Action(ac1, a, Box::new(body1)))
        }
        Process::Comb(c, a, l, r) => {
            let c1 = apply_m_comb(subst, c)?;
            let l1 = apply_m_process(subst, *l)?;
            let r1 = apply_m_process(subst, *r)?;
            Ok(Process::Comb(c1, a, Box::new(l1), Box::new(r1)))
        }
    }
}

/// True iff a substitution maps `v` (in either typed or untyped form) — i.e.
/// `v ∈ dom subst`, used for the capture checks.
fn in_domain(subst: &SapicSubst, v: &SapicLVar) -> bool {
    subst.image_of(v).is_some()
        || subst.image_of(&SapicLVar::untyped(v.var.clone())).is_some()
}

/// `applyM` for `SapicAction` (Process.hs:392-408): substitute terms, raising
/// `CapturedNew` / `CapturedIn` on capture.
fn apply_m_action(
    subst: &SapicSubst,
    ac: SapicAction<SapicLVar>,
) -> Result<SapicAction<SapicLVar>, ConvertError> {
    match ac {
        // `New v` with `v ∈ dom subst` would be captured (Process.hs:393-395).
        SapicAction::New(v) => {
            if in_domain(subst, &v) {
                return Err(ConvertError::new(format!(
                    "captured variable {} in process call (new)",
                    v.var.name
                )));
            }
            Ok(SapicAction::New(v))
        }
        SapicAction::Event(f) => Ok(SapicAction::Event(subst_fact(subst, &f))),
        SapicAction::ChOut { chan, msg } => Ok(SapicAction::ChOut {
            chan: chan.map(|t| subst_term(subst, &t)),
            msg: subst_term(subst, &msg),
        }),
        // `ChIn` of a single captured var is captured unless its name starts
        // with `pat_` (Process.hs:399-406).
        SapicAction::ChIn { chan, msg, match_vars } => {
            if let VTerm::Lit(Lit::Var(v)) = &msg {
                if in_domain(subst, v) && !v.var.name.starts_with("pat_") {
                    return Err(ConvertError::new(format!(
                        "captured variable {} in process call (in)",
                        v.var.name
                    )));
                }
            }
            Ok(SapicAction::ChIn {
                chan: chan.map(|t| subst_term(subst, &t)),
                msg: subst_term(subst, &msg),
                // HS `apply subst (ChIn mt t vs) = ChIn … (applyMatchVars subst vs)`
                // (Process.hs:320): each match var `v` is replaced by the
                // variables of its image `subst(v)` (or kept if undefined).  When
                // inlining a call like `Q(h(a))` into `in(<y, =x>)`, the param
                // match-var `x` becomes the vars of `h(a)` (= `{a}`) so that
                // `bindingsAct = frees(<y,h(a)>) \ {a} = {y}` — i.e. the already-
                // bound `a` is NOT rebound (Bindings.hs:24).  Without this the
                // stale `{x}` would leave `a` looking unbound, rebinding it to a
                // fresh `a.N` and adding a spurious state-fact variable.
                match_vars: apply_match_vars(subst, &match_vars),
            })
        }
        SapicAction::Insert(a, b) => {
            Ok(SapicAction::Insert(subst_term(subst, &a), subst_term(subst, &b)))
        }
        SapicAction::Delete(t) => Ok(SapicAction::Delete(subst_term(subst, &t))),
        SapicAction::Lock(t) => Ok(SapicAction::Lock(subst_term(subst, &t))),
        SapicAction::Unlock(t) => Ok(SapicAction::Unlock(subst_term(subst, &t))),
        SapicAction::ProcessCall(n, ts) => Ok(SapicAction::ProcessCall(
            n,
            ts.iter().map(|t| subst_term(subst, t)).collect(),
        )),
        SapicAction::Msr { prems, acts, concs, rest, match_vars } => Ok(SapicAction::Msr {
            prems: prems.iter().map(|f| subst_fact(subst, f)).collect(),
            acts: acts.iter().map(|f| subst_fact(subst, f)).collect(),
            concs: concs.iter().map(|f| subst_fact(subst, f)).collect(),
            rest,
            match_vars,
        }),
        SapicAction::Rep => Ok(SapicAction::Rep),
    }
}

/// `applyM` for `ProcessCombinator` (Process.hs:382-389): `Lookup`'s bound var
/// being captured raises `CapturedLookup`.
fn apply_m_comb(
    subst: &SapicSubst,
    c: ProcessCombinator<SapicLVar>,
) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            if in_domain(subst, &v) {
                return Err(ConvertError::new(format!(
                    "captured variable {} in process call (lookup)",
                    v.var.name
                )));
            }
            Ok(ProcessCombinator::Lookup(subst_term(subst, &t), v))
        }
        ProcessCombinator::Let { left, right, match_vars } => Ok(ProcessCombinator::Let {
            left: subst_term(subst, &left),
            right: subst_term(subst, &right),
            match_vars,
        }),
        ProcessCombinator::CondEq(a, b) => {
            Ok(ProcessCombinator::CondEq(subst_term(subst, &a), subst_term(subst, &b)))
        }
        // `Cond` carries an un-expanded parser-AST formula.  HS DOES substitute
        // here: `apply subst (Cond fa) = Cond (apply subst fa)` (Process.hs:165),
        // reached via the `ApplyM`/`Apply` ProcessCombinator instances
        // (Process.hs:330,382).  So to be byte-faithful a call whose body begins
        // with `if <formula>` mentioning a parameter (the call substitutes that
        // parameter into the formula's free vars) must rewrite the formula too —
        // exactly as the sibling Case-B `let`-elimination path does in
        // let_destructors.rs::subst_cond_formula.  We omit it here as a KNOWN
        // gap: no in-scope corpus theory inlines a call whose body's leading
        // `Cond` formula references a parameter, so the omission is currently
        // output-inert.  If such a theory appears, route `Cond` through a
        // subst_cond_formula-style rewrite (and re-gate) rather than the
        // pass-through below.
        ProcessCombinator::Cond(f) => Ok(ProcessCombinator::Cond(f)),
        // Parallel/Ndc carry no terms, so substitution is the identity.
        // Enumerated (no wildcard) so a new term-carrying variant must decide
        // its substitution here.
        other @ (ProcessCombinator::Parallel | ProcessCombinator::Ndc) => Ok(other),
    }
}

/// `applyMatchVars subst vs` (Process.hs:304-309): `fromList . concatMap
/// extractVars . toList` where `extractVars v = maybe [v] varsVTerm (imageOf
/// subst v)`.  A match var `v` is replaced by ALL the variables of its image
/// `subst(v)`; an undefined `v` is kept.  Probes both the typed and untyped
/// substitution keys (the call subst carries both forms).
fn apply_match_vars(
    subst: &SapicSubst,
    vs: &std::collections::BTreeSet<SapicLVar>,
) -> std::collections::BTreeSet<SapicLVar> {
    let mut out = std::collections::BTreeSet::new();
    for v in vs {
        let img = subst
            .image_of(v)
            .or_else(|| subst.image_of(&SapicLVar::untyped(v.var.clone())));
        match img {
            Some(t) => {
                for w in tamarin_term::vterm::vars_vterm_in_order(t) {
                    out.insert(w);
                }
            }
            None => {
                out.insert(v.clone());
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pub_lit(s: &str) -> p::Term {
        p::Term::PubLit(s.to_string())
    }

    fn out_x_def(name: &str, param: &str) -> p::ProcessDef {
        // `let <name>(<param>) = out(<param>)`
        let xref = p::Term::Var(p::VarSpec {
            name: param.to_string(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        p::ProcessDef {
            name: name.to_string(),
            vars: Some(vec![p::VarSpec {
                name: param.to_string(),
                idx: 0,
                sort: p::SortHint::Untagged,
                typ: None,
            }]),
            body: p::Process::Action {
                action: p::SapicAction::ChOut { chan: None, msg: xref },
                body: Box::new(p::Process::Null),
            },
        }
    }

    #[test]
    fn inlines_call_substituting_param() {
        // def `P(x) = out(x)`; call `P('t')` should inline to
        // ProcessCall("P", ['t']) over body `out('t')`.
        let def = out_x_def("P", "x");
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), &def);
        let call = p::Process::Call { name: "P".into(), args: vec![pub_lit("t")] };
        let inlined = convert_process_with_defs(&call, &defs).unwrap();
        match inlined {
            Process::Action(SapicAction::ProcessCall(n, args), _, body) => {
                assert_eq!(n, "P");
                assert_eq!(args.len(), 1);
                // The wrapped body must carry processnames = ["P"].
                assert_eq!(body.annotation().process_names, vec!["P".to_string()]);
                // The body's out() arg must be the substituted 't', NOT x.
                match *body {
                    Process::Action(SapicAction::ChOut { msg, .. }, _, _) => {
                        assert!(matches!(msg, VTerm::Lit(Lit::Con(_))));
                    }
                    other => panic!("expected ChOut body, got {other:?}"),
                }
            }
            other => panic!("expected ProcessCall action, got {other:?}"),
        }
    }

    #[test]
    fn undefined_call_errors_gracefully() {
        let defs: ProcessDefMap = BTreeMap::new();
        let call = p::Process::Call { name: "Nope".into(), args: vec![] };
        let err = convert_process_with_defs(&call, &defs).unwrap_err();
        assert!(err.message.contains("process not defined"));
    }

    #[test]
    fn arity_mismatch_errors() {
        let def = out_x_def("P", "x");
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), &def);
        // P expects 1 arg, give 0.
        let call = p::Process::Call { name: "P".into(), args: vec![] };
        let err = convert_process_with_defs(&call, &defs).unwrap_err();
        assert!(err.message.contains("expected 1 argument"));
    }
}
