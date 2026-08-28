// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! the already-elaborated definitions that precede the call and substitutes the
//! parameters. Keeping resolved internal bodies in the environment is important:
//! a definition cannot acquire visibility of a later definition retroactively,
//! and recursive cycles cannot send conversion into unbounded recursion.
//!
//! The `extend_sup` "type-erasure doubling" of
//! `Theory/Text/Parser/Sapic.hs:299-306` is mirrored:
//! a typed formal `x:ty` produces TWO substitution entries (typed AND untyped
//! keyed) to the same argument, so body occurrences of either form are hit.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::vterm::{Lit, VTerm};

use crate::formula::apply_subst;
#[cfg(test)]
use crate::process_convert::{action as convert_action, combinator as convert_combinator};
use crate::process_convert::{
    add_root_annotation, convert_process_with, term as convert_term, ConvertError,
};
use crate::sapic::{
    apply_match_vars_with, subst_term, traverse_terms_action, traverse_terms_comb, try_map_process,
    PlainProcess, Process, ProcessCombinator, SapicAction, SapicLVar, SapicSubst, SapicTerm,
};
use crate::theory::ProcessDef;

/// Definitions visible at the current source position (HS `lookupProcessDef`,
/// `TheoryObject.hs:693-694`). Each body was elaborated when its declaration
/// was encountered, against the environment that existed immediately before
/// it. The item walk inserts a definition only after elaborating its body.
pub type ProcessDefMap = BTreeMap<String, ProcessDef>;

/// `convert_process` with process-definition resolution.  Identical to
/// `convert_process` for every node except `Call`, which is inlined here.
pub fn convert_process_with_defs(
    proc: &p::Process,
    defs: &ProcessDefMap,
    sig: &MaudeSig,
) -> Result<PlainProcess, ConvertError> {
    convert_process_with(proc, sig, &mut |name, args, sig| {
        inline_call(name, args, defs, sig)
    })
}

/// Inline one `P(args)` call (HS `actionprocess` identifier branch,
/// `Theory/Text/Parser/Sapic.hs:293-312`).
fn inline_call(
    name: &str,
    args: &[p::Term],
    defs: &ProcessDefMap,
    sig: &MaudeSig,
) -> Result<PlainProcess, ConvertError> {
    use crate::sapic::ProcessParsedAnnotation;

    // `checkProcess` (Theory/Text/Parser/Sapic.hs:314-317): fail if the
    // process is undefined.
    let def = defs
        .get(name)
        .ok_or_else(|| ConvertError::new(format!("process not defined: {name}")))?;

    // Convert the actual argument terms.
    let sapic_args: Vec<SapicTerm> = args
        .iter()
        .map(|a| convert_term(a, sig))
        .collect::<Result<_, _>>()?;

    // Convert the formal parameters (HS `fromMaybe [] (get pVars p)`).
    let params: Vec<SapicLVar> = def.vars.clone().unwrap_or_default();

    if params.len() != sapic_args.len() {
        return Err(ConvertError::new(format!(
            "process call {name}: expected {} argument(s), got {}",
            params.len(),
            sapic_args.len()
        )));
    }

    // The body was converted when its definition was read. Any calls it
    // contains were therefore resolved against precisely the earlier
    // definitions visible there; clone that resolved body rather than
    // re-reading it against the caller's newer environment.
    let body = def.body.clone();

    // Build the parameter substitution with HS's `extend_sup` type-erasure
    // doubling (Theory/Text/Parser/Sapic.hs:299-306): a typed formal
    // contributes both its typed and untyped keys mapping to the argument.
    let mut pairs: Vec<(SapicLVar, SapicTerm)> = Vec::new();
    for (param, arg) in params.iter().zip(sapic_args.iter()) {
        pairs.push((param.clone(), arg.clone()));
        if param.stype.is_some() {
            pairs.push((SapicLVar::untyped(param.var), arg.clone()));
        }
    }
    let subst = SapicSubst::from_list(pairs);

    // `applyM (substFromList extend_sup) p` — capture-checking substitution.
    let substituted = apply_m_process(&subst, body)?;

    // `processAddAnnotation substP (mempty {processnames = [name]})`: tag the
    // body's root node with the call name (drives `role=` / colour).
    let mut name_ann = ProcessParsedAnnotation::empty();
    name_ann.process_names = vec![name.to_string()];
    let annotated = add_root_annotation(substituted, name_ann);

    // Wrap in the `ProcessCall` marker action
    // (Theory/Text/Parser/Sapic.hs:308-311).
    Ok(Process::Action(
        SapicAction::ProcessCall(name.to_string(), sapic_args),
        ProcessParsedAnnotation::empty(),
        Box::new(annotated),
    ))
}

/// `applyM subst p` over an `LProcess` (Sapic/Process.hs:411-424): apply `subst` to
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
    try_map_process(
        &p,
        &mut |action| apply_m_action(subst, action),
        &mut |comb| apply_m_comb(subst, comb),
        &mut |ann| Ok(apply_annotation(subst, ann.clone())),
    )
}

/// Upstream #922's `applyMProcessParsedAnnotation`: locations are ordinary
/// terms, so substitution may replace a location variable by any term (not
/// merely another variable). Process names and the back-substitution are
/// deliberately left untouched.
fn apply_annotation(
    subst: &SapicSubst,
    mut ann: crate::sapic::ProcessParsedAnnotation,
) -> crate::sapic::ProcessParsedAnnotation {
    ann.location = ann.location.map(|loc| subst_term(subst, &loc));
    ann
}

/// True iff a substitution maps `v` (in either typed or untyped form) — i.e.
/// `v ∈ dom subst`, used for the capture checks.
fn in_domain(subst: &SapicSubst, v: &SapicLVar) -> bool {
    subst.image_of(v).is_some() || subst.image_of(&SapicLVar::untyped(v.var)).is_some()
}

/// `applyM` for `SapicAction` (Sapic/Process.hs:392-408): substitute terms,
/// raising `CapturedNew` / `CapturedIn` on capture.  Everything the capture
/// checks do not claim falls through to `apply subst`
/// (Sapic/Process.hs:319-321).
fn apply_m_action(
    subst: &SapicSubst,
    ac: &SapicAction<SapicLVar>,
) -> Result<SapicAction<SapicLVar>, ConvertError> {
    match ac {
        // `New v` with `v ∈ dom subst` would be captured (Sapic/Process.hs:395-398).
        SapicAction::New(v) => {
            if in_domain(subst, v) {
                return Err(ConvertError::new(format!(
                    "captured variable {} in process call (new)",
                    v.var.name
                )));
            }
            Ok(SapicAction::New(v.clone()))
        }
        // `ChIn` of a single captured var is captured unless its name starts
        // with `pat_` (Sapic/Process.hs:399-406).
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => {
            if let VTerm::Lit(Lit::Var(v)) = msg {
                if in_domain(subst, v) && !v.var.name.starts_with("pat_") {
                    return Err(ConvertError::new(format!(
                        "captured variable {} in process call (in)",
                        v.var.name
                    )));
                }
            }
            Ok(SapicAction::ChIn {
                chan: chan.as_ref().map(|t| subst_term(subst, t)),
                msg: subst_term(subst, msg),
                // HS special-cases `ChIn` in `Apply SapicSubst (SapicAction
                // SapicLVar)` (Sapic/Process.hs:319-321) to reach this rewrite.
                // When inlining a call like `Q(h(a))` into `in(<y, =x>)`, the
                // param match-var `x` becomes the vars of `h(a)` (= `{a}`) so that
                // `bindingsAct = frees(<y,h(a)>) \ {a} = {y}` — i.e. the already-
                // bound `a` is NOT rebound (Bindings.hs:21-26, see line 24).  Without this the
                // stale `{x}` would leave `a` looking unbound, rebinding it to a
                // fresh `a.N` and adding a spurious state-fact variable.
                match_vars: apply_match_vars_with(|v| call_image(subst, v), match_vars),
            })
        }
        _ => traverse_terms_action(
            |t| Ok(subst_term(subst, t)),
            // The call's arguments replace the formal parameters inside an
            // embedded `_restrict` as they do in the fact rows.  A quantifier
            // binder is a `Bound` De Bruijn index, outside the substitution's
            // domain, so it cannot capture a variable of an argument.
            |f| Ok(apply_subst(subst, f.clone())),
            // A variable the action binds on its own is either rejected above
            // or outside the substitution's domain.
            |v| Ok(v.clone()),
            ac,
        ),
    }
}

/// `applyM` for `ProcessCombinator` (Sapic/Process.hs:382-389): `Lookup`'s bound var
/// being captured raises `CapturedLookup`.
fn apply_m_comb(
    subst: &SapicSubst,
    c: &ProcessCombinator<SapicLVar>,
) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            if in_domain(subst, v) {
                return Err(ConvertError::new(format!(
                    "captured variable {} in process call (lookup)",
                    v.var.name
                )));
            }
            Ok(ProcessCombinator::Lookup(subst_term(subst, t), v.clone()))
        }
        _ => traverse_terms_comb(
            |t| Ok(subst_term(subst, t)),
            // The call's arguments replace the formal parameters inside the
            // conditional's formula.
            |f| Ok(apply_subst(subst, f.clone())),
            |v| Ok(v.clone()),
            c,
        ),
    }
}

/// The image of `v` under the parameter substitution.  `extend_sup`
/// (Theory/Text/Parser/Sapic.hs:299-306) keys a typed formal under both its
/// typed and its untyped spelling, so a variable resolves against either.  A
/// variable the substitution does not define stands for itself.
///
/// This is the `f . varTerm` that [`apply_match_vars_with`] (HS
/// `applyMatchVars'`, Theory/Sapic/Process.hs:313-317) drives.
fn call_image(subst: &SapicSubst, v: &SapicLVar) -> SapicTerm {
    subst
        .image_of(v)
        .or_else(|| subst.image_of(&SapicLVar::untyped(v.var)))
        .cloned()
        .unwrap_or_else(|| tamarin_term::vterm::var_term(v.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn pub_lit(s: &str) -> p::Term {
        p::Term::PubLit(s.to_string())
    }

    fn out_x_def(name: &str, param: &str) -> p::ProcessDef {
        // `let <name>(<param>) = out(<param>)`
        let xref = p::Term::Var(p::VarSpec {
            name: param.to_string(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        });
        p::ProcessDef {
            name: name.to_string(),
            vars: Some(vec![p::VarSpec {
                name: param.to_string(),
                idx: 0,
                sort: LSort::Msg,
                typ: None,
            }]),
            body: p::Process::Action {
                action: p::SapicAction::ChOut {
                    chan: None,
                    msg: xref,
                },
                body: Box::new(p::Process::Null),
            },
        }
    }

    fn resolved_def(def: &p::ProcessDef, sig: &MaudeSig) -> ProcessDef {
        ProcessDef {
            name: def.name.clone(),
            vars: def
                .vars
                .as_ref()
                .map(|vs| vs.iter().map(crate::elaborate::varspec_to_sapic).collect()),
            body: crate::process_convert::convert_process(&def.body, sig).unwrap(),
        }
    }

    #[test]
    fn inlines_call_substituting_param() {
        // def `P(x) = out(x)`; call `P('t')` should inline to
        // ProcessCall("P", ['t']) over body `out('t')`.
        let def = out_x_def("P", "x");
        let sig = pair_maude_sig();
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), resolved_def(&def, &sig));
        let call = p::Process::Call {
            name: "P".into(),
            args: vec![pub_lit("t")],
        };
        let inlined = convert_process_with_defs(&call, &defs, &sig).unwrap();
        match inlined {
            Process::Action(SapicAction::ProcessCall(n, args), _, body) => {
                assert_eq!(n, "P");
                assert_eq!(args.len(), 1);
                // The wrapped body must carry processnames = ["P"].
                assert_eq!(body.annotation().process_names, vec!["P".to_string()]);
                // The out() argument in the body must be the substituted 't',
                // and not x.  It must also be the same term that the call site
                // passed.  A substitution that drops the argument, or that
                // binds the wrong formal parameter, therefore cannot pass this
                // check with some other constant.
                match *body {
                    Process::Action(SapicAction::ChOut { msg, .. }, _, _) => {
                        assert_eq!(msg, args[0]);
                        assert_eq!(
                            msg,
                            crate::process_convert::term(&pub_lit("t"), &pair_maude_sig())
                                .expect("'t' converts")
                        );
                    }
                    other => panic!("expected ChOut body, got {other:?}"),
                }
            }
            other => panic!("expected ProcessCall action, got {other:?}"),
        }
    }

    fn msg_var(name: &str) -> p::VarSpec {
        p::VarSpec {
            name: name.to_string(),
            idx: 0,
            sort: LSort::Msg,
            typ: None,
        }
    }

    #[test]
    fn inlines_call_substituting_a_parameter_into_a_conditional() {
        // `let P(y) = if Eq(y,'a') then 0 else 0` called as `P('t')`: the
        // argument replaces the formal parameter inside the condition's
        // formula, so the inlined combinator is the one the callee's body
        // would convert to with `'t'` written in place of `y`.
        let cond_on = |t: p::Term| {
            p::ProcessComb::Cond(p::Condition::Formula(p::Formula::Atom(p::Atom::Eq(
                t,
                pub_lit("a"),
            ))))
        };
        let def = p::ProcessDef {
            name: "P".into(),
            vars: Some(vec![msg_var("y")]),
            body: p::Process::Comb {
                comb: cond_on(p::Term::Var(msg_var("y"))),
                left: Box::new(p::Process::Null),
                right: Box::new(p::Process::Null),
            },
        };
        let sig = pair_maude_sig();
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), resolved_def(&def, &sig));
        let call = p::Process::Call {
            name: "P".into(),
            args: vec![pub_lit("t")],
        };
        let Process::Action(SapicAction::ProcessCall(..), _, body) =
            convert_process_with_defs(&call, &defs, &sig).unwrap()
        else {
            panic!("expected a ProcessCall action");
        };
        let Process::Comb(got, ..) = *body else {
            panic!("expected a Comb node under the call marker");
        };
        assert_eq!(
            got,
            convert_combinator(&cond_on(pub_lit("t")), &sig).unwrap()
        );
    }

    #[test]
    fn inlines_call_substituting_a_parameter_into_an_embedded_restriction() {
        // `let P(y) = [ ] --[ _restrict(Q(y)) ]-> [ ]` called as `P('t')`:
        // the argument replaces the formal parameter inside the embedded
        // restriction as it does in the fact rows.
        let msr_on = |t: p::Term| p::SapicAction::Msr {
            prems: vec![],
            acts: vec![],
            concs: vec![],
            restrictions: vec![p::Formula::Atom(p::Atom::Pred(p::Fact {
                persistent: false,
                name: "Q".into(),
                args: vec![t],
                annotations: vec![],
            }))],
        };
        let def = p::ProcessDef {
            name: "P".into(),
            vars: Some(vec![msg_var("y")]),
            body: p::Process::Action {
                action: msr_on(p::Term::Var(msg_var("y"))),
                body: Box::new(p::Process::Null),
            },
        };
        let sig = pair_maude_sig();
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), resolved_def(&def, &sig));
        let call = p::Process::Call {
            name: "P".into(),
            args: vec![pub_lit("t")],
        };
        let Process::Action(SapicAction::ProcessCall(..), _, body) =
            convert_process_with_defs(&call, &defs, &sig).unwrap()
        else {
            panic!("expected a ProcessCall action");
        };
        let Process::Action(got, ..) = *body else {
            panic!("expected an action under the call marker");
        };
        assert_eq!(got, convert_action(&msr_on(pub_lit("t")), &sig).unwrap());
    }

    #[test]
    fn undefined_call_errors_gracefully() {
        let defs: ProcessDefMap = BTreeMap::new();
        let call = p::Process::Call {
            name: "Nope".into(),
            args: vec![],
        };
        let err = convert_process_with_defs(&call, &defs, &pair_maude_sig()).unwrap_err();
        assert!(err.message.contains("process not defined"));
    }

    #[test]
    fn arity_mismatch_errors() {
        let def = out_x_def("P", "x");
        let sig = pair_maude_sig();
        let mut defs: ProcessDefMap = BTreeMap::new();
        defs.insert("P".to_string(), resolved_def(&def, &sig));
        // P expects 1 arg, give 0.
        let call = p::Process::Call {
            name: "P".into(),
            args: vec![],
        };
        let err = convert_process_with_defs(&call, &defs, &sig).unwrap_err();
        assert!(err.message.contains("expected 1 argument"));
    }

    #[test]
    fn call_substitutes_compound_term_into_location() {
        // Upstream #922: `applyMProcessParsedAnnotation` uses ordinary term
        // substitution, so a location parameter can become a pair rather than
        // failing as a variable-only substitution.
        let l = msg_var("l");
        let def = p::ProcessDef {
            name: "P".into(),
            vars: Some(vec![l.clone()]),
            body: p::Process::AtAnnotation(Box::new(p::Process::Null), p::Term::Var(l)),
        };
        let sig = pair_maude_sig();
        let mut defs = ProcessDefMap::new();
        defs.insert("P".into(), resolved_def(&def, &sig));
        let location = p::Term::Pair(vec![pub_lit("loc"), pub_lit("a")]);
        let call = p::Process::Call {
            name: "P".into(),
            args: vec![location.clone()],
        };

        let Process::Action(SapicAction::ProcessCall(..), _, body) =
            convert_process_with_defs(&call, &defs, &sig).unwrap()
        else {
            panic!("expected a ProcessCall action");
        };
        assert_eq!(
            body.annotation().location,
            Some(convert_term(&location, &sig).unwrap())
        );
    }
}
