// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Process-call inlining.
//!
//! HS inlines process definitions at PARSE TIME: when the parser
//! (`actionprocess`, `Theory/Text/Parser/Sapic.hs`) reads an identifier
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
//! trivial pass-through (`Basetranslation.hs`); the real behaviour comes
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
//! `Theory/Text/Parser/Sapic.hs` is mirrored:
//! a typed formal `x:ty` produces TWO substitution entries (typed AND untyped
//! keyed) to the same argument, so body occurrences of either form are hit.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;
use tamarin_term::maude_sig::MaudeSig;

use crate::process_convert::{
    add_root_annotation, convert_process_with, term as convert_term, ConvertError,
};
use crate::sapic::{
    apply_m_process, Captured, PlainProcess, Process, SapicAction, SapicLVar, SapicSubst, SapicTerm,
};
use crate::theory::ProcessDef;

/// Definitions visible at the current source position (HS `lookupProcessDef`,
/// `TheoryObject.hs`). Each body was elaborated when its declaration
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
/// `Theory/Text/Parser/Sapic.hs`).
fn inline_call(
    name: &str,
    args: &[p::Term],
    defs: &ProcessDefMap,
    sig: &MaudeSig,
) -> Result<PlainProcess, ConvertError> {
    use crate::sapic::ProcessParsedAnnotation;

    // `checkProcess` (Theory/Text/Parser/Sapic.hs): fail if the
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
    let params: &[SapicLVar] = def.vars.as_deref().unwrap_or_default();

    // The body was converted when its definition was read. Any calls it
    // contains were therefore resolved against precisely the earlier
    // definitions visible there; substitute into that resolved body rather
    // than re-reading it against the caller's newer environment.
    let body = &def.body;

    // Build the parameter substitution with HS's `extend_sup` type-erasure
    // doubling (Theory/Text/Parser/Sapic.hs): a typed formal
    // contributes both its typed and untyped keys mapping to the argument.
    // `zip vars ts` pairs as many as both lists have: a call with the wrong
    // number of arguments is not an error.
    let mut pairs: Vec<(SapicLVar, SapicTerm)> = Vec::new();
    for (param, arg) in params.iter().zip(sapic_args.iter()) {
        pairs.push((param.clone(), arg.clone()));
        if param.stype.is_some() {
            pairs.push((SapicLVar::untyped(param.var), arg.clone()));
        }
    }
    let subst = SapicSubst::from_list(pairs);

    // `applyM (substFromList extend_sup) p` — capture-checking substitution.
    let substituted = apply_m_process(&subst, body).map_err(|captured| {
        let (v, binder) = match captured {
            Captured::In(v) => (v, "in"),
            Captured::Lookup(v) => (v, "lookup"),
            Captured::New(v) => (v, "new"),
        };
        ConvertError::new(format!(
            "captured variable {} in process call ({binder})",
            v.var.name
        ))
    })?;

    // `processAddAnnotation substP (mempty {processnames = [name]})`: tag the
    // body's root node with the call name (drives `role=` / colour).
    let mut name_ann = ProcessParsedAnnotation::empty();
    name_ann.process_names = vec![name.to_string()];
    let annotated = add_root_annotation(substituted, name_ann);

    // Wrap in the `ProcessCall` marker action
    // (Theory/Text/Parser/Sapic.hs).
    Ok(Process::Action(
        SapicAction::ProcessCall(name.to_string(), sapic_args),
        ProcessParsedAnnotation::empty(),
        Box::new(annotated),
    ))
}
