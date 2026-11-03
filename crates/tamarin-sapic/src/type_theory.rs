// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Theory-level driver of the SAPIC typing pass — HS `typeTheoryEnv`
//! (Typing.hs):
//!
//! 1. `initTEFromSig` seeds ONE [`TypingEnvironment`] from the signature;
//! 2. `mapMProcesses typeAndRenameProcess` types every process-bearing item
//!    (`ProcessItem`, `DiffEquivLemma`, `EquivLemma` — TheoryObject.hs)
//!    in source order against that shared environment;
//! 3. `mapMProcessesDef typeAndRenameProcessDef` types every `ProcessDefItem`
//!    (TheoryObject.hs) via the `ChIn`/`fAppList` wrapper trick
//!    (Typing.hs), always setting `_pVars = Just …`;
//! 4. `Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th')
//!    fte.funs` deletes every source-positioned `FunctionTypingInfo` item and
//!    re-appends one per entry of the final `funs` map — `foldrWithKey` +
//!    append ⇒ the emitted order is DESCENDING key order.
//!
//! The theory's items are rewritten in place, in the order the two `mapM`s
//! visit them; the environment is returned because its `events` map is what
//! the export backends consume.

use std::collections::BTreeSet;

use tamarin_term::function_symbols::FunSym;
use tamarin_term::term::f_app;
use tamarin_term::vterm::{var_term, Lit, VTerm};

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::sapic::{
    PlainProcess, Process, ProcessParsedAnnotation, SapicAction, SapicLVar,
};
use tamarin_theory::theory::{ProcessDef, SapicFunSym, Theory, TheoryItem, TranslationElement};

use crate::typing::{
    collect_user_fun_typings, init_te_from_sig, type_and_rename_process_in, vars_proc,
    TypingEnvironment,
};

/// `typeTheoryEnv` (Typing.hs) over the elaborated theory, whose
/// process-bearing items and `FunctionTypingInfo` items it rewrites in place —
/// HS's first return component.  The second, the environment the whole theory
/// was typed against, is handed back: no RS caller reads it, but its consumers
/// are the ProVerif / DeepSec exporters (`loadHeaders` folds over `events`,
/// Export/Sapic.hs), which are unported.  `typeTheory`
/// (Typing.hs) is this function with the environment discarded.
///
/// Runs on EVERY theory — a process-free (non-SAPIC) theory still gets its
/// `function:` items recomputed from the signature-seeded environment.
pub fn type_theory_env(thy: &mut Theory) -> Result<TypingEnvironment, ElabError> {
    let user_fun_typings = collect_user_fun_typings(thy);
    let mut env = init_te_from_sig(&thy.signature, &user_fun_typings).map_err(|e| ElabError {
        message: format!("SAPIC typing: {e}"),
    })?;

    // Pass 1 — `mapMProcesses typeAndRenameProcess` (TheoryObject.hs):
    // every process-bearing item typed in item order; `EquivLemma` types its
    // first process before its second.
    for item in &mut thy.items {
        match item {
            TheoryItem::Translation(
                TranslationElement::Process(pr) | TranslationElement::DiffEquivLemma(pr),
            ) => {
                *pr = type_one(&mut env, pr)?;
            }
            TheoryItem::Translation(TranslationElement::EquivLemma(p1, p2)) => {
                *p1 = type_one(&mut env, p1)?;
                *p2 = type_one(&mut env, p2)?;
            }
            _ => {}
        }
    }

    // Pass 2 — `mapMProcessesDef typeAndRenameProcessDef`
    // (TheoryObject.hs, Typing.hs), same environment.
    for item in &mut thy.items {
        if let TheoryItem::Translation(TranslationElement::ProcessDef(pd)) = item {
            let (vars, body) = type_process_def(&mut env, pd)?;
            pd.vars = vars;
            pd.body = body;
        }
    }

    // `Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th')`
    // (Typing.hs): every source-positioned typing item is dropped, and
    // `foldrWithKey` applies the largest key innermost while each application
    // APPENDS, so the re-emitted order is descending key order — `BTreeMap`
    // reverse iteration (`UserDefinedSym`'s derived `Ord` matches HS's tuple
    // order).
    tamarin_theory::theory::clear_function_typing_infos(thy);
    for (sym, (ins, out)) in env.funs.iter().rev() {
        thy.items.push(TheoryItem::Translation(
            TranslationElement::FunctionTypingInfo(SapicFunSym {
                sym: *sym,
                arg_types: ins.clone(),
                out_type: out.clone(),
            }),
        ));
    }
    Ok(env)
}

/// HS `typeTheoryForExport` (upstream #960): open definitions depend on the
/// caller's bindings, and pattern formals stand for syntax rather than values.
/// Export their instantiated bodies, retaining ordinary closed named calls.
/// MSR translation continues to use [`type_theory_env`] without this rewrite.
pub fn type_theory_for_export(thy: &mut Theory) -> Result<(), ElabError> {
    let expanded: BTreeSet<_> = thy
        .process_defs()
        .filter(|pd| {
            pd.vars.as_ref().is_none_or(|params| {
                let formals: BTreeSet<_> = params.iter().map(|v| v.var).collect();
                crate::bindings::acc_bindings(&pd.body)
                    .iter()
                    .any(|v| formals.contains(&v.var))
            })
        })
        .map(|pd| pd.name.clone())
        .collect();
    // Validate declarations and every call argument before removing any:
    // unused definitions can constrain types, and unused arguments can be bad.
    type_theory_env(thy)?;
    let inline = |p: &mut PlainProcess| {
        *p = inline_export_calls(p.clone(), &expanded, ProcessParsedAnnotation::empty());
    };
    thy.items.retain_mut(|item| {
        match item {
            TheoryItem::Translation(
                TranslationElement::Process(p) | TranslationElement::DiffEquivLemma(p),
            ) => inline(p),
            TheoryItem::Translation(TranslationElement::EquivLemma(left, right)) => {
                inline(left);
                inline(right);
            }
            TheoryItem::Translation(TranslationElement::ProcessDef(pd)) => {
                if expanded.contains(&pd.name) {
                    return false;
                }
                inline(&mut pd.body);
            }
            _ => {}
        }
        true
    });
    Ok(())
}

fn inline_export_calls(
    p: PlainProcess,
    expanded: &BTreeSet<String>,
    carried: ProcessParsedAnnotation,
) -> PlainProcess {
    match p {
        Process::Action(SapicAction::ProcessCall(name, _), here, rest)
            if expanded.contains(&name) =>
        {
            inline_export_calls(*rest, expanded, carried.append(here))
        }
        Process::Action(ac, here, rest) => Process::Action(
            ac,
            carried.append(here),
            Box::new(inline_export_calls(
                *rest,
                expanded,
                ProcessParsedAnnotation::empty(),
            )),
        ),
        Process::Comb(c, here, left, right) => Process::Comb(
            c,
            carried.append(here),
            Box::new(inline_export_calls(
                *left,
                expanded,
                ProcessParsedAnnotation::empty(),
            )),
            Box::new(inline_export_calls(
                *right,
                expanded,
                ProcessParsedAnnotation::empty(),
            )),
        ),
        Process::Null(here) => Process::Null(carried.append(here)),
    }
}

/// Run `typeAndRenameProcess` on one process against the shared environment.
fn type_one(env: &mut TypingEnvironment, proc: &PlainProcess) -> Result<PlainProcess, ElabError> {
    type_and_rename_process_in(env, proc).map_err(|e| ElabError {
        message: format!("SAPIC typing: {e}"),
    })
}

/// `typeAndRenameProcessDef` (Typing.hs):
///
/// ```haskell
/// let bound = S.fromList $ map toLVar $ accBindings pr
/// let pvars = fromMaybe (filter ((`S.notMember` bound) . toLVar) $ S.toList (varsProc pr)) p._pVars
/// let aux_pr = ProcessAction (ChIn Nothing (fAppList (map varTerm pvars)) S.empty) mempty pr
/// renamedP <- typeAndRenameProcess aux_pr
/// case renamedP of
///   ProcessAction (ChIn _ (viewTerm2 -> FList tVars) _) _ prf ->
///     return $ p { _pBody = prf, _pVars = Just $ map termVar' tVars}
///   _ -> return p -- should not be taken
/// ```
///
/// The `ChIn` wrapper binds the def's formals (declared `_pVars`, or the
/// body's free variables when the def was written `let P = …`), so
/// `renameUnique`/`typeProcess` treat them exactly like `in(…)`-bound
/// variables; the typed list peels back into `_pVars = Just …` — ALWAYS
/// `Just`, so a parameterless def renders `let  P () =`.
fn type_process_def(
    env: &mut TypingEnvironment,
    pd: &ProcessDef,
) -> Result<(Option<Vec<SapicLVar>>, PlainProcess), ElabError> {
    let pr = pd.body.clone();
    // The def's DECLARED formals (`_pVars`), which both the `pVars` seeding
    // below and HS's "should not be taken" fallback hand back unchanged.
    let declared: Option<Vec<SapicLVar>> = pd.vars.clone();
    let pvars: Vec<SapicLVar> = match &declared {
        Some(vs) => vs.clone(),
        None => {
            // Type annotations constrain types, not binding identities.
            let bound: BTreeSet<_> = crate::bindings::acc_bindings(&pr)
                .into_iter()
                .map(|v| v.var)
                .collect();
            vars_proc(&pr)
                .into_iter()
                .filter(|v| !bound.contains(&v.var))
                .collect()
        }
    };
    let msg = f_app(
        FunSym::List,
        pvars.iter().map(|v| var_term(v.clone())).collect(),
    );
    let aux = Process::Action(
        SapicAction::ChIn {
            chan: None,
            msg,
            match_vars: BTreeSet::new(),
        },
        ProcessParsedAnnotation::empty(),
        Box::new(pr.clone()),
    );
    let renamed = type_and_rename_process_in(env, &aux).map_err(|e| ElabError {
        message: format!("SAPIC typing: {e}"),
    })?;
    let Process::Action(
        SapicAction::ChIn {
            msg: VTerm::App(FunSym::List, t_vars),
            ..
        },
        _,
        body,
    ) = renamed
    else {
        // HS `_ -> return p` ("should not be taken").
        return Ok((declared, pr));
    };
    // `map termVar' tVars` (VTerm.hs) — every list element is
    // a variable (typing preserves the term structure).
    let vars = t_vars
        .iter()
        .map(|t| match t {
            VTerm::Lit(Lit::Var(v)) => Ok(v.clone()),
            other => Err(ElabError {
                message: format!("termVar': non-variable term {other:?}"),
            }),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((Some(vars), *body))
}

#[cfg(test)]
#[path = "type_theory_tests.rs"]
mod tests;
