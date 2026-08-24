// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Theory-level driver of the SAPIC typing pass — HS `typeTheoryEnv`
//! (Typing.hs:204-226):
//!
//! 1. `initTEFromSig` seeds ONE [`TypingEnvironment`] from the signature;
//! 2. `mapMProcesses typeAndRenameProcess` types every process-bearing item
//!    (`ProcessItem`, `DiffEquivLemma`, `EquivLemma` — TheoryObject.hs:279-291)
//!    in source order against that shared environment;
//! 3. `mapMProcessesDef typeAndRenameProcessDef` types every `ProcessDefItem`
//!    (TheoryObject.hs:294-301) via the `ChIn`/`fAppList` wrapper trick
//!    (Typing.hs:217-225), always setting `_pVars = Just …`;
//! 4. `Map.foldrWithKey addFunctionTypingInfo' (clearFunctionTypingInfos th')
//!    fte.funs` deletes every source-positioned `FunctionTypingInfo` item and
//!    re-appends one per entry of the final `funs` map — `foldrWithKey` +
//!    append ⇒ the emitted order is DESCENDING key order.
//!
//! RS keeps the parser AST immutable and returns the typed processes as a
//! [`TypedOverlay`] for `pretty_theory`'s open renderer, plus the recomputed
//! `function:` items and the final environment (whose `events` map the export
//! backends consume).

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::FunSym;
use tamarin_term::maude_sig::MaudeSig;
use tamarin_term::term::f_app;
use tamarin_term::vterm::{var_term, Lit, VTerm};

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::pretty_theory::TypedOverlay;
use tamarin_theory::sapic::{
    PlainProcess, Process, ProcessParsedAnnotation, SapicAction, SapicLVar,
};
use tamarin_theory::theory::{SapicFunSym, Theory};

use crate::inline::{collect_process_defs, convert_process_with_defs, ProcessDefMap};
use crate::typing::{
    collect_user_fun_typings, init_te_from_sig, type_and_rename_process_in, vars_proc,
    TypingEnvironment,
};

/// Everything `typeTheoryEnv` returns, split for the RS consumers: the typed
/// processes/defs (renderer overlay), the recomputed `function:` items
/// (descending key order, ready to append), and the final environment.
pub struct TypeTheoryResult {
    pub overlay: TypedOverlay,
    /// One `SapicFunSym` per entry of the final `funs` map, in HS's
    /// `Map.foldrWithKey`-append order = DESCENDING `UserDefinedSym` order.
    pub fun_items: Vec<SapicFunSym>,
    /// The environment the whole theory was typed against.  No RS caller
    /// reads it: its consumers are the ProVerif / DeepSec exporters
    /// (`loadHeaders` folds over `events`, Export.hs:2743-2754), which are
    /// unported — see `tamarin_export`'s module doc.  Returned so the
    /// exporters land against a complete `typeTheoryEnv`.
    pub env: TypingEnvironment,
}

/// `typeTheoryEnv` (Typing.hs:204-226) over the parsed + elaborated theory
/// pair.  Runs on EVERY theory — a process-free (non-SAPIC) theory still gets
/// its `function:` items recomputed from the signature-seeded environment.
pub fn type_theory_env(
    parsed: &p::Theory,
    elaborated: &Theory,
) -> Result<TypeTheoryResult, ElabError> {
    let msig = &elaborated.signature.maude_sig;
    let user_fun_typings = collect_user_fun_typings(parsed);
    let mut env = init_te_from_sig(msig, &user_fun_typings).map_err(|e| ElabError {
        message: format!("SAPIC typing: {e}"),
    })?;

    let defs = collect_process_defs(parsed);

    // Pass 1 — `mapMProcesses typeAndRenameProcess` (TheoryObject.hs:279-291):
    // one typed process per occurrence, in item order; `EquivLemma` yields two
    // (p1 first).  Conversion inlines `P(args)` calls exactly as HS's parser
    // did before the items were stored.
    let mut processes: Vec<PlainProcess> = Vec::new();
    for item in &parsed.items {
        match item {
            p::TheoryItem::TopLevelProcess(proc) | p::TheoryItem::DiffEquivLemma(proc) => {
                processes.push(type_one(&mut env, proc, &defs, msig)?);
            }
            p::TheoryItem::EquivLemma(p1, p2) => {
                processes.push(type_one(&mut env, p1, &defs, msig)?);
                processes.push(type_one(&mut env, p2, &defs, msig)?);
            }
            _ => {}
        }
    }

    // Pass 2 — `mapMProcessesDef typeAndRenameProcessDef`
    // (TheoryObject.hs:294-301, Typing.hs:217-225), same environment.
    let mut typed_defs: Vec<(Option<Vec<SapicLVar>>, PlainProcess)> = Vec::new();
    for item in &parsed.items {
        if let p::TheoryItem::ProcessDef(pd) = item {
            typed_defs.push(type_process_def(&mut env, pd, &defs, msig)?);
        }
    }

    // `Map.foldrWithKey addFunctionTypingInfo'` (Typing.hs:210,226):
    // `foldrWithKey` applies the largest key innermost and each application
    // APPENDS, so the item order is descending key order — `BTreeMap` reverse
    // iteration (`UserDefinedSym`'s derived `Ord` matches HS's tuple order).
    let fun_items: Vec<SapicFunSym> = env
        .funs
        .iter()
        .rev()
        .map(|(sym, (ins, out))| SapicFunSym {
            sym: *sym,
            arg_types: ins.clone(),
            out_type: out.clone(),
        })
        .collect();

    Ok(TypeTheoryResult {
        overlay: TypedOverlay {
            processes,
            defs: typed_defs,
        },
        fun_items,
        env,
    })
}

/// Convert one parser-AST process (inlining `let`-def calls) and run
/// `typeAndRenameProcess` on it against the shared environment.
fn type_one(
    env: &mut TypingEnvironment,
    proc: &p::Process,
    defs: &ProcessDefMap<'_>,
    sig: &MaudeSig,
) -> Result<PlainProcess, ElabError> {
    let plain = convert_process_with_defs(proc, defs, sig).map_err(|e| ElabError {
        message: format!("SAPIC translation: {}", e.message),
    })?;
    type_and_rename_process_in(env, &plain).map_err(|e| ElabError {
        message: format!("SAPIC typing: {e}"),
    })
}

/// `typeAndRenameProcessDef` (Typing.hs:217-225):
///
/// ```haskell
/// let pvars = fromMaybe (S.toList (varsProc pr) List.\\ accBindings pr) p._pVars
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
    pd: &p::ProcessDef,
    defs: &ProcessDefMap<'_>,
    sig: &MaudeSig,
) -> Result<(Option<Vec<SapicLVar>>, PlainProcess), ElabError> {
    let pr = convert_process_with_defs(&pd.body, defs, sig).map_err(|e| ElabError {
        message: format!("SAPIC translation: {}", e.message),
    })?;
    // The def's DECLARED formals (`_pVars`), which both the `pVars` seeding
    // below and HS's "should not be taken" fallback hand back unchanged.
    let declared: Option<Vec<SapicLVar>> = pd
        .vars
        .as_ref()
        .map(|vs| vs.iter().map(crate::convert::varspec_to_sapic).collect());
    let pvars: Vec<SapicLVar> = match &declared {
        Some(vs) => vs.clone(),
        None => {
            // `S.toList (varsProc pr) List.\\ accBindings pr` — the left list
            // is a dup-free set list, so `\\` (remove ONE occurrence per
            // right-hand element) equals membership filtering.
            let acc = crate::bindings::acc_bindings(&pr);
            vars_proc(&pr)
                .into_iter()
                .filter(|v| !acc.contains(v))
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
    // `map termVar' tVars` (VTerm.hs:139-141) — every list element is
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
