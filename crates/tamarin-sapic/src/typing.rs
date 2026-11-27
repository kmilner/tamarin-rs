// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.Typing` (`lib/sapic/src/Sapic/Typing.hs`) — the
//! uniqueness-renaming pass (`renameUnique`) and the lightweight type
//! inference (`typeProcess` / `typeWith`) over SAPIC processes.
//!
//! HS pipeline (`typeTheoryEnv`, Typing.hs):
//!   for each top-level process:  `renameUnique` then `typeProcess`.
//! We mirror that in [`type_and_rename_process_in`] (one shared
//! [`TypingEnvironment`] across processes, driven by
//! `crate::type_theory::type_theory`).

use std::collections::{BTreeMap, BTreeSet};

use tamarin_term::function_symbols::UserDefinedSym;
use tamarin_term::lterm::{LSort, LVar, Name};
use tamarin_term::vterm::{var_term, Lit, VTerm};
use tamarin_utils::fresh::PreciseFreshState;

use tamarin_theory::formula::for_each_free_var;
use tamarin_theory::sapic::PlainProcess;
use tamarin_theory::sapic::{
    apply_action, apply_comb, apply_process, for_each_process, traverse_terms_action,
    traverse_terms_comb, Process, ProcessCombinator, SapicAction, SapicFormula, SapicLVar,
    SapicTerm, SapicType,
};

use crate::bindings::{bindings_act, bindings_comb};
use crate::exceptions::{process_not_wellformed, SapicFunType, WfError};

// =============================================================================
// renameUnique (Typing.hs)
// =============================================================================

/// HS `apply` at `Subst Name LVar` (Theory/Sapic/Term.hs): rename each
/// variable by its `LVar`, keeping its SAPIC type.
fn renaming(subst: &BTreeMap<LVar, LVar>) -> impl Fn(&SapicLVar) -> Option<SapicTerm> + '_ {
    |sv| {
        subst
            .get(&sv.var)
            .map(|lv| var_term(SapicLVar::new(*lv, sv.stype.clone())))
    }
}

/// `renameUnique'` (Typing.hs).  `subst` is the *outstanding* renaming
/// applied at this node (`apply initSubst p`); `fresh` mints fresh indices.
/// For each binder we (1) mint a fresh copy of every bound variable, (2) record
/// the inverse renaming in the node's `back_substitution` annotation, and
/// (3) descend with the extended substitution.
fn rename_unique_go(
    fresh: &mut PreciseFreshState,
    subst: &BTreeMap<LVar, LVar>,
    p: &PlainProcess,
) -> PlainProcess {
    // `let p' = apply initSubst p` — apply the outstanding renaming to the
    // WHOLE subtree (HS Typing.hs); the children inherit the rename, then
    // are descended into with only the NEW fresh subst for this node's binders.
    let p_prime = apply_process(&renaming(subst), p);
    match p_prime {
        Process::Null(ann) => Process::Null(ann),
        Process::Action(ac, ann, body) => {
            let bvars = bindings_act(&ac);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let ac1 = apply_action(&renaming(&new_subst), &ac);
            let body1 = rename_unique_go(fresh, &new_subst, &body);
            Process::Action(ac1, ann2, Box::new(body1))
        }
        Process::Comb(c, ann, l, r) => {
            let bvars = bindings_comb(&c);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let c1 = apply_comb(&renaming(&new_subst), &c);
            let l1 = rename_unique_go(fresh, &new_subst, &l);
            let r1 = rename_unique_go(fresh, &new_subst, &r);
            Process::Comb(c1, ann2, Box::new(l1), Box::new(r1))
        }
    }
}

/// `mkSubst` (Typing.hs): for each bound variable mint a fresh LVar
/// copy (`freshLVar name sort`), returning the forward renaming `(v -> v')`
/// and the inverse `(v' -> v)` as a `Subst Name LVar` for back-substitution.
fn mk_subst(
    fresh: &mut PreciseFreshState,
    bvars: &[SapicLVar],
) -> (BTreeMap<LVar, LVar>, tamarin_term::subst::Subst<Name, LVar>) {
    let mut fwd: BTreeMap<LVar, LVar> = BTreeMap::new();
    let mut inv_pairs: Vec<(LVar, VTerm<Name, LVar>)> = Vec::new();
    for sv in bvars {
        let lv = &sv.var;
        let v_new = tamarin_term::lterm::fresh_lvar(fresh, lv.name, lv.sort);
        fwd.insert(*lv, v_new);
        inv_pairs.push((v_new, var_term(*lv)));
    }
    let inv = tamarin_term::subst::Subst::from_list(inv_pairs);
    (fwd, inv)
}

/// `renameUnique` (Typing.hs): seed the fresh-var supply so it avoids
/// every variable already present, then run `renameUnique'` from the identity
/// substitution.
pub(crate) fn rename_unique(p: &PlainProcess) -> PlainProcess {
    // `avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p`
    let avoid: Vec<(String, u64)> = vars_proc(p)
        .into_iter()
        .map(|sv| (sv.var.name.to_string(), sv.var.idx))
        .collect();
    let mut fresh = PreciseFreshState::avoid_precise(avoid);
    let empty: BTreeMap<LVar, LVar> = BTreeMap::new();
    rename_unique_go(&mut fresh, &empty, p)
}

// =============================================================================
// Type inference (typeProcess / typeWith, Typing.hs)
// =============================================================================

/// `TypingEnvironment` (Typing.hs).
/// `funs` is keyed by `UserDefinedSym`, so a user-defined AC symbol has a
/// typing entry alongside the free ones.  HS's `events` map is omitted: only
/// the unported ProVerif / DeepSec exporters read it (Export/Sapic.hs).
pub struct TypingEnvironment {
    pub vars: BTreeMap<LVar, SapicType>,
    pub funs: BTreeMap<UserDefinedSym, (Vec<SapicType>, SapicType)>,
}

/// `smallerType` (Typing.hs).
fn smaller_type(t1: &SapicType, t2: &SapicType) -> bool {
    match (t1, t2) {
        (_, None) => true,
        (Some(a), Some(b)) => a == b,
        (None, Some(_)) => false,
    }
}

/// `sqcap` (Typing.hs): more specific of two types, `None` (HS
/// `CannotMerge`) if they clash.
fn sqcap(t1: &SapicType, t2: &SapicType) -> Option<SapicType> {
    if smaller_type(t1, t2) {
        Some(t1.clone())
    } else if smaller_type(t2, t1) {
        Some(t2.clone())
    } else {
        None
    }
}

/// `catch (sqcap actual tt) (sqHandler t)` (Typing.hs): a clash is a
/// `TypingError t actual tt`.
fn sqcap_term(t: &SapicTerm, actual: &SapicType, tt: &SapicType) -> Result<SapicType, WfError> {
    sqcap(actual, tt).ok_or_else(|| WfError::Typing(t.clone(), actual.clone(), tt.clone()))
}

/// `defaultFunctionType n = (replicate n Nothing, Nothing)` (Typing.hs).
fn default_function_type(n: usize) -> (Vec<SapicType>, SapicType) {
    (vec![None; n], None)
}

/// `typeWith` (Typing.hs).  Types term `t` against target `tt`,
/// returning the typed term and its inferred type, updating `env`.
fn type_with(
    env: &mut TypingEnvironment,
    t: &SapicTerm,
    tt: &SapicType,
) -> Result<(SapicTerm, SapicType), WfError> {
    match t {
        VTerm::Lit(Lit::Var(v)) => {
            let lvar = &v.var;
            // CASE: variable.
            let stype = if lvar.sort == LSort::Pub {
                None
            } else {
                match env.vars.get(lvar) {
                    None => return Err(WfError::Unbound(BTreeSet::from([*lvar]))),
                    Some(ty) => ty.clone(),
                }
            };
            let merged = sqcap_term(t, &stype, tt)?;
            env.vars.insert(*lvar, merged.clone());
            Ok((var_term(SapicLVar::new(*lvar, merged.clone())), merged))
        }
        VTerm::App(sym, args) => {
            use tamarin_term::function_symbols::FunSym;
            match sym {
                // HS `typeWith` dispatches on `viewTerm2 t`: a NoEq application
                // whose head is one of the SPECIAL symbols (`pair`, `exp`, `inv`,
                // `pmult`, `diff`, `one`, `natOne`, `dhNeutral`) does NOT view as
                // `FAppNoEq` (Term/Raw.hs) — it views as its own
                // constructor (`FPair`, `FExp`, …).  None of those match the
                // `FAppNoEq fs ts` case (Typing.hs), so they fall through to
                // the polymorphic `FApp fs ts <- viewTerm t` branch (Typing.hs)
                // which types arguments with `Nothing` and learns NO function
                // type.  Crucially this means pairs (`<a,b>`) do NOT back-propagate
                // an argument type onto `a`/`b` — matching HS, which keeps
                // tuple-component variables untyped.
                FunSym::NoEq(fs) if !fs.is_view_term2_special() => {
                    let n = fs.arity;
                    // HS keys the typing environment by `NoEqUser fs`
                    // (Typing.hs).
                    let key = UserDefinedSym::NoEqUser(*fs);
                    // First pass: refine output type from target.
                    let (intypes1, outtype1) = get_fun(env, n, &key);
                    let mintype1 = sqcap_term(t, &outtype1, tt)?;
                    insert_fun(env, &key, (intypes1.clone(), mintype1))?;
                    // Type args (discard results, just to learn input types).
                    let mut ptypes: Vec<SapicType> = Vec::with_capacity(args.len());
                    for (a, want) in args.iter().zip(intypes1.iter()) {
                        let (_, ty) = type_with(env, a, want)?;
                        ptypes.push(ty);
                    }
                    // Recompute output type, having learnt arg types.
                    let (intypes2, outtype2) = get_fun(env, n, &key);
                    let mintype2 = sqcap_term(t, &outtype2, tt)?;
                    insert_fun(env, &key, (ptypes, mintype2))?;
                    // Type args for real.
                    let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(args.len());
                    let mut ptypes2: Vec<SapicType> = Vec::with_capacity(args.len());
                    for (a, want) in args.iter().zip(intypes2.iter()) {
                        let (a_new, ty) = type_with(env, a, want)?;
                        ts_new.push(a_new);
                        ptypes2.push(ty);
                    }
                    insert_fun(env, &key, (ptypes2, outtype2.clone()))?;
                    Ok((tamarin_term::term::f_app(*sym, ts_new), outtype2))
                }
                // list / AC / C symbol: polymorphic, type args with Nothing.
                _ => {
                    let mut ts_new = Vec::with_capacity(args.len());
                    for a in args.iter() {
                        let (a_new, _) = type_with(env, a, &None)?;
                        ts_new.push(a_new);
                    }
                    Ok((tamarin_term::term::f_app(*sym, ts_new), None))
                }
            }
        }
        // Constant literal: never occurs as the variable/funapp cases; type Nothing.
        VTerm::Lit(Lit::Con(_)) => Ok((t.clone(), None)),
    }
}

fn get_fun(env: &TypingEnvironment, n: usize, fs: &UserDefinedSym) -> (Vec<SapicType>, SapicType) {
    env.funs
        .get(fs)
        .cloned()
        .unwrap_or_else(|| default_function_type(n))
}

fn insert_fun(
    env: &mut TypingEnvironment,
    fs: &UserDefinedSym,
    new_ty: SapicFunType,
) -> Result<(), WfError> {
    let merged = match env.funs.get(fs) {
        None => new_ty,
        Some(old) => merge_fun_types(&new_ty, old)
            .ok_or_else(|| WfError::FunctionMerge(*fs, new_ty, old.clone()))?,
    };
    env.funs.insert(*fs, merged);
    Ok(())
}

fn merge_fun_types(a: &SapicFunType, b: &SapicFunType) -> Option<SapicFunType> {
    let ins =
        a.0.iter()
            .zip(b.0.iter())
            .map(|(x, y)| sqcap(x, y))
            .collect::<Option<Vec<_>>>()?;
    Some((ins, sqcap(&a.1, &b.1)?))
}

/// `typeProcess` (Typing.hs) via `traverseProcess`
/// (Sapic/Process.hs):
///   1. `fAct`/`fComb` — insert this node's bound vars (PRE-order, on the way
///      down);
///   2. recurse into the subtree (`p''<- traverseProcess … p'`);
///   3. `gAct`/`gComb` — reconstruct THIS node's terms (`typeWith'`), POST-order,
///      i.e. AFTER the whole subtree has been typed.
///
/// The post-order step (3) is what BACK-PROPAGATES a type learned deeper in the
/// process onto an earlier term: e.g. with `f(bitstring):bitstring`, typing
/// `out(y); out(f(y))` learns `y:bitstring` from `out(f(y))` (deeper) into the
/// shared `vars` env, and the earlier `out(y)` — reconstructed afterwards — then
/// renders `out(y:bitstring)`.  A pre-order single pass would miss this.
///
/// A `WFerror` from step 3 is rethrown as `ProcessNotWellformed` with the
/// node over its typed subprocess (`typeWith'`'s `handleEx`); the others
/// escape bare.
fn type_process(env: &mut TypingEnvironment, p: &PlainProcess) -> Result<PlainProcess, String> {
    match p {
        Process::Null(ann) => Ok(Process::Null(ann.clone())),
        Process::Action(ac, ann, body) => {
            // 1. fAct: insert bound vars (with their declared types).
            for v in bindings_act(ac) {
                insert_var(env, &v).map_err(|e| e.to_string())?;
            }
            // 2. recurse into the subtree FIRST (learns deeper types into `env`).
            let body1 = type_process(env, body)?;
            // 3. gAct: type the action's terms, with the now-complete `env`.
            let ac1 = type_action(env, ac).map_err(|e| {
                let node = Process::Action(ac.clone(), ann.clone(), Box::new(body1.clone()));
                process_not_wellformed(&e, &node)
            })?;
            // The `gAct ac@(Event ..)` case (Typing.hs) types the original
            // arguments a second time for the `events` map.  The map is not
            // kept, but that typing still updates `env` and can fail.
            if let SapicAction::Event(f) = ac {
                for t in f.terms.iter() {
                    type_with(env, t, &None).map_err(|e| e.to_string())?;
                }
            }
            Ok(Process::Action(ac1, ann.clone(), Box::new(body1)))
        }
        Process::Comb(c, ann, l, r) => {
            // 1. fComb: insert bound vars.
            for v in bindings_comb(c) {
                insert_var(env, &v).map_err(|e| e.to_string())?;
            }
            // 2. recurse into BOTH children first.
            let l1 = type_process(env, l)?;
            let r1 = type_process(env, r)?;
            // 3. gComb: type this node's terms with the completed `env`.
            let c1 = type_comb(env, c).map_err(|e| {
                let node = Process::Comb(
                    c.clone(),
                    ann.clone(),
                    Box::new(l1.clone()),
                    Box::new(r1.clone()),
                );
                process_not_wellformed(&e, &node)
            })?;
            Ok(Process::Comb(c1, ann.clone(), Box::new(l1), Box::new(r1)))
        }
    }
}

/// `insertVar` (Typing.hs).
fn insert_var(env: &mut TypingEnvironment, v: &SapicLVar) -> Result<(), WfError> {
    if env.vars.contains_key(&v.var) {
        return Err(WfError::BoundTwice(v.clone()));
    }
    env.vars.insert(v.var, v.stype.clone());
    Ok(())
}

/// `traverseTermsAction (typeWith' ..) typeWithFact typeWithVar`
/// (Typing.hs).  `typeWithVar` replaces a missing type by
/// `defaultSapicType = Nothing`, so it is the identity.  `typeWithFact = return` (Typing.hs) leaves an
/// MSR's embedded `_restrict` formulas untyped, because a quantified variable
/// has no entry in `env.vars`.
fn type_action(
    env: &mut TypingEnvironment,
    a: &SapicAction<SapicLVar>,
) -> Result<SapicAction<SapicLVar>, WfError> {
    traverse_terms_action(
        |t| type_term(env, t),
        |f| Ok(f.clone()),
        |v| Ok(v.clone()),
        a,
    )
}

/// `traverseTermsComb (typeWith' ..) typeWithFact typeWithVar`
/// (Typing.hs).
fn type_comb(
    env: &mut TypingEnvironment,
    c: &ProcessCombinator<SapicLVar>,
) -> Result<ProcessCombinator<SapicLVar>, WfError> {
    traverse_terms_comb(
        |t| type_term(env, t),
        |f| Ok(f.clone()),
        |v| Ok(v.clone()),
        c,
    )
}

/// `typeWith' t = fst <$> typeWith t Nothing` (Typing.hs).
fn type_term(env: &mut TypingEnvironment, t: &SapicTerm) -> Result<SapicTerm, WfError> {
    let (t1, _) = type_with(env, t, &None)?;
    Ok(t1)
}

// =============================================================================
// initTEFromSig + type_theory orchestration
// =============================================================================

/// A user `functions:` typing declaration — the function name, its declared
/// argument types and return type (HS `SapicFunSym = (UserDefinedSym,
/// [SapicType], SapicType)`, the payload of `theoryFunctionTypingInfos`).
pub(crate) type UserFunTyping = (UserDefinedSym, Vec<SapicType>, SapicType);

/// `toSapicTerm` (Typing.hs): re-tag an `LNTerm`'s variables as
/// untyped `SapicLVar`s (a structure-preserving `fmap`).
pub(crate) fn to_sapic_term(t: &tamarin_term::lterm::LNTerm) -> SapicTerm {
    tamarin_term::term::map_lits(t, &mut |lit| match lit {
        Lit::Var(v) => Lit::Var(SapicLVar::untyped(*v)),
        Lit::Con(c) => Lit::Con(*c),
    })
}

/// `typeTermsWithEnv` (Typing.hs): type a term list against `env`,
/// ignoring unbound variables by first (re)binding every free variable of the
/// terms to `Nothing` (HS `Map.insert x Nothing` — an OVERWRITE, so a
/// previously learnt var type is reset).  Updates `env.funs` with whatever the
/// typing learns; term results are discarded.
fn type_terms_with_env(env: &mut TypingEnvironment, terms: &[SapicTerm]) -> Result<(), WfError> {
    // `freeVars = foldl (\acc x -> acc `List.union` frees x) [] (map toLNTerm
    // terms)` — the terms' variables stripped to bare `LVar`s.
    for t in terms {
        for sv in tamarin_term::vterm::vars_vterm(t) {
            env.vars.insert(sv.var, None);
        }
    }
    for t in terms {
        type_with(env, t, &None)?;
    }
    Ok(())
}

/// `typeRule` (Typing.hs): type both sides of a subterm rewrite rule
/// (`ctxtStRuleToRRule r = lhs `RRule` rhs`) via [`type_terms_with_env`].
fn type_rule(
    env: &mut TypingEnvironment,
    r: &tamarin_term::subterm_rule::CtxtStRule,
) -> Result<(), WfError> {
    let rr = r.to_rrule();
    type_terms_with_env(env, &[to_sapic_term(&rr.lhs), to_sapic_term(&rr.rhs)])
}

/// `initTEFromSig` (Typing.hs): seed every signature function symbol —
/// the free ones (`stFunSyms`) with `defaultFunctionType` of their arity and the
/// user-defined AC ones (`stACFunSyms`) with `defaultFunctionType 2` — THEN
/// overlay the user-declared function typings (`withUserDefinedFuns`,
/// Typing.hs).  The user typings carry the declared argument / return types
/// (e.g. `f(bitstring):bitstring`) that `typeWith` propagates onto the bound
/// variables.  Finally `foldM typeRule initTE sigRules` types every subterm
/// rewrite rule (`stRules`) of the signature, so declared function types
/// propagate through the theory's equations into `funs` (and equation-side
/// variables remain in `vars` — HS clears `vars` per process, not here).
///
/// This is the environment `typeTheoryEnv` seeds before threading it through
/// every process (Typing.hs).
pub(crate) fn init_te_from_sig(
    maude_sig: &tamarin_term::maude_sig::MaudeSig,
    user_fun_typings: &[UserFunTyping],
) -> Result<TypingEnvironment, String> {
    let mut funs: BTreeMap<UserDefinedSym, (Vec<SapicType>, SapicType)> = BTreeMap::new();
    for fs in &maude_sig.st_fun_syms {
        funs.insert(
            UserDefinedSym::NoEqUser(*fs),
            default_function_type(fs.arity),
        );
    }
    // AC symbols are binary, so their default type is `defaultFunctionType 2`.
    for fs in &maude_sig.st_ac_fun_syms {
        funs.insert(UserDefinedSym::AcFctUser(*fs), default_function_type(2));
    }
    // `withUserDefinedFuns`: overlay declared types onto the declared symbol.
    // HS keys them by the declaration's own symbol; the port looks it up in
    // the signature by kind, name and arity, so the key is the actual term
    // symbol with the privacy and constructability flags the process terms
    // carry. An AC and a free symbol of the same name stay distinct.
    // HS foldr: the first declaration of a symbol wins.
    for (declared, arg_types, out_type) in user_fun_typings.iter().rev() {
        let key = match declared {
            UserDefinedSym::NoEqUser(d) => maude_sig
                .st_fun_syms
                .iter()
                .find(|fs| fs.name == d.name && fs.arity == d.arity)
                .map(|fs| UserDefinedSym::NoEqUser(*fs)),
            UserDefinedSym::AcFctUser(d) => maude_sig
                .st_ac_fun_syms
                .iter()
                .find(|fs| fs.name == d.name)
                .map(|fs| UserDefinedSym::AcFctUser(*fs)),
        };
        if let Some(key) = key {
            funs.insert(key, (arg_types.clone(), out_type.clone()));
        }
    }
    let mut env = TypingEnvironment {
        vars: BTreeMap::new(),
        funs,
    };
    // `foldM typeRule initTE sigRules` — ascending `Set` order (the RS
    // `StRules` iterates its `BTreeSet` in the same structural order).
    for r in maude_sig.st_rules.iter() {
        type_rule(&mut env, r).map_err(|e| e.to_string())?;
    }
    Ok(env)
}

/// `typeAndRenameProcess` as run inside `typeTheoryEnv` (Typing.hs):
/// `renameUnique`, clear the per-process `vars` map (`modify' (\s -> s { vars
/// = Map.empty})`), then `typeProcess` — against a SHARED environment whose
/// `funs` accumulate across processes.
pub(crate) fn type_and_rename_process_in(
    env: &mut TypingEnvironment,
    p: &PlainProcess,
) -> Result<PlainProcess, String> {
    let renamed = rename_unique(p);
    env.vars.clear();
    type_process(env, &renamed)
}

/// `S.toList (varsProc p)` (Sapic/Process.hs): every SAPIC variable that
/// occurs anywhere in `p`, as the sorted deduplicated `Set` list.  HS folds
/// the derived `Foldable`, which reaches the free variables of `Cond` and MSR
/// `_restrict` formulas too.  Two occurrences of the same `LVar` under
/// different `stype` tags are distinct elements, exactly as in HS.
pub(crate) fn vars_proc<A>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    type Vars = BTreeSet<SapicLVar>;
    fn var(v: &SapicLVar, out: &mut Vars) {
        if !out.contains(v) {
            out.insert(v.clone());
        }
    }
    fn term(t: &SapicTerm, out: &mut Vars) {
        match t {
            VTerm::Lit(Lit::Var(v)) => var(v, out),
            VTerm::Lit(Lit::Con(_)) => {}
            VTerm::App(_, args) => args.iter().for_each(|a| term(a, out)),
        }
    }
    fn formula(f: &SapicFormula, out: &mut Vars) {
        for_each_free_var(f, &mut |v| var(v, out));
    }
    fn facts(fas: &[tamarin_theory::sapic::SapicLNFact], out: &mut Vars) {
        fas.iter()
            .flat_map(|fa| fa.terms.iter())
            .for_each(|t| term(t, out));
    }
    // The terms, formulas and variables `map_terms_action`/`map_terms_comb`
    // visit; process annotations are not part of HS's `Foldable` here.
    let mut vars = Vars::new();
    for_each_process(p, &mut |node| match node {
        Process::Null(_) => {}
        Process::Action(a, _, _) => match a {
            SapicAction::New(v) => var(v, &mut vars),
            SapicAction::ChIn {
                chan,
                msg,
                match_vars,
            } => {
                chan.iter().chain([msg]).for_each(|t| term(t, &mut vars));
                match_vars.iter().for_each(|v| var(v, &mut vars));
            }
            SapicAction::ChOut { chan, msg } => {
                chan.iter().chain([msg]).for_each(|t| term(t, &mut vars));
            }
            SapicAction::Insert(t1, t2) => {
                term(t1, &mut vars);
                term(t2, &mut vars);
            }
            SapicAction::Delete(t) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
                term(t, &mut vars)
            }
            SapicAction::Event(fa) => facts(std::slice::from_ref(fa), &mut vars),
            SapicAction::Msr {
                prems,
                acts,
                concs,
                rest,
                match_vars,
            } => {
                facts(prems, &mut vars);
                facts(acts, &mut vars);
                facts(concs, &mut vars);
                rest.iter().for_each(|f| formula(f, &mut vars));
                match_vars.iter().for_each(|v| var(v, &mut vars));
            }
            SapicAction::Rep => {}
            SapicAction::ProcessCall(_, ts) => ts.iter().for_each(|t| term(t, &mut vars)),
        },
        Process::Comb(c, _, _, _) => match c {
            ProcessCombinator::Cond(f) => formula(f, &mut vars),
            ProcessCombinator::CondEq(t1, t2) => {
                term(t1, &mut vars);
                term(t2, &mut vars);
            }
            ProcessCombinator::Let {
                left,
                right,
                match_vars,
            } => {
                term(left, &mut vars);
                term(right, &mut vars);
                match_vars.iter().for_each(|v| var(v, &mut vars));
            }
            ProcessCombinator::Lookup(t, v) => {
                term(t, &mut vars);
                var(v, &mut vars);
            }
            ProcessCombinator::Parallel | ProcessCombinator::Ndc => {}
        },
    });
    vars.into_iter().collect()
}

/// The theory's `FunctionTypingInfo` items (HS `theoryFunctionTypingInfos`,
/// TheoryObject.hs) as the `(name, arg_types, out_type)` triples
/// [`init_te_from_sig`] overlays.  Plain `f/2` declarations carry `Nothing`
/// types (the `defaultFunctionType`), which the typing env already holds — so
/// they are harmless overlays.
pub(crate) fn collect_user_fun_typings(thy: &tamarin_theory::theory::Theory) -> Vec<UserFunTyping> {
    thy.function_typing_infos()
        .map(|fs| (fs.sym, fs.arg_types.clone(), fs.out_type.clone()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::NoEqSym;

    /// `initTEFromSig`'s `foldM typeRule initTE sigRules` (Typing.hs): typing the signature's subterm rewrite rules propagates a
    /// DECLARED function type through an equation onto another symbol.  Here
    /// `g(f(x)) = x` with `f(bitstring):bitstring` teaches `g` the argument
    /// type `bitstring` (from `f`'s output type).
    #[test]
    fn init_te_from_sig_types_signature_equations() {
        use tamarin_term::function_symbols::{Constructability, FunSym, Privacy};
        use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
        use tamarin_term::term::f_app;

        let f = NoEqSym::new(
            b"f".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let g = NoEqSym::new(
            b"g".to_vec(),
            1,
            Privacy::Public,
            Constructability::Constructor,
        );
        let mut sig = tamarin_term::maude_sig::MaudeSig::default();
        sig.st_fun_syms.insert(f);
        sig.st_fun_syms.insert(g);
        let x = LVar::new("x", LSort::Msg, 0);
        let lhs: tamarin_term::lterm::LNTerm = f_app(
            FunSym::NoEq(g),
            vec![f_app(FunSym::NoEq(f), vec![var_term(x)])],
        );
        sig.st_rules.insert(CtxtStRule::new(
            lhs,
            StRhs {
                positions: vec![vec![0, 0]],
                term: var_term(x),
            },
        ));

        let env = init_te_from_sig(
            &sig,
            &[(
                UserDefinedSym::NoEqUser(f),
                vec![Some("bitstring".to_string())],
                Some("bitstring".to_string()),
            )],
        )
        .unwrap();
        assert_eq!(
            env.funs.get(&UserDefinedSym::NoEqUser(g)),
            Some(&(vec![Some("bitstring".to_string())], None)),
            "g must learn its argument type from f's declared output type"
        );
        // The equation's variable stays in `vars` (HS clears `vars` per
        // process, not in `initTEFromSig`), typed by `f`'s argument type.
        assert_eq!(env.vars.get(&x), Some(&Some("bitstring".to_string())));
    }
}
