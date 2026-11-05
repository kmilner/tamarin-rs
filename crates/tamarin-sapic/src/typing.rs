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
//! `crate::type_theory::type_theory_env`) and the per-process convenience
//! wrapper [`type_and_rename_process`].

use std::collections::BTreeMap;

use tamarin_term::function_symbols::{NoEqSym, UserDefinedSym};
use tamarin_term::lterm::{LSort, LVar, Name};
use tamarin_term::vterm::{var_term, Lit, VTerm};
use tamarin_utils::fresh::PreciseFreshState;

#[cfg(test)]
use tamarin_theory::formula::formula_frees;
use tamarin_theory::sapic::{map_process, map_terms_action, map_terms_comb, PlainProcess};
use tamarin_theory::sapic::{
    traverse_terms_action, traverse_terms_comb, Process, ProcessCombinator, SapicAction, SapicLVar,
    SapicTerm, SapicType,
};

use crate::bindings::{bindings_act, bindings_comb};
pub(crate) use tamarin_theory::sapic_scope::vars_proc;
use tamarin_theory::sapic_scope::{
    action_binder_declarations, combinator_binder_declarations, compose_renaming, rename_action,
    rename_action_binders, rename_annotation, rename_comb, rename_combinator_binders,
    vars_proc_with_annotations,
};

// =============================================================================
// renameUnique (Typing.hs)
// =============================================================================

/// `varsProc`: every SAPIC variable that occurs anywhere in `p` (HS
/// `varsProc = foldMap Data.Set.singleton`, Sapic/Process.hs — a Set, so sorted
/// and deduplicated).  We return the underlying `LVar`s used to seed the
/// avoidance state for `renameUnique`.
fn proc_lvars(p: &PlainProcess) -> Vec<LVar> {
    // `avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar)` — strip types.
    vars_proc_with_annotations(p)
        .into_iter()
        .map(|sv| sv.var)
        .collect()
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
    match p {
        Process::Null(ann) => Process::Null(ann.clone()),
        Process::Action(ac, ann, body) => {
            let ac = rename_action(subst, ac);
            let mut ann = rename_annotation(subst, ann);
            let (ren, inv) = mk_subst(fresh, &bindings_act(&ac));
            ann.back_substitution = ann.back_substitution.compose(&inv);
            let ac = rename_action_binders(&ren, &ac);
            let body = rename_unique_go(fresh, &compose_renaming(&ren, subst), body);
            Process::Action(ac, ann, Box::new(body))
        }
        Process::Comb(c, ann, l, r) => {
            let c = rename_comb(subst, c);
            let mut ann = rename_annotation(subst, ann);
            let (ren, inv) = mk_subst(fresh, &bindings_comb(&c));
            ann.back_substitution = ann.back_substitution.compose(&inv);
            let c = rename_combinator_binders(&ren, &c);
            let l = rename_unique_go(fresh, &compose_renaming(&ren, subst), l);
            let r = rename_unique_go(fresh, subst, r);
            Process::Comb(c, ann, Box::new(l), Box::new(r))
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
    let avoid: Vec<(String, u64)> = proc_lvars(p)
        .into_iter()
        .map(|lv| (lv.name.to_string(), lv.idx))
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
/// typing entry alongside the free ones.  `events` records, per event fact
/// tag, the inferred argument types of its LAST typed occurrence (HS
/// `Map.insert tag …`, Typing.hs — later events overwrite earlier ones).
/// `events` has no RS reader: its consumer is `loadHeaders`'
/// `event e(t1,…)` emission (Export/Sapic.hs), part of the unported
/// ProVerif / DeepSec export backends.
pub struct TypingEnvironment {
    pub vars: BTreeMap<LVar, SapicType>,
    pub funs: BTreeMap<UserDefinedSym, (Vec<SapicType>, SapicType)>,
    pub events: BTreeMap<tamarin_theory::fact::FactTag, Vec<SapicType>>,
}

/// `smallerType` (Typing.hs).
fn smaller_type(t1: &SapicType, t2: &SapicType) -> bool {
    match (t1, t2) {
        (_, None) => true,
        (Some(a), Some(b)) => a == b,
        (None, Some(_)) => false,
    }
}

/// `sqcap` (Typing.hs): more specific of two types, error if they clash.
fn sqcap(t1: &SapicType, t2: &SapicType) -> Result<SapicType, String> {
    if smaller_type(t1, t2) {
        Ok(t1.clone())
    } else if smaller_type(t2, t1) {
        Ok(t2.clone())
    } else {
        Err(format!("Cannot merge types {t1:?} and {t2:?}."))
    }
}

/// `sqHandler` adds the offending term to type conflicts during `typeWith`.
fn sqcap_for_term(
    t: &SapicTerm,
    actual: &SapicType,
    expected: &SapicType,
) -> Result<SapicType, String> {
    sqcap(actual, expected).map_err(|_| {
        format!(
            "Typing error: expected term {} to have type {expected:?}, but found {actual:?}",
            tamarin_term::pretty::pretty_nterm(t).render(),
        )
    })
}

/// `defaultFunctionType n = (replicate n Nothing, Nothing)` (Typing.hs).
fn default_function_type(n: usize) -> (Vec<SapicType>, SapicType) {
    (vec![None; n], None)
}

/// True iff `fs` is a `viewTerm2`-SPECIAL NoEq symbol (Term/Raw.hs):
/// `pair`, `exp`, `pmult`, `diff`, `inv`, `one`, `natOne`, `dhNeutral`.  HS's
/// `viewTerm2` renders these as dedicated constructors (`FPair`/`FExp`/…) rather
/// than `FAppNoEq`, so `typeWith` treats them via the polymorphic `viewTerm`
/// branch (no function-type learning / no argument back-propagation).
#[allow(clippy::nonminimal_bool)] // intentional per-symbol -> arity enumeration
fn is_special_viewterm2_sym(fs: &NoEqSym) -> bool {
    use tamarin_term::function_symbols::{
        DH_NEUTRAL_SYM_STRING, DIFF_SYM_STRING, EXP_SYM_STRING, INV_SYM_STRING, NAT_ONE_SYM_STRING,
        ONE_SYM_STRING, PMULT_SYM_STRING,
    };
    let n = fs.name;
    (n == b"pair" && fs.arity == 2)
        || (n == EXP_SYM_STRING && fs.arity == 2)
        || (n == PMULT_SYM_STRING && fs.arity == 2)
        || (n == DIFF_SYM_STRING && fs.arity == 2)
        || (n == INV_SYM_STRING && fs.arity == 1)
        || (n == ONE_SYM_STRING && fs.arity == 0)
        || (n == NAT_ONE_SYM_STRING && fs.arity == 0)
        || (n == DH_NEUTRAL_SYM_STRING && fs.arity == 0)
}

/// `typeWith` (Typing.hs).  Types term `t` against target `tt`,
/// returning the typed term and its inferred type, updating `env`.
fn type_with(
    env: &mut TypingEnvironment,
    t: &SapicTerm,
    tt: &SapicType,
) -> Result<(SapicTerm, SapicType), String> {
    match t {
        VTerm::Lit(Lit::Var(v)) => {
            let lvar = &v.var;
            // CASE: variable.
            let stype = if lvar.sort == LSort::Pub {
                None
            } else {
                match env.vars.get(lvar) {
                    None => return Err(format!("The variable(s) {lvar} are not bound.")),
                    Some(ty) => ty.clone(),
                }
            };
            let merged = sqcap_for_term(t, &stype, tt)?;
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
                FunSym::NoEq(fs) if !is_special_viewterm2_sym(fs) => {
                    let n = fs.arity;
                    // HS keys the typing environment by `NoEqUser fs`
                    // (Typing.hs).
                    let key = UserDefinedSym::NoEqUser(*fs);
                    // First pass: refine output type from target.
                    let (intypes1, outtype1) = get_fun(env, n, &key);
                    let mintype1 = sqcap_for_term(t, &outtype1, tt)?;
                    insert_fun(env, &key, (intypes1.clone(), mintype1))?;
                    // Type args (discard results, just to learn input types).
                    let ts: Vec<SapicTerm> = args.to_vec();
                    let mut ptypes: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes1.iter()) {
                        let (_, ty) = type_with(env, a, want)?;
                        ptypes.push(ty);
                    }
                    // Recompute output type, having learnt arg types.
                    let (intypes2, outtype2) = get_fun(env, n, &key);
                    let mintype2 = sqcap_for_term(t, &outtype2, tt)?;
                    insert_fun(env, &key, (ptypes, mintype2))?;
                    // Type args for real.
                    let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(ts.len());
                    let mut ptypes2: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes2.iter()) {
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
    new_ty: (Vec<SapicType>, SapicType),
) -> Result<(), String> {
    match env.funs.get(fs).cloned() {
        None => {
            env.funs.insert(*fs, new_ty);
            Ok(())
        }
        Some(old) => {
            let merged = merge_fun_types(&new_ty, &old)?;
            env.funs.insert(*fs, merged);
            Ok(())
        }
    }
}

fn merge_fun_types(
    a: &(Vec<SapicType>, SapicType),
    b: &(Vec<SapicType>, SapicType),
) -> Result<(Vec<SapicType>, SapicType), String> {
    let mut ins = Vec::with_capacity(a.0.len());
    for (x, y) in a.0.iter().zip(b.0.iter()) {
        ins.push(sqcap(x, y)?);
    }
    let out = sqcap(&a.1, &b.1)?;
    Ok((ins, out))
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
fn type_process(env: &mut TypingEnvironment, p: &PlainProcess) -> Result<PlainProcess, String> {
    let typed = type_process_go(env, p)?;
    let final_var = |v: &SapicLVar| {
        SapicLVar::new(
            v.var,
            env.vars
                .get(&v.var)
                .cloned()
                .unwrap_or_else(|| v.stype.clone()),
        )
    };
    let final_term = |t: &SapicTerm| {
        tamarin_term::term::map_lits(t, &mut |lit| match lit {
            Lit::Var(v) => Lit::Var(final_var(v)),
            Lit::Con(c) => Lit::Con(*c),
        })
    };
    // An earlier action can refine a variable after reconstructing its
    // continuation. Apply final types everywhere except quantified formulas.
    Ok(map_process(
        &typed,
        &mut |a| map_terms_action(final_term, |f| f.clone(), final_var, a),
        &mut |c| map_terms_comb(final_term, |f| f.clone(), final_var, c),
        &mut |ann| {
            let mut ann = ann.clone();
            ann.location = ann.location.as_ref().map(final_term);
            ann
        },
    ))
}

fn type_process_go(env: &mut TypingEnvironment, p: &PlainProcess) -> Result<PlainProcess, String> {
    match p {
        Process::Null(ann) => Ok(Process::Null(ann.clone())),
        Process::Action(ac, ann, body) => {
            // 1. fAct: insert bound vars (with their declared types).
            insert_declarations(env, action_binder_declarations(ac))?;
            // 2. recurse into the subtree FIRST (learns deeper types into `env`).
            let body1 = type_process_go(env, body)?;
            // 3. gAct: type the action's terms, with the now-complete `env`.
            let ac1 = type_action(env, ac)?;
            // The `gAct ac@(Event (Fact tag _ ts))` case (Typing.hs):
            // after `traverseTermsAction` produced the typed action, the
            // ORIGINAL argument terms are typed a second time (`argTypes <-
            // mapM (`typeWith` Nothing) ts`) and their result TYPES recorded
            // in the `events` map keyed by the fact tag.
            if let SapicAction::Event(f) = ac {
                let mut arg_types = Vec::with_capacity(f.terms.len());
                for t in f.terms.iter() {
                    let (_, ty) = type_with(env, t, &None)?;
                    arg_types.push(ty);
                }
                env.events.insert(f.tag, arg_types);
            }
            Ok(Process::Action(ac1, ann.clone(), Box::new(body1)))
        }
        Process::Comb(c, ann, l, r) => {
            // 1. fComb: insert bound vars.
            insert_declarations(env, combinator_binder_declarations(c))?;
            // 2. recurse into BOTH children first.
            let l1 = type_process_go(env, l)?;
            let r1 = type_process_go(env, r)?;
            // 3. gComb: type this node's terms with the completed `env`.
            let c1 = type_comb(env, c)?;
            Ok(Process::Comb(c1, ann.clone(), Box::new(l1), Box::new(r1)))
        }
    }
}

/// `insertVar` (Typing.hs).
fn insert_declarations(env: &mut TypingEnvironment, vars: Vec<SapicLVar>) -> Result<(), String> {
    let mut local: BTreeMap<LVar, SapicType> = BTreeMap::new();
    for v in vars {
        let ty = match local.get(&v.var) {
            None => v.stype,
            Some(previous) => sqcap(previous, &v.stype).map_err(|_| {
                format!(
                    "Typing error: expected term {} to have type {:?}, but found {:?}",
                    v.var, previous, v.stype,
                )
            })?,
        };
        local.insert(v.var, ty);
    }
    for (var, ty) in local {
        insert_var(env, &SapicLVar::new(var, ty))?;
    }
    Ok(())
}

fn insert_var(env: &mut TypingEnvironment, v: &SapicLVar) -> Result<(), String> {
    if env.vars.contains_key(&v.var) {
        return Err(format!("variable bound twice: {:?}", v.var));
    }
    env.vars.insert(v.var, v.stype.clone());
    Ok(())
}

/// `typeWithVar` (Typing.hs): a standalone bound variable is already
/// correctly typed; if untyped, give it `defaultSapicType` (= `Nothing`).
fn type_with_var(v: &SapicLVar) -> SapicLVar {
    match &v.stype {
        None => SapicLVar::new(v.var, None),
        Some(_) => v.clone(),
    }
}

/// `traverseTermsAction (typeWith' ..) typeWithFact typeWithVar`
/// (Typing.hs).  `typeWithFact = return` (Typing.hs) leaves an
/// MSR's embedded `_restrict` formulas untyped, because a quantified variable
/// has no entry in `env.vars`.
fn type_action(
    env: &mut TypingEnvironment,
    a: &SapicAction<SapicLVar>,
) -> Result<SapicAction<SapicLVar>, String> {
    traverse_terms_action(
        |t| type_term(env, t),
        |f| Ok(f.clone()),
        |v| Ok(type_with_var(v)),
        a,
    )
}

/// `traverseTermsComb (typeWith' ..) typeWithFact typeWithVar`
/// (Typing.hs).
fn type_comb(
    env: &mut TypingEnvironment,
    c: &ProcessCombinator<SapicLVar>,
) -> Result<ProcessCombinator<SapicLVar>, String> {
    traverse_terms_comb(
        |t| type_term(env, t),
        |f| Ok(f.clone()),
        |v| Ok(type_with_var(v)),
        c,
    )
}

/// `typeWith' t = fst <$> typeWith t Nothing` (Typing.hs).
fn type_term(env: &mut TypingEnvironment, t: &SapicTerm) -> Result<SapicTerm, String> {
    let (t1, _) = type_with(env, t, &None)?;
    Ok(t1)
}

// =============================================================================
// initTEFromSig + type_theory orchestration
// =============================================================================

/// A user `functions:` typing declaration — the function name, its declared
/// argument types and return type (HS `SapicFunSym = (UserDefinedSym,
/// [SapicType], SapicType)`, the payload of `theoryFunctionTypingInfos`).
pub(crate) type UserFunTyping = (String, Vec<SapicType>, SapicType);

/// `toSapicTerm` (Typing.hs): re-tag an `LNTerm`'s variables as
/// untyped `SapicLVar`s (a structure-preserving `fmap`).
fn to_sapic_term(t: &tamarin_term::lterm::LNTerm) -> SapicTerm {
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
fn type_terms_with_env(env: &mut TypingEnvironment, terms: &[SapicTerm]) -> Result<(), String> {
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
) -> Result<(), String> {
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
    // `withUserDefinedFuns`: overlay declared types onto the matching signature
    // symbol (matched by name + arity, so the BTreeMap key — the actual term
    // symbol — is preserved exactly, keeping the privacy/constructability flags
    // that the process terms carry).  A declaration matches a free symbol first
    // and an AC symbol (always binary) otherwise.
    // HS foldr: the first declaration of a name wins.
    for (name, arg_types, out_type) in user_fun_typings.iter().rev() {
        let arity = arg_types.len();
        let key = maude_sig
            .st_fun_syms
            .iter()
            .find(|fs| fs.name == name.as_bytes() && fs.arity == arity)
            .map(|fs| UserDefinedSym::NoEqUser(*fs))
            .or_else(|| {
                if arity != 2 {
                    return None;
                }
                maude_sig
                    .st_ac_fun_syms
                    .iter()
                    .find(|fs| fs.name == name.as_bytes())
                    .map(|fs| UserDefinedSym::AcFctUser(*fs))
            });
        if let Some(key) = key {
            funs.insert(key, (arg_types.clone(), out_type.clone()));
        }
    }
    let mut env = TypingEnvironment {
        vars: BTreeMap::new(),
        funs,
        events: BTreeMap::new(),
    };
    // `foldM typeRule initTE sigRules` — ascending `Set` order (the RS
    // `StRules` iterates its `BTreeSet` in the same structural order).
    for r in maude_sig.st_rules.iter() {
        type_rule(&mut env, r)?;
    }
    Ok(env)
}

/// `typeAndRenameProcess` as run inside `typeTheoryEnv` (Typing.hs):
/// `renameUnique`, clear the per-process `vars` map (`modify' (\s -> s { vars
/// = Map.empty})`), then `typeProcess` — against a SHARED environment whose
/// `funs`/`events` accumulate across processes.
pub(crate) fn type_and_rename_process_in(
    env: &mut TypingEnvironment,
    p: &PlainProcess,
) -> Result<PlainProcess, String> {
    let renamed = rename_unique(p);
    env.vars.clear();
    type_process(env, &renamed)
}

/// Single-process convenience wrapper: a fresh environment per call.
/// Equivalent to HS `typeTheory` on a theory holding exactly one process.
pub(crate) fn type_and_rename_process(
    maude_sig: &tamarin_term::maude_sig::MaudeSig,
    user_fun_typings: &[UserFunTyping],
    p: &PlainProcess,
) -> Result<PlainProcess, String> {
    let mut env = init_te_from_sig(maude_sig, user_fun_typings)?;
    type_and_rename_process_in(&mut env, p)
}

/// The theory's `FunctionTypingInfo` items (HS `theoryFunctionTypingInfos`,
/// TheoryObject.hs) as the `(name, arg_types, out_type)` triples
/// [`init_te_from_sig`] overlays.  Plain `f/2` declarations carry `Nothing`
/// types (the `defaultFunctionType`), which the typing env already holds — so
/// they are harmless overlays.
pub(crate) fn collect_user_fun_typings(thy: &tamarin_theory::theory::Theory) -> Vec<UserFunTyping> {
    thy.function_typing_infos()
        .map(|fs| {
            (
                String::from_utf8_lossy(fs.sym.name()).into_owned(),
                fs.arg_types.clone(),
                fs.out_type.clone(),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    fn slv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(|s| s.to_string()))
    }

    #[test]
    fn rename_unique_mints_x1_for_new_x0() {
        // new x:lol; 0  with x at index 0 → x.1
        let new = Process::Action(
            SapicAction::New(slv("x", 0, Some("lol"))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let r = rename_unique(&new);
        if let Process::Action(SapicAction::New(v), _, _) = r {
            assert_eq!(v.var.idx, 1);
            assert_eq!(v.var.name, "x");
            assert_eq!(v.stype, Some("lol".to_string()));
        } else {
            panic!("expected New action");
        }
    }

    #[test]
    fn inferred_types_reach_binders_and_earlier_reconstructed_unlocks() {
        let parsed = tamarin_parser::parse_theory(
            "theory T begin functions: f(a):a process: new s; lock s; out(f(s)); unlock s end",
            &[],
        )
        .unwrap();
        let thy = tamarin_theory::elaborate::elaborate(&parsed).unwrap();
        let typed = type_and_rename_process(
            &thy.signature,
            &collect_user_fun_typings(&thy),
            thy.processes().next().unwrap(),
        )
        .unwrap();
        let vars = vars_proc(&typed);
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].stype.as_deref(), Some("a"));
        let mut keys = vec![];
        tamarin_theory::sapic::for_each_process(&typed, &mut |node| {
            if let Process::Action(SapicAction::Lock(t) | SapicAction::Unlock(t), _, _) = node {
                keys.push(t.clone());
            }
        });
        assert_eq!(keys.len(), 2);
        assert_eq!(keys[0], keys[1]);
    }

    #[test]
    fn rename_unique_renames_location_terms() {
        let mut body_ann = ProcessParsedAnnotation::empty();
        body_ann.location = Some(var_term(slv("x", 0, None)));
        let proc = Process::Action(
            SapicAction::New(slv("x", 0, None)),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Action(
                SapicAction::Rep,
                body_ann.clone(),
                Box::new(Process::Null(body_ann)),
            )),
        );

        let Process::Action(_, _, body) = rename_unique(&proc) else {
            panic!("expected New action");
        };
        assert_eq!(
            body.annotation().location,
            Some(var_term(slv("x", 1, None)))
        );
        let Process::Action(_, _, null) = *body else {
            panic!("expected replication");
        };
        // Null annotations are deliberately untouched by uniqueness renaming.
        assert_eq!(
            null.annotation().location,
            Some(var_term(slv("x", 0, None)))
        );
    }

    /// An MSR's embedded `_restrict(...)` alpha-renames with the rest of the
    /// rule body: HS maps the formula list with the SAME substitution as the
    /// fact rows (`mapTermsAction f ff fv (MSR ..) = MSR .. (fmap ff rest) ..`).
    /// A stale variable here leaks into the `process="..."` attribute AND into
    /// the generated `Restr_*` action fact's arguments.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468) for
    /// `in(k); [ ] --[ Ev(k), _restrict(k = 'b') ]-> [ ]; out('y')`:
    ///   `_restrict(k.1 = 'b')` — index 1, matching the renamed `Ev( k.1 )`.
    #[test]
    fn rename_unique_renames_msr_embedded_restriction() {
        use tamarin_theory::atom::ProtoAtom;
        use tamarin_theory::formula::ProtoFormula;

        // `k = 'b'`, with `k` the process variable the enclosing `new` binds.
        let restr = ProtoFormula::Atom(ProtoAtom::EqE(
            var_term(tamarin_term::lterm::BVar::Free(slv("k", 0, None))),
            VTerm::Lit(Lit::Con(Name::new(tamarin_term::lterm::NameTag::Pub, "b"))),
        ));
        let ev = tamarin_theory::fact::Fact::new(
            tamarin_theory::fact::FactTag::Proto(
                tamarin_theory::fact::Multiplicity::Linear,
                "Ev",
                1,
            ),
            vec![var_term(slv("k", 0, None))],
        );
        let msr = Process::Action(
            SapicAction::Msr {
                prems: Vec::new(),
                acts: vec![ev],
                concs: Vec::new(),
                rest: vec![restr],
                match_vars: std::collections::BTreeSet::new(),
            },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        // `new k; <msr>` — the binder renames `k` to `k.1` throughout the body.
        let proc = Process::Action(
            SapicAction::New(slv("k", 0, None)),
            ProcessParsedAnnotation::empty(),
            Box::new(msr),
        );

        let Process::Action(_, _, body) = rename_unique(&proc) else {
            panic!("expected New action");
        };
        let Process::Action(SapicAction::Msr { acts, rest, .. }, _, _) = *body else {
            panic!("expected MSR action");
        };
        // The action row renamed...
        assert_eq!(
            acts[0].terms[0],
            var_term(slv("k", 1, None)),
            "Ev's argument must be k.1"
        );
        // ...and so did the embedded restriction.
        assert_eq!(
            formula_frees(&rest[0]),
            vec![slv("k", 1, None)],
            "the restriction's only free variable must be k.1"
        );
    }

    /// The `gAct Event` case (Typing.hs) records the event's inferred
    /// argument types in `env.events`, keyed by the fact tag.
    #[test]
    fn typing_records_event_arg_types_in_env() {
        use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
        // new x:lol; event Run(x); 0
        let x = slv("x", 0, Some("lol"));
        let run = Fact::new(
            FactTag::Proto(Multiplicity::Linear, "Run", 1),
            vec![var_term(slv("x", 0, None))],
        );
        let proc = Process::Action(
            SapicAction::New(x),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Action(
                SapicAction::Event(run),
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Null(ProcessParsedAnnotation::empty())),
            )),
        );
        let mut env = TypingEnvironment {
            vars: BTreeMap::new(),
            funs: BTreeMap::new(),
            events: BTreeMap::new(),
        };
        type_process(&mut env, &proc).unwrap();
        assert_eq!(
            env.events
                .get(&FactTag::Proto(Multiplicity::Linear, "Run", 1)),
            Some(&vec![Some("lol".to_string())])
        );
    }

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
                "f".to_string(),
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
