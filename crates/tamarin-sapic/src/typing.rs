// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Typing` (`lib/sapic/src/Sapic/Typing.hs`) — the
//! uniqueness-renaming pass (`renameUnique`) and the lightweight type
//! inference (`typeProcess` / `typeWith`) over SAPIC processes.
//!
//! HS pipeline (`typeTheoryEnv`, Typing.hs:204-226):
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

use tamarin_theory::formula::{apply_rename, formula_frees};
use tamarin_theory::sapic::PlainProcess;
use tamarin_theory::sapic::{
    map_terms_action, map_terms_comb, traverse_terms_action, traverse_terms_comb, Process,
    ProcessCombinator, ProcessParsedAnnotation, SapicAction, SapicLVar, SapicTerm, SapicType,
};

use crate::bindings::{bindings_act, bindings_comb};

// =============================================================================
// renameUnique (Typing.hs:232-269)
// =============================================================================

/// `varsProc`: every SAPIC variable that occurs anywhere in `p` (HS
/// `varsProc = foldMap Data.Set.singleton`, Sapic/Process.hs:361-362 — a Set, so sorted
/// and deduplicated).  We return the underlying `LVar`s used to seed the
/// avoidance state for `renameUnique`.
fn proc_lvars(p: &PlainProcess) -> Vec<LVar> {
    // `avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar)` — strip types.
    vars_proc(p).into_iter().map(|sv| sv.var).collect()
}

fn collect_proc_vars<A>(
    p: &Process<A, SapicLVar>,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    tamarin_theory::sapic::for_each_process(p, &mut |node| match node {
        Process::Null(_) => {}
        Process::Action(action, _, _) => collect_action_vars(action, out),
        Process::Comb(comb, _, _, _) => collect_comb_vars(comb, out),
    });
}

fn collect_term_vars(t: &SapicTerm, out: &mut std::collections::BTreeSet<SapicLVar>) {
    for v in tamarin_term::vterm::vars_vterm(t) {
        out.insert(v);
    }
}

fn collect_fact_vars(
    f: &tamarin_theory::sapic::SapicLNFact,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    for t in f.terms.iter() {
        collect_term_vars(t, out);
    }
}

fn collect_action_vars(
    a: &SapicAction<SapicLVar>,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    match a {
        SapicAction::New(v) => {
            out.insert(v.clone());
        }
        SapicAction::Event(f) => collect_fact_vars(f, out),
        SapicAction::ChOut { chan, msg } => {
            if let Some(c) = chan {
                collect_term_vars(c, out);
            }
            collect_term_vars(msg, out);
        }
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => {
            if let Some(c) = chan {
                collect_term_vars(c, out);
            }
            collect_term_vars(msg, out);
            for v in match_vars {
                out.insert(v.clone());
            }
        }
        SapicAction::Insert(a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        SapicAction::Delete(t) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
            collect_term_vars(t, out)
        }
        SapicAction::ProcessCall(_, ts) => {
            for t in ts {
                collect_term_vars(t, out);
            }
        }
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            ..
        } => {
            for f in prems.iter().chain(acts).chain(concs) {
                collect_fact_vars(f, out);
            }
            // HS's derived `Foldable (SapicAction v)` reaches the `iRest ::
            // [SapicNFormula v]` field too, so `varsProc` counts the embedded
            // `_restrict` formulas' FREE variables (bound `BVar` quantifier vars
            // are not `v`).  They seed the `renameUnique` avoidance set, so a
            // variable occurring ONLY in a restriction still shifts the fresh
            // indices minted for the rest of the process.
            for f in rest {
                for v in formula_frees(f) {
                    out.insert(v);
                }
            }
        }
        SapicAction::Rep => {}
    }
}

fn collect_comb_vars(
    c: &ProcessCombinator<SapicLVar>,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            collect_term_vars(t, out);
            out.insert(v.clone());
        }
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        } => {
            collect_term_vars(left, out);
            collect_term_vars(right, out);
            for v in match_vars {
                out.insert(v.clone());
            }
        }
        ProcessCombinator::CondEq(a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        // HS `varsProc = foldMap singleton` over the derived `Foldable (Process)`
        // folds the `v` occurrences inside `Cond (SapicNFormula v)` too — i.e.
        // the formula's FREE variables (bound `BVar` quantifier vars are not
        // `v`).  Collect them so they seed the `renameUnique` avoidance set and
        // reach `type_process_def`'s formals, which print with their tag.
        ProcessCombinator::Cond(f) => {
            for v in formula_frees(f) {
                out.insert(v);
            }
        }
        ProcessCombinator::Parallel | ProcessCombinator::Ndc => {}
    }
}

/// Rename a SAPIC term's variables according to `subst` (`LVar -> LVar`),
/// preserving each variable's SAPIC type.  HS `renameUnique'` uses
/// `apply subst`, where `subst` only ever maps to `varTerm v'` (a renaming),
/// so a structural LVar→LVar rewrite is faithful.
fn rename_term(subst: &BTreeMap<LVar, LVar>, t: &SapicTerm) -> SapicTerm {
    tamarin_term::term::map_lits(t, &mut |lit| match lit {
        Lit::Var(sv) => {
            let new_lv = subst.get(&sv.var).copied().unwrap_or(sv.var);
            Lit::Var(SapicLVar::new(new_lv, sv.stype.clone()))
        }
        Lit::Con(c) => Lit::Con(*c),
    })
}

fn rename_sv(subst: &BTreeMap<LVar, LVar>, sv: &SapicLVar) -> SapicLVar {
    let new_lv = subst.get(&sv.var).copied().unwrap_or(sv.var);
    SapicLVar::new(new_lv, sv.stype.clone())
}

fn rename_action(
    subst: &BTreeMap<LVar, LVar>,
    a: &SapicAction<SapicLVar>,
) -> SapicAction<SapicLVar> {
    map_terms_action(
        |t| rename_term(subst, t),
        // HS `apply subst` on a formula (Sapic/Process.hs:319-321) renames the
        // free variables of an embedded `_restrict` along with the fact rows
        // that mention them; a bound De Bruijn index and its binder hint cross
        // unchanged.
        |f| apply_rename(f.clone(), &mut |v| rename_sv(subst, v)),
        |v| rename_sv(subst, v),
        a,
    )
}

fn rename_comb(
    subst: &BTreeMap<LVar, LVar>,
    c: &ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    map_terms_comb(
        |t| rename_term(subst, t),
        |f| apply_rename(f.clone(), &mut |v| rename_sv(subst, v)),
        |v| rename_sv(subst, v),
        c,
    )
}

/// `renameUnique'` (Typing.hs:242-261). `fresh` mints fresh indices.
/// For each binder we (1) mint a fresh copy of every bound variable, (2) record
/// the inverse renaming in the node's `back_substitution` annotation, and
/// (3) descend with the extended substitution.
fn rename_unique_go(fresh: &mut PreciseFreshState, p: &PlainProcess) -> PlainProcess {
    // Materialize the process once; carry composed renamings instead of
    // repeatedly copying and rewriting every remaining suffix.
    let mut out = p.clone();
    crate::process_walk::walk_mut(
        &mut out,
        BTreeMap::<LVar, LVar>::new(),
        |node, inherited| {
            let (ann, new_subst, inv) = match node {
                Process::Null(ann) => {
                    *ann = rename_annotation(inherited, ann);
                    return Ok::<_, std::convert::Infallible>(true);
                }
                Process::Action(ac, ann, _) => {
                    *ac = rename_action(inherited, ac);
                    let (new_subst, inv) = mk_subst(fresh, &bindings_act(ac));
                    if !new_subst.is_empty() {
                        *ac = rename_action(&new_subst, ac);
                    }
                    (ann, new_subst, inv)
                }
                Process::Comb(c, ann, _, _) => {
                    *c = rename_comb(inherited, c);
                    let (new_subst, inv) = mk_subst(fresh, &bindings_comb(c));
                    if !new_subst.is_empty() {
                        *c = rename_comb(&new_subst, c);
                    }
                    (ann, new_subst, inv)
                }
            };
            // The node's own location receives only the inherited renaming.
            *ann = rename_annotation(inherited, ann);
            ann.back_substitution = ann.back_substitution.compose(&inv);
            if !new_subst.is_empty() {
                // Function composition, not map union: shadowed binders can
                // rename an earlier substitution's image a second time.
                for image in inherited.values_mut() {
                    *image = new_subst.get(image).copied().unwrap_or(*image);
                }
                for (key, value) in new_subst {
                    inherited.entry(key).or_insert(value);
                }
            }
            Ok(true)
        },
    )
    .unwrap();
    out
}

fn rename_annotation(
    subst: &BTreeMap<LVar, LVar>,
    ann: &ProcessParsedAnnotation,
) -> ProcessParsedAnnotation {
    ann.clone()
        .map_location(|location| rename_term(subst, &location))
}

/// `mkSubst` (Typing.hs:266-272): for each bound variable mint a fresh LVar
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

/// `renameUnique` (Typing.hs:232-240): seed the fresh-var supply so it avoids
/// every variable already present, then run `renameUnique'` from the identity
/// substitution.
pub(crate) fn rename_unique(p: &PlainProcess) -> PlainProcess {
    let avoid: Vec<(String, u64)> = proc_lvars(p)
        .into_iter()
        .map(|lv| (lv.name.to_string(), lv.idx))
        .collect();
    let mut fresh = PreciseFreshState::avoid_precise(avoid);
    rename_unique_go(&mut fresh, p)
}

// =============================================================================
// Type inference (typeProcess / typeWith, Typing.hs:73-200)
// =============================================================================

/// `TypingEnvironment` (Typing.hs:55-59).
/// `funs` is keyed by `UserDefinedSym`, so a user-defined AC symbol has a
/// typing entry alongside the free ones.  `events` records, per event fact
/// tag, the inferred argument types of its LAST typed occurrence (HS
/// `Map.insert tag …`, Typing.hs:149 — later events overwrite earlier ones).
/// `events` has no RS reader: its consumer is `loadHeaders`'
/// `event e(t1,…)` emission (Export.hs:2743-2754), part of the unported
/// ProVerif / DeepSec export backends.
pub struct TypingEnvironment {
    pub vars: BTreeMap<LVar, SapicType>,
    pub funs: BTreeMap<UserDefinedSym, (Vec<SapicType>, SapicType)>,
    pub events: BTreeMap<tamarin_theory::fact::FactTag, Vec<SapicType>>,
}

/// `smallerType` (Typing.hs:32-35).
fn smaller_type(t1: &SapicType, t2: &SapicType) -> bool {
    match (t1, t2) {
        (_, None) => true,
        (Some(a), Some(b)) => a == b,
        (None, Some(_)) => false,
    }
}

/// `sqcap` (Typing.hs:45-49): more specific of two types, error if they clash.
fn sqcap(t1: &SapicType, t2: &SapicType) -> Result<SapicType, String> {
    if smaller_type(t1, t2) {
        Ok(t1.clone())
    } else if smaller_type(t2, t1) {
        Ok(t2.clone())
    } else {
        Err(format!("Cannot merge types {t1:?} and {t2:?}."))
    }
}

/// `defaultFunctionType n = (replicate n Nothing, Nothing)` (Typing.hs:52-53, see line 53).
fn default_function_type(n: usize) -> (Vec<SapicType>, SapicType) {
    (vec![None; n], None)
}

/// True iff `fs` is a `viewTerm2`-SPECIAL NoEq symbol (Term/Raw.hs:191-204):
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

/// `typeWith` (Typing.hs:63-124).  Types term `t` against target `tt`,
/// returning the typed term and its inferred type, updating `env`.
fn type_with(
    env: &mut TypingEnvironment,
    t: &SapicTerm,
    tt: &SapicType,
) -> Result<(SapicTerm, SapicType), String> {
    // Cache only visits that learned nothing, and invalidate on every effective
    // environment mutation. Both inference passes and their error order matter.
    // First-pass typed subtrees are often reused by the second pass; omitting
    // their construction can repeat inference instead of saving work. See
    // docs/nesting-design.md for the propagation-only experiments.
    type CacheKey = (*const SapicTerm, SapicType);
    #[derive(Default)]
    struct Cache {
        generation: usize,
        values: tamarin_utils::FastMap<CacheKey, (SapicTerm, SapicType)>,
    }
    impl Cache {
        fn changed(&mut self) {
            self.generation += 1;
            self.values.clear();
        }
    }

    fn visit(
        env: &mut TypingEnvironment,
        t: &SapicTerm,
        tt: &SapicType,
        cache: &mut Cache,
        cache_result: bool,
    ) -> Result<(SapicTerm, SapicType), String> {
        tamarin_utils::stack::ensure_sufficient_stack(|| {
            use tamarin_term::function_symbols::FunSym;
            // The root is visited once; avoid allocating a cache entry for it.
            let key = if cache_result
                && matches!(t, VTerm::App(FunSym::NoEq(fs), _) if !is_special_viewterm2_sym(fs))
            {
                Some((std::ptr::from_ref(t), tt.clone()))
            } else {
                None
            };
            if let Some(value) = key.as_ref().and_then(|key| cache.values.get(key)) {
                return Ok(value.clone());
            }
            let generation = cache.generation;
            let result = (|| match t {
                VTerm::Lit(Lit::Var(v)) => {
                    let lvar = &v.var;
                    let stype = if lvar.sort == LSort::Pub {
                        None
                    } else {
                        match env.vars.get(lvar) {
                            None => return Err(format!("unbound variable {lvar:?}")),
                            Some(ty) => ty.clone(),
                        }
                    };
                    let merged = sqcap(&stype, tt)?;
                    if env.vars.get(lvar) != Some(&merged) {
                        env.vars.insert(*lvar, merged.clone());
                        cache.changed();
                    }
                    Ok((var_term(SapicLVar::new(*lvar, merged.clone())), merged))
                }
                VTerm::App(sym, args) => {
                    use tamarin_term::function_symbols::FunSym;
                    match sym {
                        FunSym::NoEq(fs) if !is_special_viewterm2_sym(fs) => {
                            let n = fs.arity;
                            let key = UserDefinedSym::NoEqUser(*fs);
                            let (intypes1, outtype1) = get_fun(env, n, &key);
                            let mintype1 = sqcap(&outtype1, tt)?;
                            if insert_fun(env, &key, (intypes1.clone(), mintype1))? {
                                cache.changed();
                            }
                            let ts = args;
                            let mut ptypes: Vec<SapicType> = Vec::with_capacity(ts.len());
                            for (a, want) in ts.iter().zip(intypes1.iter()) {
                                let (_, ty) = visit(env, a, want, cache, true)?;
                                ptypes.push(ty);
                            }
                            let (intypes2, outtype2) = get_fun(env, n, &key);
                            let mintype2 = sqcap(&outtype2, tt)?;
                            if insert_fun(env, &key, (ptypes, mintype2))? {
                                cache.changed();
                            }
                            let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(ts.len());
                            let mut ptypes2: Vec<SapicType> = Vec::with_capacity(ts.len());
                            for (a, want) in ts.iter().zip(intypes2.iter()) {
                                let (a_new, ty) = visit(env, a, want, cache, true)?;
                                ts_new.push(a_new);
                                ptypes2.push(ty);
                            }
                            if insert_fun(env, &key, (ptypes2, outtype2.clone()))? {
                                cache.changed();
                            }
                            Ok((tamarin_term::term::f_app(*sym, ts_new), outtype2))
                        }
                        _ => {
                            let mut ts_new = Vec::with_capacity(args.len());
                            for a in args.iter() {
                                let (a_new, _) = visit(env, a, &None, cache, true)?;
                                ts_new.push(a_new);
                            }
                            Ok((tamarin_term::term::f_app(*sym, ts_new), None))
                        }
                    }
                }
                VTerm::Lit(Lit::Con(_)) => Ok((t.clone(), None)),
            })()?;
            if generation == cache.generation
                && let Some(key) = key
            {
                cache.values.insert(key, result.clone());
            }
            Ok(result)
        })
    }
    visit(env, t, tt, &mut Cache::default(), false)
}

fn get_fun(env: &TypingEnvironment, n: usize, fs: &UserDefinedSym) -> (Vec<SapicType>, SapicType) {
    env.funs
        .get(fs)
        .cloned()
        .unwrap_or_else(|| default_function_type(n))
}

// Report effective mutations so inference can invalidate completed visits.
fn insert_fun(
    env: &mut TypingEnvironment,
    fs: &UserDefinedSym,
    new_ty: (Vec<SapicType>, SapicType),
) -> Result<bool, String> {
    let merged = match env.funs.get(fs) {
        None => new_ty,
        Some(old) => {
            let merged = merge_fun_types(&new_ty, old)?;
            if &merged == old {
                return Ok(false);
            }
            merged
        }
    };
    env.funs.insert(*fs, merged);
    Ok(true)
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

/// `typeProcess` (Typing.hs:135-168) via `traverseProcess`
/// (Sapic/Process.hs:221-234):
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
    // A false flag enters a node (register binders); true finishes it after
    // its children have updated the shared typing environment.
    let mut pending = vec![(p, false)];
    let mut output = Vec::new();
    while let Some((node, finish)) = pending.pop() {
        match node {
            Process::Null(ann) => output.push(Process::Null(ann.clone())),
            Process::Action(ac, ann, body) => {
                if !finish {
                    for v in bindings_act(ac) {
                        insert_var(env, &v)?;
                    }
                    pending.push((node, true));
                    pending.push((body, false));
                    continue;
                }
                let ac1 = type_action(env, ac)?;
                // HS Typing.hs:145-150: infer Event's original arguments a
                // second time and record their types after typing the action.
                if let SapicAction::Event(f) = ac {
                    let mut arg_types = Vec::with_capacity(f.terms.len());
                    for t in f.terms.iter() {
                        let (_, ty) = type_with(env, t, &None)?;
                        arg_types.push(ty);
                    }
                    env.events.insert(f.tag, arg_types);
                }
                let body = output.pop().expect("typed action body");
                output.push(Process::Action(ac1, ann.clone(), Box::new(body).into()));
            }
            Process::Comb(c, ann, left, right) => {
                if !finish {
                    for v in bindings_comb(c) {
                        insert_var(env, &v)?;
                    }
                    pending.push((node, true));
                    pending.push((right, false));
                    pending.push((left, false));
                    continue;
                }
                let c1 = type_comb(env, c)?;
                let right = output.pop().expect("typed right branch");
                let left = output.pop().expect("typed left branch");
                output.push(Process::Comb(
                    c1,
                    ann.clone(),
                    Box::new(left).into(),
                    Box::new(right).into(),
                ));
            }
        }
    }
    Ok(output.pop().expect("typed process"))
}

/// `insertVar` (Typing.hs:162-167).
fn insert_var(env: &mut TypingEnvironment, v: &SapicLVar) -> Result<(), String> {
    if env.vars.contains_key(&v.var) {
        return Err(format!("variable bound twice: {:?}", v.var));
    }
    env.vars.insert(v.var, v.stype.clone());
    Ok(())
}

/// `typeWithVar` (Typing.hs:158-160): a standalone bound variable is already
/// correctly typed; if untyped, give it `defaultSapicType` (= `Nothing`).
fn type_with_var(v: &SapicLVar) -> SapicLVar {
    match &v.stype {
        None => SapicLVar::new(v.var, None),
        Some(_) => v.clone(),
    }
}

/// `traverseTermsAction (typeWith' ..) typeWithFact typeWithVar`
/// (Typing.hs:145-150).  `typeWithFact = return` (Typing.hs:161) leaves an
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
/// (Typing.hs:153-155).
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

/// `typeWith' t = fst <$> typeWith t Nothing` (Typing.hs:135-168, see line 157).
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

/// `toSapicTerm` (Typing.hs:173-178): re-tag an `LNTerm`'s variables as
/// untyped `SapicLVar`s (a structure-preserving `fmap`).
fn to_sapic_term(t: &tamarin_term::lterm::LNTerm) -> SapicTerm {
    tamarin_term::term::map_lits(t, &mut |lit| match lit {
        Lit::Var(v) => Lit::Var(SapicLVar::untyped(*v)),
        Lit::Con(c) => Lit::Con(*c),
    })
}

/// `typeTermsWithEnv` (Typing.hs:128-134): type a term list against `env`,
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

/// `typeRule` (Typing.hs:179-181): type both sides of a subterm rewrite rule
/// (`ctxtStRuleToRRule r = lhs `RRule` rhs`) via [`type_terms_with_env`].
fn type_rule(
    env: &mut TypingEnvironment,
    r: &tamarin_term::subterm_rule::CtxtStRule,
) -> Result<(), String> {
    let rr = r.to_rrule();
    type_terms_with_env(env, &[to_sapic_term(&rr.lhs), to_sapic_term(&rr.rhs)])
}

/// `initTEFromSig` (Typing.hs:183-201): seed every signature function symbol —
/// the free ones (`stFunSyms`) with `defaultFunctionType` of their arity and the
/// user-defined AC ones (`stACFunSyms`) with `defaultFunctionType 2` — THEN
/// overlay the user-declared function typings (`withUserDefinedFuns`,
/// Typing.hs:195).  The user typings carry the declared argument / return types
/// (e.g. `f(bitstring):bitstring`) that `typeWith` propagates onto the bound
/// variables.  Finally `foldM typeRule initTE sigRules` types every subterm
/// rewrite rule (`stRules`) of the signature, so declared function types
/// propagate through the theory's equations into `funs` (and equation-side
/// variables remain in `vars` — HS clears `vars` per process, not here).
///
/// This is the environment `typeTheoryEnv` seeds before threading it through
/// every process (Typing.hs:207).
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

/// `typeAndRenameProcess` as run inside `typeTheoryEnv` (Typing.hs:213-216):
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

/// `S.toList (varsProc p)` (Sapic/Process.hs:361-362): every SAPIC variable that
/// occurs anywhere in `p`, as the sorted deduplicated `Set` list.  Two
/// occurrences of the same `LVar` under DIFFERENT `stype` tags are distinct
/// set elements, exactly as in HS.  Generic in the annotation, as HS's
/// `Foldable (Process ann)` is.
pub(crate) fn vars_proc<A>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    let mut set = std::collections::BTreeSet::new();
    collect_proc_vars(p, &mut set);
    set.into_iter().collect()
}

/// The theory's `FunctionTypingInfo` items (HS `theoryFunctionTypingInfos`,
/// TheoryObject.hs:368-369) as the `(name, arg_types, out_type)` triples
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
#[path = "typing_tests.rs"]
mod tests;
