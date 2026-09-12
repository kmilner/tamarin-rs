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
    map_process, map_terms_action, map_terms_comb, traverse_terms_action, traverse_terms_comb,
    Process, ProcessCombinator, ProcessParsedAnnotation, SapicAction, SapicLVar, SapicTerm,
    SapicType,
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
    let mut pending = vec![p];
    while let Some(node) = pending.pop() {
        match node {
            Process::Null(_) => {}
            Process::Action(a, _, body) => {
                collect_action_vars(a, out);
                pending.push(body);
            }
            Process::Comb(c, _, left, right) => {
                collect_comb_vars(c, out);
                pending.push(right);
                pending.push(left);
            }
        }
    }
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

/// `renameUnique'` (Typing.hs:242-261).  `subst` is the *outstanding* renaming
/// applied at this node (`apply initSubst p`); `fresh` mints fresh indices.
/// For each binder we (1) mint a fresh copy of every bound variable, (2) record
/// the inverse renaming in the node's `back_substitution` annotation, and
/// (3) descend with the extended substitution.
fn rename_unique_go(
    fresh: &mut PreciseFreshState,
    subst: &BTreeMap<LVar, LVar>,
    p: &PlainProcess,
) -> PlainProcess {
    // Materialize the process once; carry composed renamings instead of
    // repeatedly copying and rewriting every remaining suffix.
    let mut out = rename_process_full(subst, p);
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
                    *ac = rename_action(&new_subst, ac);
                    (ann, new_subst, inv)
                }
                Process::Comb(c, ann, _, _) => {
                    *c = rename_comb(inherited, c);
                    let (new_subst, inv) = mk_subst(fresh, &bindings_comb(c));
                    *c = rename_comb(&new_subst, c);
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

/// `apply subst p` over an entire process subtree (terms + bound vars), used to
/// mirror HS's `apply initSubst p` (Typing.hs:242-261, see line 246).
/// Parsed location annotations are terms too, so they receive the same rename;
/// `renameUnique_go` updates `back_substitution` per node afterwards.
fn rename_process_full(subst: &BTreeMap<LVar, LVar>, p: &PlainProcess) -> PlainProcess {
    map_process(
        p,
        &mut |action| rename_action(subst, action),
        &mut |comb| rename_comb(subst, comb),
        &mut |ann| rename_annotation(subst, ann),
    )
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
    let empty: BTreeMap<LVar, LVar> = BTreeMap::new();
    rename_unique_go(&mut fresh, &empty, p)
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
    use tamarin_term::function_symbols::FunSym;
    // Keep both inference passes and their error order. Reuse an ordinary
    // application only if its entire previous visit left the environment
    // unchanged, and nothing has changed since. Caching a visit that learned
    // types would preserve stale types in its earlier children.
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
    let mut cache = Cache::default();
    enum Work<'a> {
        Visit(&'a SapicTerm, SapicType),
        Remember(CacheKey, usize),
        Poly(FunSym, usize),
        Learn {
            sym: FunSym,
            args: &'a [SapicTerm],
            key: UserDefinedSym,
            target: SapicType,
            count: usize,
        },
        Real {
            sym: FunSym,
            key: UserDefinedSym,
            out: SapicType,
            count: usize,
        },
    }
    let mut pending = vec![Work::Visit(t, tt.clone())];
    let mut output: Vec<(SapicTerm, SapicType)> = Vec::new();
    while let Some(work) = pending.pop() {
        match work {
            Work::Visit(VTerm::Lit(Lit::Var(v)), target) => {
                let lvar = &v.var;
                let stype = if lvar.sort == LSort::Pub {
                    None
                } else {
                    env.vars
                        .get(lvar)
                        .ok_or_else(|| format!("unbound variable {lvar:?}"))?
                        .clone()
                };
                let merged = sqcap(&stype, &target)?;
                if env.vars.get(lvar) != Some(&merged) {
                    env.vars.insert(*lvar, merged.clone());
                    cache.changed();
                }
                output.push((var_term(SapicLVar::new(*lvar, merged.clone())), merged));
            }
            Work::Visit(t @ VTerm::Lit(Lit::Con(_)), _) => output.push((t.clone(), None)),
            Work::Remember(key, generation) => {
                if generation == cache.generation {
                    cache.values.insert(key, output.last().unwrap().clone());
                }
            }
            Work::Visit(node @ VTerm::App(sym, args), target) => {
                if let FunSym::NoEq(fs) = sym
                    && !is_special_viewterm2_sym(fs)
                {
                    // The root is visited once; caching it would allocate for
                    // every ordinary flat application without saving any work.
                    if !std::ptr::eq(node, t) {
                        let cache_key = (std::ptr::from_ref(node), target.clone());
                        if let Some(result) = cache.values.get(&cache_key) {
                            output.push(result.clone());
                            continue;
                        }
                        pending.push(Work::Remember(cache_key, cache.generation));
                    }
                    let key = UserDefinedSym::NoEqUser(*fs);
                    let (intypes, outtype) = get_fun(env, fs.arity, &key);
                    let merged = sqcap(&outtype, &target)?;
                    if insert_fun(env, &key, (intypes.clone(), merged))? {
                        cache.changed();
                    }
                    let count = args.len().min(intypes.len());
                    pending.push(Work::Learn {
                        sym: *sym,
                        args,
                        key,
                        target,
                        count,
                    });
                    pending.extend(
                        args.iter()
                            .zip(intypes)
                            .rev()
                            .map(|(a, w)| Work::Visit(a, w)),
                    );
                } else {
                    pending.push(Work::Poly(*sym, args.len()));
                    pending.extend(args.iter().rev().map(|a| Work::Visit(a, None)));
                }
            }
            Work::Poly(sym, count) => {
                let terms = output
                    .drain(output.len() - count..)
                    .map(|(t, _)| t)
                    .collect();
                output.push((tamarin_term::term::f_app(sym, terms), None));
            }
            Work::Learn {
                sym,
                args,
                key,
                target,
                count,
            } => {
                let types = output
                    .drain(output.len() - count..)
                    .map(|(_, t)| t)
                    .collect();
                let FunSym::NoEq(fs) = sym else {
                    unreachable!()
                };
                let (intypes, outtype) = get_fun(env, fs.arity, &key);
                let merged = sqcap(&outtype, &target)?;
                if insert_fun(env, &key, (types, merged))? {
                    cache.changed();
                }
                let count = args.len().min(intypes.len());
                pending.push(Work::Real {
                    sym,
                    key,
                    out: outtype,
                    count,
                });
                pending.extend(
                    args.iter()
                        .zip(intypes)
                        .rev()
                        .map(|(a, w)| Work::Visit(a, w)),
                );
            }
            Work::Real {
                sym,
                key,
                out,
                count,
            } => {
                let (terms, types) = output.drain(output.len() - count..).unzip();
                if insert_fun(env, &key, (types, out.clone()))? {
                    cache.changed();
                }
                output.push((tamarin_term::term::f_app(sym, terms), out));
            }
        }
    }
    Ok(output.pop().unwrap())
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
mod tests {
    use super::*;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    fn reference_rename(
        fresh: &mut PreciseFreshState,
        subst: &BTreeMap<LVar, LVar>,
        p: &PlainProcess,
    ) -> PlainProcess {
        // `let p' = apply initSubst p` — apply the outstanding renaming to the
        // WHOLE subtree (HS Typing.hs:242-261, see line 246); the children inherit the rename, then
        // are descended into with only the NEW fresh subst for this node's binders.
        let p_prime = rename_process_full(subst, p);
        match p_prime {
            Process::Null(ann) => Process::Null(ann),
            Process::Action(ac, ann, body) => {
                let bvars = bindings_act(&ac);
                let (new_subst, inv) = mk_subst(fresh, &bvars);
                let mut ann2 = ann;
                ann2.back_substitution = ann2.back_substitution.compose(&inv);
                let ac1 = rename_action(&new_subst, &ac);
                let body1 = reference_rename(fresh, &new_subst, &body);
                Process::Action(ac1, ann2, Box::new(body1).into())
            }
            Process::Comb(c, ann, l, r) => {
                let bvars = bindings_comb(&c);
                let (new_subst, inv) = mk_subst(fresh, &bvars);
                let mut ann2 = ann;
                ann2.back_substitution = ann2.back_substitution.compose(&inv);
                let c1 = rename_comb(&new_subst, &c);
                let l1 = reference_rename(fresh, &new_subst, &l);
                let r1 = reference_rename(fresh, &new_subst, &r);
                Process::Comb(c1, ann2, Box::new(l1).into(), Box::new(r1).into())
            }
        }
    }

    #[test]
    fn renaming_matches_suffix_substitution_with_shadowing_and_branches() {
        // Include annotation-only names that can collide with minted names,
        // repeated binders, typed variables, and independent sibling scopes.
        for seed in 0..24 {
            let ann = |i| {
                let mut a = ProcessParsedAnnotation::empty();
                a.location = Some(var_term(slv("x", i, Some("site"))));
                a
            };
            let mut p = Process::Null(ann(seed % 5));
            for i in 0..8 {
                p = if (seed + i) % 3 == 0 {
                    Process::Comb(
                        ProcessCombinator::Lookup(
                            var_term(slv("x", 0, None)),
                            slv("x", i % 2, None),
                        ),
                        ann(i % 5),
                        Box::new(p).into(),
                        Box::new(Process::Action(
                            SapicAction::New(slv("x", 0, None)),
                            ann(1),
                            Box::new(Process::Null(ann(2))).into(),
                        ))
                        .into(),
                    )
                } else {
                    Process::Action(
                        SapicAction::New(slv("x", i % 2, Some("message"))),
                        ann(i % 5),
                        Box::new(p).into(),
                    )
                };
            }
            let avoid = proc_lvars(&p)
                .into_iter()
                .map(|v| (v.name.to_string(), v.idx))
                .collect::<Vec<_>>();
            let expected = reference_rename(
                &mut PreciseFreshState::avoid_precise(avoid),
                &BTreeMap::new(),
                &p,
            );
            assert_eq!(rename_unique(&p), expected, "seed {seed}");
        }
    }

    #[test]
    fn deep_typing_and_variable_collection_use_bounded_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let x = slv("x", 0, Some("message"));
                let mut process = Process::Action(
                    SapicAction::New(x.clone()),
                    ProcessParsedAnnotation::empty(),
                    Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
                );
                for _ in 0..100_000 {
                    process = Process::Action(
                        SapicAction::Rep,
                        ProcessParsedAnnotation::empty(),
                        Box::new(process).into(),
                    );
                }
                assert_eq!(vars_proc(&process), vec![x.clone()]);
                let env = || TypingEnvironment {
                    vars: BTreeMap::new(),
                    funs: BTreeMap::new(),
                    events: BTreeMap::new(),
                };
                // Also release the renamed temporary owned by the complete pipeline.
                drop(type_and_rename_process_in(&mut env(), &process).unwrap());
                let typed = type_process(&mut env(), &process).unwrap();
                assert_eq!(vars_proc(&typed), vec![x.clone()]);
                typed.drop_iteratively();
                // The left branch is already rebuilt when the right branch's
                // duplicate binder fails; its cleanup must use the worklist too.
                let input = Process::Comb(
                    ProcessCombinator::Parallel,
                    ProcessParsedAnnotation::empty(),
                    Box::new(process).into(),
                    Box::new(Process::Action(
                        SapicAction::New(x),
                        ProcessParsedAnnotation::empty(),
                        Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
                    ))
                    .into(),
                );
                let error = type_process(&mut env(), &input).unwrap_err();
                assert!(error.contains("variable bound twice"));
                input.drop_iteratively();
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn typing_visits_children_before_parent_terms_and_left_before_right() {
        use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
        let x = slv("x", 0, Some("learned"));
        let tag = FactTag::Proto(Multiplicity::Linear, "Learned", 1);
        // The parent event can only type x after visiting the child's binder.
        let input = Process::Action(
            SapicAction::Event(Fact::new(tag, vec![var_term(slv("x", 0, None))])),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Comb(
                ProcessCombinator::Parallel,
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Action(
                    SapicAction::New(x),
                    ProcessParsedAnnotation::empty(),
                    Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
                ))
                .into(),
                Box::new(Process::Action(
                    SapicAction::Event(Fact::new(tag, vec![var_term(slv("x", 0, None))])),
                    ProcessParsedAnnotation::empty(),
                    Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
                ))
                .into(),
            ))
            .into(),
        );
        let mut env = TypingEnvironment {
            vars: BTreeMap::new(),
            funs: BTreeMap::new(),
            events: BTreeMap::new(),
        };
        let typed = type_process(&mut env, &input).unwrap();
        assert_eq!(env.events[&tag], vec![Some("learned".into())]);
        let Process::Action(SapicAction::Event(event), _, _) = &typed else {
            panic!("typed event")
        };
        assert_eq!(event.terms[0], var_term(slv("x", 0, Some("learned"))));
    }

    fn slv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(|s| s.to_string()))
    }

    #[test]
    fn rename_unique_mints_x1_for_new_x0() {
        // new x:lol; 0  with x at index 0 → x.1
        let new = Process::Action(
            SapicAction::New(slv("x", 0, Some("lol"))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
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
    fn rename_unique_renames_location_terms() {
        let mut body_ann = ProcessParsedAnnotation::empty();
        body_ann.location = Some(var_term(slv("x", 0, None)));
        let proc = Process::Action(
            SapicAction::New(slv("x", 0, None)),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(body_ann)).into(),
        );

        let Process::Action(_, _, body) = rename_unique(&proc) else {
            panic!("expected New action");
        };
        assert_eq!(
            body.annotation().location,
            Some(var_term(slv("x", 1, None)))
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
            Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
        );
        // `new k; <msr>` — the binder renames `k` to `k.1` throughout the body.
        let proc = Process::Action(
            SapicAction::New(slv("k", 0, None)),
            ProcessParsedAnnotation::empty(),
            Box::new(msr).into(),
        );

        let Process::Action(_, _, body) = rename_unique(&proc) else {
            panic!("expected New action");
        };
        let Process::Action(SapicAction::Msr { acts, rest, .. }, _, _) = body.into_inner() else {
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

    /// The `gAct Event` case (Typing.hs:145-150) records the event's inferred
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
                Box::new(Process::Null(ProcessParsedAnnotation::empty())).into(),
            ))
            .into(),
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

    /// `initTEFromSig`'s `foldM typeRule initTE sigRules` (Typing.hs:185,
    /// 179-181): typing the signature's subterm rewrite rules propagates a
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
    #[test]
    fn deep_polymorphic_type_inference_uses_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut t: SapicTerm = tamarin_term::lterm::pub_term("a");
                for _ in 0..20_000 {
                    t = tamarin_term::term::f_app(
                        tamarin_term::function_symbols::FunSym::List,
                        vec![t],
                    );
                }
                let mut env = TypingEnvironment {
                    vars: BTreeMap::new(),
                    funs: BTreeMap::new(),
                    events: BTreeMap::new(),
                };
                let (typed, ty) = type_with(&mut env, &t, &None).unwrap();
                assert_eq!(typed, t);
                assert_eq!(ty, None);
                drop((typed, t));
            })
            .unwrap()
            .join()
            .unwrap();
    }
    fn reference_type_with(
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
                        None => return Err(format!("unbound variable {lvar:?}")),
                        Some(ty) => ty.clone(),
                    }
                };
                let merged = sqcap(&stype, tt)?;
                env.vars.insert(*lvar, merged.clone());
                Ok((var_term(SapicLVar::new(*lvar, merged.clone())), merged))
            }
            VTerm::App(sym, args) => {
                use tamarin_term::function_symbols::FunSym;
                match sym {
                    // HS `typeWith` dispatches on `viewTerm2 t`: a NoEq application
                    // whose head is one of the SPECIAL symbols (`pair`, `exp`, `inv`,
                    // `pmult`, `diff`, `one`, `natOne`, `dhNeutral`) does NOT view as
                    // `FAppNoEq` (Term/Raw.hs:191-204) — it views as its own
                    // constructor (`FPair`, `FExp`, …).  None of those match the
                    // `FAppNoEq fs ts` case (Typing.hs:63-124, see line 83), so they fall through to
                    // the polymorphic `FApp fs ts <- viewTerm t` branch (Typing.hs:63-124, see line 102)
                    // which types arguments with `Nothing` and learns NO function
                    // type.  Crucially this means pairs (`<a,b>`) do NOT back-propagate
                    // an argument type onto `a`/`b` — matching HS, which keeps
                    // tuple-component variables untyped.
                    FunSym::NoEq(fs) if !is_special_viewterm2_sym(fs) => {
                        let n = fs.arity;
                        // HS keys the typing environment by `NoEqUser fs`
                        // (Typing.hs:63-124, see line 83).
                        let key = UserDefinedSym::NoEqUser(*fs);
                        // First pass: refine output type from target.
                        let (intypes1, outtype1) = get_fun(env, n, &key);
                        let mintype1 = sqcap(&outtype1, tt)?;
                        insert_fun(env, &key, (intypes1.clone(), mintype1))?;
                        // Type args (discard results, just to learn input types).
                        let ts: Vec<SapicTerm> = args.to_vec();
                        let mut ptypes: Vec<SapicType> = Vec::with_capacity(ts.len());
                        for (a, want) in ts.iter().zip(intypes1.iter()) {
                            let (_, ty) = reference_type_with(env, a, want)?;
                            ptypes.push(ty);
                        }
                        // Recompute output type, having learnt arg types.
                        let (intypes2, outtype2) = get_fun(env, n, &key);
                        let mintype2 = sqcap(&outtype2, tt)?;
                        insert_fun(env, &key, (ptypes, mintype2))?;
                        // Type args for real.
                        let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(ts.len());
                        let mut ptypes2: Vec<SapicType> = Vec::with_capacity(ts.len());
                        for (a, want) in ts.iter().zip(intypes2.iter()) {
                            let (a_new, ty) = reference_type_with(env, a, want)?;
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
                            let (a_new, _) = reference_type_with(env, a, &None)?;
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
    #[test]
    fn deep_ordinary_inference_reuses_unchanged_visits() {
        use tamarin_term::function_symbols::{Constructability, FunSym, NdcState, Privacy};
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let symbol = NoEqSym {
                    name: b"deep_inference",
                    arity: 1,
                    privacy: Privacy::Public,
                    constructability: Constructability::Constructor,
                    ndc: NdcState::NotNdc,
                };
                for declared in [false, true] {
                    let x = LVar::new("x", LSort::Msg, 0);
                    let ty = declared.then(|| "a".to_string());
                    let mut term = var_term(SapicLVar::new(x, None));
                    for _ in 0..20_000 {
                        term = tamarin_term::term::f_app(FunSym::NoEq(symbol), vec![term]);
                    }
                    let mut env = TypingEnvironment {
                        vars: [(x, None)].into(),
                        funs: if declared {
                            [(
                                UserDefinedSym::NoEqUser(symbol),
                                (vec![ty.clone()], ty.clone()),
                            )]
                            .into()
                        } else {
                            BTreeMap::new()
                        },
                        events: BTreeMap::new(),
                    };
                    let (typed, actual_ty) = type_with(&mut env, &term, &ty).unwrap();
                    assert_eq!(actual_ty, ty);
                    assert_eq!(env.vars[&x], ty);
                    assert_eq!(tamarin_term::term::term_depth(&typed), 20_001);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn branching_inference_matches_two_pass_reference() {
        use tamarin_term::function_symbols::{Constructability, FunSym, NdcState, Privacy};
        use tamarin_term::term::{f_app, f_app_list};
        let symbol = |name, arity| NoEqSym {
            name,
            arity,
            privacy: Privacy::Public,
            constructability: Constructability::Constructor,
            ndc: NdcState::NotNdc,
        };
        let symbols = [
            symbol(b"cache_f", 1),
            symbol(b"cache_g", 1),
            symbol(b"cache_h", 2),
        ];
        let vars = [
            LVar::new("x", LSort::Msg, 0),
            LVar::new("y", LSort::Msg, 0),
            LVar::new("p", LSort::Pub, 0),
        ];
        fn term(seed: &mut u64, depth: usize, syms: &[NoEqSym; 3], vars: &[LVar; 3]) -> SapicTerm {
            *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let choice = (*seed >> 32) as usize;
            if depth == 0 || choice % 7 < 3 {
                return var_term(SapicLVar::new(vars[choice % 3], None));
            }
            let left = term(seed, depth - 1, syms, vars);
            match choice % 7 {
                3 | 4 => f_app(FunSym::NoEq(syms[choice % 7 - 3]), vec![left]),
                5 => f_app(
                    FunSym::NoEq(syms[2]),
                    vec![left, term(seed, depth - 1, syms, vars)],
                ),
                _ => f_app_list(vec![left, term(seed, depth - 1, syms, vars)]),
            }
        }
        for case in 0..1000u64 {
            let t = term(&mut (case + 1), 4, &symbols, &vars);
            for target in [None, Some("a".to_string()), Some("b".to_string())] {
                let make_env = || {
                    let mut env = TypingEnvironment {
                        vars: [(vars[0], None), (vars[1], Some("a".to_string()))].into(),
                        funs: BTreeMap::new(),
                        events: BTreeMap::new(),
                    };
                    if case % 2 == 0 {
                        env.funs.insert(
                            UserDefinedSym::NoEqUser(symbols[0]),
                            (vec![Some("a".to_string())], None),
                        );
                    }
                    if case % 3 == 0 {
                        env.funs.insert(
                            UserDefinedSym::NoEqUser(symbols[1]),
                            (vec![None], Some("b".to_string())),
                        );
                    }
                    if case % 5 == 0 {
                        env.vars.remove(&vars[1]);
                    }
                    env
                };
                let mut actual = make_env();
                let mut expected = make_env();
                assert_eq!(
                    type_with(&mut actual, &t, &target),
                    reference_type_with(&mut expected, &t, &target),
                    "case {case}: {t:?}"
                );
                assert_eq!(actual.vars, expected.vars, "case {case}: variables");
                assert_eq!(actual.funs, expected.funs, "case {case}: functions");
            }
        }
    }

    #[test]
    fn ordinary_function_inference_matches_two_pass_reference() {
        use tamarin_term::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
        use tamarin_term::term::f_app;
        let symbol = NoEqSym {
            name: b"test_inference",
            arity: 1,
            privacy: Privacy::Public,
            constructability: Constructability::Constructor,
            ndc: tamarin_term::function_symbols::NdcState::NotNdc,
        };
        for depth in [0, 1, 4, 10] {
            for initial in [None, Some("a".to_string())] {
                for target in [None, Some("a".to_string()), Some("b".to_string())] {
                    let v = LVar::new("x", LSort::Msg, 0);
                    let mut t = var_term(SapicLVar::new(v, initial.clone()));
                    for _ in 0..depth {
                        t = f_app(FunSym::NoEq(symbol), vec![t]);
                    }
                    let env = || TypingEnvironment {
                        vars: [(v, initial.clone())].into(),
                        funs: BTreeMap::new(),
                        events: BTreeMap::new(),
                    };
                    let mut actual = env();
                    let mut expected = env();
                    assert_eq!(
                        type_with(&mut actual, &t, &target),
                        reference_type_with(&mut expected, &t, &target)
                    );
                    assert_eq!(actual.vars, expected.vars);
                    assert_eq!(actual.funs, expected.funs);
                }
            }
        }
    }
}
