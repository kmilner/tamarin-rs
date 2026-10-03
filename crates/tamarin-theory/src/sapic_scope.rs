// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Scoped SAPIC binders and renaming, from Theory.Sapic.Process.

use crate::formula::{apply_rename, formula_frees};
use crate::sapic::*;
use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::lterm::LVar;
use tamarin_term::vterm::Lit;

fn collect_proc_vars<A>(
    p: &Process<A, SapicLVar>,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    match p {
        Process::Null(_) => {}
        Process::Action(a, _, body) => {
            collect_action_vars(a, out);
            collect_proc_vars(body, out);
        }
        Process::Comb(c, _, l, r) => {
            collect_comb_vars(c, out);
            collect_proc_vars(l, out);
            collect_proc_vars(r, out);
        }
    }
}

fn collect_term_vars(t: &SapicTerm, out: &mut std::collections::BTreeSet<SapicLVar>) {
    for v in tamarin_term::vterm::vars_vterm(t) {
        out.insert(v);
    }
}

fn collect_fact_vars(
    f: &crate::sapic::SapicLNFact,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    for t in f.terms.iter() {
        collect_term_vars(t, out);
    }
}

pub fn collect_action_vars(
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

pub fn collect_comb_vars(
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
pub fn rename_term(subst: &BTreeMap<LVar, LVar>, t: &SapicTerm) -> SapicTerm {
    tamarin_term::term::map_lits(t, &mut |lit| match lit {
        Lit::Var(sv) => {
            let new_lv = subst.get(&sv.var).copied().unwrap_or(sv.var);
            Lit::Var(SapicLVar::new(new_lv, sv.stype.clone()))
        }
        Lit::Con(c) => Lit::Con(*c),
    })
}

pub fn rename_sv(subst: &BTreeMap<LVar, LVar>, sv: &SapicLVar) -> SapicLVar {
    let new_lv = subst.get(&sv.var).copied().unwrap_or(sv.var);
    SapicLVar::new(new_lv, sv.stype.clone())
}

pub fn rename_action(
    subst: &BTreeMap<LVar, LVar>,
    a: &SapicAction<SapicLVar>,
) -> SapicAction<SapicLVar> {
    map_terms_action(
        |t| rename_term(subst, t),
        // HS `apply subst` on a formula (Sapic/Process.hs) renames the
        // free variables of an embedded `_restrict` along with the fact rows
        // that mention them; a bound De Bruijn index and its binder hint cross
        // unchanged.
        |f| apply_rename(f.clone(), &mut |v| rename_sv(subst, v)),
        |v| rename_sv(subst, v),
        a,
    )
}

pub fn rename_comb(
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

pub fn vars_proc<A>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    let mut vars = BTreeSet::new();
    collect_proc_vars(p, &mut vars);
    vars.into_iter().collect()
}

pub fn vars_proc_with_annotations<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    let mut vars: BTreeSet<_> = vars_proc(p).into_iter().collect();
    for_each_process(p, &mut |node| {
        let ann = node.annotation().parsed();
        if let Some(loc) = &ann.location {
            vars.extend(frees_sapic_term(loc));
        }
        vars.extend(ann.generated_binders.iter().cloned());
    });
    vars.into_iter().collect()
}

fn pattern_declarations(vars: Vec<SapicLVar>, matches: &BTreeSet<SapicLVar>) -> Vec<SapicLVar> {
    let ids: BTreeSet<_> = matches.iter().map(|v| v.var).collect();
    vars.into_iter().filter(|v| !ids.contains(&v.var)).collect()
}

pub fn action_binder_declarations(a: &SapicAction<SapicLVar>) -> Vec<SapicLVar> {
    match a {
        SapicAction::New(v) => vec![v.clone()],
        SapicAction::ChIn {
            msg, match_vars, ..
        } => pattern_declarations(frees_sapic_term(msg), match_vars),
        SapicAction::Msr {
            prems, match_vars, ..
        } => pattern_declarations(
            prems.iter().flat_map(frees_sapic_fact).collect(),
            match_vars,
        ),
        _ => vec![],
    }
}

pub fn combinator_binder_declarations(c: &ProcessCombinator<SapicLVar>) -> Vec<SapicLVar> {
    match c {
        ProcessCombinator::Lookup(_, v) => vec![v.clone()],
        ProcessCombinator::Let {
            left, match_vars, ..
        } => pattern_declarations(frees_sapic_term(left), match_vars),
        _ => vec![],
    }
}

fn unique_identities(vars: Vec<SapicLVar>) -> Vec<SapicLVar> {
    let mut seen = BTreeSet::new();
    vars.into_iter().filter(|v| seen.insert(v.var)).collect()
}

pub fn action_binders(a: &SapicAction<SapicLVar>) -> Vec<SapicLVar> {
    unique_identities(action_binder_declarations(a))
}

pub fn combinator_binders(c: &ProcessCombinator<SapicLVar>) -> Vec<SapicLVar> {
    unique_identities(combinator_binder_declarations(c))
}

pub fn rename_action_binders(
    ren: &BTreeMap<LVar, LVar>,
    a: &SapicAction<SapicLVar>,
) -> SapicAction<SapicLVar> {
    match a {
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => SapicAction::ChIn {
            chan: chan.clone(),
            msg: rename_term(ren, msg),
            match_vars: match_vars.clone(),
        },
        _ => rename_action(ren, a),
    }
}

pub fn rename_combinator_binders(
    ren: &BTreeMap<LVar, LVar>,
    c: &ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    match c {
        ProcessCombinator::Lookup(key, v) => {
            ProcessCombinator::Lookup(key.clone(), rename_sv(ren, v))
        }
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        } => ProcessCombinator::Let {
            left: rename_term(ren, left),
            right: right.clone(),
            match_vars: match_vars.clone(),
        },
        _ => c.clone(),
    }
}

pub fn compose_renaming(
    new: &BTreeMap<LVar, LVar>,
    old: &BTreeMap<LVar, LVar>,
) -> BTreeMap<LVar, LVar> {
    let mut result = new.clone();
    for (k, v) in old {
        result.insert(*k, new.get(v).copied().unwrap_or(*v));
    }
    result
}

pub fn rename_annotation(
    ren: &BTreeMap<LVar, LVar>,
    ann: &ProcessParsedAnnotation,
) -> ProcessParsedAnnotation {
    ann.clone().map_terms(|t| rename_term(ren, &t))
}
