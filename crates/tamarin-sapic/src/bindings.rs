// Currently GPL 3.0 until granted permission by the following authors:
//   rkunnema, charlie-j, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Bindings.hs,
//   lib/term/src/Term/Maude/Process.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Sapic/Term.hs

//! Port of `Sapic.Bindings` from `lib/sapic/src/Sapic/Bindings.hs`.
//!
//! Compute the variables bound by SAPIC process actions / combinators, and
//! (via [`captured_variables`]) the variables that are bound twice on a single
//! path through the process — i.e. captured by a binder lower in the tree.

use std::collections::BTreeSet;

use tamarin_utils::prelude_ext::nub_on;
use crate::base_translation::{list_intersect, list_union};
use tamarin_theory::sapic::{
    frees_sapic_fact, frees_sapic_term, pfold_map, GoodAnnotation, Process, ProcessCombinator,
    SapicAction, SapicLVar,
};

/// `bindings`: variables bound *precisely at this point* in `p`.
pub fn bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    match p {
        Process::Null(_) => Vec::new(),
        Process::Comb(c, _, _, _) => bindings_comb(c),
        Process::Action(a, _, _) => bindings_act(a),
    }
}

/// `bindingsAct`: variables bound by an action (`new x`, `in(c, t)`, etc.).
pub fn bindings_act(a: &SapicAction<SapicLVar>) -> Vec<SapicLVar> {
    match a {
        // HS: `(New v) -> [v]` (Bindings.hs:21-26, see line 23).
        SapicAction::New(v) => vec![v.clone()],
        // HS: `nub (freesSapicTerm t) \\ S.toList vs` (Bindings.hs:21-26, see line 24).
        SapicAction::ChIn { msg, match_vars, .. } => {
            nub_difference(frees_sapic_term(msg), match_vars)
        }
        // HS: `nub (foldMap freesSapicFact l) \\ S.toList mv` (Bindings.hs:21-26, see line 25).
        // `nub` is applied AFTER concatenating across all premises (not
        // per-fact), so accumulate first, then nub-and-difference.
        SapicAction::Msr { prems, match_vars, .. } => {
            let mut all = Vec::new();
            for f in prems { all.extend(frees_sapic_fact(f)); }
            nub_difference(all, match_vars)
        }
        // HS `bindingsAct _ = []` (Bindings.hs:21-26, see line 26): every other action binds
        // nothing.  Enumerated (no wildcard) so a new binding-carrying variant
        // must decide its bound set here.
        SapicAction::Rep
        | SapicAction::ChOut { .. }
        | SapicAction::Insert(..)
        | SapicAction::Delete(..)
        | SapicAction::Lock(..)
        | SapicAction::Unlock(..)
        | SapicAction::Event(..)
        | SapicAction::ProcessCall(..) => Vec::new(),
    }
}

/// `bindingsComb`: variables bound by a process combinator (`lookup`, `let`).
pub fn bindings_comb(c: &ProcessCombinator<SapicLVar>) -> Vec<SapicLVar> {
    match c {
        // HS: `(Lookup _ v) -> [v]` (Bindings.hs:29-33, see line 31).
        ProcessCombinator::Lookup(_, v) => vec![v.clone()],
        // HS: `nub (freesSapicTerm t1) \\ S.toList mv` (Bindings.hs:29-33, see line 32).
        ProcessCombinator::Let { left, match_vars, .. } => {
            nub_difference(frees_sapic_term(left), match_vars)
        }
        // HS `bindingsComb _ = []` (Bindings.hs:29-33, see line 33): no other combinator binds a
        // variable.  Enumerated (no wildcard) so a new binding-carrying variant
        // must decide its bound set here.
        ProcessCombinator::Parallel
        | ProcessCombinator::Ndc
        | ProcessCombinator::Cond(_)
        | ProcessCombinator::CondEq(..) => Vec::new(),
    }
}

/// `accBindings`: every variable bound anywhere in `p` (with duplicates).
///
/// Mirrors Haskell `accBindings = pfoldMap bindings` (Bindings.hs). `pfoldMap`
/// (Process.hs:285-296) visits a `ProcessComb` *in-order*
/// (`pfoldMap f pl <> f node <> pfoldMap f pr`) and a `ProcessAction`
/// self-first (`f node <> pfoldMap f p`); `tamarin_theory::sapic::pfold_map`
/// implements exactly that order, so the bound-variable sequence matches HS.
pub fn acc_bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    pfold_map(p, &mut |node| bindings(node))
}

/// `capturedVariablesAt` (Bindings.hs:40-43): the variables bound *at this
/// node* that are *also* bound somewhere below it — i.e. captured by a deeper
/// binder on the same path:
///
/// ```text
/// capturedVariablesAt (ProcessAction ac _ p)  = bindingsAct ac `intersect` accBindings p
/// capturedVariablesAt (ProcessComb c _ pl pr) = bindingsComb c `intersect` (accBindings pl `union` accBindings pr)
/// capturedVariablesAt (ProcessNull _) = []
/// ```
fn captured_variables_at<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    match p {
        Process::Null(_) => Vec::new(),
        // `bindingsAct ac \`intersect\` accBindings body`.
        Process::Action(a, _, body) => {
            list_intersect(&bindings_act(a), &acc_bindings(body))
        }
        // `bindingsComb c \`intersect\` (accBindings pl \`union\` accBindings pr)`.
        Process::Comb(c, _, pl, pr) => {
            let below = list_union(&acc_bindings(pl), &acc_bindings(pr));
            list_intersect(&bindings_comb(c), &below)
        }
    }
}

/// `capturedVariables = pfoldMap capturedVariablesAt` (Bindings.hs:46-47):
/// run `capturedVariablesAt` at every node and concatenate the results in
/// `pfoldMap` order.  A variable appearing here is bound twice (captured) on
/// some path and yields a `WFBoundTwice` warning.
pub fn captured_variables<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    pfold_map(p, &mut captured_variables_at)
}

/// HS `nub xs \\ S.toList drop`: keep the first occurrence of each variable
/// (order-preserving `nub`), then remove members of `drop`. Because the list
/// is already deduplicated, removing the (single) first occurrence of each
/// `drop` member is equivalent to filtering all members out, so the result
/// matches HS `Data.List.(\\)` byte-for-byte while preserving source order.
fn nub_difference(xs: Vec<SapicLVar>, drop: &BTreeSet<SapicLVar>) -> Vec<SapicLVar> {
    nub_on(&xs, |v| v.clone())
        .into_iter()
        .filter(|v| !drop.contains(v))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    use tamarin_theory::sapic::{ProcessParsedAnnotation, SapicAction};

    fn slv(name: &str) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
    }

    #[test]
    fn new_binds_variable() {
        let v = slv("k");
        let act: SapicAction<SapicLVar> = SapicAction::New(v.clone());
        assert_eq!(bindings_act(&act), vec![v]);
    }

    #[test]
    fn channel_in_binds_unmatched() {
        // ChIn channel = None, msg = pair(x, y), match_vars = {x}.
        // Should bind {y}.
        use tamarin_term::builtin::pair;
        let x = slv("x");
        let y = slv("y");
        let msg = pair(var_term(x.clone()), var_term(y.clone()));
        let mut match_vars = BTreeSet::new();
        match_vars.insert(x);
        let act: SapicAction<SapicLVar> = SapicAction::ChIn {
            chan: None,
            msg,
            match_vars,
        };
        assert_eq!(bindings_act(&act), vec![y]);
    }

    #[test]
    fn channel_in_preserves_nub_order() {
        // HS `bindingsAct` for `ChIn _ (pair y x) {}` is
        // `nub (freesSapicTerm (pair y x)) \\ S.toList {}` = `[y, x]`
        // (first-occurrence order), NOT the sorted `[x, y]`.
        // freesSapicTerm = foldMap (:[]) (Theory/Sapic/Term.hs:131-132), nub keeps
        // first-occurrence order (Sapic/Bindings.hs:21-26, see line 24).
        use tamarin_term::builtin::pair;
        let x = slv("x");
        let y = slv("y");
        let msg = pair(var_term(y.clone()), var_term(x.clone()));
        let act: SapicAction<SapicLVar> = SapicAction::ChIn {
            chan: None,
            msg,
            match_vars: BTreeSet::new(),
        };
        assert_eq!(bindings_act(&act), vec![y, x]);
    }

    #[test]
    fn channel_in_nub_dedups_first_occurrence() {
        // `pair(y, pair(x, y))` -> freesSapicTerm = [y, x, y]; nub -> [y, x].
        use tamarin_term::builtin::pair;
        let x = slv("x");
        let y = slv("y");
        let msg = pair(
            var_term(y.clone()),
            pair(var_term(x.clone()), var_term(y.clone())),
        );
        let act: SapicAction<SapicLVar> = SapicAction::ChIn {
            chan: None,
            msg,
            match_vars: BTreeSet::new(),
        };
        assert_eq!(bindings_act(&act), vec![y, x]);
    }

    #[test]
    fn null_process_binds_nothing() {
        let p: Process<ProcessParsedAnnotation, SapicLVar> =
            Process::null(ProcessParsedAnnotation::empty());
        assert!(bindings(&p).is_empty());
        assert!(acc_bindings(&p).is_empty());
    }
}
