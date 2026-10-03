// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.Bindings` from `lib/sapic/src/Sapic/Bindings.hs`.
//!
//! Compute the variables bound by SAPIC process actions / combinators, and
//! (via [`captured_variables`]) the variables that are bound twice on a single
//! path through the process — i.e. captured by a binder lower in the tree.

use std::collections::BTreeMap;
#[cfg(test)]
use std::collections::BTreeSet;
use tamarin_term::lterm::LVar;

#[cfg(test)]
use tamarin_theory::sapic::ProcessCombinator;
use tamarin_theory::sapic::{for_each_process, GoodAnnotation, Process, SapicLVar};
pub(crate) use tamarin_theory::sapic_scope::{
    action_binders as bindings_act, combinator_binders as bindings_comb,
};

/// `bindings`: variables bound *precisely at this point* in `p`.
pub(crate) fn bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    match p {
        Process::Null(_) => Vec::new(),
        Process::Comb(c, _, _, _) => bindings_comb(c),
        Process::Action(a, _, _) => bindings_act(a),
    }
}

/// `accBindings`: every variable bound anywhere in `p` (with duplicates).
///
/// Mirrors Haskell `accBindings = pfoldMap bindings` (Bindings.hs). `pfoldMap`
/// (Sapic/Process.hs) visits a `ProcessComb` *in-order*
/// (`pfoldMap f pl <> f node <> pfoldMap f pr`) and a `ProcessAction`
/// self-first (`f node <> pfoldMap f p`); `tamarin_theory::sapic::for_each_process`
/// implements exactly that order, so the bound-variable sequence matches HS.
pub(crate) fn acc_bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    let mut out = Vec::new();
    for_each_process(p, &mut |node| out.extend(bindings(node)));
    out
}

/// Detect rebinding along one scoped path, comparing type-independent identities.
pub(crate) fn captured_variables<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    fn go<A: GoodAnnotation>(
        p: &Process<A, SapicLVar>,
        bound: &BTreeMap<LVar, SapicLVar>,
        out: &mut Vec<SapicLVar>,
    ) {
        let vars = bindings(p);
        let mut next = bound.clone();
        for v in vars {
            if let Some(original) = bound.get(&v.var) {
                out.push(original.clone());
            }
            next.entry(v.var).or_insert(v);
        }
        match p {
            Process::Null(_) => {}
            Process::Action(_, _, rest) => go(rest, &next, out),
            Process::Comb(_, _, left, right) => {
                go(left, &next, out);
                go(right, bound, out);
            }
        }
    }
    let mut out = vec![];
    go(p, &BTreeMap::new(), &mut out);
    out
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
    fn capture_checks_respect_failure_scope_and_ignore_types() {
        let ann = ProcessParsedAnnotation::empty;
        let x = slv("x");
        let typed = SapicLVar::new(x.var, Some("bitstring".into()));
        let new_x = || {
            Process::Action(
                SapicAction::New(typed.clone()),
                ann(),
                Box::new(Process::Null(ann())),
            )
        };
        let branch = |left, right| {
            Process::Comb(
                ProcessCombinator::Lookup(var_term(slv("key")), x.clone()),
                ann(),
                Box::new(left),
                Box::new(right),
            )
        };
        assert!(captured_variables(&branch(Process::Null(ann()), new_x())).is_empty());
        assert_eq!(
            captured_variables(&branch(new_x(), Process::Null(ann()))),
            vec![x]
        );
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
    fn channel_in_nub_dedups_first_occurrence() {
        // `pair(y, pair(x, y))` -> freesSapicTerm = [y, x, y]; nub -> [y, x].
        // This one expectation checks both halves of HS
        // `nub (freesSapicTerm t)`.  Without the `nub` the result keeps the
        // trailing duplicate.  With a sorted set for the deduplication the
        // result is `[x, y]` instead of `[y, x]`, which is the order of
        // first occurrence.  freesSapicTerm = foldMap (:[])
        // (Theory/Sapic/Term.hs), nub keeps the order of first
        // occurrence (Sapic/Bindings.hs).
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

    /// `accBindings = pfoldMap bindings` takes its visit order from
    /// `pfoldMap` (Sapic/Process.hs).  A `ProcessComb` visits in
    /// order (`pfoldMap f pl <> f node <> pfoldMap f pr`).  A
    /// `ProcessAction` visits itself first.  `capturedVariablesAt`
    /// intersects against this sequence, and `Null` must add nothing to it.
    #[test]
    fn acc_bindings_follows_pfold_map_order() {
        let ann = ProcessParsedAnnotation::empty;
        let new = |v: SapicLVar, body| Process::Action(SapicAction::New(v), ann(), Box::new(body));
        let null = || Process::null(ann());
        // The process is `new a; (new b; 0) lookup-else (new c; 0)`.  The
        // lookup binds `d`.
        let p: Process<ProcessParsedAnnotation, SapicLVar> = new(
            slv("a"),
            Process::Comb(
                ProcessCombinator::Lookup(tamarin_term::vterm::var_term(slv("cell")), slv("d")),
                ann(),
                Box::new(new(slv("b"), null())),
                Box::new(new(slv("c"), null())),
            ),
        );
        let names: Vec<String> = acc_bindings(&p)
            .iter()
            .map(|v| v.var.name.to_string())
            .collect();
        // `a` comes first, because an action visits itself first.  Then come
        // the left subtree, the combinator itself, and the right subtree.
        // The order is not `a, d, b, c`.
        assert_eq!(names, ["a", "b", "d", "c"]);
        // A `Null` node binds nothing on either entry point.
        assert!(bindings(&null()).is_empty());
        assert!(acc_bindings(&null()).is_empty());
    }
}
