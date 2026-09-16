// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::function_symbols::{pair_sym, AcSym};
use crate::term::{f_app_ac, f_app_no_eq};
use crate::vterm::{const_term, var_term};

type C = u32;
type V = &'static str;

#[test]
fn quantified_substitution_matches_eager_recursive_normalization() {
    use crate::function_symbols::{CSym, FunSym};
    use crate::term::{f_app, f_app_c, f_app_list, unsafe_f_app};
    type T = VTerm<C, BVar<V>>;
    fn reference(s: &Subst<C, V>, t: &T) -> T {
        match t {
            Term::Lit(Lit::Var(BVar::Free(v))) => s.image_of(v).map_or_else(
                || t.clone(),
                |image| {
                    map_lits(image, &mut |l| match l {
                        Lit::Con(c) => Lit::Con(*c),
                        Lit::Var(v) => Lit::Var(BVar::Free(*v)),
                    })
                },
            ),
            Term::Lit(_) => t.clone(),
            Term::App(sym, args) => f_app(*sym, args.iter().map(|a| reference(s, a)).collect()),
        }
    }
    let x = var_term(BVar::Free("x"));
    let bound = var_term(BVar::Bound(0));
    let raw = unsafe_f_app(
        FunSym::Ac(AcSym::Mult),
        vec![x.clone(), const_term(2), const_term(1)],
    );
    let terms = [
        x.clone(),
        bound.clone(),
        f_app_list(vec![]),
        raw,
        f_app_c(CSym::EMap, vec![x.clone(), bound.clone()]),
        f_app_no_eq(pair_sym(), vec![x, bound]),
    ];
    // An image containing its own domain variable must remain free and
    // be inserted once. Empty substitutions must still normalize raw apps.
    for s in [
        Subst::empty(),
        Subst::from_list([(
            "x",
            f_app_ac(AcSym::Mult, vec![var_term("x"), const_term(0)]),
        )]),
    ] {
        for t in &terms {
            assert_eq!(apply_bvterm(&s, t), reference(&s, t));
        }
    }
    assert_ne!(apply_bvterm(&Subst::empty(), &terms[3]), terms[3]);
}

#[test]
fn deep_quantified_substitution_lifts_images_without_capture() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut input: VTerm<C, BVar<V>> = var_term(BVar::Free("x"));
        let mut image: VTerm<C, V> = var_term("x");
        for _ in 0..100_000 {
            input = f_app_no_eq(pair_sym(), vec![input, var_term(BVar::Bound(7))]);
            image = f_app_no_eq(pair_sym(), vec![image, const_term(1)]);
        }
        let subst = Subst::from_list([("x", image)]);
        let result = apply_bvterm(&subst, &input);
        let mut current = &result;
        for _ in 0..100_000 {
            let Term::App(_, args) = current else {
                panic!("missing input level")
            };
            assert_eq!(args[1], var_term(BVar::Bound(7)));
            current = &args[0];
        }
        for _ in 0..100_000 {
            let Term::App(_, args) = current else {
                panic!("missing image level")
            };
            assert_eq!(args[1], const_term(1));
            current = &args[0];
        }
        assert_eq!(current, &var_term(BVar::Free("x")));
        drop((result, input, subst));
    });
}

#[test]
fn empty_substitution_is_identity() {
    let s: Subst<C, V> = Subst::empty();
    let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), const_term(1)]);
    assert_eq!(apply_vterm(&s, t.clone()), t);
}

/// `foldFrees f = foldFrees f . sMap` (SubstVFree.hs:261) through the
/// `M.Map` instance (LTerm.hs:905-909): ascending key order, and inside an
/// entry the key before its value.
#[test]
fn subst_folds_key_then_value_ascending() {
    use crate::lterm::{frees_list, LSort};
    let v = |n: &'static str, i: u64| LVar::new(n, LSort::Msg, i);
    // `Ord LVar` compares the index first (LTerm.hs:546-548), so `b.0` is
    // the smaller key even though `a` sorts before `b` by name.
    let s: Subst<C, LVar> = Subst::from_list(vec![
        (v("a", 1), var_term(v("x", 4))),
        (v("b", 0), var_term(v("y", 3))),
    ]);
    assert_eq!(
        frees_list(&s),
        vec![v("b", 0), v("y", 3), v("a", 1), v("x", 4)]
    );
}

/// `mapFrees f = (substFromList <$>) . mapFrees f . substToList`
/// (SubstVFree.hs:264): the rebuild goes back through `substFromList`, so
/// an entry the map turned into `x ~> x` disappears.
#[test]
fn subst_map_drops_identity_bindings() {
    use crate::lterm::LSort;
    let v = |n: &'static str, i: u64| LVar::new(n, LSort::Msg, i);
    let s: Subst<C, LVar> = Subst::from_list(vec![
        (v("x", 0), var_term(v("y", 1))),
        (v("z", 2), const_term(7)),
    ]);
    // Every variable goes to `y.1`, which makes the first entry
    // `y.1 ~> y.1` and leaves the second one `y.1 ~> 7`.
    let mapped = s.map_free(&mut |_| v("y", 1));
    assert_eq!(mapped.to_list(), vec![(v("y", 1), const_term(7))]);
}

#[test]
fn from_list_drops_trivial() {
    let s: Subst<C, V> = Subst::from_list(vec![("x", var_term("x")), ("y", const_term(1))]);
    // `x ~> x` is dropped, only `y ~> 1` remains.
    assert_eq!(s.dom().copied().collect::<Vec<_>>(), vec!["y"]);
}

#[test]
fn apply_replaces_variables() {
    let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(7))]);
    let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("y")]);
    let out = apply_vterm(&s, t);
    assert_eq!(
        out,
        f_app_no_eq(pair_sym(), vec![const_term(7), var_term("y")])
    );
}

#[test]
fn apply_preserves_ac_normalization() {
    // mult(x, 3) with {x ~> 1} should become mult(1, 3) — sorted.
    let t: VTerm<C, V> = f_app_ac(AcSym::Mult, vec![var_term("x"), const_term(3)]);
    let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let out = apply_vterm(&s, t);
    // Substitution may reorder; arguments must be sorted.
    if let Term::App(_, ts) = out {
        assert_eq!(&*ts, &[const_term(1), const_term(3)][..]);
    } else {
        panic!("expected AC application");
    }
}

/// `SubstView` is a pure probe-container swap: `apply_changed`/`apply`
/// must agree with the `BTreeMap` path on every term shape — hit,
/// miss, nested rebuild, AC re-normalisation, and the
/// `None`-when-unchanged convention.
#[test]
fn subst_view_matches_btree_apply() {
    let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(7)), ("y", var_term("z"))]);
    let view = SubstView::new(&s);
    let terms: Vec<VTerm<C, V>> = vec![
        var_term("x"),                                               // hit (leaf)
        var_term("w"),                                               // miss (leaf)
        const_term(3),                                               // constant
        f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("w")]), // partial rebuild
        f_app_no_eq(pair_sym(), vec![var_term("w"), const_term(1)]), // unchanged app
        f_app_ac(AcSym::Mult, vec![var_term("y"), const_term(0)]),   // AC re-sort
    ];
    for t in terms {
        assert_eq!(view.apply_changed(&t), apply_vterm_changed(&s, &t));
        assert_eq!(view.apply(t.clone()), apply_vterm(&s, t));
    }
    assert_eq!(view.image_of(&"x"), s.image_of(&"x"));
    assert_eq!(view.image_of(&"w"), s.image_of(&"w"));
}

/// `applyBLLit` (SubstVFree.hs:299-301) replaces a `Free` literal in the
/// domain by its image, lifted back into `BVar` form; a `Bound` index and
/// a constant are literals it hands back untouched.
#[test]
fn apply_bvterm_replaces_free_lits_and_keeps_bound_indices() {
    let s: Subst<C, V> = Subst::from_list(vec![(
        "x",
        f_app_no_eq(pair_sym(), vec![var_term("a"), const_term(2)]),
    )]);
    let inner: VTerm<C, BVar<V>> = f_app_no_eq(
        pair_sym(),
        vec![var_term(BVar::Bound(0)), var_term(BVar::Free("y"))],
    );
    let t: VTerm<C, BVar<V>> =
        f_app_no_eq(pair_sym(), vec![var_term(BVar::Free("x")), inner.clone()]);
    let image: VTerm<C, BVar<V>> =
        f_app_no_eq(pair_sym(), vec![var_term(BVar::Free("a")), const_term(2)]);
    assert_eq!(
        apply_bvterm(&s, &t),
        f_app_no_eq(pair_sym(), vec![image, inner])
    );
}

/// `bindTerm` rebuilds every application through `fApp`
/// (Term/Term/Raw.hs:219-221), so an AC argument list is re-sorted under
/// the images instead of keeping the positions of the original arguments.
#[test]
fn apply_bvterm_resorts_ac_arguments_after_a_rewrite() {
    // Stored AC-sorted as [Con 3, Var (Free "x")]; the image `Con 1` sorts
    // in front of `Con 3`.
    let t: VTerm<C, BVar<V>> =
        f_app_ac(AcSym::Mult, vec![var_term(BVar::Free("x")), const_term(3)]);
    let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let Term::App(_, args) = apply_bvterm(&s, &t) else {
        panic!("expected the AC application");
    };
    assert_eq!(&*args, &[const_term(1), const_term(3)][..]);
}

#[test]
fn compose_applies_right_then_left() {
    // `compose s1 s2` applied to t == s1(s2(t)) (Haskell convention:
    // s1 *after* s2).
    // s1 = {x ~> y}, s2 = {y ~> 1}.
    let s1: Subst<C, V> = Subst::from_list(vec![("x", var_term("y"))]);
    let s2: Subst<C, V> = Subst::from_list(vec![("y", const_term(1))]);
    let composed = s1.compose(&s2);
    let t: VTerm<C, V> = var_term("x");
    // composed(x) = s1(s2(x)) = s1(x) = y.
    assert_eq!(apply_vterm(&composed, t), var_term("y"));
    // And for y: s2(y) = 1, s1(1) = 1.
    let t: VTerm<C, V> = var_term("y");
    assert_eq!(apply_vterm(&composed, t), const_term(1));
}

#[test]
fn restrict_filters_domain() {
    let s: Subst<C, V> = Subst::from_list(vec![
        ("x", const_term(1)),
        ("y", const_term(2)),
        ("z", const_term(3)),
    ]);
    let r = s.restrict(&["x", "z"]);
    let dom: Vec<&V> = r.dom().collect();
    assert_eq!(dom, vec![&"x", &"z"]);
}

// =============================================================================
// Haskell-faithfulness invariants
// =============================================================================
//
// These tests pin semantic choices that were easy to miss.  See
// `unification::haskell_invariants_tests` for the rationale section.

/// `restrict` is a PURE KEY-FILTER (no chain-chase).
///
/// Haskell `Theory.Tools.EquationStore.restrict` calls
/// `Subst.restrict` (SubstVFree.hs:198-199):
/// ```haskell
/// restrict :: IsVar v => [v] -> Subst c v -> Subst c v
/// restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)
/// ```
/// Nothing else.  No chain-chase.
///
/// Do NOT chain-chase values to a fixed point before filtering:
/// collapsing `t.1 → e_A_1 → blind(...)` into `t.1 → blind(...)`
/// directly prevents Haskell-faithful `restrict` from dropping the
/// binding (since `t.1` is stable), causing foo_eligibility's `A_1`
/// case to be dropped at runtime via refineSubst-contradictory.
#[test]
fn restrict_does_not_chain_chase() {
    // Build a subst with a chain: y → z, z → 1.
    // If restrict ⊇ {y}: should keep `y → z` LITERALLY, not collapse
    // to `y → 1`.  The dangling z is fine — Haskell falls back to
    // identity for unbound vars.
    let s: Subst<C, V> = Subst::from_list(vec![("y", var_term("z")), ("z", const_term(1))]);
    let r = s.restrict(&["y"]);
    // y must map to z (the var), NOT to 1 (the chain-chased value).
    assert_eq!(
        r.image_of(&"y"),
        Some(&var_term("z")),
        "restrict must NOT chain-chase: y → z stays as y → z, \
                    not y → 1.  Chain-chase here breaks foo_eligibility."
    );
    // z is filtered out entirely.
    assert_eq!(r.image_of(&"z"), None);
}

/// `restrict stableVars` empties the subst when no key is stable.
///
/// This is the exact foo_eligibility shape: Haskell's pre-restrict
/// subst has keys like `m.19` and `sk.28` (rule-internal vars,
/// large idx), and stableVars are `{#i, t.1, t.2}` (lemma vars,
/// small idx).  Post-restrict: empty subst.
#[test]
fn restrict_empties_subst_when_no_key_is_stable() {
    // "Rule-internal" keys binding to whatever values.
    let s: Subst<C, V> = Subst::from_list(vec![
        ("m", const_term(19)),  // m.19 in spirit
        ("sk", const_term(28)), // sk.28 in spirit
    ]);
    // "Stable" vars: don't overlap.
    let r = s.restrict(&["t", "i"]);
    assert!(
        r.is_empty(),
        "When no key is in stable set, restrict produces empty subst. \
                 This is what enables foo_eligibility's clean runtime bind."
    );
}

/// `compose s1 s2` applies right-then-left.
///
/// Haskell `SubstVFree.compose` (mirrors Robinson):
/// applying `s1 ∘ s2` to a term is `s1 (s2 t)`.
///
/// If we get this backwards, downstream code that composes the
/// freshly-built subst with the running eq-store gets the wrong
/// effective substitution (and the proof state silently drifts).
#[test]
fn compose_direction_is_right_then_left() {
    // s1 = {x → 1}; s2 = {y → x}.
    // compose(s1, s2) means "apply s2 first, then s1".
    // (s1 . s2)(y) = s1(s2(y)) = s1(x) = 1.
    let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let s2: Subst<C, V> = Subst::from_list(vec![("y", var_term("x"))]);
    let composed = s1.compose(&s2);
    assert_eq!(
        apply_vterm(&composed, var_term("y")),
        const_term(1),
        "compose(s1, s2) applied to y must equal s1(s2(y)) = 1, \
                    NOT s2(s1(y)) = y.  If this fails, the direction is \
                    reversed and eq-store subst composition is silently \
                    wrong."
    );
}

/// `compose` preserves `s1`'s domain when `s2` doesn't bind it.
///
/// `compose(s1, s2)` should include bindings from s1 that aren't
/// shadowed by s2.  Specifically: s1 = {x → 1}, s2 = {y → 2};
/// composed should have BOTH x → 1 and y → 2.
#[test]
fn compose_merges_disjoint_domains() {
    let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let s2: Subst<C, V> = Subst::from_list(vec![("y", const_term(2))]);
    let composed = s1.compose(&s2);
    assert_eq!(composed.image_of(&"x"), Some(&const_term(1)));
    assert_eq!(composed.image_of(&"y"), Some(&const_term(2)));
}

/// `compose` `s1` shadows `s2` for overlapping domain.
///
/// If both bind `x`, the s1 binding wins in the final compose
/// because compose iterates s2's bindings first (applying s1 into
/// their values), then adds s1's own bindings that s2 doesn't
/// already bind.  The Rust impl adds *s1*'s own binding for x ONLY
/// IF s2 doesn't have x; this test pins that.
#[test]
fn compose_overlapping_domain_s2_takes_precedence_via_apply_subst() {
    // s1 = {x → 1}; s2 = {x → 99}.
    // compose first applies s1 to s2's range (no x in range, so
    // s2 unchanged); then adds s1's bindings whose domain isn't in
    // s2.  s2 has x, so s1's x → 1 is DROPPED.  Result: {x → 99}.
    //
    // This matches Haskell's `compose s1 s2` semantics: when s2
    // already binds v, s1's v-binding is shadowed by s2's.  Applying
    // composed to v gives s2(v) = 99.
    let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let s2: Subst<C, V> = Subst::from_list(vec![("x", const_term(99))]);
    let composed = s1.compose(&s2);
    assert_eq!(
        composed.image_of(&"x"),
        Some(&const_term(99)),
        "compose: s2's binding wins when domains overlap and \
                    s1 doesn't transform s2's value."
    );
    assert_eq!(apply_vterm(&composed, var_term("x")), const_term(99));
}

/// `apply_subst` rewrites the RANGE of `other` only.
///
/// `s1.apply_subst(s2)` rewrites every VALUE in s2 by applying s1.
/// It does NOT touch s2's keys (which would change the domain).
/// This is a building block of `compose`; getting it wrong
/// silently corrupts every composition.
#[test]
fn apply_subst_rewrites_range_only_not_keys() {
    // s1 = {x → 1}; s2 = {y → x}.
    // s1.apply_subst(s2) = {y → 1}.  Key y unchanged, range x → 1.
    let s1: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
    let s2: Subst<C, V> = Subst::from_list(vec![("y", var_term("x"))]);
    let result = s1.apply_subst(&s2);
    assert_eq!(
        result.image_of(&"y"),
        Some(&const_term(1)),
        "apply_subst rewrites s2's range"
    );
    assert_eq!(
        result.image_of(&"x"),
        None,
        "apply_subst must NOT add new keys"
    );
}
