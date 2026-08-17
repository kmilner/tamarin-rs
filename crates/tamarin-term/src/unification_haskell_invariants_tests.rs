// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::builtin::{fresh_var, msg_var, pair, pub_var};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::vterm::Lit;

/// Helper: extract the LVar from an `LNTerm` known to be a var lit.
fn as_var(t: &LNTerm) -> &LVar {
    match t {
        Term::Lit(Lit::Var(v)) => v,
        _ => panic!("expected var, got {:?}", t),
    }
}

// -------------------------------------------------------------------
// 1. `Ord LVar` is idx-first (LTerm.hs:546-548).
//
//    The most-easily-missed semantic choice.  Rust's `#[derive(Ord)]`
//    gives name-first lexicographic order, which is the *opposite*
//    of Haskell.  Without this, `restrict stableVars` produces
//    different post-filter substitutions, `BTreeMap<LVar, _>`
//    iteration order differs, and `applySource` enters the wrong
//    branch.
//
//    Comment from Haskell: "An ord instance that prefers the
//    'lvarIdx' over the 'lvarName'."
// -------------------------------------------------------------------

#[test]
fn lvar_ord_is_idx_first_then_sort_then_name() {
    // Same name, different idx — idx breaks the tie.
    let a = LVar::new("x", LSort::Msg, 1);
    let b = LVar::new("x", LSort::Msg, 5);
    assert!(a < b, "smaller idx must be < larger idx (same name)");

    // Different name, smaller idx beats larger name.
    // If Ord were name-first, "z.1" > "a.5".  Haskell-faithful:
    // idx-first means "z.1" < "a.5".
    let za = LVar::new("z", LSort::Msg, 1);
    let aa = LVar::new("a", LSort::Msg, 5);
    assert!(
        za < aa,
        "name 'z' idx 1 must be < name 'a' idx 5 (idx-first)"
    );

    // Same idx and sort, name as tiebreaker.
    let ax = LVar::new("a", LSort::Msg, 3);
    let bx = LVar::new("b", LSort::Msg, 3);
    assert!(ax < bx, "name 'a' < name 'b' when idx and sort tie");

    // Same idx and name, sort as tiebreaker.  LSort derive Ord puts
    // Pub < Fresh < Msg < Node < Nat (declaration order).  Haskell's
    // sort enum order is also declaration-based.
    let pa = LVar::new("a", LSort::Pub, 3);
    let fa = LVar::new("a", LSort::Fresh, 3);
    assert!(pa < fa, "Pub < Fresh as sort tiebreaker");
}

#[test]
fn lvar_ord_btreemap_iteration_is_idx_first() {
    // BTreeMap<LVar, ...> iteration order matters for goal-ranking
    // and subst.dom() iteration.  Insert in name order, expect
    // idx-first iteration.
    let mut m = std::collections::BTreeMap::new();
    m.insert(LVar::new("z", LSort::Msg, 1), 'a');
    m.insert(LVar::new("a", LSort::Msg, 10), 'b');
    m.insert(LVar::new("m", LSort::Msg, 5), 'c');
    let keys_in_order: Vec<u64> = m.keys().map(|k| k.idx).collect();
    assert_eq!(
        keys_in_order,
        vec![1, 5, 10],
        "BTreeMap iterates LVars in idx order, NOT name order"
    );
}

// -------------------------------------------------------------------
// 2. Same-sort var-var unification: larger-idx becomes the KEY.
//
//    Haskell `unifyRaw` (Unification.hs:273-281, see line 276):
//        (sl, sr) | sl == sr -> if vl < vr then elim vr l else elim vl r
//    `elim v t` makes `v` the KEY mapped to `t`.  So when vl < vr
//    (vl has smaller idx under idx-first Ord), eliminate vr →
//    LARGER-idx is the KEY.
//
//    This is the orientation that makes `restrict stableVars`
//    (Sources.hs:113-137, see line 123) work: stable pattern vars (small idx) stay
//    on the value side and get dropped by the key-filter.
// -------------------------------------------------------------------

#[test]
fn factored_unify_same_sort_order_independent_of_input_order() {
    // The orientation depends on Ord LVar, not the order of LHS/RHS
    // in the equation.  Swap and confirm same result.
    let stable = msg_var("t", 1);
    let rule_internal = msg_var("e", 10);

    let (s1, _) =
        unify_lnterm_factored(vec![Equal::new(stable.clone(), rule_internal.clone())]).unwrap();
    let (s2, _) =
        unify_lnterm_factored(vec![Equal::new(rule_internal.clone(), stable.clone())]).unwrap();

    let e_10 = *as_var(&rule_internal);
    // Both directions: e.10 (larger idx) is the key, regardless of
    // whether it was on lhs or rhs of the equation.
    assert!(s1.image_of(&e_10).is_some());
    assert!(s2.image_of(&e_10).is_some());
    assert_eq!(
        s1, s2,
        "orientation is determined by Ord LVar, not input order"
    );
}

#[test]
fn factored_unify_orients_var_var_per_haskell_when_idxs_tie() {
    // When idx ties, Haskell falls back to sort then name.  Two Msg
    // vars same idx, different names: name is final tiebreaker.
    let alpha = msg_var("a", 3);
    let beta = msg_var("b", 3);
    let (subst, _) = unify_lnterm_factored(vec![Equal::new(alpha.clone(), beta.clone())]).unwrap();
    let a_3 = *as_var(&alpha);
    let b_3 = *as_var(&beta);
    // Ord: a.3 < b.3 (idx tie → sort tie → name 'a' < 'b').
    // unifyRaw: vl=a.3, vr=b.3, vl<vr, elim vr l → b.3 is key.
    assert!(
        subst.image_of(&b_3).is_some(),
        "tiebreaker via name: 'b' (later) becomes key"
    );
    assert!(subst.image_of(&a_3).is_none());
}

// -------------------------------------------------------------------
// 3. Cross-sort var-var unification: narrower sort is the value.
//
//    Haskell `unifyRaw` (Unification.hs:278-281):
//        _ | sortGeqLTerm sortOf vl r -> elim vl r
//          | _                        -> elim vr l
//    When vl's sort ⊇ vr's sort, vl is bound to vr — the broader
//    var becomes the KEY mapping to the narrower one.
// -------------------------------------------------------------------

#[test]
fn factored_unify_cross_sort_binds_broader_to_narrower() {
    // Msg ⊃ Fresh, so Msg var must be bound to Fresh var, not the
    // reverse.  (If reversed, a Fresh var would end up mapped to
    // a Msg term — sort would be widened illegally.)
    let m: LNTerm = msg_var("m", 5);
    let f: LNTerm = fresh_var("k", 100);

    let (subst, _) = unify_lnterm_factored(vec![Equal::new(m.clone(), f.clone())]).unwrap();

    let m_v = *as_var(&m);
    let f_v = *as_var(&f);
    // The Msg var (broader sort) must be the KEY.
    assert!(
        subst.image_of(&m_v).is_some(),
        "broader sort (Msg) must be the KEY mapping to narrower (Fresh)"
    );
    assert!(
        subst.image_of(&f_v).is_none(),
        "narrower sort (Fresh) must NOT be a key"
    );
}

#[test]
fn factored_unify_pub_msg_binds_msg_to_pub() {
    // Same principle: Pub ⊂ Msg.
    let m: LNTerm = msg_var("m", 5);
    let p: LNTerm = pub_var("A", 100);

    let (subst, _) = unify_lnterm_factored(vec![Equal::new(m.clone(), p.clone())]).unwrap();

    let m_v = *as_var(&m);
    let p_v = *as_var(&p);
    assert!(subst.image_of(&m_v).is_some(), "Msg (broader) is key");
    assert!(subst.image_of(&p_v).is_none(), "Pub (narrower) is value");
}

#[test]
fn factored_unify_pub_fresh_no_unifier() {
    // Pub and Fresh are incomparable sorts — should fail.
    let p: LNTerm = pub_var("A", 1);
    let f: LNTerm = fresh_var("k", 2);
    let result = unify_lnterm_factored(vec![Equal::new(p, f)]);
    assert!(
        result.is_none(),
        "Pub and Fresh are incomparable; unification must fail \
                 (Haskell `unifyRaw` mzeros, returning Nothing)"
    );
}

// -------------------------------------------------------------------
// 4. Var-vs-term: the var is always the KEY.
//
//    Haskell `unifyRaw` (Unification.hs:283-284):
//        (Lit (Var vl), _           ) -> elim vl r
//        (_,            Lit (Var vr)) -> elim vr l
//    Both arms: the var (vl or vr) is the KEY, the term is the value.
// -------------------------------------------------------------------

#[test]
fn factored_unify_var_vs_app_binds_var_to_app() {
    // unify `x = pair(a, b)` → subst {x → pair(a, b)}, regardless
    // of which side x is on.
    let x = msg_var("x", 5);
    let p = pair(msg_var("a", 10), msg_var("b", 20));

    let (s1, _) = unify_lnterm_factored(vec![Equal::new(x.clone(), p.clone())]).unwrap();
    let (s2, _) = unify_lnterm_factored(vec![Equal::new(p.clone(), x.clone())]).unwrap();

    let x_v = *as_var(&x);
    assert_eq!(s1.image_of(&x_v), Some(&p));
    assert_eq!(s2.image_of(&x_v), Some(&p));
    assert_eq!(s1, s2);
}

// -------------------------------------------------------------------
// 5. `unifyLTermFactored` separates non-AC from AC residuals.
//
//    Haskell (Unification.hs:120-133):
//        unifyLTermFactored sortOf eqs = ... do
//            solve h $ execRWST unif sortOf M.empty
//        unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
//        solve _ (Just (m, [])) = (substFromMap m, [emptySubstVFresh])
//
//    For AC-free input, returns the local subst with EMPTY residuals.
//    For mixed input, returns (local subst, residuals) where the
//    residuals are AC equations only.
// -------------------------------------------------------------------

#[test]
fn factored_unify_returns_empty_residuals_on_ac_free_input() {
    // All non-AC: pair + msg_var, no XOR/mset/DH/nat/BP.
    let p1: LNTerm = pair(msg_var("a", 1), msg_var("b", 2));
    let p2: LNTerm = pair(msg_var("x", 10), msg_var("y", 20));
    let (subst, residuals) =
        unify_lnterm_factored(vec![Equal::new(p1, p2)]).expect("non-AC pair-pair must unify");
    assert!(
        residuals.is_empty(),
        "AC-free input → empty residuals (matches Haskell's \
                 `solve _ (Just (m, []))` branch).  If this fires, the \
                 unifier is incorrectly classifying something as AC."
    );
    // Subst has at least the 4 var bindings.
    assert!(
        !subst.is_empty(),
        "non-trivial input produces non-empty subst"
    );
}

#[test]
fn factored_unify_trivial_var_eq_self_returns_empty() {
    // `x = x` is trivially true — Haskell short-circuits before
    // emitting a binding.
    let x: LNTerm = msg_var("x", 5);
    let (subst, residuals) =
        unify_lnterm_factored(vec![Equal::new(x.clone(), x)]).expect("x = x must unify trivially");
    assert!(residuals.is_empty());
    assert!(
        subst.is_empty(),
        "x = x must NOT introduce a self-loop binding"
    );
}

#[test]
fn factored_unify_unsatisfiable_returns_none() {
    // pair(x, y) vs single-arg constructor → no unifier.
    let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
    let k: LNTerm = crate::builtin::pk(msg_var("z", 0));
    assert!(unify_lnterm_factored(vec![Equal::new(p, k)]).is_none());
}

// -------------------------------------------------------------------
// 6. Local non-AC subst with chained var-var: only the final
//    representative survives as key when both vars are stable.
//
//    This is the foo_eligibility-class invariant: when we unify
//    `m.19 = blind(...)` AFTER having unified `t.1 = m.19`, the
//    resulting subst should have `t.1 → blind(...)` AND
//    `m.19 → blind(...)` (eliminate substitutes the value through
//    the accumulator).
//
//    Important: the orientation of `t.1 = m.19` (Haskell-faithful:
//    m.19 → t.1, so larger-idx is key) means after we then unify
//    m.19 with blind(...), m.19's existing binding to t.1 doesn't
//    create a t.1 entry — because applying the eliminate's
//    `apply_vterm(s, t)` to t.1 (not in m.19→t.1's domain) leaves
//    t.1 unchanged.  So t.1 stays unbound.
// -------------------------------------------------------------------

#[test]
fn factored_unify_chained_var_var_then_var_term() {
    // Step 1: unify t.1 = m.19.  Haskell: m.19 → t.1.
    // Step 2: unify m.19 = blind(...) (using `pair` as stand-in).
    //         After snapshot apply, m.19 substituted to t.1; then
    //         t.1 = pair(...) eliminates t.1 → pair(...).
    //         The chain: m.19 → t.1 → pair(...).  Eliminate
    //         substitutes t.1 into m.19's value, giving m.19 → pair(...).
    //         So final acc: {m.19 → pair(...), t.1 → pair(...)}.
    //
    // This is exactly the foo_eligibility shape — both bindings
    // exist, but the KEY for the "structural" binding (pair) is on
    // both t.1 AND m.19.
    let t_1 = msg_var("t", 1);
    let m_19 = msg_var("m", 19);
    let blind = pair(msg_var("m", 28), msg_var("r", 28));

    let (subst, _) = unify_lnterm_factored(vec![
        Equal::new(t_1.clone(), m_19.clone()),
        Equal::new(m_19.clone(), blind.clone()),
    ])
    .unwrap();

    let t_1_v = *as_var(&t_1);
    let m_19_v = *as_var(&m_19);
    assert_eq!(
        subst.image_of(&m_19_v),
        Some(&blind),
        "m.19 must end bound to the structural term"
    );
    // Crucially, t.1 should ALSO be bound — because eliminate(t.1, pair)
    // happens after snapshot apply of m.19→t.1, so the second eq
    // becomes t.1 = pair(...).  Both bindings end up.
    assert_eq!(
        subst.image_of(&t_1_v),
        Some(&blind),
        "t.1 must also end bound (eliminate adds it as key)"
    );
}

// -------------------------------------------------------------------
// 7. Occurs check (Unification.hs:310-315, see line 311): `v `occurs` t` → no unifier.
// -------------------------------------------------------------------

#[test]
fn factored_unify_occurs_check() {
    // x = pair(x, y) — x occurs in RHS → no unifier.
    let x: LNTerm = msg_var("x", 0);
    let rhs: LNTerm = pair(x.clone(), msg_var("y", 0));
    assert!(unify_lnterm_factored(vec![Equal::new(x, rhs)]).is_none());
}

// -------------------------------------------------------------------
// 8. The factored unify and the older `unify_lnterm_no_ac` agree on
//    orientation for var-vs-non-var (both bind the var to the term)
//    AND on same-sort var-var (Haskell-faithful: larger-idx is key,
//    Unification.hs:273-281, see line 276).  These tests pin both invariants.
// -------------------------------------------------------------------

#[test]
fn old_and_factored_unify_agree_on_var_vs_term() {
    let x = msg_var("x", 5);
    let p = pair(msg_var("a", 10), msg_var("b", 20));
    let old = unify_lnterm_no_ac(vec![Equal::new(x.clone(), p.clone())]).unwrap();
    let (new_, _) = unify_lnterm_factored(vec![Equal::new(x.clone(), p.clone())]).unwrap();
    assert_eq!(
        old, new_,
        "for var-vs-term, both unifiers must produce identical \
                    substs (the var is the key in both)"
    );
}

#[test]
fn old_and_factored_unify_agree_on_same_sort_var_var_orientation() {
    // Both paths follow Haskell `unifyRaw` (Unification.hs:273-281, see line 276):
    //   `if vl < vr then elim vr l else elim vl r`
    // i.e. LARGER-idx becomes KEY, smaller-idx becomes value.
    // This is the exact pattern from foo_eligibility's saturate.  `t.1` is a
    // stable pattern var, and `e.10` is rule-internal.
    let small = msg_var("t", 1); // small idx, "stable"
    let large = msg_var("e", 10); // large idx

    let old = unify_lnterm_no_ac(vec![Equal::new(small.clone(), large.clone())]).unwrap();
    let (new_, residuals) =
        unify_lnterm_factored(vec![Equal::new(small.clone(), large.clone())]).unwrap();
    assert!(residuals.is_empty(), "no AC stuff, no residuals");

    let small_v = *as_var(&small);
    let large_v = *as_var(&large);

    // Haskell-faithful: larger-idx is key in BOTH paths.
    assert!(
        old.image_of(&large_v).is_some(),
        "`unify_raw`: larger-idx (e.10) is the key"
    );
    assert!(old.image_of(&small_v).is_none());
    assert!(
        new_.image_of(&large_v).is_some(),
        "`unify_raw_factored`: larger-idx (e.10) is the key"
    );
    assert!(
        new_.image_of(&small_v).is_none(),
        "smaller-idx (t.1, stable) must NOT be a key — otherwise \
                    `restrict stableVars` would keep it and downstream \
                    applySource would see a baked-in binding instead of an \
                    unbound stable var"
    );

    assert_eq!(
        old, new_,
        "Both unifiers must produce identical substs \
                    (Haskell-faithful: Unification.hs:276)."
    );
}
