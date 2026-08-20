// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::test_maude::maude_path;
use tamarin_term::lterm::LSort;
use tamarin_term::subst_vfresh::SubstVFresh;

fn fresh_subst() -> LNSubstVFresh {
    let v = LVar::new("x", LSort::Msg, 0);
    let t =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new("y", LSort::Msg, 0)));
    SubstVFresh::from_list(vec![(v, t)])
}

// A distinct subst per `idx`.  `add_disj`/`add_rule_variants` dedup
// identical substs (HS-faithful `S.fromList`, EquationStore.hs),
// so building a multi-element disjunction from repeated `fresh_subst()`
// collapses to a single element.  Tests that need a genuine N-element
// disjunction use distinct substs via this helper.
fn fresh_subst_n(idx: u64) -> LNSubstVFresh {
    let v = LVar::new("x", LSort::Msg, idx);
    let t = tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
        "y",
        LSort::Msg,
        idx,
    )));
    SubstVFresh::from_list(vec![(v, t)])
}

#[test]
fn empty_store_is_consistent() {
    let s = EquationStore::empty();
    assert!(!s.is_false());
    assert!(s.splits().is_empty());
}

#[test]
fn empty_disj_makes_store_false() {
    let mut s = EquationStore::empty();
    let id = s.add_disj(vec![]);
    assert_eq!(id, SplitId(0));
    assert!(s.is_false());
}

#[test]
fn add_disj_assigns_fresh_ids() {
    let mut s = EquationStore::empty();
    let id1 = s.add_disj(vec![fresh_subst()]);
    let id2 = s.add_disj(vec![fresh_subst_n(0), fresh_subst_n(1)]);
    assert_eq!(id1, SplitId(0));
    assert_eq!(id2, SplitId(1));
    assert!(!s.is_false());
    assert_eq!(s.split_size(id1), Some(1));
    assert_eq!(s.split_size(id2), Some(2));
    assert!(s.split_exists(id2));
}

#[test]
fn splits_sorted_by_size() {
    let mut s = EquationStore::empty();
    // Distinct substs, or `add_disj`'s dedup would collapse `big` to one
    // case and both disjunctions would tie on size.  `big` is added LAST,
    // so it heads `conj`: the assertions below fail unless `splits` really
    // reorders by size.
    let small = s.add_disj(vec![fresh_subst_n(0)]);
    let big = s.add_disj(vec![fresh_subst_n(1), fresh_subst_n(2), fresh_subst_n(3)]);
    assert_eq!(
        s.conj[0].split_id, big,
        "conj is insertion-ordered, big first"
    );
    let sorted = s.splits();
    assert_eq!(sorted[0], small);
    assert_eq!(sorted[1], big);
}

#[test]
fn perform_split_branches() {
    let mut s = EquationStore::empty();
    let id = s.add_disj(vec![fresh_subst_n(0), fresh_subst_n(1)]);
    let branches = s.perform_split(id).unwrap();
    assert_eq!(branches.len(), 2);
    // Each branch contains a single-case disjunction.
    for b in &branches {
        assert_eq!(b.conj.len(), 1);
        assert_eq!(b.conj[0].substs.len(), 1);
    }
}

#[test]
fn perform_split_unknown_id() {
    let s = EquationStore::empty();
    assert!(s.perform_split(SplitId(42)).is_none());
}

/// A subst mapping `x.k ↦ y.v` for each `(k, v)` pair.
fn subst_xy(pairs: &[(u64, u64)]) -> LNSubstVFresh {
    SubstVFresh::from_list(pairs.iter().map(|(k, v)| {
        (
            LVar::new("x", LSort::Msg, *k),
            tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new(
                "y",
                LSort::Msg,
                *v,
            ))),
        )
    }))
}

// `ordered_substs` needs BOTH stages, applied in that order: the
// α-canonical `drop_name_hints` key decides whenever two keys differ,
// and the raw `Ord` (`S.toList`) order underneath breaks the ties the
// key leaves, because the key sort is stable.
#[test]
fn ordered_substs_applies_both_sort_stages() {
    // Canonical keys DIFFER here and disagree with raw `Ord`: raw
    // compares the `x` images first (y.2 < y.5), while the canonical key
    // ties on `x` (both renumber to _0) and compares the `x.1` images
    // (_0 < _1).
    let repeated = subst_xy(&[(0, 5), (1, 5)]); // canonical {x ↦ _0, x.1 ↦ _0}
    let distinct = subst_xy(&[(0, 2), (1, 7)]); // canonical {x ↦ _0, x.1 ↦ _1}
    assert!(distinct < repeated, "raw Ord puts `distinct` first");
    assert!(
        repeated.drop_name_hints() < distinct.drop_name_hints(),
        "canonical key puts `repeated` first"
    );
    for input in [
        vec![repeated.clone(), distinct.clone()],
        vec![distinct.clone(), repeated.clone()],
    ] {
        assert_eq!(
            ordered_substs(&input),
            vec![&repeated, &distinct],
            "canonical key must decide when the keys differ"
        );
    }

    // Canonical keys TIE (both {x ↦ _0}), so the raw order underneath is
    // what survives — and it is not the stored order.
    let hi = subst_xy(&[(0, 5)]);
    let lo = subst_xy(&[(0, 3)]);
    assert_eq!(hi.drop_name_hints(), lo.drop_name_hints());
    assert_eq!(ordered_substs(&[hi.clone(), lo.clone()]), vec![&lo, &hi]);
}

// The cases `perform_split` emits carry positional `split_case_i` labels,
// so their order is `ordered_substs`' order — the same helper
// `pretty_system::pp_disj` numbers a displayed disjunction with.
#[test]
fn perform_split_cases_follow_ordered_substs() {
    let substs = vec![subst_xy(&[(0, 5)]), subst_xy(&[(0, 3)])];
    let mut store = EquationStore::empty();
    // Pushed verbatim: `add_disj` would apply the raw `Ord` sort itself.
    store.conj.push(EqDisj {
        split_id: SplitId(0),
        substs: substs.clone(),
    });
    store.next_split = SplitId(1);
    let cases: Vec<LNSubstVFresh> = store
        .perform_split(SplitId(0))
        .expect("split exists")
        .into_iter()
        .map(|b| b.conj[0].substs[0].clone())
        .collect();
    let expected: Vec<LNSubstVFresh> = ordered_substs(&substs).into_iter().cloned().collect();
    assert_eq!(cases, expected);
    assert_ne!(cases, substs, "the stored order is not the case order");
}

#[test]
fn set_false_marks_store_false() {
    let s = EquationStore::empty().set_false();
    assert!(s.is_false());
}

#[test]
fn rule_variants_added_as_disjunction() {
    let mut store = EquationStore::empty();
    let id = store
        .add_rule_variants(vec![fresh_subst_n(0), fresh_subst_n(1)])
        .expect("add_rule_variants");
    assert_eq!(id, SplitId(0));
    assert_eq!(store.split_size(id), Some(2));
}

#[test]
fn rule_variants_rejects_overlapping_domain() {
    let mut store = EquationStore::empty();
    // Pre-populate the free subst with `x`.
    let v = LVar::new("x", LSort::Msg, 0);
    let t =
        tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(LVar::new("z", LSort::Msg, 0)));
    store.subst = LNSubst::from_list(vec![(v, t)]);
    // Variant subst also touches `x`.
    let res = store.add_rule_variants(vec![fresh_subst()]);
    assert!(res.is_err());
}

#[test]
fn simp_empty_disj_makes_store_false() {
    let mut store = EquationStore::empty();
    // Add an empty disjunction.
    let _ = store.add_disj(vec![]);
    let changed = store.simp_empty_disj();
    assert!(changed);
    assert!(store.is_false());
}

/// `simp` runs its passes to a fixpoint. HS does the same with the `changed`
/// loop in `simp1`. A second run must therefore change nothing on a store that
/// the first run already settled. The settled store must also still hold the
/// disjunction. No pass may empty the store or make it false. A pass must not
/// treat a satisfiable singleton as a contradiction.
#[test]
fn simp_is_idempotent_on_a_consistent_store() {
    let mut store = EquationStore::empty();
    let id = store.add_disj(vec![fresh_subst()]);
    let once = store.simp(|_, _| false);
    assert!(!once.is_false());
    assert_eq!(once.split_size(id), Some(1), "the disjunction survives");
    let twice = once.clone().simp(|_, _| false);
    assert_eq!(twice, once, "simp must already be at its fixpoint");
}

#[test]
fn simp_abstract_name_factors_common_constant() {
    // Build a two-case disjunction where every subst maps `x → 'foo'` (pub
    // constant) while disagreeing on `y`. simp_abstract_name should hoist
    // the common `x` mapping into the free substitution and leave `y` alone.
    // The cases must differ, or `add_disj`'s dedup would collapse them to
    // one and the "common to every subst" condition would be vacuous.
    use tamarin_term::lterm::{Name, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let con = |n: &str| -> LNTerm { Term::Lit(Lit::Con(Name::new(NameTag::Pub, n.to_string()))) };
    let v = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let foo = con("foo");
    let s1 = LNSubstVFresh::from_list(vec![(v, foo.clone()), (y, con("a"))]);
    let s2 = LNSubstVFresh::from_list(vec![(v, foo.clone()), (y, con("b"))]);
    let mut store = EquationStore::empty();
    let id = store.add_disj(vec![s1, s2]);
    assert_eq!(store.split_size(id), Some(2), "both cases must survive");
    assert!(store.simp_abstract_name());
    // Free subst should now contain x → foo.
    let dom: Vec<&LVar> = store.subst.dom().collect();
    assert_eq!(dom, vec![&v]);
}

#[test]
fn add_eqs_xor_produces_disjunction() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::xor_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
    // x XOR a =? b XOR y has multiple AC unifiers.
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::term::{f_app_ac, Term};
    use tamarin_term::vterm::Lit;
    let v = |n: &str| LVar::new(n, LSort::Msg, 0);
    let lhs: LNTerm = f_app_ac(
        AcSym::Xor,
        vec![Term::Lit(Lit::Var(v("x"))), Term::Lit(Lit::Var(v("a")))],
    );
    let rhs: LNTerm = f_app_ac(
        AcSym::Xor,
        vec![Term::Lit(Lit::Var(v("b"))), Term::Lit(Lit::Var(v("y")))],
    );
    let mut store = EquationStore::empty();
    let split = store
        .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs, rhs }])
        .expect("add_eqs xor");
    // AC unification has many unifiers, so we should get a fresh disjunction.
    assert!(split.is_some(), "expected disjunction split");
    assert!(!store.is_false());
    assert!(!store.conj.is_empty());
}

/// `removePermutations` drops the substitutions of a disjunction that
/// only permute the images of the two given variables — here through the
/// `equalUpToRenaming` branch, whose swapped call fails on the pair-vs-var
/// shape and whose unswapped call matches.  Substitutions of a different
/// domain size are never permutations of each other and survive.
#[test]
fn remove_permutations_drops_renamed_variants() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
    use tamarin_term::function_symbols::{pair_sym, FunSym};
    use tamarin_term::term::{f_app, Term};
    use tamarin_term::vterm::Lit;
    let msg = |n: &'static str, i: u64| LVar::new(n, LSort::Msg, i);
    let var = |n: &'static str, i: u64| -> LNTerm { Term::Lit(Lit::Var(msg(n, i))) };
    let pair = |t: LNTerm| f_app(FunSym::NoEq(pair_sym()), vec![t.clone(), t]);
    let v1 = msg("x", 1);
    let v2 = msg("x", 2);
    // `keep` and `renamed` are equal up to a renaming of their msg-var
    // images; `wider` binds a third variable.
    let keep = SubstVFresh::from_list(vec![(v1, pair(var("y", 1))), (v2, var("y", 2))]);
    let renamed = SubstVFresh::from_list(vec![(v1, pair(var("z", 3))), (v2, var("z", 4))]);
    let wider = SubstVFresh::from_list(vec![
        (v1, pair(var("y", 1))),
        (v2, var("y", 2)),
        (msg("w", 5), var("y", 6)),
    ]);
    let mut store = EquationStore::empty();
    let id = store.add_disj(vec![keep.clone(), renamed, wider.clone()]);
    let store = store
        .remove_permutations(&h, id, &v1, &v2)
        .expect("remove_permutations");
    let kept = &store
        .conj
        .iter()
        .find(|d| d.split_id == id)
        .expect("split survives")
        .substs;
    assert_eq!(kept, &vec![keep, wider]);
}

// =========================================================================
// Haskell-faithfulness invariants for `add_eqs`.
//
// These tests pin the eq-store's orientation choices.  See
// `tamarin_term::unification::haskell_invariants_tests` for the rationale.
// =========================================================================

/// `add_eqs` for AC-free, same-sort var-var input must orient the
/// resulting subst with LARGER-idx as KEY (Haskell `unifyRaw`
/// convention, Unification.hs:273-281, see line 276).
///
/// This is the most important orientation invariant for downstream
/// `restrict stableVars`: stable pattern vars (small idx) must stay
/// on the VALUE side so they get filtered out (they're never keys
/// in Haskell's subst).
///
/// **If this test fails, foo_eligibility-class divergences will
/// silently appear in the corpus.**
#[test]
fn add_eqs_ac_free_var_var_uses_haskell_orientation() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");

    // Mimic the foo_eligibility shape: stable pattern var t.1 unified
    // with rule-internal var e.10.  Both Msg, same sort.  Haskell
    // convention: e.10 (larger idx) is the key.
    let t1 = LVar::new("t", LSort::Msg, 1);
    let e10 = LVar::new("e", LSort::Msg, 10);
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let lt1: LNTerm = Term::Lit(Lit::Var(t1));
    let le10: LNTerm = Term::Lit(Lit::Var(e10));

    let mut store = EquationStore::empty();
    let split = store
        .add_eqs(
            &h,
            &[tamarin_term::rewriting::Equal {
                lhs: lt1,
                rhs: le10,
            }],
        )
        .expect("add_eqs");
    assert!(split.is_none(), "var-var unification produces a single mgu");
    assert!(!store.is_false());

    // Haskell-faithful: e.10 (larger idx) is the KEY.
    assert!(
        store.subst.image_of(&e10).is_some(),
        "add_eqs MUST orient same-sort var-var with larger-idx (e.10) \
                 as KEY.  If this fails, foo_eligibility::eligibility and \
                 friends will silently diverge from Haskell."
    );
    assert!(
        store.subst.image_of(&t1).is_none(),
        "smaller-idx (t.1, the stable pattern var) must NOT be a key"
    );
}

/// `add_eqs` for an unbinding (`x = y` where neither is in the
/// existing subst) must NOT introduce a Maude witness ~mw.
///
/// We use the local non-AC fast path for AC-free signatures, which
/// just orients the bind directly.  If we accidentally regress to
/// the witness-heavy Maude shape (`{x → ~mw, y → ~mw}`), the
/// downstream `enforce_fresh_node_uniqueness_pass` will bucket
/// nodes by witness and merge Fresh nodes that should stay
/// distinct (the TLS_Handshake prem_idx_clash class).
#[test]
fn add_eqs_ac_free_var_var_does_not_introduce_witness() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let tx: LNTerm = Term::Lit(Lit::Var(x));
    let ty: LNTerm = Term::Lit(Lit::Var(y));
    let mut store = EquationStore::empty();
    let _ = store
        .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }])
        .expect("add_eqs");
    assert!(
        !store.subst.is_empty(),
        "same-sort var-var unification must bind one of the two vars — \
         an empty subst makes the witness scan below vacuous"
    );

    // Unifying two free Msg vars must yield a simple orientation
    // between x and y (HS-faithful var-var orient gives `{y → x}`),
    // NOT a fresh `~mw`-style witness.  So flag any subst var that is
    // neither x nor y — that would be a freshly-introduced witness.
    // (Witness introduction here regressed TLS_Handshake::prem_idx_clash.)
    // x legitimately appears in the range of `{y → x}`, so the check
    // below flags any subst var other than x or y, not just non-`x`
    // values.
    use tamarin_term::lterm::HasFrees;
    let mut witness_found = false;
    for (key, term) in store.subst.to_list() {
        if key.name != "x" && key.name != "y" {
            witness_found = true;
        }
        term.for_each_free(&mut |v| {
            if v.name != "x" && v.name != "y" {
                witness_found = true;
            }
        });
    }
    assert!(
        !witness_found,
        "AC-free var-var unification must NOT introduce ~mw \
                 witnesses.  Witness introduction here regressed \
                 TLS_Handshake::prem_idx_clash historically."
    );
}

/// `add_eqs` is idempotent for an already-implied equation.
///
/// If the eq-store already has `x → 1`, calling `add_eqs([x = 1])`
/// must NOT introduce new bindings or witnesses or contradictions.
/// This is a regression guard for the eq-store's snapshot/apply
/// chain in `add_eqs_inner` (we apply `self.subst` to inputs first).
#[test]
fn add_eqs_idempotent_for_already_implied_eq() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 5);
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let tx: LNTerm = Term::Lit(Lit::Var(x));
    let ty: LNTerm = Term::Lit(Lit::Var(y));
    let mut store = EquationStore::empty();
    let _ = store
        .add_eqs(
            &h,
            &[tamarin_term::rewriting::Equal {
                lhs: tx.clone(),
                rhs: ty.clone(),
            }],
        )
        .expect("first add_eqs");
    let dom_before: Vec<LVar> = store.subst.dom().copied().collect();

    // Repeat — should be a no-op.
    let _ = store
        .add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs: tx, rhs: ty }])
        .expect("second add_eqs");
    let dom_after: Vec<LVar> = store.subst.dom().copied().collect();
    assert_eq!(
        dom_before, dom_after,
        "Repeated add_eqs of an already-implied equation must \
                    not change the subst domain."
    );
    assert!(
        !store.is_false(),
        "Repeating an equation must not produce a contradiction."
    );
}

/// `add_eqs` with an unsatisfiable input marks the store false.
///
/// Constructor mismatch (pair vs pk) is unsatisfiable in non-AC.
/// Our `add_eqs_inner` should set the store to false, not panic or
/// silently succeed.
#[test]
fn add_eqs_unsatisfiable_sets_store_false() {
    let Some(path) = maude_path() else { return };
    let sig = tamarin_term::maude_sig::pair_maude_sig();
    let h = tamarin_term::maude_proc::MaudeHandle::start(&path, sig).expect("start");
    use tamarin_term::builtin::{msg_var, pair, pk};
    let lhs: LNTerm = pair(msg_var("a", 1), msg_var("b", 2));
    let rhs: LNTerm = pk(msg_var("c", 3));
    let mut store = EquationStore::empty();
    let _ = store.add_eqs(&h, &[tamarin_term::rewriting::Equal { lhs, rhs }]);
    assert!(
        store.is_false(),
        "constructor mismatch must set store to false"
    );
}
