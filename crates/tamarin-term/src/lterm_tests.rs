// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::function_symbols::pair_sym;
use crate::term::f_app_no_eq;
use crate::vterm::var_term;

#[test]
fn deep_free_walks_and_cow_maps_use_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let mut t: LNTerm = var_term(x);
        for _ in 0..32768 {
            t = f_app_no_eq(pair_sym(), vec![t, var_term(y)]);
        }
        let seen = frees_list(&t);
        assert_eq!(seen.len(), 32769);
        assert_eq!(seen[0], x);
        assert!(seen[1..].iter().all(|v| *v == y));
        let identity = t.clone().map_free(&mut |v| v);
        let (Term::App(_, original), Term::App(_, unchanged)) = (&t, &identity) else {
            unreachable!()
        };
        assert_eq!(original.as_ptr(), unchanged.as_ptr());
        for monotone in [false, true] {
            let mapped = t
                .clone()
                .map_free_with(&mut |v| LVar::new(v.name, v.sort, v.idx + 1), monotone);
            let vars = frees_list(&mapped);
            assert_eq!(vars.len(), seen.len());
            assert!(vars
                .iter()
                .zip(&seen)
                .all(|(a, b)| a.name == b.name && a.idx == b.idx + 1));
        }
    });
}

#[test]
fn free_mapping_keeps_monotone_order_and_normalizes_arbitrary_changes() {
    use crate::function_symbols::{AcSym, FunSym};
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("x", LSort::Msg, 1);
    let term: LNTerm = crate::term::f_app_ac(AcSym::Mult, vec![var_term(x), var_term(y)]);
    let reversed = term.clone().map_free(&mut |v| if v == x { y } else { x });
    assert_eq!(reversed, term);
    let shifted = term
        .clone()
        .map_free_monotone(&mut |v| LVar::new(v.name, v.sort, v.idx + 10));
    assert_eq!(
        shifted,
        crate::term::f_app(
            FunSym::Ac(AcSym::Mult),
            vec![
                var_term(LVar::new("x", LSort::Msg, 10)),
                var_term(LVar::new("x", LSort::Msg, 11))
            ]
        )
    );
}

/// `Name`'s derived `Ord` compares the tag before the identifier, and
/// `NameId`'s compares its one string, as HS's declarations do.
#[test]
fn name_ord_compares_the_tag_before_the_id() {
    let fresh_z = Name::new(NameTag::Fresh, "z");
    let pub_a = Name::new(NameTag::Pub, "a");
    assert!(fresh_z < pub_a, "the tag decides before the identifier");
    assert!(Name::new(NameTag::Pub, "a") < Name::new(NameTag::Pub, "b"));
    assert!(NameId::new("a") < NameId::new("b"));
}

/// `Bound` before `Free`, the variant order of HS's `BVar v`.
#[test]
fn bvar_ord_puts_bound_before_free() {
    let bound: BVar<LVar> = BVar::Bound(9);
    let free = BVar::Free(LVar::new("x", LSort::Msg, 0));
    assert!(bound < free);
    assert!(BVar::<LVar>::Bound(0) < BVar::Bound(1));
}

#[test]
fn name_sort_mapping() {
    assert_eq!(sort_of_name(&Name::new(NameTag::Fresh, "k")), LSort::Fresh);
    assert_eq!(sort_of_name(&Name::new(NameTag::Pub, "p")), LSort::Pub);
    assert_eq!(sort_of_name(&Name::new(NameTag::Node, "n")), LSort::Node);
    assert_eq!(sort_of_name(&Name::new(NameTag::Nat, "n")), LSort::Nat);
    // The web abbreviation tag has no sort of its own.  It falls back to
    // Msg (LTerm.hs:266).  It is the one tag whose sort does not carry
    // the name of the tag.
    assert_eq!(sort_of_name(&Name::new(NameTag::Abbrev, "a")), LSort::Msg);
}

#[test]
fn arc_walks_and_maps_the_payload() {
    use std::sync::Arc;
    let v = LVar::new("x", LSort::Msg, 3);
    let shared: Arc<LNTerm> = Arc::new(var_term(v));
    assert_eq!(frees_list(&shared), vec![v]);
    // A second handle forces the payload to be cloned before it is
    // mapped, and leaves the original handle's term alone.
    let other = Arc::clone(&shared);
    let mapped = other.map_free(&mut |w| LVar::new(w.name, w.sort, w.idx + 1));
    assert_eq!(*mapped, var_term(LVar::new("x", LSort::Msg, 4)));
    assert_eq!(*shared, var_term(v));
}

#[test]
fn lvar_predicates() {
    let v = LVar::new("x", LSort::Msg, 0);
    let t: LNTerm = var_term(v);
    assert!(is_msg_var(&t));
    assert!(!is_pub_var(&t));
    assert_eq!(get_var(&t), Some(&v));
}

/// The `LSortNode` guard is the MinValueEq `WrongEquality` invariant: a
/// message variable is not a node id, so a negated equality over two of
/// them stays a formula instead of splitting into an ordering
/// disjunction.
#[test]
fn lterm_node_id_rejects_a_message_sorted_variable() {
    let i = LVar::new("i", LSort::Node, 0);
    let n: LNTerm = var_term(i);
    assert_eq!(lterm_node_id(&n), Some(i));
    let m: LNTerm = var_term(LVar::new("a", LSort::Msg, 0));
    assert_eq!(lterm_node_id(&m), None);
}

#[test]
fn lterm_node_id_rejects_an_application() {
    let n: LNTerm = var_term(LVar::new("i", LSort::Node, 0));
    let t: LNTerm = f_app_no_eq(pair_sym(), vec![n.clone(), n]);
    assert_eq!(lterm_node_id(&t), None);
}

#[test]
fn pub_const_check() {
    let p: LNTerm = pub_term("alice");
    assert!(is_pub_const(&p));
    let f: LNTerm = fresh_term("k");
    assert!(!is_pub_const(&f));
}

#[test]
fn flattened_ac_extracts_terms() {
    use crate::function_symbols::AcSym;
    use crate::term::f_app_ac;
    let a: LNTerm = pub_term("a");
    let b: LNTerm = pub_term("b");
    let c: LNTerm = pub_term("c");
    let inner: LNTerm = f_app_ac(AcSym::Mult, vec![a.clone(), b.clone()]);
    let outer: LNTerm = f_app_ac(AcSym::Mult, vec![inner, c.clone()]);
    // The children come back in their AC-sorted order, and not merely as
    // three children.  Callers index this list by position.
    assert_eq!(flattened_ac_terms(AcSym::Mult, &outer), vec![&a, &b, &c]);
    // A different AC operator does not flatten the term.  The complete
    // term comes back as the single child.
    assert_eq!(flattened_ac_terms(AcSym::Xor, &outer), vec![&outer]);
}

#[test]
fn flattened_ac_terms_handles_raw_deep_nesting_on_a_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let leaf: LNTerm = pub_term("a");
        let mut nested = leaf.clone();
        for _ in 0..32768 {
            nested = Term::App(FunSym::Ac(AcSym::Mult), vec![nested].into());
        }
        assert_eq!(flattened_ac_terms(AcSym::Mult, &nested), vec![&leaf]);
    });
}

#[test]
fn contains_private_detects_private_symbol() {
    // diff is private.
    let t: LNTerm = f_app_no_eq(
        crate::function_symbols::diff_sym(),
        vec![pub_term("a"), pub_term("b")],
    );
    assert!(contains_private(&t));
    let t: LNTerm = f_app_no_eq(pair_sym(), vec![pub_term("a"), pub_term("b")]);
    assert!(!contains_private(&t));
}

// =========================================================================
// Haskell-faithfulness invariants for enum declaration order.
//
// For every Haskell `data X = A | B | C deriving (Ord, ...)`, the
// induced `Ord` is the declaration order.  If our Rust enum reorders
// variants, BTreeMap/BTreeSet iteration over X-keyed maps silently
// sorts differently — and proof state inspection by downstream code
// (goal-ranking, case dedup, source-case ordering) diverges.
//
// **Pin every Ord-bearing enum's declaration order to its Haskell
// counterpart by checked file:line below.**
// =========================================================================

/// LTerm.hs:165-170:
///     data LSort = LSortPub | LSortFresh | LSortMsg | LSortNode | LSortNat
///                deriving( Eq, Ord, ... )
#[test]
fn lsort_ord_matches_haskell_declaration() {
    // Pub < Fresh < Msg < Node < Nat
    assert!(LSort::Pub < LSort::Fresh);
    assert!(LSort::Fresh < LSort::Msg);
    assert!(LSort::Msg < LSort::Node);
    assert!(LSort::Node < LSort::Nat);
    // Transitive.
    assert!(LSort::Pub < LSort::Nat);
}

/// LTerm.hs:219:
///     data NameTag = FreshName | PubName | NodeName | NatName | AbbrevName
#[test]
fn name_tag_ord_matches_haskell_declaration() {
    assert!(NameTag::Fresh < NameTag::Pub);
    assert!(NameTag::Pub < NameTag::Node);
    assert!(NameTag::Node < NameTag::Nat);
    assert!(NameTag::Nat < NameTag::Abbrev);
}

/// Haskell `sortCompare` (LTerm.hs:181-191) is a PARTIAL ORDER, NOT
/// the same as `Ord LSort`.  Specifically:
///   - Msg is greater than every other comparable sort
///   - Node is incomparable to ALL other sorts (returns Nothing)
///   - Pub, Fresh, Nat are pairwise incomparable
///
/// **Do not confuse with `Ord LSort`.** `Ord LSort` is the derived
/// total order from declaration order, used as BTreeMap/Set key.
/// `sortCompare` is the order-sorted lattice used during unification
/// for sort narrowing.  Mixing them up breaks unify_raw cross-sort
/// handling.
#[test]
fn sort_compare_is_partial_not_total() {
    // Reflexive.
    assert_eq!(
        sort_compare(LSort::Fresh, LSort::Fresh),
        Some(Ordering::Equal)
    );
    // Comparable: Msg dominates, in both directions.
    assert_eq!(sort_compare(LSort::Fresh, LSort::Msg), Some(Ordering::Less));
    assert_eq!(
        sort_compare(LSort::Msg, LSort::Pub),
        Some(Ordering::Greater)
    );
    assert_eq!(
        sort_compare(LSort::Msg, LSort::Fresh),
        Some(Ordering::Greater)
    );
    assert_eq!(
        sort_compare(LSort::Msg, LSort::Nat),
        Some(Ordering::Greater)
    );
    // Pub, Fresh, Nat are pairwise incomparable.
    assert_eq!(sort_compare(LSort::Pub, LSort::Fresh), None);
    assert_eq!(sort_compare(LSort::Pub, LSort::Nat), None);
    assert_eq!(sort_compare(LSort::Fresh, LSort::Nat), None);
    // Node is incomparable to all.
    assert_eq!(sort_compare(LSort::Node, LSort::Msg), None);
    assert_eq!(sort_compare(LSort::Node, LSort::Pub), None);
    assert_eq!(sort_compare(LSort::Node, LSort::Fresh), None);
    assert_eq!(sort_compare(LSort::Node, LSort::Nat), None);
    // BUT `Ord LSort` total order differs!  Pub < Fresh < Msg < Node
    // in Ord, even though Pub vs Fresh is incomparable in sortCompare.
    assert!(
        LSort::Pub < LSort::Fresh,
        "Ord LSort is total — Pub < Fresh by declaration order. \
                 (sort_compare returns None for this pair; the two \
                 contracts are deliberately different.)"
    );
}

/// LTerm.hs `sortPrefix`: sort prefixes for variable rendering.  These
/// show up in the proof skeleton as `~k` / `$A` / `#i` / `%n` and a parse
/// regression in the renderer would break corpus diffing.
#[test]
fn sort_prefixes_match_haskell() {
    assert_eq!(sort_prefix(LSort::Fresh), "~");
    assert_eq!(sort_prefix(LSort::Pub), "$");
    assert_eq!(sort_prefix(LSort::Node), "#");
    assert_eq!(sort_prefix(LSort::Nat), "%");
    assert_eq!(sort_prefix(LSort::Msg), "");
}

/// LTerm.hs sort suffix strings used in maude bridge interchange.
#[test]
fn sort_suffixes_match_haskell() {
    assert_eq!(sort_suffix(LSort::Msg), "msg");
    assert_eq!(sort_suffix(LSort::Fresh), "fresh");
    assert_eq!(sort_suffix(LSort::Pub), "pub");
    assert_eq!(sort_suffix(LSort::Node), "node");
    assert_eq!(sort_suffix(LSort::Nat), "nat");
}
