// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use crate::function_symbols::{exp_sym, pair_sym, AcSym, CSym, FunSym};

/// The pinned submodule's `lib/term/src/Term/Term/Raw.hs`, embedded at
/// build time.
const RAW_HS: &str = include_str!("../../../tamarin-prover/lib/term/src/Term/Term/Raw.hs");

#[test]
fn literal_binding_visits_inputs_once_and_cleans_up_on_panic() {
    let input = f_app_list(vec![lit(0u8), lit(1)]);
    let mut seen = Vec::new();
    let result = bind_lits(&input, &mut |v| {
        seen.push(*v);
        f_app_list(vec![lit(v + 2)])
    });
    assert_eq!(seen, [0, 1]);
    assert_eq!(
        result,
        f_app_list(vec![f_app_list(vec![lit(2)]), f_app_list(vec![lit(3)])])
    );

    tamarin_test_support::on_stack(256 * 1024, || {
        let mut deep = lit(0u8);
        for _ in 0..100_000 {
            deep = f_app_list(vec![deep]);
        }
        let tree = f_app_list(vec![deep, lit(9)]);
        // The deep left result is complete when the right callback fails.
        assert!(std::panic::catch_unwind(|| {
            bind_lits(&tree, &mut |v| {
                assert_ne!(*v, 9, "fail after completing the left child");
                lit(7u8)
            })
        })
        .is_err());
        drop(tree);
    });
}

#[test]
fn last_owner_drop_is_iterative_and_preserves_leaf_order() {
    tamarin_test_support::on_stack(256 * 1024, || {
        struct Leaf(usize, Arc<std::sync::Mutex<Vec<usize>>>, Option<usize>);
        impl Drop for Leaf {
            fn drop(&mut self) {
                self.1.lock().unwrap().push(self.0);
                assert_ne!(Some(self.0), self.2, "leaf panic");
            }
        }
        for panic_at in [None, Some(0), Some(1234)] {
            let dropped = Arc::new(std::sync::Mutex::new(Vec::new()));
            let mut term = Term::Lit(Leaf(0, dropped.clone(), panic_at));
            for i in 1..100_000 {
                term = Term::App(
                    FunSym::NoEq(pair_sym()),
                    vec![term, Term::Lit(Leaf(i, dropped.clone(), panic_at))].into(),
                );
            }
            assert_eq!(
                std::panic::catch_unwind(|| drop(term)).is_err(),
                panic_at.is_some()
            );
            assert_eq!(*dropped.lock().unwrap(), (0..100_000).collect::<Vec<_>>());
        }
    });
}

#[test]
fn shared_terms_release_leaves_once_even_across_threads() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Barrier,
    };
    #[derive(Clone)]
    struct Leaf(Arc<AtomicUsize>);
    impl Drop for Leaf {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    for _ in 0..8 {
        let dropped = Arc::new(AtomicUsize::new(0));
        let mut term = Term::App(
            FunSym::NoEq(pair_sym()),
            vec![Term::Lit(Leaf(dropped.clone()))].into(),
        );
        for _ in 0..100_000 {
            term = Term::App(FunSym::NoEq(pair_sym()), vec![term.clone(), term].into());
        }
        drop(term.clone());
        assert_eq!(dropped.load(Ordering::Relaxed), 0);
        let barrier = Arc::new(Barrier::new(2));
        let threads: Vec<_> = [term.clone(), term]
            .map(|term| Term::App(FunSym::NoEq(pair_sym()), vec![term].into()))
            .into_iter()
            .map(|term| {
                let barrier = barrier.clone();
                std::thread::Builder::new()
                    .stack_size(256 * 1024)
                    .spawn(move || {
                        barrier.wait();
                        drop(term);
                    })
                    .unwrap()
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
        assert_eq!(dropped.load(Ordering::Relaxed), 1);
    }
}

/// [`FAPP_AC_EMPTY_SITE`] is pasted verbatim into a `HasCallStack` frame
/// the port must emit byte-for-byte, and the stderr tests for that frame
/// compare the port against bytes captured from the port — so they agree
/// with a stale coordinate.  Read it back out of the pinned source.
#[test]
fn fapp_ac_empty_site_is_the_pinned_call_site() {
    let (idx, line) = RAW_HS
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains(FAPP_AC_EMPTY_MSG))
        .expect("no `fAppAC` empty-list `error` in the pinned Raw.hs");
    let col = line.find("error").expect("no `error` token") + 1;
    assert_eq!(FAPP_AC_EMPTY_SITE, format!("{}:{}", idx + 1, col));
}

fn nat(n: u64) -> Term<u64> {
    lit(n)
}

#[test]
fn ac_flattens_and_sorts() {
    // mult(mult(3, 1), 2) → mult(1, 2, 3)
    let inner = f_app_ac(AcSym::Mult, vec![nat(3), nat(1)]);
    let outer = f_app_ac(AcSym::Mult, vec![inner, nat(2)]);
    match outer {
        Term::App(FunSym::Ac(AcSym::Mult), ref ts) => {
            let lits: Vec<u64> = ts
                .iter()
                .map(|t| match t {
                    Term::Lit(n) => *n,
                    _ => unreachable!(),
                })
                .collect();
            assert_eq!(lits, vec![1, 2, 3]);
        }
        _ => panic!("expected AC Mult application"),
    }
}

#[test]
fn ac_singleton_unwrap() {
    let t = f_app_ac(AcSym::Mult, vec![nat(7)]);
    assert_eq!(t, nat(7));
}

#[test]
fn prot_subterms_descend_through_pair_and_ac() {
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    let h1 = NoEqSym::new(b"h", 1, Privacy::Public, Constructability::Constructor);
    let mk_h = |x: Term<u64>| Term::App(FunSym::NoEq(h1), vec![x].into());
    // pair(h(1), mult(h(2), 3)): protected subterms are h(1), h(2)
    // (descend through pair and the AC mult; bare 3 is a Lit → none).
    let pr = Term::App(
        FunSym::NoEq(pair_sym()),
        vec![
            mk_h(nat(1)),
            f_app_ac(AcSym::Mult, vec![mk_h(nat(2)), nat(3)]),
        ]
        .into(),
    );
    assert!(is_pair(&pr));
    assert!(!is_ac(&pr));
    let subs = all_prot_subterms(&pr);
    assert_eq!(subs, vec![mk_h(nat(1)), mk_h(nat(2))]);
    // A protected term itself: its top is returned, then its protected children.
    assert_eq!(all_prot_subterms(&mk_h(nat(1))), vec![mk_h(nat(1))]);
    // A bare literal has no protected subterms.
    assert_eq!(all_prot_subterms(&nat(5)), Vec::<Term<u64>>::new());
}

/// An Xor that is already flat, inside another Xor, gives exactly one Xor
/// over the union of the arguments.  The constructor sorts that union
/// again.  It merges the new argument into the flattened list.  It does
/// not add the new argument after that list.
#[test]
fn ac_flattening_absorbs_a_nested_same_symbol_app() {
    let t1 = f_app_ac(AcSym::Xor, vec![nat(1), nat(2), nat(3)]);
    let t2 = f_app_ac(AcSym::Xor, vec![t1, nat(0)]);
    assert_eq!(
        t2,
        unsafe_f_app(FunSym::Ac(AcSym::Xor), vec![nat(0), nat(1), nat(2), nat(3)])
    );
}

#[test]
fn c_sorts_arguments() {
    let t = f_app_c(CSym::EMap, vec![nat(2), nat(1)]);
    match t {
        Term::App(FunSym::C(CSym::EMap), ts) => {
            assert_eq!(&*ts, &[nat(1), nat(2)]);
        }
        _ => panic!(),
    }
}

#[test]
fn no_eq_preserves_order() {
    // pair(1, 2) keeps argument order; pair is not commutative.
    let t = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
    match t {
        Term::App(FunSym::NoEq(s), ts) => {
            assert_eq!(s, pair_sym());
            assert_eq!(&*ts, &[nat(1), nat(2)]);
        }
        _ => panic!(),
    }
}

#[test]
fn subterm_basics() {
    let inner = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
    let outer = f_app_no_eq(exp_sym(), vec![inner.clone(), nat(3)]);
    assert!(is_subterm(&inner, &outer));
    assert!(is_subterm(&nat(2), &outer));
    assert!(!is_subterm(&nat(99), &outer));
    // A term is its own subterm but not its own proper subterm.
    assert!(is_subterm(&outer, &outer));
    assert!(!is_proper_subterm(&outer, &outer));
}

#[test]
fn count_subterms_counts_occurrences() {
    // pair(x, pair(x, y)) contains x twice.
    let x = nat(1);
    let y = nat(2);
    let inner = f_app_no_eq(pair_sym(), vec![x.clone(), y.clone()]);
    let outer = f_app_no_eq(pair_sym(), vec![x.clone(), inner]);
    assert_eq!(count_subterms(&x, &outer), 2);
    assert_eq!(count_subterms(&y, &outer), 1);
}

/// [`replace_subterm`] applies `f` to the complete term first.  It then
/// descends into the result of `f`.  So it also visits the new subterms
/// that a rewrite introduces.  It never visits the original children of a
/// node that `f` replaced.
///
/// A bottom-up traversal visits the children first and applies `f` last.
/// That order gives the same result for an `f` that changes only leaves.
/// So the `f` here maps an `exp` node onto a `pair` of two new leaves.
/// The top-down order rewrites the top node.  It then increments the two
/// leaves it has just introduced.  It never sees the original `1` and
/// `2`.  [`replace_proper_subterm`] runs the same descent, but it does
/// not apply `f` at the root.
#[test]
fn replace_subterm_is_top_down() {
    let t = f_app_no_eq(exp_sym(), vec![nat(1), nat(2)]);
    let mut f = |t: Term<u64>| match t {
        Term::Lit(n) => Term::Lit(n + 10),
        Term::App(s, _) if s == FunSym::NoEq(exp_sym()) => {
            f_app_no_eq(pair_sym(), vec![nat(7), nat(8)])
        }
        other => other,
    };
    assert_eq!(
        replace_subterm(&mut f, t.clone()),
        f_app_no_eq(pair_sym(), vec![nat(17), nat(18)])
    );
    // `replace_proper_subterm` skips the root.  The `exp` node stays.
    // Each child goes to the full top-down `replace_subterm`.
    assert_eq!(
        replace_proper_subterm(&mut f, t),
        f_app_no_eq(exp_sym(), vec![nat(11), nat(12)])
    );
}

/// The hand-written `PartialEq`/`Ord`/`PartialOrd`/`Hash` on [`Term`]
/// contain an `Arc::ptr_eq` fast path.  So they must still give exactly
/// the answers of the derived, purely structural implementations.  That
/// means three things.  `Lit` comes before `App`, which is the
/// declaration order.  That order puts constants before applications in
/// every `f_app_ac`/`f_app_c` argument sort.  Inside `App`, the symbol
/// comes before the arguments.  The answer is the same whether or not the
/// two argument slices are the same allocation.
#[test]
fn term_ord_is_structural_whether_or_not_args_are_shared() {
    use std::cmp::Ordering;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    fn hash_of(t: &Term<u64>) -> u64 {
        let mut h = DefaultHasher::new();
        t.hash(&mut h);
        h.finish()
    }
    // `Lit` sorts before `App`, for any payloads.
    let big_lit = nat(u64::MAX);
    let app = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
    assert!(big_lit < app);
    assert_eq!(app.cmp(&big_lit), Ordering::Greater);
    assert_eq!(big_lit.partial_cmp(&app), Some(Ordering::Less));
    assert!(big_lit != app);
    // Inside `App`, the symbol has priority over the arguments.  `exp` is
    // less than `pair` in `NoEqSym` order.  So `exp(9,9)` sorts below
    // `pair(0,0)`.
    assert!(exp_sym() < pair_sym());
    let exp_big = f_app_no_eq(exp_sym(), vec![nat(9), nat(9)]);
    let pair_small = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
    assert!(exp_big < pair_small);
    // Here are two argument slices: one shared, one built separately.
    // `shared` is a clone, so it holds the same `Arc` and the pointer
    // fast path applies.  `rebuilt` is an equal slice at a different
    // address, so the fast path does not apply and the structural walk
    // gives the answer.  All three answers must be the same.
    let shared = app.clone();
    let rebuilt = f_app_no_eq(pair_sym(), vec![nat(0), nat(0)]);
    if let (Term::App(_, a), Term::App(_, b), Term::App(_, c)) = (&app, &shared, &rebuilt) {
        assert!(a.ptr_eq(b));
        assert!(!a.ptr_eq(c));
    } else {
        panic!("expected three applications");
    }
    for other in [&shared, &rebuilt] {
        assert_eq!(&app, other);
        assert_eq!(app.cmp(other), Ordering::Equal);
        assert_eq!(app.partial_cmp(other), Some(Ordering::Equal));
        // `Hash` must agree with that `Eq`.  `Hash` uses the content, so
        // the term with the shared pointer and the rebuilt term give the
        // same hash.
        assert_eq!(hash_of(&app), hash_of(other));
    }
    // The comparison still finds a different argument through the
    // fast-path guard.
    let differing = f_app_no_eq(pair_sym(), vec![nat(0), nat(1)]);
    assert_ne!(app, differing);
    assert_eq!(app.cmp(&differing), Ordering::Less);
}

// =========================================================================
// Haskell-faithfulness invariants for AC/C/NoEq term constructors.
// =========================================================================

/// AC terms with the same multiset are *equal* mod-AC: `+(a, b)` and
/// `+(b, a)` get sorted to the same canonical form, so structural
/// equality holds.  Haskell-faithful: AC canonicalization happens at
/// construction time (`fAppAC` in Term/Term/Raw.hs).
#[test]
fn ac_terms_are_equal_modulo_argument_order() {
    let t1 = f_app_ac(AcSym::Mult, vec![nat(7), nat(2), nat(5)]);
    let t2 = f_app_ac(AcSym::Mult, vec![nat(5), nat(7), nat(2)]);
    let t3 = f_app_ac(AcSym::Mult, vec![nat(2), nat(5), nat(7)]);
    assert_eq!(
        t1, t2,
        "AC terms with same multiset of args must compare equal — \
             smart constructor canonicalizes order"
    );
    assert_eq!(t1, t3);
}

/// AC vs C distinction: C terms ARE sorted but NOT flattened.  NoEq
/// terms preserve argument order.
#[test]
fn ac_flattens_but_c_does_not() {
    // AC: mult(mult(1,2), 3) → mult(1,2,3) — flat.
    let nested_ac = f_app_ac(
        AcSym::Mult,
        vec![f_app_ac(AcSym::Mult, vec![nat(1), nat(2)]), nat(3)],
    );
    match &nested_ac {
        Term::App(FunSym::Ac(AcSym::Mult), ts) => {
            assert_eq!(ts.len(), 3, "AC must flatten nested same-sym");
        }
        _ => panic!(),
    }
    // C is non-associative; nested EMap doesn't flatten.
    let nested_c = f_app_c(
        CSym::EMap,
        vec![f_app_c(CSym::EMap, vec![nat(1), nat(2)]), nat(3)],
    );
    match &nested_c {
        Term::App(FunSym::C(CSym::EMap), ts) => {
            assert_eq!(ts.len(), 2, "C must NOT flatten — non-associative");
        }
        _ => panic!(),
    }
}

/// Lit::Con < Lit::Var: constants sort before variables.
/// VTerm.hs:56: `data Lit c v = Con c | Var v`.
///
/// This matters for `f_app_ac`/`f_app_c` argument sorting: if a
/// term mixes constants and variables, constants always sort first.
/// Downstream code in atom_valuation expects constants in fixed
/// positions when matching.
#[test]
fn lit_con_sorts_before_lit_var() {
    use crate::lterm::{LNTerm, LSort, LVar, Name, NameId, NameTag};
    use crate::vterm::Lit;

    // Variant tags: Con=0, Var=1 in Haskell decl order.
    let pub_a = Name {
        tag: NameTag::Pub,
        id: NameId::new("a"),
    };
    let v_x = LVar::new("x", LSort::Msg, 0);
    let con: LNTerm = Term::Lit(Lit::Con(pub_a));
    let var: LNTerm = Term::Lit(Lit::Var(v_x));
    assert!(
        con < var,
        "Lit::Con must sort before Lit::Var (Haskell decl order). \
                 AC term canonicalization relies on this — `+(x, 'a')` \
                 canonicalizes to `+('a', x)`."
    );
}

/// `BVar::Bound < BVar::Free` from LTerm.hs:451-453 declaration order.
/// `data BVar v = Bound Integer | Free v`
///
/// This drives the BTreeMap key order for guarded-formula
/// binders/bound-var lookup — when we de Bruijn-index a formula's
/// quantified variables, the bound positions sort before any free
/// occurrences.
#[test]
fn bvar_bound_sorts_before_bvar_free() {
    use crate::lterm::{BVar, LSort, LVar};
    let bound: BVar<LVar> = BVar::Bound(5);
    let free: BVar<LVar> = BVar::Free(LVar::new("x", LSort::Msg, 0));
    assert!(
        bound < free,
        "BVar::Bound must sort before BVar::Free \
                 (Haskell LTerm.hs:451 declaration order)"
    );
}

/// `fAppAC _ [] = error "Term.fAppAC: empty argument list"` (Raw.hs:120).
/// The payload carries GHC's `displayException` text so the binary's hook
/// can print it verbatim; the end-to-end stderr and exit code are pinned in
/// `tamarin-prover/tests/ac_empty_args_error.rs`.
#[test]
fn empty_ac_argument_list_raises_the_hs_error_payload() {
    use crate::function_symbols::AcSym;

    let raised = std::panic::catch_unwind(|| f_app_ac::<u32>(AcSym::Mult, Vec::new()))
        .expect_err("an empty argument list must raise");
    assert_eq!(
        hs_error_text(raised.as_ref()),
        Some(
            "Term.fAppAC: empty argument list\nCallStack (from HasCallStack):\n  \
                 error, called at src/Term/Term/Raw.hs:120:20 in \
                 tamarin-prover-term-1.13.0-HEWlVEyEBKAFHPl3i5M61g:Term.Term.Raw"
        )
    );
    // An ordinary Rust panic keeps Rust's own report.
    let plain = std::panic::catch_unwind(|| panic!("boom")).expect_err("the closure must panic");
    assert_eq!(hs_error_text(plain.as_ref()), None);
}

/// `map_lits` rebuilds every application with `f_app`, so swapping the
/// literals of an AC term re-sorts its operands instead of keeping the
/// mapped literals in their original positions.
#[test]
fn map_lits_rebuilds_ac_through_f_app() {
    use crate::lterm::{LNTerm, LSort, LVar};
    use crate::vterm::{var_term, Lit};

    let x = LVar::new("x", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let prod: LNTerm = f_app(FunSym::Ac(AcSym::Mult), vec![var_term(x), var_term(z)]);
    let Term::App(_, args) = &prod else {
        panic!("expected an AC application");
    };
    assert_eq!(&args[..], &[var_term(x), var_term(z)]);

    let swapped = map_lits(&prod, &mut |l| match l {
        Lit::Var(v) if *v == x => Lit::Var(z),
        Lit::Var(v) if *v == z => Lit::Var(x),
        other => *other,
    });
    let Term::App(_, args) = &swapped else {
        panic!("expected an AC application");
    };
    assert_eq!(&args[..], &[var_term(x), var_term(z)]);
    assert_eq!(swapped, prod);
}

// =========================================================================
// `show_term` — the raw Haskell `Show (Term a)` form.
// =========================================================================

/// The literal type the `show_term` tests build over.
type ShowT = crate::vterm::VTerm<crate::lterm::Name, crate::lterm::LVar>;

fn show_msg_var(name: &str) -> ShowT {
    use crate::lterm::{LSort, LVar};
    crate::vterm::var_term(LVar::new(name, LSort::Msg, 0))
}

fn show_noeq(name: &[u8], arity: usize) -> NoEqSym {
    use crate::function_symbols::{Constructability, Privacy};
    NoEqSym::new(
        name.to_vec(),
        arity,
        Privacy::Public,
        Constructability::Constructor,
    )
}

fn show_acfct(name: &[u8]) -> AcFctSym {
    use crate::function_symbols::{Constructability, NdcState, Privacy};
    AcFctSym::new(
        name.to_vec(),
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    )
}

/// `FApp (NoEq (s,_)) [] -> BC.unpack s` and
/// `FApp (AC (ACfct (s,_))) [] -> BC.unpack s` (Term/Raw.hs:227-237, see
/// line 231): the two nullary arms write the name alone.
#[test]
fn show_term_writes_a_nullary_symbol_without_parentheses() {
    let g: ShowT = f_app_no_eq(show_noeq(b"g", 0), vec![]);
    assert_eq!(show_term(&g), "g");
    let nil: ShowT = unsafe_f_app(FunSym::Ac(AcSym::AcFct(show_acfct(b"nil"))), vec![]);
    assert_eq!(show_term(&nil), "nil");
}

/// `intercalate ","` (Term/Raw.hs:227-237, see line 232): no space follows
/// a comma, and each argument is itself shown, so the form nests.
#[test]
fn show_term_writes_comma_separated_arguments() {
    let (x, y) = (show_msg_var("x"), show_msg_var("y"));
    let inner = f_app_no_eq(show_noeq(b"h", 2), vec![x.clone(), y.clone()]);
    assert_eq!(show_term(&inner), "h(x,y)");
    let outer = f_app_no_eq(show_noeq(b"k", 3), vec![inner, x, f_app_list(vec![y])]);
    assert_eq!(show_term(&outer), "k(h(x,y),x,LIST(y))");
}

/// `FApp (AC o) as -> show o ++ …` (Term/Raw.hs:227-237, see line 237)
/// writes the derived `ACSym` constructor name
/// (Term/Term/FunctionSymbols.hs:138-139); the `ACfct` arm (see line 234)
/// writes the user symbol's own name instead.
#[test]
fn show_writes_an_ac_head_by_its_constructor_name() {
    let (x, y) = (show_msg_var("x"), show_msg_var("y"));
    for (sym, name) in [
        (AcSym::Union, "Union"),
        (AcSym::Mult, "Mult"),
        (AcSym::Xor, "Xor"),
        (AcSym::NatPlus, "NatPlus"),
    ] {
        let t: ShowT = f_app_ac(sym, vec![x.clone(), y.clone()]);
        assert_eq!(show_term(&t), format!("{}(x,y)", name));
    }
    let user: ShowT = f_app_acfct(show_acfct(b"xorr"), vec![x, y]);
    assert_eq!(show_term(&user), "xorr(x,y)");
}

/// `pair` and `exp` are `NoEq` symbols, so `show` writes them prefix; the
/// `<a, b>` and `a^b` spellings belong to `prettyTerm`.
#[test]
fn show_writes_a_pairing_as_the_prefix_symbol() {
    use crate::lterm::pub_term;
    let p: ShowT = f_app_no_eq(pair_sym(), vec![pub_term("a"), pub_term("b")]);
    assert_eq!(show_term(&p), "pair('a','b')");
    let e: ShowT = f_app_no_eq(exp_sym(), vec![p, pub_term("c")]);
    assert_eq!(show_term(&e), "exp(pair('a','b'),'c')");
}
