// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

use super::*;
use tamarin_term::lterm::LSort;

#[test]
fn deep_alternate_formula_debug_uses_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut formula: LNFormula = ProtoFormula::Tf(true);
        for _ in 0..8192 {
            formula = formula.not();
        }
        let text = format!("{formula:#?}");
        assert_eq!(text.matches("Not(").count(), 8192);
        assert!(text.contains("Tf(true)"));
    });
}

#[test]
fn deep_read_only_formula_walks_preserve_order_and_combined_depth() {
    tamarin_test_support::on_stack(256 * 1024, || {
        type F = ProtoFormula<Unit2, (String, LSort), u32, u32>;
        let mut term = var_term(BVar::Free(0));
        for _ in 0..100_000 {
            term = tamarin_term::term::f_app_list(vec![term, var_term(BVar::Bound(0))]);
        }
        let mut formula: F = ProtoFormula::Atom(ProtoAtom::Last(term));
        for i in 1..=100_000 {
            formula = match i % 3 {
                0 => formula.not(),
                1 => ProtoFormula::for_all((String::new(), LSort::Msg), formula),
                _ => formula.and(ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Free(i))))),
            };
        }
        assert_eq!(formula_depth(&formula), 200_002);
        let want: Vec<_> = std::iter::once(0)
            .chain((1..=100_000).filter(|i| i % 3 == 2))
            .collect();
        assert_eq!(formula_frees_list(&formula), want);
        let mut atoms = 0;
        for_each_formula_atom(&formula, &mut |_| atoms += 1);
        assert_eq!(atoms, want.len());
        // Unwinding a callback only releases borrowed worklist entries.
        assert!(std::panic::catch_unwind(|| {
            for_each_formula_atom(&formula, &mut |_| panic!("stop at first atom"));
        })
        .is_err());
        formula.drop_iteratively();
    });
}

#[test]
fn read_only_formula_walks_match_recursive_reference() {
    type F = ProtoFormula<Unit2, (), u32, u32>;
    fn reference<'a>(
        fm: &'a F,
        atoms: &mut Vec<&'a ProtoAtom<Unit2, VTerm<u32, BVar<u32>>>>,
    ) -> usize {
        match fm {
            ProtoFormula::Atom(atom) => {
                atoms.push(atom);
                let mut depth = 0;
                fold_atom(atom, &mut |t| {
                    depth = depth.max(tamarin_term::term::term_depth(t))
                });
                1 + depth
            }
            ProtoFormula::Tf(_) => 1,
            ProtoFormula::Not(body) | ProtoFormula::Qua(_, _, body) => 1 + reference(body, atoms),
            ProtoFormula::Conn(_, left, right) => {
                let l = reference(left, atoms);
                1 + l.max(reference(right, atoms))
            }
        }
    }
    let atom = || ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Free(4))));
    let cases: [F; 5] = [
        ProtoFormula::Tf(false),
        ProtoFormula::Atom(ProtoAtom::Syntactic(Unit2)),
        atom().not().and(ProtoFormula::Tf(true).not().not().not()),
        ProtoFormula::exists((), atom().or(atom().not())),
        atom().and(atom()).iff(atom().implies(atom())),
    ];
    for formula in cases {
        let mut expected = Vec::new();
        assert_eq!(formula_depth(&formula), reference(&formula, &mut expected));
        let mut actual = Vec::new();
        for_each_formula_atom(&formula, &mut |a| actual.push(a));
        assert_eq!(actual.len(), expected.len());
        assert!(actual
            .iter()
            .zip(expected)
            .all(|(a, b)| std::ptr::eq(*a, b)));
    }
}

#[test]
fn deep_formula_rebuilding_and_failure_cleanup_use_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        type F = ProtoFormula<Unit2, u64, u32, u32>;
        fn atom(n: u32) -> F {
            ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Free(n))))
        }
        fn deep() -> F {
            let mut fm = atom(0);
            for i in 0..100_000 {
                fm = ProtoFormula::for_all(i, fm.not());
            }
            fm
        }
        let input = deep();
        let copied =
            traverse_formula_atom(&input, &mut |a| Ok::<F, ()>(ProtoFormula::Atom(a.clone())))
                .unwrap();
        assert_eq!(formula_depth(&copied), 200_002);
        input.drop_iteratively();
        let mut seen = Vec::new();
        let mapped = map_atoms(copied.and(atom(1)), &mut |depth, a| {
            seen.push(depth);
            a.clone()
        });
        assert_eq!(seen, [100_000, 0]);
        assert_eq!(formula_depth(&mapped), 200_003);
        mapped.drop_iteratively();

        // A completed deep replacement must be released when the next
        // callback fails. Its own atoms must not be visited again.
        let input = atom(0).and(atom(1)).and(deep());
        let mut calls = 0;
        let failed = traverse_formula_atom(&input, &mut |_| {
            calls += 1;
            if calls == 1 {
                Ok(deep())
            } else {
                Err("stop")
            }
        });
        assert!(matches!(failed, Err("stop")));
        assert_eq!(calls, 2);
        assert!(std::panic::catch_unwind(|| {
            let mut calls = 0;
            let _: Result<F, ()> = traverse_formula_atom(&input, &mut |_| {
                calls += 1;
                assert_eq!(calls, 1, "fail after completing a deep replacement");
                Ok(deep())
            });
        })
        .is_err());
        input.drop_iteratively();

        // Both the rebuilt left sibling and the unvisited right sibling
        // are owned by pending frames at the panic site.
        let input = deep().and(atom(1)).and(deep());
        assert!(std::panic::catch_unwind(move || {
            map_atoms(input, &mut |_, a| {
                if matches!(a, ProtoAtom::Last(Term::Lit(Lit::Var(BVar::Free(1))))) {
                    panic!("stop between deep siblings");
                }
                a.clone()
            });
        })
        .is_err());
    });
}

#[test]
fn formula_rebuild_preserves_scope_hint_order_and_splices_once() {
    use std::cell::RefCell;
    use std::rc::Rc;
    struct Hint(u32, Rc<RefCell<Vec<u32>>>);
    impl Drop for Hint {
        fn drop(&mut self) {
            self.1.borrow_mut().push(self.0 + 10);
        }
    }
    impl Clone for Hint {
        fn clone(&self) -> Self {
            self.1.borrow_mut().push(self.0);
            Self(self.0, self.1.clone())
        }
    }
    type F = ProtoFormula<Unit2, Hint, u32, u32>;
    let events = Rc::new(RefCell::new(Vec::new()));
    let atom = || ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Free(0))));
    let input: F = ProtoFormula::for_all(Hint(1, events.clone()), atom().not()).iff(
        ProtoFormula::exists(Hint(2, events.clone()), atom().and(ProtoFormula::Tf(false))),
    );
    let output = traverse_formula_atom(&input, &mut |_| {
        events.borrow_mut().push(3);
        Ok::<F, ()>(atom().implies(atom()))
    })
    .unwrap();
    assert_eq!(*events.borrow(), [1, 3, 2, 3]);
    assert!(matches!(&output, ProtoFormula::Conn(Connective::Iff, l, r)
        if matches!(&**l, ProtoFormula::Qua(Quantifier::All, h, _) if h.0 == 1)
        && matches!(&**r, ProtoFormula::Qua(Quantifier::Ex, h, _) if h.0 == 2)));
    events.borrow_mut().clear();
    let mut depths = Vec::new();
    let output = map_atoms(output, &mut |d, a| {
        depths.push(d);
        a.clone()
    });
    assert_eq!(depths, [1, 1, 1, 1]);
    assert!(
        events.borrow().is_empty(),
        "owned mapping must move, not clone hints"
    );
    input.drop_iteratively();
    output.drop_iteratively();
    assert_eq!(*events.borrow(), [11, 12, 11, 12]);
}

#[test]
fn retained_formula_lifecycle_and_conversions_use_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let mut parsed = p::Formula::True;
        for _ in 0..100_000 {
            parsed = p::Formula::Not(Box::new(parsed));
        }
        let syntactic = from_parser(&parsed, &MaudeSig::default()).unwrap();
        let formula = to_lnformula(&syntactic).unwrap();
        let copy = formula.clone();
        assert_eq!(formula, copy);
        assert_eq!(formula.cmp(&copy), std::cmp::Ordering::Equal);
        assert_eq!(format!("{formula:?}").len(), 500_008);
        // Ordinary drops, including a formula retained in a collection,
        // must use the child owners without caller-specific cleanup.
        drop((parsed, syntactic, vec![formula, copy]));
    });
}

fn lftrue() -> LNFormula {
    ProtoFormula::ltrue()
}
fn lffalse() -> LNFormula {
    ProtoFormula::lfalse()
}

/// Each builder tags the node with its own connective or quantifier.  The
/// four `Conn` builders are the same in every other way, and so are the
/// two `Qua` builders.  So the shape alone does not show a copy-paste
/// mistake between them.
#[test]
fn builders_tag_their_own_connective_and_quantifier() {
    let hint = || ("x".to_string(), LSort::Msg);
    let cases: [(LNFormula, Connective); 4] = [
        (lftrue().and(lffalse()), Connective::And),
        (lftrue().or(lffalse()), Connective::Or),
        (lftrue().implies(lffalse()), Connective::Imp),
        (lftrue().iff(lffalse()), Connective::Iff),
    ];
    for (f, want) in cases {
        match f {
            ProtoFormula::Conn(c, l, r) => {
                assert_eq!(c, want);
                assert_eq!(
                    (l.into_inner(), r.into_inner()),
                    (lftrue(), lffalse()),
                    "operand order for {want:?}"
                );
            }
            other => panic!("expected Conn({want:?}), got {other:?}"),
        }
    }
    assert!(matches!(lftrue().not(), ProtoFormula::Not(b) if *b == lftrue()));
    let all: LNFormula = ProtoFormula::for_all(hint(), lftrue());
    assert!(matches!(all, ProtoFormula::Qua(Quantifier::All, h, _) if h == hint()));
    let ex: LNFormula = ProtoFormula::exists(hint(), lftrue());
    assert!(matches!(ex, ProtoFormula::Qua(Quantifier::Ex, h, _) if h == hint()));
}

/// `exists_var` closes the variable, and `quantify` turns its free
/// occurrences into the new binder's De Bruijn index.
#[test]
fn exists_var_binds_the_free_var() {
    use tamarin_term::vterm::var_term;

    let x = LVar::new("x", LSort::Msg, 0);
    let atom = ProtoAtom::EqE(var_term(BVar::Free(x)), var_term(BVar::Free(x)));
    let fm: LNFormula = ProtoFormula::Atom(atom);

    let ProtoFormula::Qua(q, hint, body) = exists_var(("x".to_string(), LSort::Msg), &x, fm) else {
        panic!("expected an existential quantifier around the atom");
    };
    assert_eq!(q, Quantifier::Ex);
    assert_eq!(hint, ("x".to_string(), LSort::Msg));
    let bound = ProtoAtom::EqE(var_term(BVar::Bound(0)), var_term(BVar::Bound(0)));
    assert_eq!(*body, ProtoFormula::Atom(bound));
}

/// The binder depth counts the quantifiers between the atom and the new
/// binder (HS `foldFormulaScope`'s `go (succ i)`).
#[test]
fn quantify_uses_the_enclosing_binder_depth() {
    use tamarin_term::vterm::var_term;

    let x = LVar::new("x", LSort::Msg, 0);
    let atom = ProtoAtom::Last(var_term(BVar::Free(x)));
    // ∀ y. last(x) — one binder between the atom and the new one.
    let hint = ("y".to_string(), LSort::Node);
    let inner: LNFormula = ProtoFormula::for_all(hint, ProtoFormula::Atom(atom));
    let ProtoFormula::Qua(_, _, body) = quantify(&x, inner) else {
        panic!("expected the inner quantifier to survive quantify");
    };
    let bound = ProtoAtom::Last(var_term(BVar::Bound(1)));
    assert_eq!(*body, ProtoFormula::Atom(bound));
}

/// `shiftFreeIndices n` raises exactly the indices that dangle past the
/// formula's own binders: at an atom under one binder, `Bound(0)` is that
/// binder's and stays, while `Bound(1)` points outside and moves.
#[test]
fn shift_free_indices_lifts_only_the_indices_above_the_scope() {
    use tamarin_term::vterm::var_term;

    let atom = |i: u64, j: u64| -> LNFormula {
        ProtoFormula::Atom(ProtoAtom::Less(
            var_term(BVar::Bound(i)),
            var_term(BVar::Bound(j)),
        ))
    };
    let hint = ("y".to_string(), LSort::Node);
    let fm: LNFormula = ProtoFormula::for_all(hint.clone(), atom(0, 1)).and(atom(0, 1));
    let ProtoFormula::Conn(_, under, outside) = shift_free_indices(2, fm) else {
        panic!("expected the conjunction to survive the shift");
    };
    assert_eq!(
        *under,
        ProtoFormula::for_all(hint, atom(0, 3)),
        "under the binder only the dangling index moves"
    );
    assert_eq!(*outside, atom(2, 3), "outside it both move");
}

fn x_var() -> LVar {
    LVar::new("x", LSort::Msg, 0)
}

/// `Pred(F(x))` as a sugared atom over `BVar` terms.
fn pred_atom(arg: BVar<LVar>) -> SyntacticAtom<BLNTerm> {
    use crate::fact::{Fact, FactTag};
    use tamarin_term::vterm::var_term;

    ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
        FactTag::Term,
        vec![var_term(arg)],
    )))
}

/// `frees` descends into the sugar's fact (the `Foldable SyntacticSugar`
/// instance), so a variable that occurs only inside a `Pred` is free.
#[test]
fn formula_frees_includes_pred_terms() {
    let fm: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
    assert_eq!(formula_frees(&fm), vec![x_var()]);
    let closed: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Bound(0)));
    assert_eq!(formula_frees(&closed), Vec::<LVar>::new());
}

/// `quantify` maps through the sugar (the `Functor SyntacticSugar`
/// instance), so `exists` closes a variable that occurs inside a `Pred`.
#[test]
fn quantify_closes_pred_terms() {
    let hint = ("x".to_string(), LSort::Msg);
    let fm: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
    let want: SyntacticLNFormula =
        ProtoFormula::exists(hint.clone(), ProtoFormula::Atom(pred_atom(BVar::Bound(0))));
    assert_eq!(exists_var(hint, &x_var(), fm), want);
}

/// `toLNFormula` is `Nothing` while any atom still carries sugar, however
/// deep it sits.
#[test]
fn to_lnformula_rejects_sugar() {
    let pred: SyntacticLNFormula = ProtoFormula::Atom(pred_atom(BVar::Free(x_var())));
    let fm: SyntacticLNFormula = ProtoFormula::for_all(
        ("x".to_string(), LSort::Msg),
        ProtoFormula::ltrue().and(pred.not()),
    );
    assert_eq!(to_lnformula(&fm), None);
}

/// `All #x. (x < y) ==> not(last(x))` over any sugar type: no atom uses
/// the sugar, so the same construction types as both formula forms.
fn plain_formula<S>() -> LNProtoFormula<S> {
    use tamarin_term::vterm::var_term;

    let less = ProtoAtom::Less(var_term(BVar::Bound(0)), var_term(BVar::Free(x_var())));
    let last = ProtoAtom::Last(var_term(BVar::Bound(0)));
    ProtoFormula::for_all(
        ("x".to_string(), LSort::Node),
        ProtoFormula::Atom(less).implies(ProtoFormula::Atom(last).not()),
    )
}

/// Plain atoms cross `toLNFormula` unchanged, only their sugar type
/// becomes `Unit2`; every formula constructor above them is kept.
#[test]
fn to_lnformula_strips_unit2_atoms() {
    let fm: SyntacticLNFormula = plain_formula();
    let want: LNFormula = plain_formula();
    assert_eq!(to_lnformula(&fm), Some(want));
}

// =========================================================================
// from_parser / open_bound_term
// =========================================================================

use crate::fact::{FactTag, Multiplicity};
use tamarin_parser::parser::{parse_formula_str, parse_theory};
use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::intern::intern_str;
use tamarin_term::maude_sig::pair_maude_sig;
use tamarin_term::term::{f_app_ac, f_app_no_eq, Term};
use tamarin_term::vterm::var_term;

fn parsed(src: &str) -> SyntacticLNFormula {
    parsed_with(src, &pair_maude_sig())
}

/// [`parsed`] against a theory's own signature, for the sources whose
/// meaning depends on a declaration.
fn parsed_with(src: &str, msig: &tamarin_term::maude_sig::MaudeSig) -> SyntacticLNFormula {
    from_parser(&parse_formula_str(src, msig).unwrap(), msig).unwrap()
}

fn free(name: &str, sort: LSort, idx: u64) -> BLNTerm {
    var_term(BVar::Free(LVar::new(name, sort, idx)))
}

fn bound(i: u64) -> BLNTerm {
    var_term(BVar::Bound(i))
}

fn proto_fact<T>(name: &str, args: Vec<T>) -> Fact<T> {
    Fact::new(
        FactTag::Proto(Multiplicity::Linear, intern_str(name), args.len()),
        args,
    )
}

fn pred(name: &str, args: Vec<BLNTerm>) -> SyntacticLNFormula {
    ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(proto_fact(
        name, args,
    ))))
}

fn hint(name: &str, sort: LSort) -> (String, LSort) {
    (name.to_string(), sort)
}

fn parser_var(name: &str, sort: LSort) -> p::Term {
    p::Term::Var(p::VarSpec {
        name: name.to_string(),
        idx: 0,
        sort,
        typ: None,
    })
}

/// `foldr (hinted q) f vs` puts the last binder innermost, so the
/// innermost binder is `Bound(0)` at the atom and the `@` operand stays a
/// free `Node` variable.
#[test]
fn from_parser_nests_binders_innermost_zero() {
    let want = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::Action(
                free("i", LSort::Node, 0),
                proto_fact("P", vec![bound(1), bound(0)]),
            )),
        ),
    );
    assert_eq!(parsed("All x. Ex y. P(x, y) @ #i"), want);
}

/// The `@` operand is `Node` whatever its hint, so it is closed by the
/// `#k` binder, while the `k` inside the fact is `Msg` and closed by the
/// message binder of the same name.
#[test]
fn from_parser_resolves_sort_by_position() {
    let pair = f_app_no_eq(
        tamarin_term::function_symbols::pair_sym(),
        vec![bound(1), bound(2)],
    );
    let want = ProtoFormula::exists(
        hint("k", LSort::Msg),
        ProtoFormula::exists(
            hint("m", LSort::Msg),
            ProtoFormula::exists(
                hint("k", LSort::Node),
                ProtoFormula::Atom(ProtoAtom::Action(bound(0), proto_fact("G", vec![pair]))),
            ),
        ),
    );
    assert_eq!(parsed("Ex k m #k. G(<m, k>) @ k"), want);
}

/// `#k = l` is HS's node equality: the bare `l` is a `nodevar`, so the
/// `#l` binder closes it, while a message-term equality `k = l` keeps
/// the bare `l` as `Msg` (probe `S0_bare_name_under_node_binder.spthy`).
#[test]
fn from_parser_node_equality_binds_bare_right_operand() {
    let want = ProtoFormula::for_all(
        hint("k", LSort::Node),
        ProtoFormula::for_all(
            hint("l", LSort::Node),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
        ),
    );
    assert_eq!(parsed("All #k #l. #k = l"), want);
    assert_eq!(parsed("All #k #l. k:node = l"), want);
    let msg = ProtoFormula::for_all(
        hint("l", LSort::Node),
        ProtoFormula::Atom(ProtoAtom::EqE(
            free("k", LSort::Msg, 0),
            free("l", LSort::Msg, 0),
        )),
    );
    assert_eq!(parsed("All #l. k = l"), msg);
}

/// Closing compares the whole `LVar`: a `~k` binder does not capture the
/// message-sorted `k` of the body.
#[test]
fn from_parser_leaves_other_sorted_name_free() {
    let want = ProtoFormula::exists(
        hint("k", LSort::Fresh),
        pred("Made", vec![free("k", LSort::Msg, 0)]),
    );
    assert_eq!(parsed("Ex ~k. Made(k)"), want);
}

#[test]
fn rule_let_freshening_preserves_typed_free_variables() {
    let theory = tamarin_parser::parse_theory(
        "theory T begin rule R: let x = y.1 in []
         --[_restrict(Ex y.1 #i. A(x,y.1,y:foo) @ i)]-> [] end",
        &[],
    )
    .unwrap();
    let tamarin_parser::ast::TheoryItem::Rule(rule) = &theory.items[0] else {
        panic!("expected a rule");
    };
    let formula = from_parser(&rule.embedded_restrictions[0], &pair_maude_sig()).unwrap();
    assert_eq!(
        formula_frees(&formula),
        vec![LVar::new("y", LSort::Msg, 0), LVar::new("y", LSort::Msg, 1)]
    );
    assert_eq!(formula, parsed("Ex y.2 #i. A(y.1,y.2,y:foo) @ i"));
}

#[test]
fn rule_let_substitution_uses_untyped_variable_identity() {
    for (binding, input, expected) in [
        ("x=y", "Ex y. A(x,y:foo)", "Ex y.1. A(y,y.1)"),
        ("x=y:foo", "Ex y. A(x,y)", "Ex y.1. A(y,y.1)"),
        ("x=z", "Ex x:foo. A(x)", "Ex x. A(x)"),
        ("x=z", "A(x:foo)", "A(z)"),
        (
            "x=y",
            "Ex y. A(x,y:foo) & (Ex y:foo. B(y))",
            "Ex y.1. A(y,y.1) & (Ex y.2. B(y.2))",
        ),
        ("x=z", "Ex #x. A(x,x.1) @ x", "Ex #x. A(z,x.1) @ x"),
    ] {
        let source =
            format!("theory T begin rule R: let {binding} in [] --[_restrict({input})]-> [] end");
        let theory = parse_theory(&source, &[]).unwrap();
        let tamarin_parser::ast::TheoryItem::Rule(rule) = &theory.items[0] else {
            panic!("expected a rule");
        };
        let actual = from_parser(&rule.embedded_restrictions[0], &pair_maude_sig()).unwrap();
        assert_eq!(actual, parsed(expected), "{binding}: {input}");
    }
}

/// The inner binder closes the occurrence first, so the outer binder of
/// the same name finds nothing left to close.
#[test]
fn from_parser_inner_binder_shadows() {
    let want = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::for_all(hint("x", LSort::Msg), pred("P", vec![bound(0)])),
    );
    assert_eq!(parsed("All x. All x. P(x)"), want);
}

/// A bare identifier that names a nullary user symbol is that symbol's
/// application (HS `nullaryApp`), so a binder of the same name closes
/// nothing.
#[test]
fn from_parser_keeps_nullary_symbol_constant() {
    let thy = parse_theory("theory T begin\nfunctions: zero/0\nend", &[]).unwrap();
    let elab = crate::elaborate::elaborate(&thy).unwrap();

    let ProtoFormula::Qua(Quantifier::All, h, body) =
        parsed_with("All zero. P(zero)", &elab.signature)
    else {
        panic!("expected a universal quantifier");
    };
    assert_eq!(h, hint("zero", LSort::Msg));
    let ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(fa))) = body.into_inner()
    else {
        panic!("expected a predicate atom");
    };
    match &fa.terms[..] {
        [Term::App(FunSym::NoEq(sym), args)] => {
            assert_eq!(sym.name, b"zero");
            assert!(args.is_empty());
        }
        other => panic!("expected the nullary application, got {other:?}"),
    }
}

/// `t (<) t` is the `Smaller` predicate (HS `smallerp`).
#[test]
fn from_parser_less_mset_is_smaller_pred() {
    let f = p::Formula::Atom(p::Atom::LessMset(
        parser_var("x", LSort::Msg),
        parser_var("y", LSort::Msg),
    ));
    let want = ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(smaller_fact(
        free("x", LSort::Msg, 0),
        free("y", LSort::Msg, 0),
    ))));
    assert_eq!(from_parser(&f, &pair_maude_sig()).unwrap(), want);
}

/// A SAPIC `=t` pattern has no `LNTerm` form.
#[test]
fn from_parser_rejects_pat_match() {
    let pat = p::Term::PatMatch(Box::new(parser_var("x", LSort::Msg)));
    let in_term = p::Formula::Atom(p::Atom::Eq(pat.clone(), parser_var("y", LSort::Msg)));
    let err = from_parser(&in_term, &pair_maude_sig()).unwrap_err();
    assert_eq!(err.message, "could not elaborate term in formula");
    let in_fact = p::Formula::Atom(p::Atom::Pred(p::Fact {
        persistent: false,
        name: "F".to_string(),
        args: vec![pat],
        annotations: Vec::new(),
    }));
    assert!(from_parser(&in_fact, &pair_maude_sig()).is_err());
}

// =========================================================================
// sapic_from_parser
// =========================================================================

fn sapic_parsed(src: &str) -> SapicFormula {
    let msig = pair_maude_sig();
    let parsed =
        tamarin_parser::parse_theory(&format!("theory T begin process: if {src} then 0 end"), &[])
            .unwrap();
    let condition = parsed
        .items
        .iter()
        .find_map(|item| match item {
            p::TheoryItem::TopLevelProcess(p::Process::Comb {
                comb: p::ProcessComb::Cond(condition),
                ..
            }) => Some(condition),
            _ => None,
        })
        .unwrap();
    let formula = match condition {
        p::Condition::Formula(formula) => formula.clone(),
        p::Condition::Eq(left, right) => p::Formula::Atom(p::Atom::Eq(left.clone(), right.clone())),
    };
    sapic_from_parser(&formula, &msig).unwrap()
}

fn sapic_free(name: &str, sort: LSort, typ: Option<&str>) -> VTerm<Name, BVar<SapicLVar>> {
    var_term(BVar::Free(SapicLVar::new(
        LVar::new(name, sort, 0),
        typ.map(str::to_string),
    )))
}

fn sapic_bound(i: u64) -> VTerm<Name, BVar<SapicLVar>> {
    var_term(BVar::Bound(i))
}

fn sapic_pred(name: &str, args: Vec<VTerm<Name, BVar<SapicLVar>>>) -> SapicFormula {
    ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(proto_fact(
        name, args,
    ))))
}

/// `sapicvar` carries the written `name:type` into the binder and into
/// every term literal (Token.hs:506-510), and a binder closes the
/// occurrences equal to its whole `SapicLVar`, so the untagged `x` of the
/// same name and sort stays free.
#[test]
fn sapic_from_parser_keeps_the_written_type_tag() {
    let want = ProtoFormula::exists(
        hint("x", LSort::Msg),
        sapic_pred("P", vec![sapic_bound(0), sapic_free("x", LSort::Msg, None)]),
    );
    assert_eq!(sapic_parsed("Ex x:foo. P(x:foo, x)"), want);
}

/// `nodevarTerm` reads its variable with `nodep = sapicnodevar`, which
/// stamps `defaultSapicNodeType` (Token.hs:522-525,
/// Theory/Sapic/Term.hs:99-100), in the three positions `blatom` writes
/// it: `last`'s argument, an action's timepoint and both operands of `<`
/// (Theory/Text/Parser/Formula.hs:46-49).
#[test]
fn sapic_from_parser_tags_a_timepoint_operand_node() {
    let node = |n: &str| sapic_free(n, LSort::Node, Some("node"));
    assert_eq!(
        sapic_parsed("#k < #l"),
        ProtoFormula::Atom(ProtoAtom::Less(node("k"), node("l")))
    );
    assert_eq!(
        sapic_parsed("last(#m)"),
        ProtoFormula::Atom(ProtoAtom::Last(node("m")))
    );
    assert_eq!(
        sapic_parsed("Ev(x) @ #n"),
        ProtoFormula::Atom(ProtoAtom::Action(
            node("n"),
            proto_fact("Ev", vec![sapic_free("x", LSort::Msg, None)])
        ))
    );
}

/// A predicate's arguments are read by `varp = sapicvar`; current
/// `sapicvar` defaults a node-sorted variable to type `node`.
#[test]
fn sapic_from_parser_tags_a_node_sorted_predicate_argument() {
    assert_eq!(
        sapic_parsed("P(#p, y)"),
        sapic_pred(
            "P",
            vec![
                sapic_free("p", LSort::Node, Some("node")),
                sapic_free("y", LSort::Msg, None)
            ]
        )
    );
}

/// The node-defaulting fix makes a `sapicvar` quantifier binder equal to
/// the tagged `sapicnodevar` occurrence, so `quantify` closes it.
#[test]
fn a_sapic_node_binder_closes_a_tagged_timepoint_occurrence() {
    let want = ProtoFormula::exists(
        hint("j", LSort::Node),
        ProtoFormula::Atom(ProtoAtom::Action(
            sapic_bound(0),
            proto_fact("Foo", vec![sapic_free("x", LSort::Msg, None)]),
        )),
    );
    let got = sapic_parsed("Ex #j. Foo(x)@#j");
    assert_eq!(got, want);
    assert_eq!(
        formula_frees(&got),
        vec![SapicLVar::untyped(LVar::new("x", LSort::Msg, 0))]
    );
}

/// The two instantiations of the closing walk agree once `toLFormula`
/// drops the tags.
#[test]
fn to_lformula_of_sapic_from_parser_equals_from_parser() {
    for src in [
        "All x. P(x) & x = 'a'",
        "Ex y. Q(y) ==> last(#i)",
        "#k < #l",
        "x:foo = 'a'",
        "All x:foo. P(x:foo)",
        "Ex ~k. K(~k) @ #i & #i < #j",
        "Ex #j. Foo(x) @ #j",
    ] {
        assert_eq!(
            crate::sapic::to_lformula(&sapic_parsed(src)),
            parsed(src),
            "{src}"
        );
    }
}

/// Opening against the binders that `quantify` closed gives the original
/// term back, AC argument order included.
#[test]
fn open_bound_term_round_trips_quantify() {
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let original: LNTerm = f_app_ac(AcSym::Mult, vec![var_term(x), var_term(y), var_term(z)]);
    let lifted = lift_free(&original);
    let fm: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(lifted));
    // Outer binder `y`, inner binder `x`: `x` is `Bound(0)`, `y` `Bound(1)`.
    let closed = for_all_var(
        (y.name.to_string(), y.sort),
        &y,
        for_all_var((x.name.to_string(), x.sort), &x, fm),
    );
    let ProtoFormula::Qua(_, _, inner) = closed else {
        panic!("expected the outer quantifier");
    };
    let ProtoFormula::Qua(_, _, body) = inner.into_inner() else {
        panic!("expected the inner quantifier");
    };
    let ProtoFormula::Atom(ProtoAtom::Last(term)) = body.into_inner() else {
        panic!("expected the atom");
    };
    assert_eq!(
        term,
        f_app_ac(
            AcSym::Mult,
            vec![bound(0), bound(1), lift_free(&var_term(z))]
        )
    );
    assert_eq!(open_bound_term(&term, &[y, x]), original);
}

/// An index past the scope is HS `extractFree`'s error.
#[test]
#[should_panic(expected = "prettyFormula: illegal bound variable '1'")]
fn open_bound_term_panics_past_scope() {
    let x = LVar::new("x", LSort::Msg, 0);
    open_bound_term(&bound(1), &[x]);
}

// =========================================================================
// map_atoms / apply_subst / apply_rename
// =========================================================================

/// The callback's `i` counts the binders between the formula's root and
/// the atom, so the two atoms of one formula are seen at their own depths.
#[test]
fn map_atoms_threads_the_binder_depth() {
    let last_i = || ProtoFormula::Atom(ProtoAtom::Last(free("i", LSort::Node, 0)));
    // All x. ((Ex y. last(#i)) & last(#i))
    let fm: SyntacticLNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::exists(hint("y", LSort::Msg), last_i()).and(last_i()),
    );
    let mut depths = Vec::new();
    let out = map_atoms(fm.clone(), &mut |i, a| {
        depths.push(i);
        a.clone()
    });
    assert_eq!(depths, vec![2, 1]);
    assert_eq!(out, fm);
}

/// The substitution reaches every free occurrence, inside a `Pred`'s fact
/// too, and leaves a bound index alone.
#[test]
fn apply_subst_rewrites_free_occurrences_only() {
    let x = LVar::new("x", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 0);
    let s: Subst<Name, LVar> = Subst::from_list(vec![(x, var_term(z))]);
    let fm: SyntacticLNFormula = ProtoFormula::exists(
        hint("y", LSort::Msg),
        pred("P", vec![free("x", LSort::Msg, 0), bound(0)]),
    );
    let want: SyntacticLNFormula = ProtoFormula::exists(
        hint("y", LSort::Msg),
        pred("P", vec![free("z", LSort::Msg, 0), bound(0)]),
    );
    assert_eq!(apply_subst(&s, fm), want);
}

/// A binder is a De Bruijn index, which no substitution has in its domain,
/// so an image variable that spells the binder's own hint stays free where
/// it lands.
#[test]
fn a_bound_index_cannot_be_captured_by_a_substitution() {
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let s: Subst<Name, LVar> = Subst::from_list(vec![(x, var_term(y))]);
    // Ex y. x = y, with the body's `y` the binder's own index.
    let fm: LNFormula = ProtoFormula::exists(
        hint("y", LSort::Msg),
        ProtoFormula::Atom(ProtoAtom::EqE(free("x", LSort::Msg, 0), bound(0))),
    );
    let want: LNFormula = ProtoFormula::exists(
        hint("y", LSort::Msg),
        ProtoFormula::Atom(ProtoAtom::EqE(free("y", LSort::Msg, 0), bound(0))),
    );
    let out = apply_subst(&s, fm);
    assert_eq!(out, want);
    assert_eq!(formula_frees(&out), vec![y]);
}

/// Renaming rewrites each free variable through the caller's function and
/// keeps the bound indices, whatever the variable type carries.
#[test]
fn apply_rename_rewrites_free_variables_and_keeps_bound_indices() {
    let fm: SyntacticLNFormula = ProtoFormula::for_all(
        hint("y", LSort::Msg),
        pred("P", vec![free("x", LSort::Msg, 0), bound(0)]),
    );
    let want: SyntacticLNFormula = ProtoFormula::for_all(
        hint("y", LSort::Msg),
        pred("P", vec![free("x", LSort::Msg, 7), bound(0)]),
    );
    assert_eq!(
        apply_rename(fm, &mut |v| LVar::new(v.name, v.sort, 7)),
        want
    );
}

// =========================================================================
// open_formula / open_formula_prefix
// =========================================================================

/// The freshened binder replaces the index that belongs to it and nothing
/// else: an index of an enclosing binder counts one level further out
/// under the opened quantifier and stays bound.
#[test]
fn open_formula_replaces_only_its_own_index() {
    // All x. Ex y. x = y
    let fm: LNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
        ),
    );
    let mut fresh = PreciseFreshState::nothing_used();
    let (qua, x, body) = open_formula(&fm, &mut fresh).expect("the outermost quantifier");
    assert_eq!(qua, Quantifier::All);
    assert_eq!(x, LVar::new("x", LSort::Msg, 0));
    let want: LNFormula = ProtoFormula::exists(
        hint("y", LSort::Msg),
        ProtoFormula::Atom(ProtoAtom::EqE(free("x", LSort::Msg, 0), bound(0))),
    );
    assert_eq!(body, want);

    let tf: LNFormula = ProtoFormula::ltrue();
    assert!(open_formula(&tf, &mut fresh).is_none());
}

#[test]
fn prefix_opening_matches_successive_binders_and_fresh_supply() {
    fn reference(
        f: &LNFormula,
        fresh: &mut PreciseFreshState,
    ) -> (Vec<LVar>, Quantifier, LNFormula) {
        let (qua, x, mut body) = open_formula(f, fresh).unwrap();
        let mut vars = vec![x];
        while let ProtoFormula::Qua(next, hint, inner) = &body {
            if *next != qua {
                break;
            }
            let (x, opened) = open_binder(hint, inner, fresh);
            vars.push(x);
            body = opened;
        }
        (vars, qua, body)
    }
    for count in [1, 2, 7, 32] {
        for qua in [Quantifier::All, Quantifier::Ex] {
            for inner_depth in [0, 1, 3] {
                let indices = [
                    0,
                    inner_depth,
                    inner_depth + count - 1,
                    inner_depth + count,
                    u64::MAX,
                ];
                let raw = tamarin_term::term::unsafe_f_app(
                    tamarin_term::function_symbols::FunSym::Ac(
                        tamarin_term::function_symbols::AcSym::Mult,
                    ),
                    indices.iter().rev().map(|i| bound(*i)).collect(),
                );
                let mut body: LNFormula =
                    ProtoFormula::Atom(ProtoAtom::EqE(raw, free("x", LSort::Msg, 12)));
                for _ in 0..inner_depth {
                    body = ProtoFormula::Qua(
                        if qua == Quantifier::All {
                            Quantifier::Ex
                        } else {
                            Quantifier::All
                        },
                        hint("y", LSort::Msg),
                        Box::new(body).into(),
                    );
                }
                for _ in 0..count {
                    body = ProtoFormula::Qua(qua, hint("x", LSort::Msg), Box::new(body).into());
                }
                let mut old = PreciseFreshState::avoid_precise(vec![("x".into(), 20)]);
                let mut new = old.clone();
                assert_eq!(
                    open_formula_prefix(&body, &mut new),
                    reference(&body, &mut old)
                );
                for name in ["x", "y", "other"] {
                    assert_eq!(new.fresh_ident(name), old.fresh_ident(name));
                }
            }
        }
    }
}

#[test]
fn deep_prefix_opens_once_on_small_stack() {
    tamarin_test_support::on_stack(256 * 1024, || {
        let count = 8192;
        let mut f: LNFormula = ProtoFormula::Atom(ProtoAtom::EqE(bound(count - 1), bound(0)));
        for _ in 0..count {
            f = ProtoFormula::for_all(hint("x", LSort::Msg), f);
        }
        let (vars, qua, body) = open_formula_prefix(&f, &mut PreciseFreshState::nothing_used());
        assert_eq!(vars.len(), count as usize);
        assert_eq!(qua, Quantifier::All);
        assert_eq!(
            body,
            ProtoFormula::Atom(ProtoAtom::EqE(
                lift_free(&var_term(vars[0])),
                lift_free(&var_term(vars[count as usize - 1]))
            ))
        );
    });
}

/// The prefix is returned in binder order, outermost first, and every
/// binder's occurrences resolve to its own variable.
#[test]
fn open_formula_prefix_returns_the_binders_outermost_first() {
    // All x y. x = y
    let fm: LNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::for_all(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
        ),
    );
    let mut fresh = PreciseFreshState::nothing_used();
    let (xs, qua, body) = open_formula_prefix(&fm, &mut fresh);
    assert_eq!(
        xs,
        vec![LVar::new("x", LSort::Msg, 0), LVar::new("y", LSort::Msg, 0)]
    );
    assert_eq!(qua, Quantifier::All);
    assert_eq!(
        body,
        ProtoFormula::Atom(ProtoAtom::EqE(
            free("x", LSort::Msg, 0),
            free("y", LSort::Msg, 0)
        ))
    );
}

/// A binder of the other quantifier ends the prefix, and HS's guard
/// `q' == q` runs before the fresh draw, so that binder takes no index.
#[test]
fn open_formula_prefix_stops_at_a_different_quantifier() {
    // All x. Ex y. x = y
    let fm: LNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::exists(
            hint("y", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
        ),
    );
    let mut fresh = PreciseFreshState::nothing_used();
    let (xs, qua, body) = open_formula_prefix(&fm, &mut fresh);
    assert_eq!(xs, vec![LVar::new("x", LSort::Msg, 0)]);
    assert_eq!(qua, Quantifier::All);
    assert!(matches!(body, ProtoFormula::Qua(Quantifier::Ex, _, _)));
    assert_eq!(fresh.fresh_ident("y"), 0);
}

/// Two binders of one prefix that share a name are drawn as `x` and
/// `x.1`, so the inner one keeps its own identity after opening.
#[test]
fn open_formula_prefix_freshens_a_shadowed_binder() {
    // All x. All x. x = x
    let fm: LNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::for_all(
            hint("x", LSort::Msg),
            ProtoFormula::Atom(ProtoAtom::EqE(bound(1), bound(0))),
        ),
    );
    let mut fresh = PreciseFreshState::nothing_used();
    let (xs, _, body) = open_formula_prefix(&fm, &mut fresh);
    assert_eq!(
        xs,
        vec![LVar::new("x", LSort::Msg, 0), LVar::new("x", LSort::Msg, 1)]
    );
    assert_eq!(
        body,
        ProtoFormula::Atom(ProtoAtom::EqE(
            free("x", LSort::Msg, 0),
            free("x", LSort::Msg, 1)
        ))
    );
}

/// The supply is the caller's and is not rolled back per prefix, so two
/// sibling prefixes that use one binder name get distinct indices.  HS's
/// guarded conversion opens its prefixes this way (`convEx`/`convAll`,
/// Guarded.hs:535-564); its printer wraps each prefix in `scopeFreshness`
/// instead (Theory/Model/Formula.hs:503-506).
#[test]
fn open_formula_draws_from_one_unscoped_supply() {
    let prefix = || -> LNFormula {
        ProtoFormula::exists(
            hint("i", LSort::Node),
            ProtoFormula::Atom(ProtoAtom::Last(bound(0))),
        )
    };
    let mut fresh = PreciseFreshState::nothing_used();
    let (left, _, _) = open_formula_prefix(&prefix(), &mut fresh);
    let (right, _, _) = open_formula_prefix(&prefix(), &mut fresh);
    assert_eq!(left, vec![LVar::new("i", LSort::Node, 0)]);
    assert_eq!(right, vec![LVar::new("i", LSort::Node, 1)]);
}

/// `quantify` closes the variable `open_formula` drew, so putting the
/// binder back rebuilds the formula the opening started from.
#[test]
fn quantify_inverts_open_formula() {
    // All x. x = z
    let fm: LNFormula = ProtoFormula::for_all(
        hint("x", LSort::Msg),
        ProtoFormula::Atom(ProtoAtom::EqE(bound(0), free("z", LSort::Msg, 0))),
    );
    let mut fresh = avoid_precise_lnformula(&fm);
    let (qua, x, body) = open_formula(&fm, &mut fresh).expect("the quantifier");
    assert_eq!(qua, Quantifier::All);
    assert_eq!(for_all_var((x.name.to_string(), x.sort), &x, body), fm);
}

/// [`traverse_formula_atom`] hands the callback the atom itself, and the
/// callback's own `map_atom` walk of an `Action` reads the time point
/// before the fact's arguments (HS `Functor (ProtoAtom s)`,
/// Theory/Model/Atom.hs:121-127#fmap).  Atoms arrive left to right and
/// each returned formula is spliced in place of its atom.
#[test]
fn traverse_formula_atom_visits_the_action_timepoint_first() {
    use crate::fact::{FactTag, Multiplicity};

    let v = |n: &str, s| tamarin_term::vterm::var_term(BVar::Free(LVar::new(n, s, 0)));
    let action: LNFormula = ProtoFormula::Atom(ProtoAtom::Action(
        v("i", LSort::Node),
        Fact::new(
            FactTag::Proto(Multiplicity::Linear, "A", 2),
            vec![v("a", LSort::Msg), v("b", LSort::Msg)],
        ),
    ));
    let last: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(v("j", LSort::Node)));
    let fm = ProtoFormula::exists(("z".to_string(), LSort::Msg), action.and(last));

    let mut seen: Vec<String> = Vec::new();
    let out: LNFormula = traverse_formula_atom(&fm, &mut |a| {
        let _ = map_atom(a, &mut |t: &BLNTerm| {
            seen.push(match t {
                Term::Lit(Lit::Var(BVar::Free(x))) => x.name.to_string(),
                _ => "?".to_string(),
            });
            t.clone()
        });
        Ok::<LNFormula, ()>(ProtoFormula::ltrue())
    })
    .unwrap();

    assert_eq!(seen, vec!["i", "a", "b", "j"]);
    let expected: LNFormula = ProtoFormula::exists(
        ("z".to_string(), LSort::Msg),
        ProtoFormula::ltrue().and(ProtoFormula::ltrue()),
    );
    assert_eq!(out, expected);
}

// =========================================================================
// Haskell-faithfulness invariants for Connective and Quantifier order.
//
// Theory/Model/Formula.hs:106-108: `data Connective = And | Or | Imp | Iff`
// Theory/Model/Formula.hs:110-112: `data Quantifier = All | Ex`
//
// These orders matter for any BTreeMap<Connective,_> iteration and for
// Haskell-faithful structural comparison / round-tripping of formulas.
// =========================================================================

/// `Connective` Ord — `And < Or < Imp < Iff` from Theory/Model/Formula.hs:107.
#[test]
fn connective_ord_matches_haskell_declaration() {
    assert!(Connective::And < Connective::Or);
    assert!(Connective::Or < Connective::Imp);
    assert!(Connective::Imp < Connective::Iff);
}

/// `Quantifier` Ord — `All < Ex` from Theory/Model/Formula.hs:111.
///
/// The All<Ex order is required for Haskell-faithful structural /
/// BTreeMap comparisons and round-tripping of formulas, matching the
/// `data Quantifier = All | Ex` declaration order. (The guarded-formula
/// simplifier does not iterate quantifiers in this order; it
/// pattern-matches structurally — see `simplify_guarded_with`.)
#[test]
fn quantifier_ord_matches_haskell_declaration() {
    assert!(
        Quantifier::All < Quantifier::Ex,
        "All MUST sort before Ex (Theory/Model/Formula.hs:111)"
    );
}

/// `A(x) @ i` as an atom over `BVar` terms.
fn action_atom(name: &'static str) -> SyntacticAtom<BLNTerm> {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use tamarin_term::vterm::var_term;

    ProtoAtom::Action(
        var_term(BVar::Free(LVar::new("i", LSort::Node, 0))),
        Fact::new(
            FactTag::Proto(Multiplicity::Linear, name, 1),
            vec![var_term(BVar::Free(x_var()))],
        ),
    )
}

/// `formulaFacts` yields the fact of an `Action` atom and of nothing else.
/// A `Syntactic` atom carries a fact too and is skipped, which is the one
/// arm HS spells out (Theory/Tools/Wellformedness.hs:902).  The facts come
/// out in `foldFormula` order: left operand before right, through `Not`
/// and through a binder.
#[test]
fn formula_facts_collects_action_atoms_only() {
    use crate::fact::fact_tag_name;
    use tamarin_term::vterm::var_term;

    let eq: SyntacticLNFormula = ProtoFormula::Atom(ProtoAtom::EqE(
        var_term(BVar::Free(x_var())),
        var_term(BVar::Free(x_var())),
    ));
    let fm: SyntacticLNFormula = ProtoFormula::exists(
        ("x".to_string(), LSort::Msg),
        ProtoFormula::Atom(action_atom("A"))
            .and(ProtoFormula::Atom(pred_atom(BVar::Free(x_var()))).or(eq))
            .implies(ProtoFormula::Atom(action_atom("B")).not()),
    );
    let names: Vec<String> = formula_facts(&fm)
        .iter()
        .map(|fa| fact_tag_name(&fa.tag))
        .collect();
    assert_eq!(names, vec!["A".to_string(), "B".to_string()]);
}
#[test]
fn borrowed_atom_mapping_matches_owned_mapping_at_every_scope() {
    let var = tamarin_term::vterm::var_term(BVar::Bound(0));
    let mut formula: LNFormula = ProtoFormula::Atom(ProtoAtom::EqE(var.clone(), var));
    for i in 0..64 {
        formula = if i % 3 == 0 {
            ProtoFormula::Qua(
                Quantifier::All,
                ("x".into(), LSort::Msg),
                Box::new(formula).into(),
            )
        } else {
            ProtoFormula::Conn(
                Connective::And,
                Box::new(ProtoFormula::Atom(ProtoAtom::Last(
                    tamarin_term::vterm::var_term(BVar::Bound(i)),
                )))
                .into(),
                Box::new(formula).into(),
            )
        };
    }
    let mut depths = Vec::new();
    let got = map_atoms_ref(&formula, &mut |depth, atom| {
        depths.push(depth);
        atom.clone()
    });
    let mut old_depths = Vec::new();
    let want = map_atoms(formula, &mut |depth, atom| {
        old_depths.push(depth);
        atom.clone()
    });
    assert_eq!(got, want);
    assert_eq!(depths, old_depths);
}

#[test]
fn generic_tree_owners_keep_field_and_sibling_drop_order_on_unwind() {
    use crate::sapic::{Process, ProcessCombinator, SapicAction};
    use std::sync::{Arc, Mutex};
    struct Payload(usize, Option<usize>, Arc<Mutex<Vec<usize>>>);
    impl Drop for Payload {
        fn drop(&mut self) {
            self.2.lock().unwrap().push(self.0);
            assert_ne!(Some(self.0), self.1, "payload panic");
        }
    }
    for panic_at in [None, Some(0), Some(1), Some(2), Some(3)] {
        for process in [false, true] {
            let log = Arc::new(Mutex::new(Vec::new()));
            let payload = |i| Payload(i, panic_at, log.clone());
            let result = std::panic::catch_unwind(|| {
                if process {
                    let leaf = |i| Process::<_, u8>::Null(payload(i));
                    // Two siblings remain pending when the inner payload
                    // panics, so reversing the pending stack is observable.
                    drop(Process::Comb(
                        ProcessCombinator::Parallel,
                        payload(0),
                        Box::new(Process::Comb(
                            ProcessCombinator::Ndc,
                            payload(1),
                            Box::new(Process::Action(
                                SapicAction::Rep,
                                payload(2),
                                Box::new(leaf(3)).into(),
                            ))
                            .into(),
                            Box::new(leaf(4)).into(),
                        ))
                        .into(),
                        Box::new(leaf(5)).into(),
                    ));
                } else {
                    type F = ProtoFormula<Payload, Payload, u8, u8>;
                    let leaf = |i| F::Atom(ProtoAtom::Syntactic(payload(i)));
                    drop(F::for_all(
                        payload(0),
                        F::for_all(payload(1), F::exists(payload(2), leaf(3)))
                            .and(leaf(4))
                            .or(leaf(5)),
                    ));
                }
            });
            assert_eq!(result.is_err(), panic_at.is_some());
            assert_eq!(
                *log.lock().unwrap(),
                [0, 1, 2, 3, 4, 5],
                "process={process}, panic={panic_at:?}"
            );
        }
    }
}
