// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::atom::Unit2;
use tamarin_parser::ast as p;

/// HS `ppStep` (ProofSkeleton.hs) puts `/* unannotated */` beside an
/// unannotated step's method with `sep`: inline while both fit the ribbon
/// (73), on a line of its own at the step's indent once they do not.  An
/// annotated step carries no comment.  Rows are `(method, indent,
/// annotated, rendered)`.
#[test]
fn step_line_with_unann_table() {
    use crate::pretty_hpj::Doc;
    // With the comment this method overruns the ribbon.
    let long = "solve( (last(#k))  \u{2225} (something quite long here indeed yes) )";
    let rows = [
        (
            "simplify",
            2,
            false,
            "simplify /* unannotated */".to_string(),
        ),
        ("by sorry", 4, true, "by sorry".to_string()),
        (long, 2, false, format!("{long}\n  /* unannotated */")),
    ];
    for (method, indent, annotated, want) in rows {
        assert_eq!(
            step_line_with_unann(Doc::text(method), indent, annotated, ""),
            want
        );
    }
}

// =============================================================================
// Locally-nameless printer
// =============================================================================

/// Every sample printed through both locally-nameless printers, pinned to
/// the oracle's `--parse-only` render of the lemma-header shape, and the
/// two printers compared through the nested restriction-body wrapper as
/// well.  Rows are `(signature, formula, lines)`.
#[test]
fn lnformula_doc_renders_the_oracle_samples() {
    use crate::formula::{from_parser, to_lnformula};
    use tamarin_parser::parser::{parse_formula_str, parse_theory};

    // `builtins: multiset` opens `msetterm`'s `+` level
    // (Theory/Text/Parser/Term.hs).
    const MSET: &str = "builtins: multiset";
    const EXTRA: &str = "builtins: hashing, multiset\nfunctions: zero/0";
    let sig = |decls: &str| {
        let thy = parse_theory(&format!("theory T begin\n{decls}\nend"), &[]).unwrap();
        crate::elaborate::elaborate(&thy).unwrap().signature
    };

    let samples: &[(&str, &str, &[&str])] = &[
        (MSET, "T", &["  all-traces \"⊤\""]),
        (MSET, "F", &["  all-traces \"⊥\""]),
        (
            MSET,
            "(A(x) @ #i & B(x) @ #j) | C(x) @ #k",
            &["  all-traces \"((A( x ) @ #i) ∧ (B( x ) @ #j)) ∨ (C( x ) @ #k)\""],
        ),
        (
            MSET,
            "(not (D(x) @ #l) ==> E(x) @ #m) <=> C(x) @ #n",
            &["  all-traces \"((¬(D( x ) @ #l)) ⇒ (E( x ) @ #m)) ⇔ (C( x ) @ #n)\""],
        ),
        (
            MSET,
            "not (Ex x. A(x) @ #i)",
            &["  all-traces \"¬(∃ x. A( x ) @ #i)\""],
        ),
        (
            MSET,
            "All x y #i. A(x, y) @ #i",
            &["  all-traces \"∀ x y #i. A( x, y ) @ #i\""],
        ),
        (
            MSET,
            "All x. Ex #i. A(x) @ #i",
            &["  all-traces \"∀ x. ∃ #i. A( x ) @ #i\""],
        ),
        // The inner binder shadows the outer one: `x` and `x.1`.
        (
            MSET,
            "All x. Ex x. A(x) @ #i",
            &["  all-traces \"∀ x. ∃ x.1. A( x.1 ) @ #i\""],
        ),
        // Closed, the union is `[Bound 0, Bound 1]` = `y, x`; opening
        // rebuilds it through `f_app`, which re-sorts under the display
        // `LVar`s.
        (
            MSET,
            "All x y. (x + y) = z",
            &["  all-traces \"∀ x y. (x++y) = z\""],
        ),
        // A predicate atom and one with a bound argument; `to_lnformula`
        // is `None` for these.
        (MSET, "All x. P(x, y)", &["  all-traces \"∀ x. P( x, y )\""]),
        (
            MSET,
            "All x. Ex y. P(x, y)",
            &["  all-traces \"∀ x. ∃ y. P( x, y )\""],
        ),
        (
            MSET,
            "All x #i #j. OnlyOnce(x) @ i & OnlyOnce(x) @ j ==> #i = #j",
            &[
                "  all-traces",
                "  \"∀ x #i #j. ((OnlyOnce( x ) @ #i) ∧ (OnlyOnce( x ) @ #j)) ⇒ (#i = #j)\"",
            ],
        ),
        // The `_restrict` lifting shape: `#NOW` and an `x.1` binder.
        (
            MSET,
            "All x #NOW x.1. Restr_C_2_1(x, x.1) @ NOW ==> x = x.1",
            &["  all-traces \"∀ x #NOW x.1. (Restr_C_2_1( x, x.1 ) @ #NOW) ⇒ (x = x.1)\""],
        ),
        // Twelve conjuncts: the body wraps at the 110-column page width.
        (
            MSET,
            "All x #i1 #i2 #i3 #i4 #i5 #i6 #i7 #i8 #i9 #i10 #i11 #i12. \
             A(x) @ #i1 & A(x) @ #i2 & A(x) @ #i3 & A(x) @ #i4 & A(x) @ #i5 & \
             A(x) @ #i6 & A(x) @ #i7 & A(x) @ #i8 & A(x) @ #i9 & A(x) @ #i10 & \
             A(x) @ #i11 & A(x) @ #i12 ==> F",
            &[
                "  all-traces",
                "  \"∀ x #i1 #i2 #i3 #i4 #i5 #i6 #i7 #i8 #i9 #i10 #i11 #i12.",
                "    ((((((((((((A( x ) @ #i1) ∧ (A( x ) @ #i2)) ∧ (A( x ) @ #i3)) ∧",
                "             (A( x ) @ #i4)) ∧",
                "            (A( x ) @ #i5)) ∧",
                "           (A( x ) @ #i6)) ∧",
                "          (A( x ) @ #i7)) ∧",
                "         (A( x ) @ #i8)) ∧",
                "        (A( x ) @ #i9)) ∧",
                "       (A( x ) @ #i10)) ∧",
                "      (A( x ) @ #i11)) ∧",
                "     (A( x ) @ #i12)) ⇒",
                "    (⊥)\"",
            ],
        ),
        // Sorted binders, merged same-kind quantifier blocks with a
        // shadowed name, the binder supply restored after each block, the
        // `⊏`, `last` and `<` atoms, terms inside a fact, and a binder whose
        // source index is not its display index.
        (
            EXTRA,
            "All ~k $p #i. K(~k, $p) @ #i",
            &["  all-traces \"∀ ~k $p #i. K( ~k, $p ) @ #i\""],
        ),
        (
            EXTRA,
            "All x. All x. A(x) @ #i",
            &["  all-traces \"∀ x x.1. A( x.1 ) @ #i\""],
        ),
        (
            EXTRA,
            "All x. All y. P(x, y) @ #i",
            &["  all-traces \"∀ x y. P( x, y ) @ #i\""],
        ),
        (
            EXTRA,
            "(All x. A(x) @ #i) & (All x. B(x) @ #j)",
            &["  all-traces \"(∀ x. A( x ) @ #i) ∧ (∀ x. B( x ) @ #j)\""],
        ),
        (
            EXTRA,
            "All x. ((Ex y. A(y) @ #i) & (Ex y. B(y) @ #j)) ==> A(x) @ #k",
            &[
                "  all-traces",
                "  \"∀ x. ((∃ y. A( y ) @ #i) ∧ (∃ y. B( y ) @ #j)) ⇒ (A( x ) @ #k)\"",
            ],
        ),
        (EXTRA, "All x y. x << y", &["  all-traces \"∀ x y. x ⊏ y\""]),
        (
            EXTRA,
            "All #i. last(#i)",
            &["  all-traces \"∀ #i. last(#i)\""],
        ),
        (
            EXTRA,
            "All #i #j. #i < #j",
            &["  all-traces \"∀ #i #j. #i < #j\""],
        ),
        (
            EXTRA,
            "All x y. P(<x, y>, h(x)) @ #i",
            &["  all-traces \"∀ x y. P( <x, y>, h(x) ) @ #i\""],
        ),
        (
            EXTRA,
            "All x. P(x, zero) @ #i",
            &["  all-traces \"∀ x. P( x, zero ) @ #i\""],
        ),
        (
            EXTRA,
            "All x. A(x) @ #i ==> Ex x.1. B(x.1) @ #i",
            &["  all-traces \"∀ x. (A( x ) @ #i) ⇒ (∃ x.1. B( x.1 ) @ #i)\""],
        ),
        (
            EXTRA,
            "All x.1. A(x.1) @ #i ==> Ex x. B(x) @ #i",
            &["  all-traces \"∀ x. (A( x ) @ #i) ⇒ (∃ x.1. B( x.1 ) @ #i)\""],
        ),
        // `quantify` closes only what equals its `LVar` in name, sort AND
        // index (Theory/Model/Formula.hs), so a message `k` under a `~k` or
        // `$k` binder stays free and pushes the binder to `k.1`.
        (
            MSET,
            "Ex ~k #i. Made(k) @ i",
            &["  all-traces \"∃ ~k.1 #i. Made( k ) @ #i\""],
        ),
        (
            MSET,
            "Ex $k #i. Made(k) @ i",
            &["  all-traces \"∃ $k.1 #i. Made( k ) @ #i\""],
        ),
    ];
    for (decls, src, expected_lines) in samples {
        let msig = sig(decls);
        let expected = expected_lines.join("\n");
        let f = parse_formula_str(src, &msig).unwrap();
        let ln = from_parser(&f, &msig).unwrap();
        assert_eq!(
            lemma_header_line_doc("all-traces", syntactic_lnformula_doc(&ln)),
            expected,
            "syntactic_lnformula_doc on {src}"
        );
        // `to_lnformula` is `None` for a predicate atom.
        if let Some(plain) = to_lnformula(&ln) {
            assert_eq!(
                lemma_header_line_doc("all-traces", lnformula_doc(&plain)),
                expected,
                "lnformula_doc on {src}"
            );
            assert_eq!(
                doublequoted_nested_doc(lnformula_doc(&plain), 2),
                doublequoted_nested_doc(syntactic_lnformula_doc(&ln), 2),
                "nested body on {src}"
            );
        }
    }
}

/// `prettyAtom = prettyProtoAtom (const emptyDoc)` (Atom.hs): the
/// sugar-free atom renders as the empty document.
#[test]
fn lnformula_doc_prints_unit2_syntactic_as_empty() {
    let atom: LNFormula = ProtoFormula::Atom(ProtoAtom::Syntactic(Unit2));
    assert_eq!(lnformula_doc(&atom).render(), "");
    let conj: LNFormula =
        ProtoFormula::ltrue().and(ProtoFormula::Atom(ProtoAtom::Syntactic(Unit2)));
    assert_eq!(lnformula_doc(&conj).render(), "(⊤) ∧ ()");
}

/// A `Bound` index with no enclosing binder is HS `extractFree`'s error
/// (Theory/Model/Formula.hs).
#[test]
#[should_panic(expected = "prettyFormula: illegal bound variable '0'")]
fn lnformula_doc_panics_on_unbound_index() {
    use tamarin_term::lterm::BVar;
    use tamarin_term::vterm::var_term;

    let f: LNFormula = ProtoFormula::Atom(ProtoAtom::Last(var_term(BVar::Bound(0))));
    let _ = lnformula_doc(&f);
}

#[test]
fn wrapped_conditional_node_names_round_trip() {
    use crate::formula::from_parser;
    use tamarin_parser::parser::{parse_formula_str, parse_theory};
    let signature = crate::elaborate::elaborate(&parse_theory("theory T begin end", &[]).unwrap())
        .unwrap()
        .signature;
    for reserved in ["ifdef", "else", "endif"] {
        let names = [
            "xxxxxxxxxxxxxxxxxxx0",
            "xxxxxxxxxxxxxxxxxxx1",
            "xxxxxxxxxxxxxxxxxxx2",
            reserved,
            "xxxxxxxxxxxxxxxxxxx3",
            "xxxxxxxxxxxxxxxxxxx4",
        ];
        let binders = names
            .iter()
            .map(|name| format!("#{name}"))
            .collect::<Vec<_>>()
            .join(" ");
        let atoms = names
            .iter()
            .map(|name| format!("Seen() @ #{name}"))
            .collect::<Vec<_>>()
            .join(" & ");
        let formula = parse_formula_str(&format!("All {binders}. {atoms}"), &signature).unwrap();
        let original = from_parser(&formula, &signature).unwrap();
        for width in [24, 40, 80] {
            let rendered = syntactic_lnformula_doc(&original).render_with(width, width);
            let source = format!("theory T begin\nlemma L: \"{rendered}\"\nend");
            let reparsed =
                parse_theory(&source, &[]).unwrap_or_else(|error| panic!("{source}: {error}"));
            let p::TheoryItem::Lemma(lemma) = &reparsed.items[0] else {
                panic!("missing lemma")
            };
            assert_eq!(from_parser(&lemma.formula, &signature).unwrap(), original);
        }
    }
}
