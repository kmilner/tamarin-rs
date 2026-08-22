// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Where the SAPIC `=v` match pattern is grammar and where it is not.
//!
//! HS threads a PATTERN literal parser (`ltypedpatternlit = vlit
//! sapicpatternvar`, Theory/Text/Parser/Sapic.hs:52-53) into exactly three
//! positions: an `in` message (Parser/Sapic.hs:102,109), the pattern side of a
//! process `let` binding (`sapicpatternterm`, Parser/Sapic.hs:61,264), and an
//! embedded MSR rule with its `_restrict` formulas (`genericRule
//! sapicpatternvar`, Parser/Sapic.hs:155).  `sapicpatternvar` itself is `=` followed
//! by a VARIABLE (Token.hs:512-519) — never an application or a tuple.
//! Everywhere else the literal parser has no `=` alternative, so a `=` starts
//! no term at all.
//!
//! Every rejected source below was run against the pinned oracle (ef3f0468):
//! the line/column of each error is the oracle's.  Each test pins that
//! position; the sorted-variable alternation pins its expected set too.  The
//! comments record the oracle's frame where the port's report differs.

use tamarin_parser::ast as p;
use tamarin_parser::{parse_theory, ParseError};

/// Parse expecting failure; return the error.
fn parse_err(src: &str) -> ParseError {
    parse_theory(src, &[]).expect_err("the oracle rejects this source")
}

/// The `(line, col)` of the rejected source's error.
fn err_pos(src: &str) -> (u32, u32) {
    let e = parse_err(src);
    let at = *e.location();
    (at.line, at.col)
}

/// Asserts the source fails at `line`:`col` carrying exactly the sorted-lvar
/// prefix labels of `sortedLVarNoSuffix` (Token.hs:486-499).
#[track_caller]
fn assert_sorted_lvar_expected(src: &str, line: u32, col: u32) {
    let e = parse_err(src);
    let at = *e.location();
    assert_eq!((at.line, at.col), (line, col), "position of {e:?}");
    assert_eq!(
        e.expected().unwrap_or_default(),
        ["\"$\"", "\"~\"", "identifier", "\"#\"", "\"%\""],
        "expected set of {e:?}"
    );
}

/// The `SapicAction` chain of the theory's single top-level process,
/// flattened in source order.
fn process_actions(src: &str) -> Vec<p::SapicAction> {
    let thy = parse_theory(src, &[]).expect("the oracle accepts this source");
    let proc = thy
        .items
        .iter()
        .find_map(|it| match it {
            p::TheoryItem::TopLevelProcess(pr) => Some(pr.clone()),
            _ => None,
        })
        .expect("theory has a top-level process");
    let mut out = Vec::new();
    let mut cur = proc;
    while let p::Process::Action { action, body } = cur {
        out.push(action);
        cur = *body;
    }
    out
}

// ---------------------------------------------------------------------------
// Accepted pattern positions
// ---------------------------------------------------------------------------

#[test]
fn in_message_keeps_the_pattern_marker_on_the_variable() {
    // Loads with exit 0 on both engines (bound `x`, then a match on it).
    let acts = process_actions(
        "theory T begin\nprocess:\n  in('c', x); in('c', <=x, y>); out('c', y)\nend\n",
    );
    let p::SapicAction::ChIn { msg, .. } = &acts[1] else {
        panic!("second action is the pattern in");
    };
    let p::Term::Pair(items) = msg else {
        panic!("message is the tuple");
    };
    // The parser stores the marker as-is; the SAPIC conversion strips it and
    // records the match-var (`unpattern`/`extractMatchingVariables`,
    // Parser/Sapic.hs:113-114).
    assert!(
        matches!(&items[0], p::Term::PatMatch(inner)
            if matches!(&**inner, p::Term::Var(v) if v.name == "x")),
        "`=x` is a PatMatch over the bare variable"
    );
    assert!(matches!(&items[1], p::Term::Var(v) if v.name == "y"));
}

#[test]
fn pattern_variable_carries_its_sapic_type() {
    // `=x:nat` — `sapicvar` takes `option Nothing (colon *> typep)`
    // (Token.hs:506-510).  Loads with exit 0 on both engines.
    let acts = process_actions(
        "theory T begin\nprocess:\n  in('c', x:nat); in('c', <=x:nat, y>); out('c', y)\nend\n",
    );
    let p::SapicAction::ChIn { msg, .. } = &acts[1] else {
        panic!("second action is the pattern in");
    };
    let p::Term::Pair(items) = msg else {
        panic!("message is the tuple");
    };
    let p::Term::PatMatch(inner) = &items[0] else {
        panic!("`=x:nat` is a PatMatch");
    };
    let p::Term::Var(v) = &**inner else {
        panic!("the pattern wraps a variable");
    };
    assert_eq!(v.typ.as_deref(), Some("nat"));
}

#[test]
fn embedded_msr_facts_and_restrict_formulas_take_patterns() {
    // The whole embedded rule parses with pattern literals (`genericRule
    // sapicpatternvar`, Parser/Sapic.hs:155) — fact rows and `_restrict` formulas
    // alike.  This is scripts/divergence_fixtures/sapic_msr_pattern_restrict
    // at the AST layer: the parser keeps both markers, and the SAPIC
    // conversion strips them (facts via `unpattern`, formulas via
    // `unpatternVar` — Parser/Sapic.hs:156-160).
    let acts = process_actions(
        "theory T begin\nprocess:\n  in('c', x); \
         [ St(=x) ] --[ Ev(x), _restrict( =x = x ) ]-> [ Out(x) ]\nend\n",
    );
    let p::SapicAction::Msr {
        prems,
        restrictions,
        ..
    } = &acts[1]
    else {
        panic!("second action is the embedded MSR");
    };
    assert!(
        matches!(&prems[0].args[0], p::Term::PatMatch(_)),
        "the premise keeps its `=x` marker for the conversion to strip"
    );
    let p::FormulaKind::Atom(p::Atom::Eq(lhs, _)) = &restrictions[0].kind else {
        panic!("the restriction is the equality atom");
    };
    assert!(
        matches!(lhs, p::Term::PatMatch(_)),
        "the `_restrict` formula keeps its `=x` marker too"
    );
}

#[test]
fn let_binding_pattern_side_takes_a_pattern_variable() {
    // Parsing at all is the assertion: the pattern side accepted `=y`.
    parse_theory(
        "theory T begin\nprocess:\n  in('c', y); let =y = y in out('c', y)\nend\n",
        &[],
    )
    .expect("the oracle accepts this source");
}

// ---------------------------------------------------------------------------
// Rejected: `=` on a non-variable inside a pattern position
// ---------------------------------------------------------------------------

#[test]
fn eq_on_a_tuple_or_literal_needs_a_sort_prefix() {
    // `sapicvar` starts with one of the five sort prefixes
    // (`sortedLVarNoSuffix`, Token.hs:486-499); anything else fails with the
    // alternation's five labels, which the oracle printed as
    // `expecting "$", "~", identifier, "#" or "%"`.
    assert_sorted_lvar_expected(
        "theory T begin\nprocess:\n  in('c', =<x, y>); out('c', 'k')\nend\n",
        3,
        12,
    );
    assert_sorted_lvar_expected(
        "theory T begin\nprocess:\n  in('c', ='d'); out('c', 'k')\nend\n",
        3,
        12,
    );
}

#[test]
fn eq_on_an_application_is_rejected_at_the_open_paren() {
    // `=h(x)` parses as the match-var `h`; the `(` then breaks the enclosing
    // grammar.  Oracle frame (in): `(line 4, column 13): unexpected "(" /
    // expecting letter or digit, ".", ":" or ")"`.  The port reports the same
    // position.
    assert_eq!(
        err_pos(
            "theory T begin\nfunctions: h/1\nprocess:\n  in('c', =h(x)); out('c', 'ok')\nend\n"
        ),
        (4, 13)
    );

    // Oracle frame (let): `(line 4, column 21): unexpected "(" /
    // expecting letter or digit, ".", ":" or "="`.
    assert_eq!(
        err_pos(
            "theory T begin\nfunctions: h/1\nprocess:\n  in('c', y); let =h(x) = y in out('c', 'ok')\nend\n"
        ),
        (4, 21)
    );
}

// ---------------------------------------------------------------------------
// Rejected: `=` outside every pattern position
// ---------------------------------------------------------------------------

#[test]
fn eq_starts_no_term_outside_pattern_positions() {
    // An `out` message parses with `ltypedlit` (Parser/Sapic.hs:117-131) and a plain
    // rule's facts with `msgvar` — neither has a `=` alternative, so the
    // oracle stops at the `=` itself: `unexpected "=" / expecting term or
    // ")"`.  The port rejects at the same position: the `allow_pat`
    // gate is what makes these a parse error rather than something
    // translation or elaboration reports later with an unrelated message.
    assert_eq!(
        err_pos("theory T begin\nprocess:\n  in('c', x); out('c', =x)\nend\n"),
        (3, 24)
    );

    assert_eq!(
        err_pos("theory T begin\nrule R: [ In(=x) ] --> [ Out(x) ]\nend\n"),
        (2, 14)
    );
}
