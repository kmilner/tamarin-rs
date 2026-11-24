// Currently GPL 3.0; see README.md for licensing details.

//! The parse-time duplicate-rule check against HS, around HS's lazy
//! `fAppAC: empty argument list` error.
//!
//! HS builds terms lazily, so an `[AC]` symbol applied to nothing raises
//! only where something forces it, and which error HS reports first depends
//! on how far its evaluation gets. The port's check treats such a term as an
//! inert constant and the load raises the error, so the contract is:
//!
//! - a theory without one gets HS's outcome exactly;
//! - a theory with one is rejected, as a duplicate rule or with `fAppAC`;
//! - `input-manifest` exits 3 exactly when the parse is rejected, and never
//!   reports the `fAppAC` error, which belongs to the load.
//!
//! Each row's HS outcome was captured from the pinned oracle's
//! `--parse-only`.
//!
//! A rule's `let` bindings are the exception, checked exactly: HS evaluates
//! an unused binding's image only as far as its outermost symbol.

mod common;

use common::{maude_available, run_binary};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    /// `duplicate rule`.
    Dup,
    /// `fAppAC: empty argument list`.
    Ac,
    /// A rejection of the syntax.
    Syntax,
    Ok,
}

#[derive(Clone, Copy)]
enum Row {
    /// No empty AC application: HS's outcome, given.
    Valid(Outcome),
    /// An empty AC application and no syntax error: `Dup` or `Ac`.
    EmptyAc,
    /// A syntax error, which the parse reports as HS does.
    Syntax,
}

fn outcome(code: i32, stderr: &str) -> Outcome {
    if stderr.contains("fAppAC") {
        Outcome::Ac
    } else if stderr.contains("Conflicting rule") || stderr.contains("duplicate rule") {
        Outcome::Dup
    } else if code != 0 {
        Outcome::Syntax
    } else {
        Outcome::Ok
    }
}

const CASES: &[(&str, &str, Row)] = &[
    ("dup_ac_parent", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f(f(), 'a')) ]\nrule R: [ ] --> [ Out(h('b')) ]\nend\n", Row::EmptyAc),
    ("dup_ac_parent_same_sym", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f(f(), 'a')) ]\nrule R: [ ] --> [ Out(f('b', 'c')) ]\nend\n", Row::EmptyAc),
    ("dup_after_bad_equation", "theory T begin\nfunctions: f/2 [AC], h/1\nequations: h(x) = f()\nrule R [color=#ff0000]: [ ] --> [ Out('a') ]\nrule R [color=#00ff00]: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_after_bad_macro", "theory T begin\nfunctions: f/2 [AC], h/1\nmacros: boom(x) = f()\nrule R [color=#ff0000]: [ ] --> [ Out('a') ]\nrule R [color=#00ff00]: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_after_bad_pred", "theory T begin\nfunctions: f/2 [AC], h/1\npredicates: P(x) <=> x = f()\nrule R [color=#ff0000]: [ ] --> [ Out('a') ]\nrule R [color=#00ff00]: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_attrs_differ", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R [color=#ff0000]: [ ] --> [ Out(f()) ]\nrule R [color=#00ff00]: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_concs_bottom_acts_differ", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --[ A('x') ]-> [ Out(f()) ]\nrule R: [ ] --[ B('x') ]-> [ Out(f()) ]\nend\n", Row::EmptyAc),
    ("dup_concs_differ_acts_bottom", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --[ A('x') ]-> [ Out('a') ]\nrule R: [ ] --[ A(f()) ]-> [ Out('b') ]\nend\n", Row::EmptyAc),
    ("dup_fact_tag_differs", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\nrule R: [ ] --> [ Foo(f()) ]\nend\n", Row::EmptyAc),
    ("dup_identical", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\nrule R: [ ] --> [ Out(f()) ]\nend\n", Row::EmptyAc),
    ("dup_noeq_parent_differs", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(h(f())) ]\nrule R: [ ] --> [ Out(<'a','b'>) ]\nend\n", Row::EmptyAc),
    ("dup_noeq_parent_same_root", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(h(f())) ]\nrule R: [ ] --> [ Out(h('b')) ]\nend\n", Row::EmptyAc),
    ("dup_prems_differ_first", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ Fr(~x) ] --> [ Out(f()) ]\nrule R: [ In(x) ] --> [ Out(f()) ]\nend\n", Row::EmptyAc),
    ("dup_restr_pred_bottom", "theory T begin\nfunctions: f/2 [AC], h/1\npredicates: P(x) <=> x = f()\nrule R: [ ] --[ _restrict(P('a')) ]-> [ Out('a') ]\nrule R: [ ] --[ _restrict(P('a')) ]-> [ Out('b') ]\nend\n", Row::Syntax),
    ("dup_restr_vs_none", "theory T begin\nfunctions: f/2 [AC], h/1\npredicates: P(x) <=> x = f()\nrule R: [ ] --[ _restrict(P('a')) ]-> [ Out('a') ]\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_same_attrs_term_vs_lit", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("dup_second_errs", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out('a') ]\nrule R: [ ] --> [ Out(f()) ]\nend\n", Row::EmptyAc),
    ("dup_valid_differs", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out('a') ]\nrule R: [ ] --> [ Out('b') ]\nend\n", Row::Valid(Outcome::Dup)),
    ("dup_valid_identical", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out('a') ]\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::Valid(Outcome::Ok)),
    ("dup_via_include", "theory T begin\nfunctions: f/2 [AC], h/1\n#include \"inc_rule.inc\"\nrule R: [ ] --> [ Out('b') ]\nend\n", Row::EmptyAc),
    ("embedded_restr", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --[ _restrict(All x #i. A(x)@i ==> x = f()) ]-> [ ]\nend\n", Row::EmptyAc),
    ("equation", "theory T begin\nfunctions: f/2 [AC], h/1\nequations: h(x) = f()\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("equation_via_include", "theory T begin\nfunctions: f/2 [AC], h/1\n#include \"inc_eq.inc\"\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("lemma", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --[ A('a') ]-> [ ]\nlemma L: \"All x #i. A(x)@i ==> x = f()\"\nend\n", Row::EmptyAc),
    ("let_binding", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: let y = f() in [ ] --> [ Out(y) ]\nend\n", Row::EmptyAc),
    ("macro", "theory T begin\nfunctions: f/2 [AC], h/1\nmacros: boom(x) = f()\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("macro_used", "theory T begin\nfunctions: f/2 [AC], h/1\nmacros: boom(x) = f()\nrule R: [ ] --> [ Out(boom('a')) ]\nend\n", Row::EmptyAc),
    ("predicate", "theory T begin\nfunctions: f/2 [AC], h/1\npredicates: P(x) <=> x = f()\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::EmptyAc),
    ("restriction_item", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --[ A('a') ]-> [ ]\nrestriction X: \"All x #i. A(x)@i ==> x = f()\"\nend\n", Row::EmptyAc),
    ("rule_body", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\nend\n", Row::EmptyAc),
    ("syntax_after_dup", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\nrule R: [ ] --> [ Out(f()) ]\n?\nend\n", Row::Syntax),
    ("syntax_after_rule", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f()) ]\n? \nend\n", Row::Syntax),
    ("valid_ac_flatten", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f('a',f('b','c'))) ]\nrule R: [ ] --> [ Out(f(f('a','b'),'c')) ]\nend\n", Row::Valid(Outcome::Ok)),
    ("valid_ac_order", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(f('a','b')) ]\nrule R: [ ] --> [ Out(f('b','a')) ]\nend\n", Row::Valid(Outcome::Ok)),
    ("valid_colour_spelling", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R [color=#ff0000]: [ ] --> [ Out('a') ]\nrule R [colour=#ff0000]: [ ] --> [ Out('a') ]\nend\n", Row::Valid(Outcome::Ok)),
    ("valid_differs_later", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(h('a')) ]\nrule S: [ ] --> [ Out('b') ]\nrule R: [ ] --> [ Out(h('b')) ]\nend\n", Row::Valid(Outcome::Dup)),
    ("valid_let_vs_expansion", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: let x = 'a' in [ ] --> [ Out(x) ]\nrule R: [ ] --> [ Out('a') ]\nend\n", Row::Valid(Outcome::Ok)),
    ("valid_pair_sugar", "theory T begin\nfunctions: f/2 [AC], h/1\nrule R: [ ] --> [ Out(<'a','b'>) ]\nrule R: [ ] --> [ Out(pair('a','b')) ]\nend\n", Row::Valid(Outcome::Ok)),
];

#[test]
fn duplicate_rule_check_rejects_what_haskell_rejects() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let dir = std::env::temp_dir().join(format!(
        "tamarin_parse_time_empty_ac_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("inc_rule.inc"), "rule R: [ ] --> [ Out(f()) ]\n").unwrap();
    std::fs::write(dir.join("inc_eq.inc"), "equations: h(x) = f()\n").unwrap();
    let mut failures = Vec::new();
    for &(name, source, row) in CASES {
        let theory = dir.join(format!("{name}.spthy"));
        std::fs::write(&theory, source).unwrap();
        let (code, _, stderr) = run_binary(&["--parse-only"], &[&theory]);
        let got = outcome(code, &stderr);
        let allowed = match row {
            Row::Valid(hs) => got == hs,
            Row::EmptyAc => matches!(got, Outcome::Dup | Outcome::Ac),
            Row::Syntax => got == Outcome::Syntax,
        };
        if !allowed {
            failures.push(format!("{name}: --parse-only gave {got:?}\n{stderr}"));
        }
        let rejected_by_parse = matches!(got, Outcome::Dup | Outcome::Syntax);
        let (code, _, stderr) = run_binary(&["input-manifest"], &[&theory]);
        if code != if rejected_by_parse { 3 } else { 0 } {
            failures.push(format!(
                "{name}: input-manifest exited {code} after {got:?}\n{stderr}"
            ));
        }
    }
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `--parse-only` of a rule `let` block, with the pinned oracle's outcome.
const LET_CASES: &[(&str, &str, Outcome)] = &[
    ("used", "let x = h(f()) in [ ] --> [ Out(x) ]", Outcome::Ac),
    (
        "used_through_binding",
        "let a = h(f())\n b = h(a) in [ ] --> [ Out(b) ]",
        Outcome::Ac,
    ),
    (
        "unused_empty",
        "let u = f() in [ ] --> [ Out('a') ]",
        Outcome::Ac,
    ),
    (
        "unused_nested",
        "let u = h(f()) in [ ] --> [ Out('a') ]",
        Outcome::Ok,
    ),
    (
        "unused_pair",
        "let u = <f(), 'b'> in [ ] --> [ Out('a') ]",
        Outcome::Ok,
    ),
    (
        "unused_chain",
        "let a = h(f())\n b = h(a) in [ ] --> [ Out('c') ]",
        Outcome::Ok,
    ),
    (
        "unused_wrong_arity",
        "let u = h('a', 'b') in [ ] --> [ Out('a') ]",
        Outcome::Ok,
    ),
];

#[test]
fn let_bindings_raise_where_haskell_does() {
    if !maude_available() {
        eprintln!("skipping: maude not on path");
        return;
    }
    let dir = std::env::temp_dir().join(format!("tamarin_let_empty_ac_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut failures = Vec::new();
    for &(name, rule, hs) in LET_CASES {
        let theory = dir.join(format!("{name}.spthy"));
        let source = format!("theory T begin\nfunctions: f/2 [AC], h/1\nrule R: {rule}\nend\n");
        std::fs::write(&theory, source).unwrap();
        let (code, _, stderr) = run_binary(&["--parse-only"], &[&theory]);
        let got = outcome(code, &stderr);
        if got != hs {
            failures.push(format!(
                "{name}: --parse-only gave {got:?}, HS {hs:?}\n{stderr}"
            ));
        }
    }
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
