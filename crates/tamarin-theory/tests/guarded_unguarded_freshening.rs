// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the variable names in the `unguarded variable(s) …` diagnostic.
//!
//! `formulaToGuarded` runs the whole conversion inside a `Precise.FreshT`
//! seeded with `avoidPrecise fmOrig` (Guarded.hs:472-474).  Every quantifier
//! prefix it opens draws its binders through `freshLVar`
//! (Theory/Model/Formula.hs:296-309), and `noUnguardedVars`
//! (Guarded.hs:506-512) reports
//! the survivors under those FRESHENED names.  So the reported index depends
//! on state threaded across the entire formula — the free variables that
//! seeded it, and every binder of the same name opened earlier, whether
//! enclosing or merely to the left.
//!
//! Expected strings are the pinned oracle's bytes for the same lemmas
//! (`tamarin-prover` at the submodule pin, plain no-prove render).

use tamarin_parser::parse_theory;
use tamarin_theory::guarded::formula_to_guarded_parsed;

/// Convert lemma `name` of `theory` and return the rejection's first line.
fn unguarded_message(theory: &str, name: &str) -> String {
    let parsed = parse_theory(theory, &[]).expect("theory parses");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("theory elaborates");
    let lemma = parsed
        .items
        .iter()
        .find_map(|i| match i {
            tamarin_parser::ast::TheoryItem::Lemma(l) if l.name == name => Some(l),
            _ => None,
        })
        .unwrap_or_else(|| panic!("lemma `{}` present", name));
    formula_to_guarded_parsed(&lemma.formula, &elaborated.signature.maude_sig)
        .expect_err("formula is unguardable")
        .message
}

/// The inner `x` shadows the already-opened outer `x`, so the supply for
/// "x" is at 1 by the time the inner prefix is drawn.
#[test]
fn shadowed_binder_reported_freshened() {
    const THEORY: &str = r#"theory GDlem
begin
lemma L1:
  "All x #NOW. Foo(x) @ #NOW ==> (All x z. (<x, z> = x) ==> F)"
rule A: [ In(x) ] --[ Foo(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L1"),
        "unguarded variable(s) 'x.1', 'z' in the subformula"
    );
}

/// One state for the whole formula, not a count of ENCLOSING binders: in
/// `L2` the guardable left conjunct has already consumed `x`, in `L3` the
/// unguardable conjunct is reached first and `x` is still untouched.
#[test]
fn sibling_prefix_consumes_the_supply() {
    const THEORY: &str = r#"theory GDsib
begin
lemma L2:
  "(All x #i. Foo(x) @ #i ==> F) & (All x z. (<x, z> = x) ==> F)"
lemma L3:
  "(All x z. (<x, z> = x) ==> F) & (All x #i. Foo(x) @ #i ==> F)"
rule A: [ In(x) ] --[ Foo(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L2"),
        "unguarded variable(s) 'x.1', 'z' in the subformula"
    );
    assert_eq!(
        unguarded_message(THEORY, "L3"),
        "unguarded variable(s) 'x', 'z' in the subformula"
    );
}

/// `avoidPrecise` seeds `name -> maxIdx+1` over the FREE variables
/// (LTerm.hs:706-709, 714-715): a free `x.3` puts the supply at 4 before
/// conversion
/// starts.
#[test]
fn free_variable_seeds_the_supply() {
    const THEORY: &str = r#"theory GDfree
begin
lemma L4:
  "Foo(x.3) @ #i ==> (All x z. (<x, z> = x) ==> F)"
rule A: [ In(x) ] --[ Foo(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L4"),
        "unguarded variable(s) 'x.4', 'z' in the subformula"
    );
}

/// `avoidPreciseVars` keys on the bare `lvarName` (LTerm.hs:706-709), so a
/// free TEMPORAL `#x.2` pushes the supply a message-sorted binder `x` draws
/// from.
#[test]
fn supply_is_shared_across_sorts_of_one_name() {
    const THEORY: &str = r#"theory GDfree2
begin
lemma L5:
  "Foo(y) @ #x.2 ==> (All x z. (<x, z> = x) ==> F)"
rule A: [ In(x) ] --[ Foo(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L5"),
        "unguarded variable(s) 'x.3', 'z' in the subformula"
    );
}

/// Which occurrences a binder captures is decided at full `Eq LVar`
/// (`quantify`, Theory/Model/Formula.hs:347-352), so under `∀ x` the
/// occurrence `x.1`
/// stays FREE and seeds the supply to 2 — the left conjunct then takes 2 and
/// the failing prefix reports 3.
#[test]
fn binder_capture_is_index_aware() {
    const THEORY: &str = r#"theory GDscope
begin
lemma L6:
  "(All x #i. Foo(x) @ #i ==> Bar(x.1) @ #i) & (All x z. (<x, z> = x) ==> F)"
rule A: [ In(x) ] --[ Foo(x), Bar(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L6"),
        "unguarded variable(s) 'x.3', 'z' in the subformula"
    );
}

/// Same rule on the sort component: the timepoint `#x` is not captured by
/// the message-sorted binder `x`, so it seeds the supply to 1.
#[test]
fn binder_capture_is_sort_aware() {
    const THEORY: &str = r#"theory GDsort
begin
lemma L8:
  "(All x. (Foo(x) @ #x ==> F)) & (All x z. (<x, z> = x) ==> F)"
rule A: [ In(x) ] --[ Foo(x) ]-> [ ]
end
"#;
    assert_eq!(
        unguarded_message(THEORY, "L8"),
        "unguarded variable(s) 'x.2', 'z' in the subformula"
    );
}
