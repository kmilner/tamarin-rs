// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Byte-pins the `// safety formula` annotation a restriction carries.
//!
//! HS `prettyRestriction` (TheoryObject.hs:889-901, see line 894) prints
//! `nest 2 (lineComment_ "safety formula")` under the restriction's formula
//! iff `isSafetyFormula (formulaToGuarded_ expandedFormula)` holds, and
//! `isSafetyFormula` (Guarded.hs:156-164) demands the guarded formula be
//! CLOSED (`null (frees [gf0])`) as well as existential-free.  The three
//! restrictions below cover the annotated case and both rejection reasons.
//!
//! Expected strings are the pinned oracle's bytes for the same theory
//! (`tamarin-prover` at the submodule pin, plain no-prove render).

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::pretty_theory::web_restrictions;

const THEORY: &str = r#"theory SafetyCmt
begin

restriction Closed:
  "All x #i. Foo(x) @ #i ==> F"

restriction FreeVar:
  "All #i. Foo(x) @ #i ==> F"

restriction Existential:
  "All x #i. Foo(x) @ #i ==> (Ex #j. Bar(x) @ #j)"

rule A: [ In(x) ] --[ Foo(x), Bar(x) ]-> [ ]

end
"#;

/// Closed and existential-free: annotated.
const EXPECTED_CLOSED: &str = r#"restriction Closed:
  "∀ x #i. (Foo( x ) @ #i) ⇒ (⊥)"
  // safety formula

  /*
  expanded formula:
  "∀ x #i. (Foo( x ) @ #i) ⇒ (⊥)"
  */"#;

/// Guardable but NOT closed (`x` is free): no annotation.
const EXPECTED_FREE_VAR: &str = r#"restriction FreeVar:
  "∀ #i. (Foo( x ) @ #i) ⇒ (⊥)"

  /*
  expanded formula:
  "∀ #i. (Foo( x ) @ #i) ⇒ (⊥)"
  */"#;

/// Closed but carries an existential under the all-quantifier: no annotation.
const EXPECTED_EXISTENTIAL: &str = r#"restriction Existential:
  "∀ x #i. (Foo( x ) @ #i) ⇒ (∃ #j. Bar( x ) @ #j)"

  /*
  expanded formula:
  "∀ x #i. (Foo( x ) @ #i) ⇒ (∃ #j. Bar( x ) @ #j)"
  */"#;

#[test]
fn safety_formula_comment_matches_oracle() {
    let parsed = parse_theory(THEORY, &[]).expect("theory parses");
    let elaborated = elaborate(&parsed).expect("theory elaborates");
    let rendered = web_restrictions(&parsed, &elaborated);
    assert_eq!(rendered.len(), 3, "three restrictions rendered");
    assert_eq!(rendered[0], EXPECTED_CLOSED);
    assert_eq!(rendered[1], EXPECTED_FREE_VAR);
    assert_eq!(rendered[2], EXPECTED_EXISTENTIAL);
}
