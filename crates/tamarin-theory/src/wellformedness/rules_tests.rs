// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use crate::atom::ProtoAtom;
use crate::formula::{BLNTerm, Quantifier};
use crate::guarded::Guarded;
use tamarin_term::lterm::BVar;
use tamarin_term::term::Term;
use tamarin_term::vterm::{var_term, Lit as VLit};

#[test]
fn bound_terms_open_outer_variables_below_nested_guards() {
    fn bound(index: u64) -> BLNTerm {
        Term::Lit(VLit::Var(BVar::Bound(index)))
    }

    fn guarded(vars: &[(&str, LSort)], body: Guarded) -> Guarded {
        Guarded::GGuarded {
            qua: Quantifier::All,
            vars: vars
                .iter()
                .map(|(name, sort)| ((*name).to_owned(), *sort))
                .collect::<Vec<_>>()
                .into(),
            guards: Vec::new().into(),
            body: std::sync::Arc::new(body),
        }
    }

    // Below the two inner binders, Bound(3) names outer `t3` and Bound(1)
    // names inner `t1`.  The cumulative assignment must shift outer indices
    // when each nested block is entered.
    let formula = guarded(
        &[("x", LSort::Msg), ("y", LSort::Msg), ("t3", LSort::Node)],
        guarded(
            &[("t2", LSort::Node)],
            guarded(
                &[("t1", LSort::Node), ("yp", LSort::Msg)],
                Guarded::Atom(ProtoAtom::Less(bound(3), bound(1))),
            ),
        ),
    );
    let mut terms = Vec::new();
    for_each_bound_guarded_term(&formula, &[], &mut |term| terms.push(term.clone()));
    assert_eq!(
        terms,
        vec![
            var_term(LVar::new("t3", LSort::Node, 0)),
            var_term(LVar::new("t1", LSort::Node, 0)),
        ]
    );
}
