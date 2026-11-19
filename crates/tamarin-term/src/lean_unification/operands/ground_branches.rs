//! Replace one ground-sided equation by each complete match and keep every other constraint.
use super::super::{ac_children, ground_component, match_compound_ground, Error, Outcome};
use crate::lterm::LNTerm;
use crate::rewriting::Equal;
use crate::term::Term;
use crate::vterm::{is_ground_vterm, Lit};

pub(in crate::lean_unification) fn split(
    equations: &[Equal<LNTerm>],
) -> Result<Option<impl DoubleEndedIterator<Item = Vec<Equal<LNTerm>>> + '_>, Error> {
    for (pos, eq) in equations.iter().enumerate() {
        let Some((symbol, lhs, rhs)) = ac_children(eq) else {
            continue;
        };
        let (pattern, subject, reverse) = match (is_ground_vterm(&eq.lhs), is_ground_vterm(&eq.rhs))
        {
            (false, true) => (lhs, rhs, false),
            (true, false) => (rhs, lhs, true),
            _ => continue,
        };
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let matches = match ground_component(symbol, pattern, subject)? {
            Outcome::Unsupported if reverse => match_compound_ground(&[Equal {
                lhs: eq.rhs.clone(),
                rhs: eq.lhs.clone(),
            }])?,
            Outcome::Unsupported => match_compound_ground(std::slice::from_ref(eq))?,
            complete => complete,
        };
        if let Outcome::Complete(arms) = matches {
            // A ground match describes ordinary bindings. Putting them first lets the
            // residual worklist propagate them through every other equation in this arm.
            return Ok(Some(arms.into_iter().map(move |arm| {
                arm.into_iter()
                    .map(|(v, rhs)| Equal {
                        lhs: Term::Lit(Lit::Var(v)),
                        rhs,
                    })
                    .chain(
                        equations[..pos]
                            .iter()
                            .chain(&equations[pos + 1..])
                            .cloned(),
                    )
                    .collect()
            })));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::hash;
    use crate::function_symbols::AcSym;
    use crate::lterm::{pub_term, LSort, LVar};
    use crate::term::f_app_ac;

    #[test]
    fn matching_closed_compounds_preserves_multiplicity_and_the_remaining_constraint() {
        let var = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
        let compound = |s| hash(pub_term(s));
        let sum = |factors| f_app_ac(AcSym::Union, factors);
        let ground = sum(vec![compound("a"), compound("b"), compound("b")]);
        let pattern = sum(vec![var("x"), compound("a")]);
        let pending = Equal {
            lhs: sum(vec![var("x"), compound("c")]),
            rhs: sum(vec![var("z"), compound("b")]),
        };
        let binding = Equal {
            lhs: var("x"),
            rhs: sum(vec![compound("b"), compound("b")]),
        };
        for (lhs, rhs) in [(ground.clone(), pattern.clone()), (pattern, ground)] {
            let conjunction = [pending.clone(), Equal { lhs, rhs }];
            let branches = split(&conjunction).unwrap().unwrap().collect::<Vec<_>>();
            assert_eq!(branches, vec![vec![binding.clone(), pending.clone()]]);
        }
    }
}
