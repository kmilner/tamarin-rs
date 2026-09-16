// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Bounded recursive conversion oracle, independent of the production scheduler.
//! Scope primitives are shared; Boolean meaning is checked separately by truth tables.
use super::*;
pub(super) fn convert_reference(
    polarity: bool,
    f: &crate::formula::LNFormula,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{open_formula_prefix, Connective, ProtoFormula, Quantifier};
    match f {
        ProtoFormula::Tf(b) => Ok(gtf(polarity != *b)),
        ProtoFormula::Atom(a) => {
            if polarity {
                Ok(gnot_atom(a))
            } else {
                Ok(Guarded::Atom(a.clone()))
            }
        }
        ProtoFormula::Not(g) => convert_reference(!polarity, g, fresh),
        ProtoFormula::Conn(Connective::And, a, b) => {
            let sub = vec![
                convert_reference(polarity, a, fresh)?,
                convert_reference(polarity, b, fresh)?,
            ];
            Ok(if polarity { gdisj(sub) } else { gconj(sub) })
        }
        ProtoFormula::Conn(Connective::Or, a, b) => {
            let sub = vec![
                convert_reference(polarity, a, fresh)?,
                convert_reference(polarity, b, fresh)?,
            ];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        ProtoFormula::Conn(Connective::Imp, a, b) => {
            // p ⇒ q is ¬p ∨ q.
            let nag = convert_reference(!polarity, a, fresh)?;
            let cag = convert_reference(polarity, b, fresh)?;
            let sub = vec![nag, cag];
            Ok(if polarity { gconj(sub) } else { gdisj(sub) })
        }
        ProtoFormula::Conn(Connective::Iff, a, b) => {
            let lhs = ProtoFormula::Conn(Connective::Imp, a.clone(), b.clone());
            let rhs = ProtoFormula::Conn(Connective::Imp, b.clone(), a.clone());
            let arms = vec![
                convert_reference(polarity, &lhs, fresh)?,
                convert_reference(polarity, &rhs, fresh)?,
            ];
            Ok(if polarity { gdisj(arms) } else { gconj(arms) })
        }
        // The quantifier decides whether the body must be a top-level
        // implication (`convAll`) or a conjunction (`convEx`); the polarity
        // decides which quantifier the guarded formula carries and which
        // polarity the sub-formulas take (Guarded.hs:499-505).  The whole
        // prefix of like quantifiers is opened at once, each binder drawn
        // fresh and substituted into the body, so the guard check and the
        // diagnostic name the binders HS names.
        ProtoFormula::Qua(qua0, _, _) => {
            let (xs, _, body) = open_formula_prefix(f, fresh);
            let result = match qua0 {
                Quantifier::All => {
                    let out_qua = if polarity {
                        Quantifier::Ex
                    } else {
                        Quantifier::All
                    };
                    convert_all_reference(&xs, &body, polarity, out_qua, fresh)
                }
                Quantifier::Ex => {
                    let out_qua = if polarity {
                        Quantifier::All
                    } else {
                        Quantifier::Ex
                    };
                    convert_ex_reference(&xs, &body, polarity, out_qua, fresh)
                }
            };
            // Both throws of this arm quote `ppFormula f0`, the quantifier
            // sub-formula they were reached through (Guarded.hs:513, :562),
            // and the exception carries that quote out unchanged — so the
            // innermost quantifier is the one named, which the guard below
            // reproduces by setting the field once.
            result.map_err(|mut e| {
                if e.subject_formula.is_none() {
                    e.subject_formula = Some(f.clone());
                }
                e
            })
        }
    }
}
fn convert_ex_reference(
    xs: &[LVar],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quantifier,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    let (atoms, others) = split_conj_actions_eqs(body.clone());
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut converted = Vec::with_capacity(others.len());
    for f in others {
        converted.push(convert_reference(polarity, &f, fresh)?);
    }
    let body_guarded = if polarity {
        gdisj(converted)
    } else {
        gconj(converted)
    };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}
fn convert_all_reference(
    xs: &[LVar],
    body: &crate::formula::LNFormula,
    polarity: bool,
    out_qua: Quantifier,
    fresh: &mut tamarin_utils::fresh::PreciseFreshState,
) -> Result<Guarded, GuardError> {
    use crate::formula::{Connective, ProtoFormula};
    let ProtoFormula::Conn(Connective::Imp, ante, succ) = body else {
        return Err(err("universal quantifier without toplevel implication"));
    };
    let (atoms, ante_others) = split_conj_actions_eqs((**ante).clone());
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded, xs));
    }
    let mut sub = Vec::with_capacity(ante_others.len() + 1);
    for f in ante_others {
        sub.push(convert_reference(!polarity, &f, fresh)?);
    }
    sub.push(convert_reference(polarity, succ, fresh)?);
    let body_guarded = if polarity { gconj(sub) } else { gdisj(sub) };
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
}
