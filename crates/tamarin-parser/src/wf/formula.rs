//! Single-line unicode pretty-printer for trace formulas, calibrated from the
//! oracle (e.g. ks1 lemma L2 -> "∀ x #i #j. (Act( x ) @ #i) ⇒ (x = x)").
//! Wide formulas in the oracle wrap across multiple indented lines; this
//! printer emits a single line and is therefore exact only for formulas that
//! the oracle also keeps on one line (see BEHAVIOR.md gaps).

use crate::ast::*;
use super::pretty::{pp_fact, pp_term};

pub fn pp_formula(f: &Formula) -> String {
    match f {
        Formula::False => "⊥".to_string(),
        Formula::True => "⊤".to_string(),
        Formula::Atom(a) => pp_atom(a),
        Formula::Not(g) => format!("¬({})", pp_formula(g)),
        Formula::And(a, b) => format!("({}) ∧ ({})", pp_formula(a), pp_formula(b)),
        Formula::Or(a, b) => format!("({}) ∨ ({})", pp_formula(a), pp_formula(b)),
        Formula::Implies(a, b) => format!("({}) ⇒ ({})", pp_formula(a), pp_formula(b)),
        Formula::Iff(a, b) => format!("({}) ⇔ ({})", pp_formula(a), pp_formula(b)),
        Formula::Forall(vs, g) => format!("∀ {}. {}", pp_bound_vars(vs), pp_formula(g)),
        Formula::Exists(vs, g) => format!("∃ {}. {}", pp_bound_vars(vs), pp_formula(g)),
    }
}

fn pp_bound_vars(vs: &[VarSpec]) -> String {
    vs.iter()
        .map(super::pretty::pp_var)
        .collect::<Vec<_>>()
        .join(" ")
}

fn pp_atom(a: &Atom) -> String {
    match a {
        Atom::Eq(x, y) => format!("{} = {}", pp_term(x), pp_term(y)),
        Atom::Less(x, y) => format!("{} < {}", pp_term(x), pp_term(y)),
        Atom::LessMset(x, y) => format!("{} ⋖ {}", pp_term(x), pp_term(y)),
        Atom::Subterm(x, y) => format!("{} ⊏ {}", pp_term(x), pp_term(y)),
        Atom::Action(f, t) => format!("{} @ {}", pp_fact(f), pp_term(t)),
        Atom::Last(t) => format!("last({})", pp_term(t)),
        Atom::Pred(f) => pp_fact(f),
    }
}
