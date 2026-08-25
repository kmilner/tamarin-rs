// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193).
//!
//! For every rule carrying `_restrict(φ)` formulas — which the parser keeps in
//! `Rule.embedded_restrictions` (parser `ast.rs`) — each formula is closed
//! against the theory's signature, its predicate atoms are expanded
//! (`liftedExpandFormula`, Theory/Text/Parser.hs:178), and
//! [`crate::restriction::from_rule_restriction`] turns it into the global
//! restriction `Restr_<rule>_<i>` plus the action fact that reaches it.  The
//! restrictions are added before the rule and the actions are appended to it.
//!
//! HS does this DURING parsing, building the `OpenTheory` rule by rule.  The
//! port runs it over the parser-AST theory right after `parse_theory`, so the
//! transformed theory drives wellformedness, elaboration and the renderer
//! alike, and projects the generated values back into that AST.
//!
//! Run it exactly ONCE per parsed theory: `addActions` rebuilds only `rActs`
//! (Theory/Text/Parser.hs:188), so the rule keeps its `_restrict` formulas and
//! a second call would generate a second copy of every restriction.  The
//! production callers are `run.rs`'s per-file pipeline and the web server's
//! `theory_io`.
//!
//! The predicates come from the WHOLE theory, where HS's `liftedExpandFormula`
//! reads `theoryPredicates thy` — the ones parsed so far
//! (Theory/Text/Parser.hs:112-114).  Three corpus theories declare a second
//! `predicates:` block after their `_restrict`s, and none of them calls a late
//! predicate from an early `_restrict`, so the two readings agree on the
//! corpus.

use tamarin_parser::ast as p;
use tamarin_term::maude_sig::MaudeSig;

use crate::elaborate::{lnfact_to_parser, parse_time_signature, ElabError};
use crate::fact::LNFact;
use crate::formula::LNFormula;
use crate::predicate::Predicate;
use crate::pretty_formula::lnformula_to_parser;
use crate::restriction::{from_rule_restriction, Restriction};

/// Run the `_restrict` lifting pass over a parsed theory in place.
pub fn lift_rule_restrictions(thy: &mut p::Theory) -> Result<(), ElabError> {
    let sig = parse_time_signature(thy)?;
    let mut predicates: Vec<Predicate> = Vec::new();
    for item in &thy.items {
        if let p::TheoryItem::Predicates(ps) = item {
            for pd in ps {
                predicates.push(crate::predicate::from_parser(pd, &sig)?);
            }
        }
    }
    let mut new_items: Vec<p::TheoryItem> = Vec::with_capacity(thy.items.len());
    for item in std::mem::take(&mut thy.items) {
        match item {
            p::TheoryItem::Rule(rule) if !rule.embedded_restrictions.is_empty() => {
                let (restrs, new_rule) = lift_one_rule(rule, &predicates, &sig)?;
                // HS adds the generated restrictions to the theory accumulated
                // so far and the rule after them.
                for r in restrs {
                    new_items.push(p::TheoryItem::Restriction(r));
                }
                new_items.push(p::TheoryItem::Rule(new_rule));
            }
            other => new_items.push(other),
        }
    }
    thy.items = new_items;
    Ok(())
}

/// Lift one rule's embedded restrictions, projecting both outputs back into
/// the parser AST: the generated restrictions in `1..n` order and the rule
/// with the `Restr_<rule>_<i>` actions appended.
///
/// Public so the SAPIC translation (`tamarin_sapic::apply`) lifts the rules it
/// synthesises the same way, HS `foldM liftedAddProtoRule`
/// (sapic/src/Sapic.hs:75).
pub fn lift_one_rule(
    mut rule: p::Rule,
    predicates: &[Predicate],
    sig: &MaudeSig,
) -> Result<(Vec<p::Restriction>, p::Rule), ElabError> {
    let mut closed: Vec<LNFormula> = Vec::with_capacity(rule.embedded_restrictions.len());
    for phi in &rule.embedded_restrictions {
        let syn = crate::formula::from_parser(phi, sig)?;
        closed.push(
            crate::predicate::expand_formula(predicates, &syn).map_err(|e| ElabError {
                message: e.to_string(),
            })?,
        );
    }
    let mut restrictions = Vec::with_capacity(closed.len());
    for (restr, action) in rule_restrictions(&rule.name, &closed) {
        restrictions.push(p::Restriction {
            name: restr.name,
            formula: lnformula_to_parser(&restr.formula),
            attributes: Vec::new(),
        });
        rule.actions.push(lnfact_to_parser(&action));
    }
    Ok((restrictions, rule))
}

/// HS `restrictions`/`actions` over `counter = zip [1..]`
/// (Theory/Text/Parser.hs:190-193): one `Restr_<rname>_<i>` restriction and
/// its action fact per formula, numbered from one.
pub fn rule_restrictions(rname: &str, formulas: &[LNFormula]) -> Vec<(Restriction, LNFact)> {
    formulas
        .iter()
        .enumerate()
        .map(|(i, f)| from_rule_restriction(&format!("{rname}_{}", i + 1), f))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lift_inserts_restriction_before_rule() {
        let src = "theory T begin\n\
            functions: true/0, eq/2\n\
            equations: eq(x,x)=x\n\
            predicate: True(x) <=> (x = true())\n\
            rule A:\n  [In(x)] --[ _restrict(True(eq(x,x))) ]-> []\n\
            end";
        let mut thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        lift_rule_restrictions(&mut thy).unwrap();
        let restr_pos = thy
            .items
            .iter()
            .position(|i| matches!(i, p::TheoryItem::Restriction(r) if r.name == "Restr_A_1"))
            .expect("restriction not generated");
        let rule_pos = thy
            .items
            .iter()
            .position(|i| matches!(i, p::TheoryItem::Rule(r) if r.name == "A"))
            .expect("rule missing");
        // HS adds the generated restrictions to the accumulated theory, and it
        // adds the rule after them.  The restriction is therefore immediately
        // before the rule.
        assert_eq!(restr_pos + 1, rule_pos, "restriction must precede rule");
        // The pass appends the rule action and leaves the `_restrict` formula
        // on the rule.
        let p::TheoryItem::Rule(r) = &thy.items[rule_pos] else {
            panic!("item at {rule_pos} is not the rule");
        };
        assert_eq!(r.embedded_restrictions.len(), 1);
        assert_eq!(r.actions.len(), 1);
        assert_eq!(r.actions[0].name, "Restr_A_1");
        // The action carries the original term, without abstraction.
        assert_eq!(r.actions[0].args.len(), 1);
        assert!(
            matches!(&r.actions[0].args[0], p::Term::App(n, args) if n == "eq" && args.len() == 2),
            "action arg must be the original eq(x,x), got {:?}",
            r.actions[0].args[0]
        );
    }
}
