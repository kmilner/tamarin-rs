// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of HS `liftedAddProtoRule` (Theory/Text/Parser.hs:175-193).
//!
//! A rule carries its `_restrict(φ)` formulas in its own info
//! (`_preRestriction`, Theory/Model/Rule.hs:424).  Each formula has its
//! predicate atoms expanded (`liftedExpandFormula`,
//! Theory/Text/Parser.hs:178) and [`crate::restriction::from_rule_restriction`]
//! turns it into the global restriction `Restr_<rule>_<i>` plus the action
//! fact that reaches it.  The restrictions go into the theory before the rule
//! and the actions are appended to the rule (Theory/Text/Parser.hs:179-180).
//!
//! HS runs this as it adds each parsed rule to the theory
//! (Theory/Text/Parser.hs:283-284), so the predicates are the ones declared
//! before the rule (`theoryPredicates thy`, Theory/Text/Parser.hs:112-114) and
//! the rule keeps its `_restrict` formulas, since `addActions` rebuilds `rActs`
//! alone (Theory/Text/Parser.hs:188).  `elaborate_items` is where the port
//! builds the theory rule by rule and calls this; `tamarin_sapic::apply` runs
//! the same lift over the rules the SAPIC translation generates.

use crate::elaborate::ElabError;
use crate::fact::LNFact;
use crate::formula::LNFormula;
use crate::predicate::Predicate;
use crate::restriction::{from_rule_restriction, Restriction};
use crate::rule::{ProtoRuleE, ProtoRuleName};

/// Lift one rule's `_restrict` formulas: expand their predicate atoms against
/// `predicates`, append the action fact of each to `rule` and hand back the
/// restrictions they generate, in `1..n` order.
pub(crate) fn lift_rule_restrictions(
    rule: &mut ProtoRuleE,
    predicates: &[Predicate],
) -> Result<Vec<Restriction>, ElabError> {
    let rname = match rule.info.name {
        ProtoRuleName::Stand(n) => n,
        // HS `liftedAddProtoRule` throws `TryingToAddFreshRule` for the
        // reserved name (Theory/Text/Parser.hs:182); the parser rejects the
        // reserved rule names, so a parsed rule never reaches this arm.
        ProtoRuleName::Fresh => "Fresh",
    };
    let mut closed: Vec<LNFormula> = Vec::with_capacity(rule.info.restrictions.len());
    for phi in &rule.info.restrictions {
        closed.push(
            crate::predicate::expand_formula(predicates, phi).map_err(|e| ElabError {
                message: e.to_string(),
            })?,
        );
    }
    let mut restrictions = Vec::with_capacity(closed.len());
    for (restr, action) in rule_restrictions(rname, &closed) {
        restrictions.push(restr);
        rule.actions.push(action);
    }
    Ok(restrictions)
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
    use crate::theory::TheoryItem;

    #[test]
    fn lift_inserts_restriction_before_rule() {
        let src = "theory T begin\n\
            functions: true/0, eq/2\n\
            equations: eq(x,x)=x\n\
            predicate: True(x) <=> (x = true())\n\
            rule A:\n  [In(x)] --[ _restrict(True(eq(x,x))) ]-> []\n\
            end";
        let parsed = tamarin_parser::parse_theory(src, &[]).unwrap();
        let thy = crate::elaborate::elaborate(&parsed).unwrap();
        let restr_pos = thy
            .items
            .iter()
            .position(|i| matches!(i, TheoryItem::Restriction(r) if r.name == "Restr_A_1"))
            .expect("restriction not generated");
        let rule_pos = thy
            .items
            .iter()
            .position(|i| matches!(i, TheoryItem::Rule(r) if r.name() == "A"))
            .expect("rule missing");
        // HS adds the generated restrictions to the accumulated theory, and it
        // adds the rule after them.  The restriction is therefore immediately
        // before the rule.
        assert_eq!(restr_pos + 1, rule_pos, "restriction must precede rule");
        // The lift appends the rule action and leaves the `_restrict` formula
        // on the rule.
        let TheoryItem::Rule(r) = &thy.items[rule_pos] else {
            panic!("item at {rule_pos} is not the rule");
        };
        assert_eq!(r.rule.info.restrictions.len(), 1);
        assert_eq!(r.rule.actions.len(), 1);
        assert_eq!(
            crate::fact::fact_tag_name(&r.rule.actions[0].tag),
            "Restr_A_1"
        );
        // The action carries the original term, without abstraction.
        assert_eq!(r.rule.actions[0].terms.len(), 1);
        let t = &r.rule.actions[0].terms[0];
        let eq_of_two = match t {
            tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(sym),
                args,
            ) => sym.name == b"eq" && args.len() == 2,
            _ => false,
        };
        assert!(
            eq_of_two,
            "action arg must be the original eq(x,x), got {t:?}"
        );
    }
}
