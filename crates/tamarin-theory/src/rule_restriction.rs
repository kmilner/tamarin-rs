// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of HS `liftedAddProtoRule` (Theory/Text/Parser.hs).
//!
//! A rule carries its `_restrict(φ)` formulas in its own info
//! (`_preRestriction`, Theory/Model/Rule.hs).  Each formula has its
//! predicate atoms expanded (`liftedExpandFormula`,
//! Theory/Text/Parser.hs) and [`crate::restriction::from_rule_restriction`]
//! turns it into the global restriction `Restr_<rule>_<i>` plus the action
//! fact that reaches it.  The restrictions go into the theory before the rule
//! and the actions are appended to the rule (Theory/Text/Parser.hs).
//!
//! HS runs this as it adds each parsed rule to the theory
//! (Theory/Text/Parser.hs), so the predicates are the ones declared
//! before the rule (`theoryPredicates thy`, Theory/Text/Parser.hs) and
//! the rule keeps its `_restrict` formulas, since `addActions` rebuilds `rActs`
//! alone (Theory/Text/Parser.hs).  `elaborate::lifted_add_proto_rule` calls
//! this for each parsed rule and each rule the SAPIC translation generates.

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
        // reserved name (Theory/Text/Parser.hs); the parser rejects the
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
/// (Theory/Text/Parser.hs): one `Restr_<rname>_<i>` restriction and
/// its action fact per formula, numbered from one.
pub fn rule_restrictions(rname: &str, formulas: &[LNFormula]) -> Vec<(Restriction, LNFact)> {
    formulas
        .iter()
        .enumerate()
        .map(|(i, f)| from_rule_restriction(&format!("{rname}_{}", i + 1), f))
        .collect()
}
