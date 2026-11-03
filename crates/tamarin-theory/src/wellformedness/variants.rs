// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Validate explicit families against computed variants, from
//! `Theory/Tools/Wellformedness.hs` and `Theory/Model/Rule.hs`.

use std::collections::{BTreeMap, BTreeSet};
use tamarin_term::function_symbols::{AcSym, FunSym};
use tamarin_term::lterm::LNTerm;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_term::term::Term;
#[cfg(test)]
use tamarin_term::{lterm::LVar, subst::Subst, vterm::var_term};

use super::{WfError, WfReport};
use crate::fact::LNFact;
use crate::pretty_hpj::{above_blank, fsep, numbered_prime, punctuate, Doc};
use crate::rule::ProtoRuleE;
use crate::theory::{closed_rules_ac, OpenProtoRule, Theory};
use crate::tools::rule_variants::{
    open_rule_has_no_variants, prepare_open_rule_variant, VariantsError,
};

pub fn fatal_wf_errors(report: &[WfError]) -> WfReport {
    report
        .iter()
        .filter(|e| {
            matches!(
                e.topic.as_str(),
                "Variants"
                    | "Unsupported actions added to variants"
                    | "Unsupported multiplication outside exponents"
            )
        })
        .cloned()
        .collect()
}

/// Ordinary warnings keep their policy, but unsupported families cannot be proved.
pub fn explicit_variants_report(
    thy: &Theory,
    maude: &MaudeHandle,
) -> Result<WfReport, VariantsError> {
    let mut report = Vec::new();
    for parent in thy.rules().filter(|r| !r.rule_ac.is_empty()) {
        let mut computed = computed_variants(parent, maude)?;
        // Partial evaluation reopens a compiled identity family under its
        // original name. Recomputing can canonicalize variable indices and
        // thereby give that sole variant a suffix. The identical E/AC pair
        // may keep its name, but must still pass the full semantic alignment.
        if let ([member], [computed], crate::rule::ProtoRuleName::Stand(name)) = (
            parent.rule_ac.as_slice(),
            computed.as_mut_slice(),
            parent.rule_e().info.name,
        ) {
            let generated = crate::rule::ProtoRuleName::Stand(tamarin_term::intern::intern_str(
                &format!("{name}___VARIANT_1"),
            ));
            if member == parent.rule_e() && computed.info.name == generated {
                computed.info.name = member.info.name;
            } else if member != parent.rule_e() && computed.info.name == parent.rule_e().info.name {
                computed.info.name = generated;
            }
        }
        let by_name: BTreeMap<_, _> = computed.iter().map(|r| (r.info.name, r)).collect();
        let mut alignments = Vec::new();
        for member in &parent.rule_ac {
            alignments.push(match by_name.get(&member.info.name) {
                Some(computed) => align_rule(maude, member, computed)?,
                None => None,
            });
        }
        let supplied: BTreeSet<_> = parent.rule_ac.iter().map(|r| r.info.name).collect();
        if alignments.iter().any(Option::is_none) || supplied != by_name.keys().copied().collect() {
            let heading = format!("Rule `{}' cannot confirm manual variants:", parent.name());
            let supplied = numbered_prime(parent.rule_ac.iter().map(rule_doc).collect());
            let recomputed = numbered_prime(computed.iter().map(rule_doc).collect());
            let body = above_blank(
                above_blank(
                    Doc::text(heading).above_g(supplied.nest(2)),
                    Doc::text("Recomputed variants: "),
                ),
                recomputed.nest(2),
            );
            report.push(WfError::underlined_block("Variants", body));
        }
        for (member, inherited) in parent.rule_ac.iter().zip(alignments) {
            if let Some(inherited) = inherited {
                report.extend(added_action_report(maude, member, &inherited));
            }
        }
    }
    Ok(report)
}

fn rule_doc(rule: &ProtoRuleE) -> Doc {
    let open = OpenProtoRule::new(rule.clone());
    crate::rule::pretty_proto_rule_ac(&closed_rules_ac(&open)[0])
}

fn computed_variants(
    parent: &OpenProtoRule,
    maude: &MaudeHandle,
) -> Result<Vec<ProtoRuleE>, VariantsError> {
    let mut computed = parent.clone();
    computed.rule_ac.clear();
    prepare_open_rule_variant(&mut computed, maude)?;
    // Public proving accepts freshly elaborated theories too: absent cached
    // variants mean "unprepared" until the computation above has run.
    if open_rule_has_no_variants(maude, &computed) {
        return Ok(vec![]);
    }
    Ok(closed_rules_ac(&computed)
        .iter()
        .flat_map(|ac| crate::tools::rule_variants::unfold_closed_rule(&computed, ac))
        .map(|o| o.rule)
        .collect())
}

#[path = "rule_alignment.rs"]
mod alignment;

fn align_rule(
    _maude: &MaudeHandle,
    member: &ProtoRuleE,
    computed: &ProtoRuleE,
) -> Result<Option<Vec<LNFact>>, VariantsError> {
    Ok(alignment::align_rule(member, computed))
}

fn added_action_report(maude: &MaudeHandle, member: &ProtoRuleE, inherited: &[LNFact]) -> WfReport {
    let mut added = member.actions.clone();
    for fact in inherited {
        if let Some(i) = added.iter().position(|f| f == fact) {
            added.remove(i);
        }
    }
    fn subterms(t: &LNTerm, out: &mut BTreeSet<LNTerm>) {
        out.insert(t.clone());
        if let Term::App(_, args) = t {
            for a in args.iter() {
                subterms(a, out);
            }
        }
    }
    let mut covered = BTreeSet::new();
    for t in member
        .premises
        .iter()
        .chain(&member.conclusions)
        .chain(inherited)
        .flat_map(|f| f.terms.iter())
    {
        subterms(t, &mut covered);
    }
    fn risky(
        t: &LNTerm,
        stable: &BTreeSet<FunSym>,
        covered: &BTreeSet<LNTerm>,
        out: &mut Vec<LNTerm>,
    ) {
        if let Term::App(sym, args) = t {
            if stable.contains(sym) && !matches!(sym, FunSym::Ac(AcSym::Mult | AcSym::Xor)) {
                for a in args.iter() {
                    risky(a, stable, covered, out);
                }
            } else if !covered.contains(t) {
                out.push(t.clone());
            }
        }
    }
    let mut uncovered = vec![];
    for term in added.iter().flat_map(|f| f.terms.iter()) {
        risky(
            term,
            &maude.maude_sig().irreducible_fun_syms,
            &covered,
            &mut uncovered,
        );
    }
    if uncovered.is_empty() {
        return vec![];
    }
    let terms = fsep(punctuate(
        Doc::text(","),
        uncovered
            .iter()
            .map(tamarin_term::pretty::pretty_nterm)
            .collect(),
    ));
    vec![WfError::underlined_block("Unsupported actions added to variants",
        Doc::text(format!("Rule {} adds actions whose instances can leave normal form:", crate::rule::pretty_proto_rule_name(&member.info.name).render()))
            .above_g(terms.nest(2))
            .above_g(Doc::text("Such subterms must already occur in the member's premises, conclusions or computed actions."))
            .above_g(Doc::text("Annotate the original rule instead, so that variant computation covers them.")))]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{proto_fact, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::lterm::LSort;

    fn manual_family() -> Theory {
        let parsed = tamarin_parser::parse_theory(
            include_str!("../../tests/fixtures/manual_variants.spthy"),
            &[],
        )
        .unwrap();
        crate::elaborate::elaborate(&parsed).unwrap()
    }

    #[test]
    fn public_wellformedness_requires_maude_for_every_explicit_family() {
        let mut theory = manual_family();
        for member_count in [2, 1] {
            for item in &mut theory.items {
                if let crate::theory::TheoryItem::Rule(rule) = item {
                    rule.rule_ac.truncate(member_count);
                }
            }
            assert!(matches!(
                crate::wellformedness::check_wellformedness(&theory, None),
                Err(VariantsError::MissingMaudeForExplicitVariants)
            ));
        }
    }

    #[test]
    fn public_wellformedness_validates_explicit_families_with_maude() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let mut theory = manual_family();
        let maude = MaudeHandle::start(&path, theory.signature.clone()).unwrap();
        crate::tools::rule_variants::populate_rule_variants(&mut theory, &maude, None).unwrap();
        let report = crate::wellformedness::check_wellformedness(&theory, Some(&maude)).unwrap();
        assert!(fatal_wf_errors(&report).is_empty(), "{report:?}");
        for item in &mut theory.items {
            if let crate::theory::TheoryItem::Rule(rule) = item {
                rule.rule_ac.truncate(1);
            }
        }
        let report = crate::wellformedness::check_wellformedness(&theory, Some(&maude)).unwrap();
        assert!(report.iter().any(|e| e.topic == "Variants"), "{report:?}");
    }

    #[test]
    fn identity_families_still_require_complete_semantic_alignment() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        for rule in [
            // One computed variant, but normalization changes the body.
            "rule R: [] --[A(sdec(senc('a','k'),'k'))]-> []",
            // The identity member alone omits the reducing variant.
            "rule R: [In(x), In(k)] --[A(sdec(x,k))]-> []",
        ] {
            let source = format!("theory Identity begin builtins: symmetric-encryption {rule} end");
            let parsed = tamarin_parser::parse_theory(&source, &[]).unwrap();
            let mut theory = crate::elaborate::elaborate(&parsed).unwrap();
            for item in &mut theory.items {
                if let crate::theory::TheoryItem::Rule(rule) = item {
                    rule.rule_ac = vec![rule.rule.clone()];
                }
            }
            let maude = MaudeHandle::start(&path, theory.signature.clone()).unwrap();
            let report = explicit_variants_report(&theory, &maude).unwrap();
            assert!(
                report.iter().any(|e| e.topic == "Variants"),
                "{source}: {report:?}"
            );
        }
    }

    #[test]
    fn identity_family_must_match_original_e_rule_not_a_restricted_compiled_rule() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let parsed = tamarin_parser::parse_theory(
            "theory Original begin rule R: [In(x)] --[A(x)]-> [] end",
            &[],
        )
        .unwrap();
        let mut theory = crate::elaborate::elaborate(&parsed).unwrap();
        let subst = Subst::from_list([(
            LVar::new("x", LSort::Msg, 0),
            tamarin_term::lterm::pub_term("a"),
        )]);
        for item in &mut theory.items {
            if let crate::theory::TheoryItem::Rule(rule) = item {
                rule.rule_e = Some(Box::new(rule.rule.clone()));
                rule.rule = crate::rule::apply_subst_rule(&subst, &rule.rule);
                rule.rule_ac = vec![rule.rule.clone()];
            }
        }
        let maude = MaudeHandle::start(&path, theory.signature.clone()).unwrap();
        let report = explicit_variants_report(&theory, &maude).unwrap();
        assert!(report.iter().any(|e| e.topic == "Variants"), "{report:?}");
    }

    #[test]
    fn alignment_requires_a_bijection_and_ordered_inherited_actions() {
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let maude = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let x = var_term(LVar::new("x", LSort::Msg, 0));
        let y = var_term(LVar::new("y", LSort::Msg, 0));
        let fact = |name, terms| proto_fact(Multiplicity::Linear, name, terms);
        let expected = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![fact("P", vec![x.clone(), y.clone()])],
            vec![],
            vec![fact("A", vec![x.clone()]), fact("B", vec![y.clone()])],
        );
        let ren = Subst::from_list([
            (
                LVar::new("x", LSort::Msg, 0),
                var_term(LVar::new("z", LSort::Msg, 8)),
            ),
            (
                LVar::new("y", LSort::Msg, 0),
                var_term(LVar::new("w", LSort::Msg, 9)),
            ),
        ]);
        let mut member = crate::rule::apply_subst_rule(&ren, &expected);
        member.actions.insert(1, fact("Extra", vec![]));
        assert!(align_rule(&maude, &member, &expected).unwrap().is_some());
        member.actions.reverse();
        assert!(align_rule(&maude, &member, &expected).unwrap().is_none());
        let collapse = Subst::from_list([(LVar::new("y", LSort::Msg, 0), x)]);
        let collapsed = crate::rule::apply_subst_rule(&collapse, &expected);
        assert!(align_rule(&maude, &collapsed, &expected).unwrap().is_none());
    }
}
