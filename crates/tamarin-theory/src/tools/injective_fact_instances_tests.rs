use super::*;

#[test]
fn monotonic_behaviour_renders_unicode() {
    assert_eq!(MonotonicBehaviour::Constant.to_string(), "=");
    assert_eq!(MonotonicBehaviour::Increasing.to_string(), "≤");
    assert_eq!(MonotonicBehaviour::StrictlyIncreasing.to_string(), "<");
    assert_eq!(MonotonicBehaviour::Unstable.to_string(), ".");
}

#[test]
fn empty_rules_no_injective_facts() {
    let r: Vec<&ProtoRuleE> = Vec::new();
    assert!(simple_injective_fact_instances(&r, &Default::default()).is_empty());
}

/// Loop-style rules: `Start: Fr(x) → A(x); Loop: A(x) → A(x); Stop: A(x) → []`.
/// `A` should be detected as injective because every rule producing it
/// either consumes `A(x)` with same first arg or has `Fr(x)` premise.
#[test]
fn loop_pattern_detects_a_as_injective() {
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let a_tag = FactTag::Proto(Multiplicity::Linear, "A", 1);
    let a_fact = Fact::new(a_tag, vec![msg_var("x", 0)]);
    let start: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Start"),
        vec![fresh_fact(msg_var("x", 0))],
        vec![a_fact.clone()],
        vec![],
    );
    let loop_r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Loop"),
        vec![a_fact.clone()],
        vec![a_fact.clone()],
        vec![],
    );
    let stop: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Stop"),
        vec![a_fact.clone()],
        vec![],
        vec![],
    );
    let rules = [start, loop_r, stop];
    let rules: Vec<&ProtoRuleE> = rules.iter().collect();
    let inj = simple_injective_fact_instances(&rules, &Default::default());
    assert_eq!(inj.len(), 1);
    assert_eq!(inj[0].0, a_tag);
}

/// `S(~id, k)` with copy rule that preserves `k` ⇒ position 1
/// behaviour should be `Constant`.
#[test]
fn copy_preserving_arg_marks_position_constant() {
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let s_tag = FactTag::Proto(Multiplicity::Linear, "S", 2);
    let s_fact = Fact::new(s_tag, vec![msg_var("id", 0), msg_var("k", 0)]);
    let init: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Init"),
        vec![fresh_fact(msg_var("id", 0))],
        vec![s_fact.clone()],
        vec![],
    );
    let copy: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Copy"),
        vec![s_fact.clone()],
        vec![s_fact.clone()],
        vec![],
    );
    let rules = [init, copy];
    let rules: Vec<&ProtoRuleE> = rules.iter().collect();
    let inj = simple_injective_fact_instances(&rules, &Default::default());
    assert_eq!(inj.len(), 1);
    assert_eq!(inj[0].0, s_tag);
    // One non-first position; its single (non-tuple) pair-leaf is Constant.
    assert_eq!(inj[0].1.len(), 1);
    assert_eq!(inj[0].1[0], vec![MonotonicBehaviour::Constant]);
}

/// Non-injective: a rule produces `B(t)` but doesn't consume `B`
/// or have a Fresh-premise binding `t`.
#[test]
fn arbitrary_production_not_injective() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let b_tag = FactTag::Proto(Multiplicity::Linear, "B", 1);
    let b_fact = Fact::new(b_tag, vec![msg_var("y", 0)]);
    // No Fresh premise binding `y`, no `B` premise.
    let weird: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Weird"),
        vec![],
        vec![b_fact.clone()],
        vec![],
    );
    assert!(simple_injective_fact_instances(&[&weird], &Default::default()).is_empty());
}

/// Pair-flattening (HS `getPairTerms` / `getShape` / `shapeTerm`):
/// `S(~id, <a, b>) → S(~id, <a, c>)`.  The non-first position is a
/// top-level tuple; it flattens to the right into two pair-leaves
/// (2.1 = `a`/`a`, 2.2 = `b`/`c`).  So the behaviour is the
/// list-of-lists `[[Constant, Unstable]]` (`[[=, .]]`) — NOT a single
/// collapsed `Unstable` over the whole `<a, b>`/`<a, c>` argument.
#[test]
fn pair_argument_is_flattened_to_the_right() {
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::{msg_var, pair};

    let s_tag = FactTag::Proto(Multiplicity::Linear, "S", 2);
    let prem_fact = Fact::new(
        s_tag,
        vec![msg_var("id", 0), pair(msg_var("a", 0), msg_var("b", 0))],
    );
    let conc_fact = Fact::new(
        s_tag,
        vec![msg_var("id", 0), pair(msg_var("a", 0), msg_var("c", 0))],
    );
    let init: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Init"),
        vec![fresh_fact(msg_var("id", 0))],
        vec![Fact::new(
            s_tag,
            vec![msg_var("id", 0), pair(msg_var("a", 0), msg_var("b", 0))],
        )],
        vec![],
    );
    let copy: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Copy"),
        vec![prem_fact.clone()],
        vec![conc_fact.clone()],
        vec![],
    );
    let inj = simple_injective_fact_instances(&[&init, &copy], &Default::default());
    assert_eq!(inj.len(), 1);
    assert_eq!(inj[0].0, s_tag);
    // One non-first position whose tuple flattens into two leaves.
    assert_eq!(
        inj[0].1,
        vec![vec![
            MonotonicBehaviour::Constant,
            MonotonicBehaviour::Unstable
        ]]
    );
}

/// `duplicateFirstTerms` (HS InjectiveFactInstances.hs:181-182,188):
/// a rule with two same-tag conclusions sharing the same first term
/// cannot be injective — `getMaybeEqMonConclusion` returns `Nothing`
/// for the duplicated conclusion, so `combineAll` drops the WHOLE tag.
/// `[A(x)] → A(x), A(x)`: `A` must NOT be injective.
#[test]
fn duplicate_first_terms_drops_tag() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let a_tag = FactTag::Proto(Multiplicity::Linear, "A", 1);
    let a_fact = Fact::new(a_tag, vec![msg_var("x", 0)]);
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Dup"),
        vec![a_fact.clone()],
        vec![a_fact.clone(), a_fact.clone()],
        vec![],
    );
    let inj = simple_injective_fact_instances(&[&r], &Default::default());
    assert!(
        inj.is_empty(),
        "two conclusions A(x), A(x) share the first term x → A cannot be \
             injective (HS duplicateFirstTerms drops the whole tag)"
    );
}

// =========================================================================
// Haskell-faithfulness invariants — pinning the candidate filter
// (#206: `Artificial::Fin_unique` regression).
//
// Mirrors Haskell `simpleInjectiveFactInstances`
// (InjectiveFactInstances.hs:121-132):
//
//   guard $ (factTagMultiplicity tag == Linear)
//        && (tag `elem` (factTag <$> rPrems ru))
//
// The `tag elem prems` check is PER-RULE, not across all rules: a
// broader filter (any rule that produces the tag) would count facts
// as injective when one rule creates them and another consumes them,
// even though no SINGLE rule has both prems AND concs — adding
// spurious less-atoms and breaking Fin_unique's case_2.
// =========================================================================

/// Fact created in Rule1 and consumed in Rule2 (no single rule has
/// it in both prems and concs) — must NOT be injective.
///
/// This is the Artificial.spthy::Fin_unique shape:
///   Step1: Fr(x) → St(x, k)
///   Step2: St(x, k) → []
/// No round-trip → St is NOT injective in Haskell.
/// Without per-rule filter, we'd mark it injective and add a
/// spurious less-atom in case_2.
#[test]
fn cross_rule_create_consume_is_not_injective() {
    use crate::fact::{fresh_fact, Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let st_tag = FactTag::Proto(Multiplicity::Linear, "St", 2);
    let st_fact = Fact::new(st_tag, vec![msg_var("x", 0), msg_var("k", 0)]);
    // Step1 creates St but doesn't consume it.
    let step1: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Step1"),
        vec![fresh_fact(msg_var("x", 0))],
        vec![st_fact.clone()],
        vec![],
    );
    // Step2 consumes St but doesn't produce it.
    let step2: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("Step2"),
        vec![st_fact.clone()],
        vec![],
        vec![],
    );

    let inj = simple_injective_fact_instances(&[&step1, &step2], &Default::default());
    assert!(
        inj.is_empty(),
        "St is created in Step1, consumed in Step2, but NO single rule \
             has St in both prems and concs → must NOT be marked injective. \
             Haskell `simpleInjectiveFactInstances` checks the per-rule \
             `tag elem rPrems ru` condition.  Otherwise spurious less-atoms \
             break Artificial::Fin_unique case_2.  (Memory: \
             project_rust_injective_fact_candidate_filter.md)"
    );
}

/// Persistent facts (multiplicity = Persistent) are never marked
/// injective.  Mirrors Haskell's
/// `guard (factTagMultiplicity tag == Linear)`.
#[test]
fn persistent_facts_are_not_injective() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    let p_tag = FactTag::Proto(Multiplicity::Persistent, "P", 1);
    let p_fact = Fact::new(p_tag, vec![msg_var("x", 0)]);
    // Even with both prems + concs (which would normally pass the
    // candidate filter), Persistent disqualifies.
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("R"),
        vec![p_fact.clone()],
        vec![p_fact.clone()],
        vec![],
    );
    let inj = simple_injective_fact_instances(&[&r], &Default::default());
    assert!(
        inj.is_empty(),
        "Persistent facts are never injective (Haskell: \
             `factTagMultiplicity tag == Linear` guard)"
    );
}

/// Arity-0 facts (no args) cannot have monotonic behaviour and
/// must be excluded.  Per Haskell `behaviourLen = max 0 (arity-1)`
/// is 0; combined with the candidate filter check, arity-0 facts
/// get filtered.  Our impl drops them via the candidate loop's
/// `if conc.terms.is_empty()` guard (HS `guard (not (null (factTerms conc)))`).
#[test]
fn arity_zero_facts_are_not_injective() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use crate::rule::{ProtoRuleEInfo, Rule};

    let z_tag = FactTag::Proto(Multiplicity::Linear, "Z", 0);
    let z_fact = Fact::new(z_tag, vec![]);
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("R"),
        vec![z_fact.clone()],
        vec![z_fact.clone()],
        vec![],
    );
    let inj = simple_injective_fact_instances(&[&r], &Default::default());
    assert!(
        inj.is_empty(),
        "Arity-0 facts have no behaviour to track → never injective"
    );
}

/// Built-in facts (Out, Ku, Kd, Fresh, etc.) are never injective.
/// Only Proto-tagged facts get the analysis.
#[test]
fn builtin_facts_are_not_injective() {
    use crate::fact::{fresh_fact, Fact, FactTag};
    use crate::rule::{ProtoRuleEInfo, Rule};
    use tamarin_term::builtin::msg_var;

    // Two Out facts — never injective regardless of pattern.
    let out_fact = Fact::new(FactTag::Out, vec![msg_var("x", 0)]);
    let r: ProtoRuleE = Rule::new(
        ProtoRuleEInfo::standard("R"),
        vec![fresh_fact(msg_var("x", 0)), out_fact.clone()],
        vec![out_fact.clone()],
        vec![],
    );
    let inj = simple_injective_fact_instances(&[&r], &Default::default());
    // Out should NOT appear (only Proto tags are candidates).
    assert!(
        inj.iter()
            .all(|(t, _)| matches!(t, FactTag::Proto(_, _, _))),
        "Only Proto facts are injective candidates"
    );
    assert!(
        !inj.iter().any(|(t, _)| matches!(t, FactTag::Out)),
        "Out is never injective"
    );
}
