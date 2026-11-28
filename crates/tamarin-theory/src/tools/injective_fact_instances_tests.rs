// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;

#[test]
fn monotonic_behaviour_renders_unicode() {
    assert_eq!(MonotonicBehaviour::Constant.to_string(), "=");
    assert_eq!(MonotonicBehaviour::Increasing.to_string(), "≤");
    assert_eq!(MonotonicBehaviour::StrictlyIncreasing.to_string(), "<");
    assert_eq!(MonotonicBehaviour::Unstable.to_string(), ".");
}

/// HS `injectiveFactInstances` (InjectiveFactInstances.hs) over the rules
/// of a theory: a linear protocol fact is injective when every rule that
/// has it in both premises and conclusions keeps its first term, with a
/// behaviour per pair-leaf of every other position.  Each row is `(rules,
/// forced tags, instances)`, an instance written `Tag/arity` followed by
/// one `[..]` per non-first position.
#[test]
fn injective_instances_table() {
    let rows: &[(&str, &[(&'static str, usize)], &[&str])] = &[
        ("", &[], &[]),
        (
            "rule Start: [Fr(~x)] --> [A(~x)]\n\
             rule Loop: [A(x)] --> [A(x)]\n\
             rule Stop: [A(x)] --> []",
            &[],
            &["A/1"],
        ),
        // A copied argument is constant.
        (
            "rule Init: [Fr(~id)] --> [S(~id, k)]\n\
             rule Copy: [S(id, k)] --> [S(id, k)]",
            &[],
            &["S/2 [=]"],
        ),
        // A top-level tuple flattens to the right into one behaviour per
        // leaf, not one collapsed behaviour for the whole argument.
        (
            "rule Init: [Fr(~id)] --> [S(~id, <a, b>)]\n\
             rule Copy: [S(id, <a, b>)] --> [S(id, <a, c>)]",
            &[],
            &["S/2 [=.]"],
        ),
        // Produced without a premise of its own tag or a fresh first term.
        ("rule Weird: [] --> [B(y)]", &[], &[]),
        // `duplicateFirstTerms`: two conclusions share the first term, so
        // the whole tag goes.
        ("rule Dup: [A(x)] --> [A(x), A(x)]", &[], &[]),
        // The premise check is per rule: no single rule both consumes and
        // produces `St`.
        (
            "rule Step1: [Fr(~x)] --> [St(~x, k)]\n\
             rule Step2: [St(x, k)] --> []",
            &[],
            &[],
        ),
        // Only linear, non-nullary protocol facts are candidates.
        ("rule R: [!P(x)] --> [!P(x)]", &[], &[]),
        ("rule R: [Z()] --> [Z()]", &[], &[]),
        ("rule R: [Fr(~x), Out(x)] --> [Out(x)]", &[], &[]),
        // HS unions forced and inferred `(tag, behaviours)` pairs, so a
        // forced tag the analysis also infers appears twice; the oracle
        // prints `L_CellLocked/2, L_PureState/2, L_PureState/2`.
        (
            "rule BeginCell: [Fr(~k)] --> [L_PureState(~k, 'v')]\n\
             rule Copy: [L_PureState(~k, x)] --> [L_PureState(~k, x)]",
            &[("L_PureState", 2), ("L_CellLocked", 2)],
            &[
                "L_CellLocked/2 [?] [?]",
                "L_PureState/2 [=]",
                "L_PureState/2 [?] [?]",
            ],
        ),
    ];
    for &(rules, forced, want) in rows {
        let theory = crate::elaborate::elaborate(
            &tamarin_parser::parse_theory(&format!("theory T begin\n{rules}\nend"), &[]).unwrap(),
        )
        .unwrap();
        let forced = forced
            .iter()
            .map(|&(name, arity)| FactTag::Proto(crate::fact::Multiplicity::Linear, name, arity))
            .collect();
        let got: Vec<String> = injective_fact_instances_for_rules(
            theory.rules(),
            &[],
            &theory.signature.reducible_fun_syms_fast,
            &forced,
        )
        .into_iter()
        .map(|(tag, positions)| {
            let FactTag::Proto(_, name, arity) = tag else {
                panic!("{rules}: a non-protocol instance {tag:?}")
            };
            let mut shown = format!("{name}/{arity}");
            for leaves in positions {
                shown.push_str(" [");
                leaves.iter().for_each(|b| shown.push_str(&b.to_string()));
                shown.push(']');
            }
            shown
        })
        .collect();
        assert_eq!(got, want, "{rules}");
    }
}

/// HS `trimmedPairTerms` (Simplify.hs): an instance whose term has fewer
/// pairs than its position's shape cannot be shaped, so it is `Nothing` and
/// `behaviourTerms`'s `mapMaybe` drops it.  A deep enough instance keeps its
/// leaves, the last one unflattened.
#[test]
fn trimmed_pair_terms_drops_an_instance_too_short_for_the_shape() {
    use crate::fact::{Fact, FactTag, Multiplicity};
    use tamarin_term::builtin::{fresh_var, msg_var, pair};
    use MonotonicBehaviour::{Constant, StrictlyIncreasing};

    let s_tag = FactTag::Proto(Multiplicity::Linear, "S", 2);
    let behaviours = vec![vec![Constant, StrictlyIncreasing]];
    let id = fresh_var("id", 0);

    let short = Fact::new(s_tag, vec![id.clone(), msg_var("x", 0)]);
    assert_eq!(trimmed_pair_terms(&short, &behaviours), None);

    let (a, b, c) = (msg_var("a", 0), msg_var("b", 0), msg_var("c", 0));
    let deep = Fact::new(
        s_tag,
        vec![id.clone(), pair(pair(a.clone(), b.clone()), c.clone())],
    );
    assert_eq!(
        trimmed_pair_terms(&deep, &behaviours),
        Some((id, vec![(Constant, pair(a, b)), (StrictlyIncreasing, c)]))
    );
}
