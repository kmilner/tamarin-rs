// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.InjectiveFactInstances`.
//!
//! Computes an under-approximation of the set of fact tags whose
//! instances always occur uniquely in a state — protocols often rely
//! on this for security arguments (e.g. session-state facts).
//!
//! The full Haskell algorithm:
//! 1. For each fact tag, collect every protocol rule that produces or
//!    consumes it.
//! 2. Trace its first argument through the rule graph, tracking
//!    monotonic behaviour at each position (Constant / Increasing /
//!    Decreasing / StrictlyIncreasing / StrictlyDecreasing /
//!    Unstable / Unspecified).
//! 3. A tag is injective if every rule using it satisfies the
//!    Fr-fact-or-single-premise condition.
//!
//! `simple_injective_fact_instances` implements this under-approximation
//! and is used in production: its result is stored in
//! `ProofContext.injective_fact_insts` (see `context.rs`) and consumed by
//! the solver (`simplify.rs`, `contradictions.rs`) and by
//! `pretty_theory.rs` (the looping-facts comment).
//!
//! The behaviour list for a tag is a list-of-lists
//! (`Vec<Vec<MonotonicBehaviour>>`, HS `[[MonotonicBehaviour]]`): the
//! outer list ranges over the non-first argument positions, and the inner
//! list over the right-flattened pair-leaves of that position
//! (`getPairTerms` / `getShape` / `shapeTerm` / `trimmedPairTerms`).  This
//! mirrors `Theory.Tools.InjectiveFactInstances.simpleInjectiveFactInstances`
//! (InjectiveFactInstances.hs).

use crate::fact::FactTag;
use crate::rule::ProtoRuleE;

/// HS `S.Set (FactTag, [[MonotonicBehaviour]])`, the `_pcInjectiveFactInsts`
/// of a proof context (System.hs).  A tag can occur with several behaviours.
pub type InjectiveFactInsts = std::collections::BTreeSet<(FactTag, Vec<Vec<MonotonicBehaviour>>)>;

/// `injFactInstances` of HS `closeRuleCache` (CloseRule.hs):
///
/// ```haskell
/// forcedInjFacts' = S.map (\x -> (x, replicate (factTagArity x) [Unspecified])) forcedInjFacts
/// injFactInstances = forcedInjFacts' `S.union`
///     simpleInjectiveFactInstances reducibles (L.get cprRuleE <$> protoRules)
/// ```
///
/// The union is of `(tag, behaviours)` pairs, so a forced tag that is also
/// inferred keeps both entries.  HS analyzes the macro-expanded original E
/// halves, even when the executable bodies have been replaced by unfolded AC
/// members.
pub fn injective_fact_instances_for_rules<'a>(
    rules: impl IntoIterator<Item = &'a crate::theory::OpenProtoRule>,
    macros: &[tamarin_term::macro_expand::LNMacro],
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
    forced: &std::collections::BTreeSet<FactTag>,
) -> InjectiveFactInsts {
    let expanded: Vec<ProtoRuleE>;
    let rules: Vec<&ProtoRuleE> = if macros.is_empty() {
        rules.into_iter().map(|rule| rule.rule_e()).collect()
    } else {
        expanded = rules
            .into_iter()
            .map(|rule| crate::rule::apply_macro_in_rule(macros, rule.rule_e().clone()))
            .collect();
        expanded.iter().collect()
    };
    let computed = simple_injective_fact_instances(&rules, reducible);
    forced
        .iter()
        .map(|&tag| {
            let arity = crate::fact::fact_tag_arity(&tag);
            (tag, vec![vec![MonotonicBehaviour::Unspecified]; arity])
        })
        .chain(computed)
        .collect()
}

/// How a particular term position evolves across rule applications.
/// Variant order matches Haskell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MonotonicBehaviour {
    Constant,
    Increasing,
    Decreasing,
    StrictlyIncreasing,
    StrictlyDecreasing,
    Unstable,
    Unspecified,
}

impl std::fmt::Display for MonotonicBehaviour {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            MonotonicBehaviour::Constant => "=",
            MonotonicBehaviour::Increasing => "≤",
            MonotonicBehaviour::Decreasing => "≥",
            MonotonicBehaviour::StrictlyIncreasing => "<",
            MonotonicBehaviour::StrictlyDecreasing => ">",
            MonotonicBehaviour::Unstable => ".",
            MonotonicBehaviour::Unspecified => "?",
        };
        write!(f, "{}", s)
    }
}

/// Combine two `MonotonicBehaviour`s — direct port of Haskell's
/// `combine` in `simpleInjectiveFactInstances`.  Used to merge the
/// per-rule shapes into a single behaviour vector for the tag.
fn combine_behaviour(x: MonotonicBehaviour, y: MonotonicBehaviour) -> MonotonicBehaviour {
    use MonotonicBehaviour::*;
    if x == y {
        return x;
    }
    match (x, y) {
        (Unstable, _) | (_, Unstable) => Unstable,
        (Unspecified, b) | (b, Unspecified) => b,
        (StrictlyIncreasing, Increasing) | (StrictlyIncreasing, Constant) => Increasing,
        (Increasing, StrictlyIncreasing) | (Constant, StrictlyIncreasing) => Increasing,
        (StrictlyDecreasing, Decreasing) | (StrictlyDecreasing, Constant) => Decreasing,
        (Decreasing, StrictlyDecreasing) | (Constant, StrictlyDecreasing) => Decreasing,
        (StrictlyIncreasing, _) | (_, StrictlyIncreasing) => Unstable,
        (StrictlyDecreasing, _) | (_, StrictlyDecreasing) => Unstable,
        (Increasing, Decreasing) | (Decreasing, Increasing) => Unstable,
        (Increasing, Constant) | (Constant, Increasing) => Increasing,
        (Decreasing, Constant) | (Constant, Decreasing) => Decreasing,
        _ => Unstable,
    }
}

/// Unfold the tuple `t` to the right at most `n - 1` times, stopping early at
/// a non-pair, so the result has at most `n` leaves.  With `n = usize::MAX`
/// this is HS `getPairTerms` (InjectiveFactInstances.hs):
///   getPairTerms <t1, t2> = t1 : getPairTerms t2
///   getPairTerms t        = [t]
fn unfold_pairs(t: &tamarin_term::lterm::LNTerm, n: usize) -> Vec<&tamarin_term::lterm::LNTerm> {
    let mut out = Vec::new();
    let mut cur = t;
    while out.len() + 1 < n {
        match cur {
            tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(s),
                args,
            ) if s.is_pair_sym() && args.len() == 2 => {
                out.push(&args[0]);
                cur = &args[1];
            }
            _ => break,
        }
    }
    out.push(cur);
    out
}

/// HS `trimmedPairTerms` (Simplify.hs): given an injective fact
/// instance and the tag's behaviour/shape, return its injective identifier
/// (the first term) and a flat list of `(behaviour, leaf-term)` pairs.
///   trimmedPairTerms (factTerms -> firstTerm:terms) = do
///     shaped <- sequence $ zipWith
///       (\behaviour term -> shapeTerm (length behaviour) term) behaviours terms
///     return (firstTerm, concat $ zipWith zip behaviours shaped)
/// Simplify.hs's `shapeTerm` is `Nothing` when a term has fewer pairs than
/// its position's shape, so an instance with any such position gives `None`
/// (e.g. `S(~id, x)` against `[[=, <]]`) and the caller drops it.
pub fn trimmed_pair_terms(
    fa: &crate::fact::LNFact,
    behaviours: &[Vec<MonotonicBehaviour>],
) -> Option<(
    tamarin_term::lterm::LNTerm,
    Vec<(MonotonicBehaviour, tamarin_term::lterm::LNTerm)>,
)> {
    let first = fa.terms.first()?.clone();
    let mut pairs = Vec::new();
    for (term, behaviour) in fa.terms.iter().skip(1).zip(behaviours.iter()) {
        let leaves = unfold_pairs(term, behaviour.len());
        if leaves.len() < behaviour.len() {
            return None;
        }
        pairs.extend(behaviour.iter().copied().zip(leaves.into_iter().cloned()));
    }
    Some((first, pairs))
}

/// Simple under-approximation of the injective-fact-instance set.
///
/// A linear fact tag `T` is **injective** iff for every protocol rule R
/// in which T appears as a conclusion, R either:
///   (a) consumes T as a premise with the same first term (a copy
///       step — Loop / Copy / Continue), or
///   (b) produces T from a `Fr(t)` premise where `t` is the first arg
///       of the new T fact (a creation step — Init / Setup).
///
/// Behaviour at non-first positions is computed per rule and combined
/// across rules via `combine_behaviour`:
///   - For a **copy rule** (T premise + T conclusion with same first
///     term), each non-first position contributes `Constant` if the
///     premise leaf and conclusion leaf are syntactically equal,
///     `StrictlyIncreasing` if
///     `elem_not_below_reducible(reducible, prem, conc)`,
///     `StrictlyDecreasing` if
///     `elem_not_below_reducible(reducible, conc, prem)`, the
///     restriction-derived `StrictlyIncreasing` / `StrictlyDecreasing`
///     hint, else `Unstable`.
///   - For a **fresh creation rule**, every position contributes
///     the default `Unspecified` shape.
///
/// The result is a per-position list of behaviour-lists: the outer list
/// ranges over the non-first argument positions (the first position is
/// the injectivity index), and each inner list over the right-flattened
/// pair-leaves of that position (HS `getPairTerms` / `getShape` /
/// `shapeTerm` / `trimmedPairTerms`).
pub fn simple_injective_fact_instances(
    rules: &[&ProtoRuleE],
    reducible: &tamarin_utils::FastSet<tamarin_term::function_symbols::FunSym>,
) -> Vec<(FactTag, Vec<Vec<MonotonicBehaviour>>)> {
    use crate::fact::{fact_tag_multiplicity, LNFact, Multiplicity};
    use std::collections::BTreeMap;
    use tamarin_term::lterm::LNTerm;
    use MonotonicBehaviour::*;

    fn first_term(f: &LNFact) -> Option<&LNTerm> {
        f.terms.first()
    }
    fn fresh_premise_for(rule: &ProtoRuleE, t: &LNTerm) -> bool {
        rule.premises
            .iter()
            .any(|p| p.tag == crate::fact::FactTag::Fresh && p.terms.first() == Some(t))
    }
    fn copy_premise_for<'a>(
        rule: &'a ProtoRuleE,
        tag: &crate::fact::FactTag,
        t: &LNTerm,
    ) -> Option<&'a crate::fact::LNFact> {
        // Mirrors HS `getPrem` (InjectiveFactInstances.hs):
        //   case filter (\faPrem -> factTag faPrem == tag && Just tConc == firstTerm faPrem) prems of
        //     [g] -> Just g
        //     _   -> Nothing  -- if there are multiple such guards, the rule cannot be executed
        // We must return the premise ONLY when there is EXACTLY one match; if
        // two or more premises share the tag and first term the rule cannot be
        // executed and the tag is treated as non-injective.
        let mut it = rule
            .premises
            .iter()
            .filter(|p| &p.tag == tag && p.terms.first() == Some(t));
        match (it.next(), it.next()) {
            (Some(g), None) => Some(g),
            _ => None,
        }
    }

    // HS `getShape` (InjectiveFactInstances.hs): for each non-first
    // term, `replicate Unspecified (length (getPairTerms term))`.
    fn get_shape(fact: &LNFact) -> Vec<Vec<MonotonicBehaviour>> {
        fact.terms
            .iter()
            .skip(1)
            .map(|t| vec![Unspecified; unfold_pairs(t, usize::MAX).len()])
            .collect()
    }

    // HS `map (map f) $ zipWith zip a b`, written by `combineShapes` with
    // `fst` (InjectiveFactInstances.hs) and by `combineAll` with
    // `combine`.  Both `zip`s truncate to the shorter list.
    fn zip_shapes(
        a: &[Vec<MonotonicBehaviour>],
        b: &[Vec<MonotonicBehaviour>],
        f: fn(MonotonicBehaviour, MonotonicBehaviour) -> MonotonicBehaviour,
    ) -> Vec<Vec<MonotonicBehaviour>> {
        a.iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.iter().zip(bi.iter()).map(|(x, y)| f(*x, *y)).collect())
            .collect()
    }

    // HS `combineShapes` (InjectiveFactInstances.hs): keep the left
    // behaviour at each surviving position.
    fn combine_shapes(
        a: &[Vec<MonotonicBehaviour>],
        b: &[Vec<MonotonicBehaviour>],
    ) -> Vec<Vec<MonotonicBehaviour>> {
        zip_shapes(a, b, |x, _| x)
    }

    // HS `combineAll` (InjectiveFactInstances.hs) folded over a list
    // of `Maybe` shapes.  `Nothing` anywhere ⇒ `Nothing` (non-injective).
    // The empty list yields the default candidate shape.
    fn combine_all(
        list: impl IntoIterator<Item = Option<Vec<Vec<MonotonicBehaviour>>>>,
        default_shape: &[Vec<MonotonicBehaviour>],
    ) -> Option<Vec<Vec<MonotonicBehaviour>>> {
        // Fold lazily with early-out on the first `None` (the result is `None`
        // iff any element is `None`); the empty list yields the default
        // candidate shape.
        let mut it = list.into_iter();
        let mut acc = match it.next() {
            Some(first) => first?,
            None => return Some(default_shape.to_vec()),
        };
        for next in it {
            acc = zip_shapes(&acc, &next?, combine_behaviour);
        }
        Some(acc)
    }

    // HS `extractConstraints` (InjectiveFactInstances.hs): from a rule
    // restriction, collect `(t1, t2)` pairs from a bare top-level `Subterm`
    // atom (every other formula shape yields `[]`).  Bound variables in a
    // top-level atom are an implementation error in HS; we drop the
    // restriction instead of panicking.
    fn extract_constraints(f: &crate::formula::SyntacticLNFormula) -> Vec<(LNTerm, LNTerm)> {
        use crate::atom::{to_atom, ProtoAtom};
        use crate::formula::ProtoFormula;
        let ProtoFormula::Atom(atom @ ProtoAtom::Subterm(_, _)) = f else {
            return vec![];
        };
        let Some(ProtoAtom::Subterm(t1, t2)) = crate::guarded::unbind_atom(&to_atom(atom.clone()))
        else {
            return vec![];
        };
        vec![(t1, t2)]
    }

    // Candidate tags + their default shape.  Mirrors HS `candidates`
    // (InjectiveFactInstances.hs): `M.fromListWith combineShapes`
    // over `(tag, combineShapes (getShape conc) (getShape prem))` for each
    // (rule, conc, prem) with:
    //   guard $ (factTagMultiplicity tag == Linear)
    //        && (tag `elem` (factTag <$> rPrems ru))
    //   guard (factTag prem == tag)
    //   guard (not (null (factTerms conc)))
    //
    // The guards above must hold PER-RULE: a tag is injective only when a
    // SINGLE rule has it in both its premises and conclusions.  Including
    // any tag that merely appears as a conclusion in some rule is too
    // permissive — it adds spurious InjectiveFacts less-atoms (via
    // `nonInjectiveFactInstances`) for protocols whose linear facts get
    // *created* in one rule and *consumed* in another (no round-trip).
    // E.g. Artificial.spthy: Step1 creates St(x, k), Step2 consumes it —
    // neither rule has both → St is not injective (Fin_unique's case_2).
    // `M.fromListWith` folds DUPLICATE keys with `combineShapes` (note the
    // args are flipped vs. the first insert, but `combineShapes` is
    // symmetric in length-trimming), so we fold on insert.
    let mut candidates: BTreeMap<FactTag, Vec<Vec<MonotonicBehaviour>>> = BTreeMap::new();
    for &r in rules {
        let prem_tags: std::collections::BTreeSet<FactTag> =
            r.premises.iter().map(|p| p.tag).collect();
        for conc in &r.conclusions {
            let tag = &conc.tag;
            if !matches!(tag, FactTag::Proto(_, _, _)) {
                continue;
            }
            if fact_tag_multiplicity(tag) != Multiplicity::Linear {
                continue;
            }
            if !prem_tags.contains(tag) {
                continue;
            }
            for prem in r.premises.iter().filter(|p| &p.tag == tag) {
                if conc.terms.is_empty() {
                    continue;
                }
                let shape = combine_shapes(&get_shape(conc), &get_shape(prem));
                candidates
                    .entry(*tag)
                    .and_modify(|existing| *existing = combine_shapes(existing, &shape))
                    .or_insert(shape);
            }
        }
    }

    // HS `getMaybeEqStrict tag ru` (InjectiveFactInstances.hs): the
    // per-rule shape, or `Nothing` if the rule violates injectivity for the
    // tag.
    let get_maybe_eq_strict = |tag: &FactTag,
                               r: &ProtoRuleE,
                               default_shape: &[Vec<MonotonicBehaviour>]|
     -> Option<Vec<Vec<MonotonicBehaviour>>> {
        let copies: Vec<&LNFact> = r.conclusions.iter().filter(|c| &c.tag == tag).collect();
        // HS `constraints = concatMap extractConstraints
        //   (preRestriction (rInfo ru))` (InjectiveFactInstances.hs).
        let constraints: Vec<(LNTerm, LNTerm)> = r
            .info
            .restrictions
            .iter()
            .flat_map(extract_constraints)
            .collect();
        // HS `duplicateFirstTerms` (InjectiveFactInstances.hs): a copy whose
        // first term another copy shares violates (2), so the rule does.
        let mut seen = std::collections::BTreeSet::new();
        if copies
            .iter()
            .filter_map(|c| first_term(c))
            .any(|t| !seen.insert(t))
        {
            return None;
        }

        // HS `getMaybeEqMonConclusion` (InjectiveFactInstances.hs).
        let get_maybe_eq_mon_conclusion =
            |fa_conc: &LNFact| -> Option<Vec<Vec<MonotonicBehaviour>>> {
                let t_conc = first_term(fa_conc)?; // Nothing if no args
                if fresh_premise_for(r, t_conc) {
                    // applying (2)(a)
                    return Some(default_shape.to_vec());
                }
                let fa_prem = copy_premise_for(r, tag, t_conc)?; // violating (2)(b)

                // HS `getBehaviour` (InjectiveFactInstances.hs).
                let get_behaviour = |t1: &LNTerm, t2: &LNTerm| -> MonotonicBehaviour {
                    if t1 == t2 {
                        Constant
                    } else if crate::tools::subterm_store::elem_not_below_reducible(
                        reducible, t1, t2,
                    ) {
                        StrictlyIncreasing
                    } else if crate::tools::subterm_store::elem_not_below_reducible(
                        reducible, t2, t1,
                    ) {
                        StrictlyDecreasing
                    } else if constraints.iter().any(|(a, b)| a == t1 && b == t2) {
                        StrictlyIncreasing
                    } else if constraints.iter().any(|(a, b)| a == t2 && b == t1) {
                        StrictlyDecreasing
                    } else {
                        Unstable
                    }
                };
                // HS `map (map getBehaviour) $ zipWith zip (trimmedPairTerms
                // faPrem) (trimmedPairTerms faConc)` (InjectiveFactInstances.hs),
                // where `trimmedPairTerms` unfolds each non-first term to its
                // default shape length (HS `shapeTerm`).  HS errors when a term
                // has too few pairs (a copy rule's premise shallower than the
                // shape inferred from the conclusions); `unfold_pairs` keeps the
                // remainder as the last leaf instead.
                let behaviours = fa_prem
                    .terms
                    .iter()
                    .zip(fa_conc.terms.iter())
                    .skip(1)
                    .zip(default_shape)
                    .map(|((p, c), shape)| {
                        unfold_pairs(p, shape.len())
                            .into_iter()
                            .zip(unfold_pairs(c, shape.len()))
                            .map(|(p, c)| get_behaviour(p, c))
                            .collect()
                    })
                    .collect();
                Some(behaviours)
            };

        combine_all(
            copies.iter().map(|c| get_maybe_eq_mon_conclusion(c)),
            default_shape,
        )
    };

    // HS top-level: `tag <- M.keys candidates`;
    //   `combineAll (map (getMaybeEqStrict tag) rules) tag`.
    let mut out: Vec<(FactTag, Vec<Vec<MonotonicBehaviour>>)> = Vec::new();
    for (tag, default_shape) in &candidates {
        let per_rule = rules
            .iter()
            .map(|&r| get_maybe_eq_strict(tag, r, default_shape));
        if let Some(behaviours) = combine_all(per_rule, default_shape) {
            out.push((*tag, behaviours));
        }
    }
    out
}

#[cfg(test)]
#[path = "injective_fact_instances_tests.rs"]
mod tests;
