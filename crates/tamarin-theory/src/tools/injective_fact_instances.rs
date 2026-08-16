// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
//! (InjectiveFactInstances.hs:100-228).

use crate::fact::FactTag;
use crate::rule::ProtoRuleE;

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
pub fn combine_behaviour(x: MonotonicBehaviour, y: MonotonicBehaviour) -> MonotonicBehaviour {
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

/// HS `getPairTerms` (InjectiveFactInstances.hs): flatten ONLY the
/// right-hand side of a tuple.
///   getPairTerms <t1, t2> = t1 : getPairTerms t2
///   getPairTerms t        = [t]
fn get_pair_terms(t: &tamarin_term::lterm::LNTerm) -> Vec<&tamarin_term::lterm::LNTerm> {
    let mut out = Vec::new();
    let mut cur = t;
    loop {
        match cur.view() {
            tamarin_term::term::TermView::App(
                tamarin_term::function_symbols::FunSym::NoEq(s),
                args,
            ) if *s == tamarin_term::function_symbols::pair_sym() && args.len() == 2 => {
                out.push(&args[0]);
                cur = &args[1];
            }
            _ => {
                out.push(cur);
                break;
            }
        }
    }
    out
}

/// HS `shapeTerm` (InjectiveFactInstances.hs:198-202 and the identical copy
/// in Simplify.hs:611-616): unfold the tuple to the right `n - 1` times,
/// returning `n` leaves.  HS errors when the term does not have enough
/// pairs; that only arises across rules with mismatched shapes, which
/// `combineShapes` already trims to the shorter shape, so we fall back to
/// treating the remainder as a single leaf rather than panicking.
pub fn shape_term(t: &tamarin_term::lterm::LNTerm, n: usize) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut out = Vec::new();
    let mut cur = t.clone();
    let mut x = n;
    while x > 1 {
        match cur.view() {
            tamarin_term::term::TermView::App(
                tamarin_term::function_symbols::FunSym::NoEq(s),
                args,
            ) if *s == tamarin_term::function_symbols::pair_sym() && args.len() == 2 => {
                out.push(args[0].clone());
                let rest = args[1].clone();
                cur = rest;
                x -= 1;
            }
            _ => {
                out.push(cur);
                return out;
            }
        }
    }
    out.push(cur);
    out
}

/// HS `trimmedPairTerms` (Simplify.hs:627-628): given an injective fact
/// instance and the tag's behaviour/shape, return its injective identifier
/// (the first term) and a flat list of `(behaviour, leaf-term)` pairs.
///   trimmedPairTerms fa = (firstTerm, concat $ zipWith
///     (\behaviour term -> zip behaviour (shapeTerm (length behaviour) term))
///     behaviours terms)
pub fn trimmed_pair_terms(
    fa: &crate::fact::LNFact,
    behaviours: &[Vec<MonotonicBehaviour>],
) -> Option<(
    tamarin_term::lterm::LNTerm,
    Vec<(MonotonicBehaviour, tamarin_term::lterm::LNTerm)>,
)> {
    let first = fa.terms.first()?.clone();
    let pairs: Vec<(MonotonicBehaviour, tamarin_term::lterm::LNTerm)> = fa
        .terms
        .iter()
        .skip(1)
        .zip(behaviours.iter())
        .flat_map(|(term, behaviour)| {
            let leaves = shape_term(term, behaviour.len());
            behaviour.iter().copied().zip(leaves).collect::<Vec<_>>()
        })
        .collect();
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
        // Mirrors HS `getPrem` (InjectiveFactInstances.hs:226-228):
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

    // HS `getShape` (InjectiveFactInstances.hs:136-138): for each non-first
    // term, `replicate Unspecified (length (getPairTerms term))`.
    fn get_shape(fact: &LNFact) -> Vec<Vec<MonotonicBehaviour>> {
        fact.terms
            .iter()
            .skip(1)
            .map(|t| vec![Unspecified; get_pair_terms(t).len()])
            .collect()
    }

    // HS `combineShapes` (InjectiveFactInstances.hs:141-142): take the
    // shorter list at each (outer and inner) position — `map (map fst) $
    // zipWith zip a b`.
    fn combine_shapes(
        a: &[Vec<MonotonicBehaviour>],
        b: &[Vec<MonotonicBehaviour>],
    ) -> Vec<Vec<MonotonicBehaviour>> {
        a.iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.iter().zip(bi.iter()).map(|(x, _)| *x).collect())
            .collect()
    }

    // HS `combineAll` (InjectiveFactInstances.hs:144-151) folded over a list
    // of `Maybe` shapes.  `Nothing` anywhere ⇒ `Nothing` (non-injective).
    // The non-empty list folds via `map (map combine) $ zipWith zip`.
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
            let next = next?;
            acc = acc
                .iter()
                .zip(next.iter())
                .map(|(ai, bi)| {
                    ai.iter()
                        .zip(bi.iter())
                        .map(|(x, y)| combine_behaviour(*x, *y))
                        .collect()
                })
                .collect();
        }
        Some(acc)
    }

    // HS `extractConstraints` (InjectiveFactInstances.hs:56-62): from a rule
    // restriction, collect `(t1, t2)` pairs from a bare top-level `Subterm`
    // atom (every other formula shape yields `[]`).  Bound variables in a
    // top-level atom are an implementation error in HS; we drop the
    // restriction instead of panicking.
    fn extract_constraints(f: &crate::rule::SyntacticLNFormula) -> Vec<(LNTerm, LNTerm)> {
        use crate::atom::ProtoAtom;
        use crate::formula::ProtoFormula;
        match f {
            ProtoFormula::Atom(ProtoAtom::Subterm(t1, t2)) => {
                match (bvar_term_to_lnterm(t1), bvar_term_to_lnterm(t2)) {
                    (Some(a), Some(b)) => vec![(a, b)],
                    _ => vec![],
                }
            }
            _ => vec![],
        }
    }

    // HS `bvarToLVar` (InjectiveFactInstances.hs:59-61): map a top-level
    // atom term `VTerm Name (BVar LVar)` to `LNTerm`, treating every Bound
    // var as an implementation error.  Returns `None` (drop the
    // constraint) instead of `error`/panic.
    fn bvar_term_to_lnterm(
        t: &tamarin_term::vterm::VTerm<
            tamarin_term::lterm::Name,
            tamarin_term::lterm::BVar<tamarin_term::lterm::LVar>,
        >,
    ) -> Option<LNTerm> {
        use tamarin_term::lterm::BVar;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Con(n)) => Some(Term::Lit(Lit::Con(*n))),
            Term::Lit(Lit::Var(BVar::Free(v))) => Some(Term::Lit(Lit::Var(*v))),
            Term::Lit(Lit::Var(BVar::Bound(_))) => None,
            Term::App(sym, args) => {
                let mapped: Option<Vec<LNTerm>> = args.iter().map(bvar_term_to_lnterm).collect();
                mapped.map(|a| Term::App(*sym, a.into()))
            }
        }
    }

    // Candidate tags + their default shape.  Mirrors HS `candidates`
    // (InjectiveFactInstances.hs:121-138): `M.fromListWith combineShapes`
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

    // HS `getMaybeEqStrict tag ru` (InjectiveFactInstances.hs:170-223): the
    // per-rule shape, or `Nothing` if the rule violates injectivity for the
    // tag.
    let get_maybe_eq_strict = |tag: &FactTag,
                               r: &ProtoRuleE,
                               default_shape: &[Vec<MonotonicBehaviour>]|
     -> Option<Vec<Vec<MonotonicBehaviour>>> {
        let copies: Vec<&LNFact> = r.conclusions.iter().filter(|c| &c.tag == tag).collect();
        // HS `constraints = concatMap extractConstraints
        //   (preRestriction (rInfo ru))` (InjectiveFactInstances.hs:100-228, see line 177).
        let constraints: Vec<(LNTerm, LNTerm)> = r
            .info
            .restrictions
            .iter()
            .flat_map(extract_constraints)
            .collect();
        // HS `duplicateFirstTerms` (InjectiveFactInstances.hs:181-182): the
        // first terms appearing at least twice among `copies`.
        let mut first_term_counts: BTreeMap<&LNTerm, usize> = BTreeMap::new();
        for c in &copies {
            if let Some(ft) = first_term(c) {
                *first_term_counts.entry(ft).or_insert(0) += 1;
            }
        }
        let duplicate_first_terms: std::collections::BTreeSet<&LNTerm> = first_term_counts
            .into_iter()
            .filter(|(_, n)| *n >= 2)
            .map(|(t, _)| t)
            .collect();

        // HS `getMaybeEqMonConclusion` (InjectiveFactInstances.hs:185-223).
        let get_maybe_eq_mon_conclusion =
            |fa_conc: &LNFact| -> Option<Vec<Vec<MonotonicBehaviour>>> {
                let t_conc = first_term(fa_conc)?; // Nothing if no args
                if duplicate_first_terms.contains(t_conc) {
                    // violating (2)
                    return None;
                }
                if fresh_premise_for(r, t_conc) {
                    // applying (2)(a)
                    return Some(default_shape.to_vec());
                }
                let fa_prem = copy_premise_for(r, tag, t_conc)?; // violating (2)(b)
                                                                 // HS `getBehaviour` (InjectiveFactInstances.hs:213-219).
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
                // HS `trimmedPairTerms` (InjectiveFactInstances.hs:205-207): unfold
                // each non-first term according to the default shape lengths.
                let shape_lens: Vec<usize> = default_shape.iter().map(|s| s.len()).collect();
                let trimmed = |fa: &LNFact| -> Vec<Vec<LNTerm>> {
                    fa.terms
                        .iter()
                        .skip(1)
                        .zip(shape_lens.iter())
                        .map(|(t, &n)| shape_term(t, n))
                        .collect()
                };
                let prem_leaves = trimmed(fa_prem);
                let conc_leaves = trimmed(fa_conc);
                // HS `zipped = zipWith zip (trimmedPairTerms faPrem)
                //   (trimmedPairTerms faConc)` then `map (map getBehaviour)`.
                let behaviours: Vec<Vec<MonotonicBehaviour>> = prem_leaves
                    .iter()
                    .zip(conc_leaves.iter())
                    .map(|(ps, cs)| {
                        ps.iter()
                            .zip(cs.iter())
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

/// HS `pureStateFactTag` / `pureStateLockFactTag` (Facts.hs:272-276): the two
/// fact tags `setforcedInjectiveFacts` forces injective when the state-channel
/// optimisation is on (lib/sapic/src/Sapic.hs:84).  Both are `L_PureState/2` /
/// `L_CellLocked/2`,
/// linear, arity 2.
pub fn pure_state_forced_fact_tags() -> Vec<FactTag> {
    use crate::fact::Multiplicity;
    vec![
        FactTag::Proto(Multiplicity::Linear, "L_PureState", 2),
        FactTag::Proto(Multiplicity::Linear, "L_CellLocked", 2),
    ]
}

/// Union the forced-injective fact tags into a computed
/// `simple_injective_fact_instances` result, mirroring HS `closeRuleCache`
/// (CloseRule.hs:417-420):
///
/// ```haskell
/// forcedInjFacts' = S.map (\x -> (x, replicate (factTagArity x) [Unspecified])) forcedInjFacts
/// injFactInstances = forcedInjFacts' `S.union` simpleInjectiveFactInstances ...
/// ```
///
/// Each forced tag carries `replicate arity [Unspecified]` as its behaviour
/// (one singleton `[Unspecified]` per argument position).  `S.union` keeps the
/// LEFT (forced) entry on a tag collision, then `S.toList` sorts by `Ord
/// FactTag`; we reproduce that with a tag-keyed merge + sort.
pub fn union_forced_injective_fact_instances(
    computed: Vec<(FactTag, Vec<Vec<MonotonicBehaviour>>)>,
    forced: &[FactTag],
) -> Vec<(FactTag, Vec<Vec<MonotonicBehaviour>>)> {
    use crate::fact::fact_tag_arity;
    use std::collections::BTreeMap;
    let mut map: BTreeMap<FactTag, Vec<Vec<MonotonicBehaviour>>> = computed.into_iter().collect();
    for tag in forced {
        // `S.union` is LEFT-biased; the forced entry wins on collision.
        let arity = fact_tag_arity(tag);
        let behaviour = vec![vec![MonotonicBehaviour::Unspecified]; arity];
        map.insert(*tag, behaviour);
    }
    map.into_iter().collect()
}

#[cfg(test)]
#[path = "injective_fact_instances_tests.rs"]
mod tests;
