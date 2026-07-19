// Currently GPL 3.0 until granted permission by the following authors:
//   charlie-j, arcz, rkunnema, and other minor contributors (see
//   upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic.hs, lib/sapic/src/Sapic/Compression.hs,
//   lib/sapic/src/Sapic/Facts.hs

//! Port of `Sapic.Compression` (`lib/sapic/src/Sapic/Compression.hs`).
//!
//! Path compression: merge adjacent "silent" SAPIC rules (rules that do not
//! perform observable actions) along the state-fact flow, starting from the
//! initial `State_( )` fact.  Gated on `_transProgress` in HS (`Sapic.hs:45-101, see line 72`).
//!
//! Operates on the final `Rule<ProtoRuleEInfo>` list (post-`toRule`).  HS uses
//! `S.Set (Rule ProtoRuleEInfo)` in `mergeRules` and `S.Set (Fact LNTerm)` for
//! the worklist; we mirror the set semantics with a faithful rule-ordering
//! (`cmp_rule`) and `BTreeSet<LNFact>` for fact sets.

use std::collections::BTreeSet;

use tamarin_theory::fact::{FactTag, LNFact, Multiplicity};
use tamarin_theory::rule::{ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};

use crate::base_translation::list_union;

type ERule = Rule<ProtoRuleEInfo>;

const NO_COMPRESS_KEYWORDS: &[&str] = &[
    "IsIn", "IsNotSet", "Insert", "Delete", "Lock", "Unlock", "Progress",
];

/// `isSapicNoCompress` (Compression.hs:32-35).
fn is_sapic_no_compress(f: &LNFact) -> bool {
    if let FactTag::Proto(_, name, _) = &f.tag {
        NO_COMPRESS_KEYWORDS.iter().any(|kw| name.starts_with(kw))
    } else {
        false
    }
}

/// `isStateFact` (Facts.hs:291-295): name starts with `State` or `Semistate`.
fn is_state_fact(f: &LNFact) -> bool {
    if let FactTag::Proto(_, name, _) = &f.tag {
        name.starts_with("State") || name.starts_with("Semistate")
    } else {
        false
    }
}

/// `isLetFact` (Facts.hs:286-289): name starts with `Let`.
fn is_let_fact(f: &LNFact) -> bool {
    if let FactTag::Proto(_, name, _) = &f.tag {
        name.starts_with("Let")
    } else {
        false
    }
}

/// `isLockFact` (Facts.hs:297-300): name starts with `L_CellLocked`.
fn is_lock_fact(f: &LNFact) -> bool {
    if let FactTag::Proto(_, name, _) = &f.tag {
        name.starts_with("L_CellLocked")
    } else {
        false
    }
}

/// `isOutFact` (Facts.hs:278-280).
fn is_out_fact(f: &LNFact) -> bool {
    matches!(f.tag, FactTag::Out)
}

/// `isPersistentFact`: a persistent-multiplicity fact.
fn is_persistent_fact(f: &LNFact) -> bool {
    matches!(&f.tag, FactTag::Proto(Multiplicity::Persistent, _, _))
}

/// `isStateProcessFact f = isStateFact f || isLetFact f` (Compression.hs:37-38).
fn is_state_process_fact(f: &LNFact) -> bool {
    is_state_fact(f) || is_let_fact(f)
}

/// `sameName` (Compression.hs:40-42): both are proto facts with the same name.
fn same_name(a: &LNFact, b: &LNFact) -> bool {
    match (&a.tag, &b.tag) {
        (FactTag::Proto(_, n1, _), FactTag::Proto(_, n2, _)) => n1 == n2,
        _ => false,
    }
}

/// `List.partition (List.any (sameName fact) . _rPrems)` (Compression.hs:45-46).
fn get_prem_rules(fact: &LNFact, rules: Vec<ERule>) -> (Vec<ERule>, Vec<ERule>) {
    rules
        .into_iter()
        .partition(|r| r.premises.iter().any(|f| same_name(fact, f)))
}

/// `getConcsRules` (Compression.hs:49-50): partition on conclusions.
fn get_concs_rules(fact: &LNFact, rules: Vec<ERule>) -> (Vec<ERule>, Vec<ERule>) {
    rules
        .into_iter()
        .partition(|r| r.conclusions.iter().any(|f| same_name(fact, f)))
}

/// `getProducedFacts` (Compression.hs:53-58): all state-process facts in the
/// conclusions of the given rules.
fn get_produced_facts(rules: &[ERule]) -> BTreeSet<LNFact> {
    let mut out = BTreeSet::new();
    for r in rules {
        for f in &r.conclusions {
            if is_state_process_fact(f) {
                out.insert(f.clone());
            }
        }
    }
    out
}

/// `mergeAttrs a a' = a <> a'` (Compression.hs:60-68, see line 67) — Semigroup on attributes.
/// `RuleAttributes::merge` is right-precedence (`other.x.or(self.x)`), matching
/// HS `a <> a'`; for two rules of the same source process the result is the same
/// either way.
fn merge_attrs(a: RuleAttributes, b: RuleAttributes) -> RuleAttributes {
    a.merge(b)
}

/// `mergeInfo` (Compression.hs:60-68): keep the FIRST rule's name, merge attrs,
/// concatenate restrictions.
fn merge_info(i1: &ProtoRuleEInfo, i2: &ProtoRuleEInfo) -> ProtoRuleEInfo {
    let name = i1.name.clone(); // `mergeStand n _ = n`
    let attributes = merge_attrs(i1.attributes.clone(), i2.attributes.clone());
    let mut restrictions = i1.restrictions.clone();
    restrictions.extend(i2.restrictions.clone());
    ProtoRuleEInfo {
        name,
        attributes,
        restrictions,
    }
}

/// `canMerge compEvents r1 r2` (Compression.hs:71-84).
fn can_merge(comp_events: bool, r1: &ERule, r2: &ERule) -> bool {
    let ract = &r1.actions;
    let rconc = &r1.conclusions;
    let rprem = &r1.premises;
    let ract2 = &r2.actions;
    let rconc2 = &r2.conclusions;
    // `rprem2' = filter (not . isLockFact) rprem2`
    let rprem2_filtered = r2.premises.iter().filter(|f| !is_lock_fact(f)).count();

    if ract.iter().any(is_sapic_no_compress) && ract2.iter().any(is_sapic_no_compress) {
        return false;
    }
    if !comp_events && !ract.is_empty() && !ract2.is_empty() {
        return false;
    }
    if rprem2_filtered > 1 && rconc.len() > 1 {
        return false;
    }
    if rconc.len() > 1 && !ract2.is_empty() {
        return false;
    }
    if rconc.iter().any(is_out_fact) && rconc2.iter().any(is_out_fact) {
        return false;
    }
    if rconc.iter().any(is_let_fact) || rprem.iter().any(is_let_fact) {
        return false;
    }
    if rconc.iter().any(is_out_fact) && !ract2.is_empty() {
        return false;
    }
    true
}

/// `merge compEvents rule1 rule2 ruleset` (Compression.hs:87-96).
fn merge(comp_events: bool, rule1: &ERule, rule2: &ERule, ruleset: &mut Vec<ERule>) {
    if can_merge(comp_events, rule1, rule2) {
        // `newprem = rprem ++ filter (`notElem` rconc) rprem2`
        let mut newprem = rule1.premises.clone();
        for f in &rule2.premises {
            if !rule1.conclusions.contains(f) {
                newprem.push(f.clone());
            }
        }
        // `newrconc = rconc2 ++ filter (`notElem` rprem2) rconc`
        let mut newrconc = rule2.conclusions.clone();
        for f in &rule1.conclusions {
            if !rule2.premises.contains(f) {
                newrconc.push(f.clone());
            }
        }
        let info = merge_info(&rule1.info, &rule2.info);
        let actions = list_union(&rule1.actions, &rule2.actions);
        let mut new_vars = rule1.new_vars.clone();
        new_vars.extend(rule2.new_vars.clone());
        let merged = Rule {
            info,
            premises: newprem,
            conclusions: newrconc,
            actions,
            new_vars,
        };
        set_insert(ruleset, merged);
    } else {
        set_insert(ruleset, rule1.clone());
        set_insert(ruleset, rule2.clone());
    }
}

/// `mergeRules compEvents leftrules rightrules` (Compression.hs:99-105).
fn merge_rules(comp_events: bool, leftrules: &[ERule], rightrules: &[ERule]) -> Vec<ERule> {
    if leftrules.len() == 1 && rightrules.len() == 1 {
        // `foldl (\set l -> foldl (flip (merge l)) set rightrules) S.empty leftrules`,
        // then `S.toList` (ascending Ord order).
        let mut ruleset: Vec<ERule> = Vec::new();
        for l in leftrules {
            for r in rightrules {
                merge(comp_events, l, r, &mut ruleset);
            }
        }
        ruleset
    } else {
        let mut out = leftrules.to_vec();
        out.extend(rightrules.to_vec());
        out
    }
}

/// `compressOne compEvents fact msr` (Compression.hs:111-118).
fn compress_one(
    comp_events: bool,
    fact: &LNFact,
    msr: Vec<ERule>,
) -> (Vec<ERule>, BTreeSet<LNFact>) {
    // HS `compressOne` (Compression.hs:111-118): the `where`-bound `new_rules` /
    // `new_facts` are SHARED across both guards — the persistent case returns the
    // UNCOMPRESSED `msr` but STILL computes `new_facts` from the merge of the
    // fact's prem/concs rules (NOT `getProducedFacts msr`).
    let persistent = is_persistent_fact(fact);
    if persistent {
        // Compute `new_facts` from the merge, but return the ORIGINAL `msr`
        // unchanged — so partition a CLONE with the same prem/concs helpers the
        // non-persistent path below uses.
        let (prem_rules, msr2) = get_prem_rules(fact, msr.clone());
        let (concs_rules, _msr3) = get_concs_rules(fact, msr2);
        let new_rules = merge_rules(comp_events, &concs_rules, &prem_rules);
        let new_facts = get_produced_facts(&new_rules);
        return (msr, new_facts);
    }
    let (prem_rules, msr2) = get_prem_rules(fact, msr);
    let (concs_rules, msr3) = get_concs_rules(fact, msr2);
    let new_rules = merge_rules(comp_events, &concs_rules, &prem_rules);
    let new_facts = get_produced_facts(&new_rules);
    // `msr3 ++ new_rules`
    let mut out = msr3;
    out.extend(new_rules);
    (out, new_facts)
}

/// `compress compEvents (fact:remainder) compressed_facts msr` (Compression.hs:121-129).
fn compress(
    comp_events: bool,
    mut worklist: Vec<LNFact>,
    mut compressed_facts: BTreeSet<LNFact>,
    mut msr: Vec<ERule>,
) -> Vec<ERule> {
    let dbg = tamarin_utils::env_gate!("TAM_COMPRESS_DBG");
    while !worklist.is_empty() {
        let fact = worklist.remove(0);
        let remainder = worklist; // the tail
        if dbg {
            eprintln!(
                "[compress] fact={} | msr=[{}] | worklist_tail=[{}]",
                tamarin_theory::fact::fact_tag_name(&fact.tag),
                msr.iter()
                    .map(|r| match &r.info.name {
                        ProtoRuleName::Stand(n) => n.to_string(),
                        _ => "?".to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
                remainder
                    .iter()
                    .map(|f| tamarin_theory::fact::fact_tag_name(&f.tag))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        let (new_msr, new_facts) = compress_one(comp_events, &fact, msr);
        msr = new_msr;
        compressed_facts.insert(fact.clone());
        // `new_facts_no_compress = new_facts \\ compressed_facts`
        // `new_facts_no_remainder = new_facts_no_compress \\ S.fromList remainder`
        // `new_facts_remainder = S.toList new_facts_no_remainder ++ remainder`
        let remainder_set: BTreeSet<LNFact> = remainder.iter().cloned().collect();
        let mut prefix: Vec<LNFact> = new_facts
            .into_iter()
            .filter(|f| !compressed_facts.contains(f) && !remainder_set.contains(f))
            .collect();
        prefix.extend(remainder); // `S.toList (...) ++ remainder`
        worklist = prefix;
    }
    msr
}

/// `pathCompression compEvents msr` (Compression.hs:133-140).
///
/// Starts from the initial `State_( )` fact and removes dangling rules (those
/// with no actions AND no conclusions).
pub fn path_compression(comp_events: bool, msr: Vec<ERule>) -> Vec<ERule> {
    // `initfact = factToFact (State LState [] S.empty)` = `State_( )`, arity 0.
    let initfact: LNFact = LNFact::new(
        FactTag::Proto(Multiplicity::Linear, "State_", 0),
        vec![],
    );
    let compressed = compress(comp_events, vec![initfact], BTreeSet::new(), msr);
    // `filterDeadend = filter (\(Rule _ _ rconc ract _) -> not (null ract && null rconc))`
    compressed
        .into_iter()
        .filter(|r| !(r.actions.is_empty() && r.conclusions.is_empty()))
        .collect()
}

// ---------------------------------------------------------------------------
// Faithful `S.Set (Rule ProtoRuleEInfo)` semantics: ordered insert (dedup) by
// the HS-derived `Ord (Rule ProtoRuleEInfo)` =
//   (info, prems, concs, acts, newVars)
// with `info = (name, attrs, restrictions)`.
// ---------------------------------------------------------------------------

/// Insert into a Vec acting as an ordered set (ascending `cmp_rule`, dedup).
fn set_insert(set: &mut Vec<ERule>, r: ERule) {
    match set.binary_search_by(|x| cmp_rule(x, &r)) {
        Ok(_) => {} // already present
        Err(pos) => set.insert(pos, r),
    }
}

/// HS-derived `Ord (Rule ProtoRuleEInfo)`.
fn cmp_rule(a: &ERule, b: &ERule) -> std::cmp::Ordering {
    cmp_info(&a.info, &b.info)
        .then_with(|| a.premises.cmp(&b.premises))
        .then_with(|| a.conclusions.cmp(&b.conclusions))
        .then_with(|| a.actions.cmp(&b.actions))
        .then_with(|| a.new_vars.cmp(&b.new_vars))
}

fn cmp_info(a: &ProtoRuleEInfo, b: &ProtoRuleEInfo) -> std::cmp::Ordering {
    // `ProtoRuleEInfo` Ord = (name, attributes, restrictions).  The SAPIC rules
    // reaching compression carry NO `info.restrictions` (the per-rule `_restrict`
    // formulas live in `AnnotatedRule.restr`, lifted separately), so comparing by
    // length is a faithful proxy — `SyntacticLNFormula` has no `Ord` and the
    // non-empty case never arises here.
    a.name
        .cmp(&b.name)
        .then_with(|| cmp_attrs(&a.attributes, &b.attributes))
        .then_with(|| a.restrictions.len().cmp(&b.restrictions.len()))
}

/// `Ord RuleAttributes` = `(ruleColor, ruleProcess, ignoreDerivChecks,
/// isSAPiCRule, role)`.  Color compared by rendered hex (a total order), process
/// by its top-level rendering.
fn cmp_attrs(a: &RuleAttributes, b: &RuleAttributes) -> std::cmp::Ordering {
    use tamarin_theory::pretty_sapic::pretty_sapic_top_level;
    let color_key = |c: &Option<tamarin_utils::color::Rgb>| {
        c.as_ref().map(|c| tamarin_utils::color::rgb_to_hex(*c))
    };
    color_key(&a.color)
        .cmp(&color_key(&b.color))
        .then_with(|| {
            let pa = a.process.as_ref().map(pretty_sapic_top_level);
            let pb = b.process.as_ref().map(pretty_sapic_top_level);
            pa.cmp(&pb)
        })
        .then_with(|| a.ignore_deriv_checks.cmp(&b.ignore_deriv_checks))
        .then_with(|| a.is_sapic_rule.cmp(&b.is_sapic_rule))
        .then_with(|| a.role.cmp(&b.role))
}
