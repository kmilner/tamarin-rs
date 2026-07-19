// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, rkunnema, beschmi, PhilipLukertWork, yavivanov,
//   rsasse, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Constraint/Solver/Goals.hs,
//   lib/theory/src/Theory/Model/Rule.hs

//! Port of `Theory.Model.Rule` from `lib/theory/src/Theory/Model/Rule.hs`.
//!
//! Rewriting rules describing protocol execution and intruder deduction.
//! This file covers the data types, accessors, queries, and basic
//! conversions.  Two related pieces of `Rule.hs` live elsewhere in the
//! crate rather than here:
//! - `someRuleACInst*` (rule instantiation) — in
//!   `constraint::solver::reduction` (`canonical_rule_inst`).
//! - Pretty-printing — `render_rule` in `pretty_theory.rs`; graph/dot
//!   rendering of rule instances lives in `tamarin-server` (`handlers/dot.rs`).
//!
//! The Haskell version uses `fclabels` lenses heavily; we replace those
//! with public fields plus accessor methods.

use std::collections::BTreeSet;

use tamarin_term::lterm::{HasFrees, LSort, LVar, Name, LNTerm};
use tamarin_term::vterm::VTerm;
use tamarin_utils::color::Rgb;

use crate::atom::SyntacticSugar;
use crate::fact::LNFact;
use crate::formula::ProtoFormula;
use crate::sapic::PlainProcess;

// =============================================================================
// Rule
// =============================================================================

/// A rewrite rule with arbitrary additional information `I` and facts over
/// `LNTerm`. `new_vars` initially holds the new (fresh) variables and is
/// then refined to their concrete instantiations.
#[derive(Debug, Clone, PartialEq)]
pub struct Rule<I> {
    pub info: I,
    pub premises: Vec<LNFact>,
    pub conclusions: Vec<LNFact>,
    pub actions: Vec<LNFact>,
    pub new_vars: Vec<LNTerm>,
}

impl<I> Rule<I> {
    pub fn new(
        info: I,
        premises: Vec<LNFact>,
        conclusions: Vec<LNFact>,
        actions: Vec<LNFact>,
    ) -> Self {
        Rule { info, premises, conclusions, actions, new_vars: Vec::new() }
    }

    pub fn with_new_vars(mut self, vars: Vec<LNTerm>) -> Self {
        self.new_vars = vars;
        self
    }

    /// `compareRulesUpToNewVars`: ordering ignoring `new_vars`.
    /// Retained for port completeness (no current callers).
    #[allow(dead_code)]
    pub(crate) fn cmp_up_to_new_vars(&self, other: &Self) -> std::cmp::Ordering
    where
        I: Ord,
    {
        self.info
            .cmp(&other.info)
            .then_with(|| self.premises.cmp(&other.premises))
            .then_with(|| self.conclusions.cmp(&other.conclusions))
            .then_with(|| self.actions.cmp(&other.actions))
    }

    /// Add an action fact, prepended, unless already present. Port of HS
    /// `addAction` (Rule.hs:1035-1039): `if act elem acts then unchanged else
    /// act:acts`.
    pub fn add_action(&mut self, act: LNFact) {
        if !self.actions.contains(&act) {
            self.actions.insert(0, act);
        }
    }

    pub fn lookup_premise(&self, i: PremIdx) -> Option<&LNFact> {
        self.premises.get(i.0)
    }
    pub fn lookup_conclusion(&self, i: ConcIdx) -> Option<&LNFact> {
        self.conclusions.get(i.0)
    }
    pub fn enumerate_premises(&self) -> impl Iterator<Item = (PremIdx, &LNFact)> {
        self.premises.iter().enumerate().map(|(i, f)| (PremIdx(i), f))
    }
    pub fn enumerate_conclusions(&self) -> impl Iterator<Item = (ConcIdx, &LNFact)> {
        self.conclusions.iter().enumerate().map(|(i, f)| (ConcIdx(i), f))
    }
}

// =============================================================================
// HasFrees instance — visit/map over premises, conclusions, actions, new_vars.
// `info` is intentionally skipped here: the generic bound is `Clone`, not
// `HasFrees`, so this impl cannot recurse into it. This is sound because every
// caller operates on `RuleACInst`, whose info (ProtoRuleACInstInfo /
// IntrRuleACInfo) carries no free LVars. Note that Haskell's `HasFrees (Rule i)`
// (Rule.hs:280-292) DOES fold over `info` first, and ProtoRuleEInfo/ProtoRuleACInfo
// info (Rule.hs:474-477, see line 476, 486-489) carry frees (restrictions / variant keys); callers
// that need those (ProtoRuleE/AC) must walk variants/restrictions separately, as
// rule_variants.rs::rename_precise_rule_with_variants does.
// =============================================================================

impl<I: Clone> HasFrees for Rule<I> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for p in &self.premises { p.for_each_free(f); }
        for c in &self.conclusions { c.for_each_free(f); }
        for a in &self.actions { a.for_each_free(f); }
        for v in &self.new_vars { v.for_each_free(f); }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        Rule {
            info: self.info,
            premises: self.premises.into_iter().map(|x| x.map_free_with(f, monotone)).collect(),
            conclusions: self.conclusions.into_iter().map(|x| x.map_free_with(f, monotone)).collect(),
            actions: self.actions.into_iter().map(|x| x.map_free_with(f, monotone)).collect(),
            new_vars: self.new_vars.into_iter().map(|x| x.map_free_with(f, monotone)).collect(),
        }
    }
}

// =============================================================================
// Premise / conclusion indices
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PremIdx(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConcIdx(pub usize);

/// Position of a term inside a rule: `(premise, fact-arg-index, term-position)`.
pub type ExtendedPosition = (PremIdx, usize, tamarin_term::positions::Position);

pub fn print_position(ep: &ExtendedPosition) -> String {
    let mut s = format!("{}_{}_", ep.0 .0, ep.1);
    for n in &ep.2 {
        s.push_str(&n.to_string());
        s.push('_');
    }
    s
}

pub fn print_fact_position(ep: &ExtendedPosition) -> String {
    ep.0 .0.to_string()
}

// =============================================================================
// RuleInfo: ProtoInfo | IntrInfo
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuleInfo<P, I> {
    Proto(P),
    Intr(I),
}

impl<P, I> RuleInfo<P, I> {
    /// `foldRuleInfo`: case-analyse the two arms.
    /// Retained for port completeness (no current callers).
    #[allow(dead_code)]
    pub(crate) fn fold<C>(&self, proto: impl FnOnce(&P) -> C, intr: impl FnOnce(&I) -> C) -> C {
        match self {
            RuleInfo::Proto(p) => proto(p),
            RuleInfo::Intr(i) => intr(i),
        }
    }
}

// =============================================================================
// Protocol rule attributes / names
// =============================================================================

#[derive(Debug, Clone, PartialEq, Default)]
pub struct RuleAttributes {
    /// Color for graphical display.
    pub color: Option<Rgb>,
    /// Source process — for SAPIC-derived rules.
    pub process: Option<PlainProcess>,
    pub ignore_deriv_checks: bool,
    pub is_sapic_rule: bool,
    /// Optional role name.
    pub role: Option<String>,
}


impl RuleAttributes {
    pub fn empty() -> Self { Self::default() }

    /// Combine two attribute sets, with `other` taking precedence on
    /// `Option`-typed fields and `||` on bool fields.
    pub fn merge(self, other: Self) -> Self {
        RuleAttributes {
            color: other.color.or(self.color),
            process: other.process.or(self.process),
            ignore_deriv_checks: self.ignore_deriv_checks || other.ignore_deriv_checks,
            is_sapic_rule: self.is_sapic_rule || other.is_sapic_rule,
            role: other.role.or(self.role),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProtoRuleName {
    /// The reserved `Fresh` rule.
    Fresh,
    /// A user-defined protocol rule.  Interned `&'static str` (see
    /// `tamarin_term::intern`): pointer-copy clone per rule instantiation.
    Stand(&'static str),
}

/// `SyntacticLNFormula` from `Theory.Model.Formula`.
pub type SyntacticLNFormula =
    ProtoFormula<SyntacticSugar<VTerm<Name, LVar>>, (String, LSort), Name, LVar>;

/// Information for protocol rules modulo E (the equational theory).
#[derive(Debug, Clone, PartialEq)]
pub struct ProtoRuleEInfo {
    pub name: ProtoRuleName,
    pub attributes: RuleAttributes,
    pub restrictions: Vec<SyntacticLNFormula>,
}

impl ProtoRuleEInfo {
    pub fn fresh() -> Self {
        ProtoRuleEInfo {
            name: ProtoRuleName::Fresh,
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        }
    }

    pub fn standard(name: impl Into<String>) -> Self {
        ProtoRuleEInfo {
            name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&name.into())),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        }
    }
}

/// Information for protocol rules modulo AC. The `variants` field holds
/// possible instantiations of the free variables.
#[derive(Debug, Clone, PartialEq)]
pub struct ProtoRuleACInfo {
    pub name: ProtoRuleName,
    pub attributes: RuleAttributes,
    /// In Haskell this is `Disj LNSubstVFresh`; we carry a `Vec` here.
    pub variants: Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    pub loop_breakers: Vec<PremIdx>,
}

/// Information for instances of protocol rules modulo AC.
#[derive(Debug, Clone, PartialEq)]
pub struct ProtoRuleACInstInfo {
    pub name: ProtoRuleName,
    pub attributes: RuleAttributes,
    pub loop_breakers: Vec<PremIdx>,
}

// =============================================================================
// Intruder rule information
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrRuleACInfo {
    ConstrRule(Vec<u8>),
    /// `(name, remaining_applications, rhs_is_proper_subterm, rhs_is_constant)`.
    /// `remaining_applications` of `0` means unbounded; `-1` means not yet
    /// determined.
    DestrRule(Vec<u8>, i64, bool, bool),
    Coerce,
    IRecv,
    ISend,
    PubConstr,
    NatConstr,
    FreshConstr,
    /// Used for the diff equivalence check.
    IEquality,
}

// =============================================================================
// Concrete rule type aliases
// =============================================================================

pub type ProtoRuleE = Rule<ProtoRuleEInfo>;
pub type ProtoRuleAC = Rule<ProtoRuleACInfo>;
pub type IntrRuleAC = Rule<IntrRuleACInfo>;
pub type RuleAC = Rule<RuleInfo<ProtoRuleACInfo, IntrRuleACInfo>>;
pub type RuleACInst = Rule<RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo>>;

// =============================================================================
// Conversions
// =============================================================================

pub fn rule_ac_to_intr_rule_ac(r: RuleAC) -> Option<IntrRuleAC> {
    if let RuleInfo::Intr(i) = r.info {
        Some(Rule { info: i, premises: r.premises, conclusions: r.conclusions, actions: r.actions, new_vars: r.new_vars })
    } else {
        None
    }
}

pub fn rule_ac_intr_to_rule_ac(r: IntrRuleAC) -> RuleAC {
    Rule {
        info: RuleInfo::Intr(r.info),
        premises: r.premises,
        conclusions: r.conclusions,
        actions: r.actions,
        new_vars: r.new_vars,
    }
}

/// Retained for port completeness (no current callers); lifts an
/// `IntrRuleAC` directly into the `RuleACInst` shape.
#[allow(dead_code)]
pub(crate) fn rule_ac_intr_to_rule_ac_inst(r: IntrRuleAC) -> RuleACInst {
    Rule {
        info: RuleInfo::Intr(r.info),
        premises: r.premises,
        conclusions: r.conclusions,
        actions: r.actions,
        new_vars: r.new_vars,
    }
}

/// Retained for port completeness (no current callers).
/// `someRuleACInst` lite: drop the AC variants from a `ProtoRuleAC`,
/// producing a `RuleACInst`. The `variants` and `loop_breakers` are
/// carried into the inst-info; `variants` is stripped because the
/// instance form refers to one chosen variant.
#[allow(dead_code)]
pub(crate) fn proto_rule_ac_to_rule_ac_inst(r: ProtoRuleAC) -> RuleACInst {
    Rule {
        info: RuleInfo::Proto(ProtoRuleACInstInfo {
            name: r.info.name,
            attributes: r.info.attributes,
            loop_breakers: r.info.loop_breakers,
        }),
        premises: r.premises,
        conclusions: r.conclusions,
        actions: r.actions,
        new_vars: r.new_vars,
    }
}

// =============================================================================
// Predicates / queries
// =============================================================================

pub fn is_destr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::DestrRule(_, _, _, _))
}
/// `isSubtermRule`: True iff the rule is a destruction rule whose
/// RHS is a true subterm of the LHS, or the IEquality rule.
/// Mirrors Haskell's `Theory.Model.Rule.isSubtermRule`
/// (`lib/theory/src/Theory/Model/Rule.hs`).
pub fn is_subterm_rule_info(info: &IntrRuleACInfo) -> bool {
    match info {
        IntrRuleACInfo::DestrRule(_, _, subterm, _) => *subterm,
        IntrRuleACInfo::IEquality => true,
        _ => false,
    }
}
pub fn is_constr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::ConstrRule(_))
}
pub fn is_pub_constr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::PubConstr)
}
pub fn is_nat_constr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::NatConstr)
}
pub fn is_fresh_constr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::FreshConstr)
}
pub fn is_irecv_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::IRecv)
}
pub fn is_isend_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::ISend)
}
pub fn is_coerce_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::Coerce)
}
pub fn is_iequality_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::IEquality)
}

pub fn is_fresh_rule_info(info: &ProtoRuleEInfo) -> bool {
    info.name == ProtoRuleName::Fresh
}

/// Generic destruction-rule predicate: matches `_<sym>` destructor
/// rules (e.g. `_exp` for `isDExpRule`).
fn is_d_rule_with_sym<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>, sym: &[u8]) -> bool {
    if let RuleInfo::Intr(IntrRuleACInfo::DestrRule(name, _, _, _)) = &rule.info {
        let mut expected = b"_".to_vec();
        expected.extend_from_slice(sym);
        name == &expected
    } else {
        false
    }
}

/// `isDExpRule`: destruction rule for `exp`.
pub fn is_d_exp_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    is_d_rule_with_sym(rule, b"exp")
}

/// `isDPMultRule`: destruction rule for `pmult`.
pub fn is_d_pmult_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    is_d_rule_with_sym(rule, b"pmult")
}

/// `isDEMapRule`: destruction rule for `em`.
pub fn is_d_emap_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    is_d_rule_with_sym(rule, b"em")
}

/// `isCoerceRule` for a `RuleACInst` / `RuleAC`.
pub fn is_coerce_rule_inst<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    matches!(&rule.info, RuleInfo::Intr(IntrRuleACInfo::Coerce))
}

/// `isDestrRule`: destruction rule (DestrRule or IEquality).
/// Retained for port completeness (no production callers; test-only).
#[allow(dead_code)]
pub(crate) fn is_destr_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    matches!(&rule.info,
        RuleInfo::Intr(IntrRuleACInfo::DestrRule(_, _, _, _))
        | RuleInfo::Intr(IntrRuleACInfo::IEquality))
}

/// `isSubtermRule` for a `Rule` shape — RHS is a true subterm of LHS,
/// or IEquality. Mirrors Haskell's `Theory.Model.Rule.isSubtermRule`.
/// Retained for port completeness (no current callers).
#[allow(dead_code)]
pub(crate) fn is_subterm_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> bool {
    match &rule.info {
        RuleInfo::Intr(info) => is_subterm_rule_info(info),
        _ => false,
    }
}

/// `getRemainingRuleApplications`: returns the chain budget for
/// destruction rules, or `0` for everything else.
pub fn get_remaining_rule_applications<I>(
    rule: &Rule<RuleInfo<I, IntrRuleACInfo>>,
) -> i64 {
    match &rule.info {
        RuleInfo::Intr(IntrRuleACInfo::DestrRule(_, n, _, _)) => *n,
        _ => 0,
    }
}

/// `setRemainingRuleApplications`: writes a new budget into the
/// DestrRule remaining-applications Int field (the 2nd field of
/// `DestrRule name n subterm constant`).  Non-destr rules are returned
/// unchanged.  Mirrors Haskell `setRemainingRuleApplications`
/// (Theory/Model/Rule.hs).
///
/// Used by `solve_chain_goal` EXTEND to decrement the destructor's
/// remaining budget when chaining into another instance of the same
/// destructor — the loop-breaker that bounds chain extensions of
/// the same rule.
pub fn set_remaining_rule_applications<I>(
    rule: Rule<RuleInfo<I, IntrRuleACInfo>>,
    n: i64,
) -> Rule<RuleInfo<I, IntrRuleACInfo>>
{
    let Rule { info, premises, conclusions, actions, new_vars } = rule;
    let info = match info {
        RuleInfo::Intr(IntrRuleACInfo::DestrRule(name, _, subterm, constant)) =>
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(name, n, subterm, constant)),
        other => other,
    };
    Rule { info, premises, conclusions, actions, new_vars }
}

/// Get the rule name for `RuleACInst` / `RuleAC` shapes — used to
/// detect "same-name" rules in `forbiddenEdge`.
///
/// Mirrors Haskell `getRuleName` (Theory/Model/Rule.hs).  Intr
/// rules — especially `DestrRule` — MUST return their proper names here;
/// otherwise the `forbiddenEdge` same-rule loop-breaker
/// (Goals.hs) never fires for destructors, letting `solveChain`
/// recurse indefinitely through `d_0_sdec → d_0_sdec → ...` chains that
/// Haskell prunes after one application (per the DestrRule
/// remaining-applications counter — `getRemainingRuleApplications` /
/// `setRemainingRuleApplications`, Rule.hs).
pub fn rule_name_string(
    rule: &RuleACInst,
) -> String
{
    match &rule.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => s.to_string(),
            ProtoRuleName::Fresh => "FreshRule".to_string(),
        },
        RuleInfo::Intr(i) => match i {
            IntrRuleACInfo::ConstrRule(name) =>
                format!("Constr{}", prefix_if_reserved(&format!("c{}",
                    String::from_utf8_lossy(name)))),
            IntrRuleACInfo::DestrRule(name, _, _, _) =>
                format!("Destr{}", prefix_if_reserved(&format!("d{}",
                    String::from_utf8_lossy(name)))),
            IntrRuleACInfo::Coerce => "Coerce".to_string(),
            IntrRuleACInfo::IRecv => "Recv".to_string(),
            IntrRuleACInfo::ISend => "Send".to_string(),
            IntrRuleACInfo::PubConstr => "PubConstr".to_string(),
            IntrRuleACInfo::NatConstr => "NatConstr".to_string(),
            IntrRuleACInfo::FreshConstr => "FreshConstr".to_string(),
            IntrRuleACInfo::IEquality => "Equality".to_string(),
        },
    }
}

/// Mirror Haskell `prefixIfReserved` (Theory/Model/Rule.hs):
/// prefixes the name with `_` if it collides with a reserved rule name
/// or already starts with `_`.
pub(crate) fn prefix_if_reserved(s: &str) -> String {
    let reserved = reserved_rule_names();
    if reserved.contains(s) || s.starts_with('_') {
        format!("_{}", s)
    } else {
        s.to_string()
    }
}

/// `reservedRuleNames` from Haskell (Theory/Model/Rule.hs):
/// `["Fresh", "irecv", "isend", "coerce", "fresh", "pub", "iequality"]`.
pub fn reserved_rule_names() -> BTreeSet<&'static str> {
    let mut s = BTreeSet::new();
    s.insert("Fresh");
    s.insert("irecv");
    s.insert("isend");
    s.insert("coerce");
    s.insert("fresh");
    s.insert("pub");
    s.insert("iequality");
    s
}

// =============================================================================
// Maude-backed unification helpers — port of `unifyRuleACInstEqs`,
// `unifiableRuleACInsts`, `unifyLNFactEqs`, `unifiableLNFacts`.
// =============================================================================

use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::rewriting::Equal;

/// `unifyLNFactEqs`: AC-unify a list of fact equalities. Returns
/// the substitution candidates (one inner Vec per disjunct, holding
/// `(var, term)` bindings). If any pair has mismatched tags or
/// arities, returns `Ok(vec![])`.
pub fn unify_ln_fact_eqs(
    maude: &MaudeHandle,
    eqs: &[Equal<LNFact>],
) -> Result<Vec<Vec<(LVar, LNTerm)>>, MaudeError> {
    let mut term_eqs = Vec::new();
    for e in eqs {
        if e.lhs.tag != e.rhs.tag { return Ok(Vec::new()); }
        if e.lhs.terms.len() != e.rhs.terms.len() { return Ok(Vec::new()); }
        for (a, b) in e.lhs.terms.iter().zip(e.rhs.terms.iter()) {
            term_eqs.push(Equal { lhs: a.clone(), rhs: b.clone() });
        }
    }
    if term_eqs.is_empty() {
        // No constraints → unique trivial unifier (empty substitution).
        return Ok(vec![Vec::new()]);
    }
    maude.unify_at("unify_ln_fact_eqs", &term_eqs)
}

/// `unifiableLNFacts`: are two facts AC-unifiable?  Routes through
/// the memoised `maude.unifiable` path — the boolean result is
/// context-free, so caching avoids redundant subprocess round-trips
/// when the simplifier re-checks the same pairs across iterations.
pub fn unifiable_ln_facts(
    maude: &MaudeHandle,
    f1: &LNFact,
    f2: &LNFact,
) -> Result<bool, MaudeError> {
    if f1.tag != f2.tag { return Ok(false); }
    if f1.terms.len() != f2.terms.len() { return Ok(false); }
    let eqs: Vec<Equal<LNTerm>> = f1.terms.iter().zip(f2.terms.iter())
        .map(|(a, b)| Equal { lhs: a.clone(), rhs: b.clone() })
        .collect();
    if eqs.is_empty() { return Ok(true); }
    maude.unifiable(&eqs)
}

/// `unifyRuleACInstEqs`: AC-unify a list of `RuleACInst` equalities.
/// The Haskell version checks that `info`, premise count, and
/// conclusion count match before delegating to fact unification on
/// the zipped premises and conclusions.
pub fn unify_rule_ac_inst_eqs(
    maude: &MaudeHandle,
    eqs: &[Equal<RuleACInst>],
) -> Result<Vec<Vec<(LVar, LNTerm)>>, MaudeError> {
    let unifiable = eqs.iter().all(|e| {
        e.lhs.info == e.rhs.info
            && e.lhs.premises.len() == e.rhs.premises.len()
            && e.lhs.conclusions.len() == e.rhs.conclusions.len()
    });
    if !unifiable { return Ok(Vec::new()); }
    let mut fact_eqs = Vec::new();
    for e in eqs {
        for (a, b) in e.lhs.premises.iter().zip(e.rhs.premises.iter()) {
            fact_eqs.push(Equal { lhs: a.clone(), rhs: b.clone() });
        }
        for (a, b) in e.lhs.conclusions.iter().zip(e.rhs.conclusions.iter()) {
            fact_eqs.push(Equal { lhs: a.clone(), rhs: b.clone() });
        }
    }
    unify_ln_fact_eqs(maude, &fact_eqs)
}

/// `unifiableRuleACInsts`: are two rule instances AC-unifiable?
/// Routes through `maude.unifiable` for memoisation; the shape-
/// mismatch fast-path mirrors `unify_rule_ac_inst_eqs`.
pub fn unifiable_rule_ac_insts(
    maude: &MaudeHandle,
    r1: &RuleACInst,
    r2: &RuleACInst,
) -> Result<bool, MaudeError> {
    if r1.info != r2.info { return Ok(false); }
    if r1.premises.len() != r2.premises.len() { return Ok(false); }
    if r1.conclusions.len() != r2.conclusions.len() { return Ok(false); }
    let mut eqs: Vec<Equal<LNTerm>> = Vec::new();
    for (a, b) in r1.premises.iter().zip(r2.premises.iter()) {
        if a.tag != b.tag || a.terms.len() != b.terms.len() { return Ok(false); }
        for (ta, tb) in a.terms.iter().zip(b.terms.iter()) {
            eqs.push(Equal { lhs: ta.clone(), rhs: tb.clone() });
        }
    }
    for (a, b) in r1.conclusions.iter().zip(r2.conclusions.iter()) {
        if a.tag != b.tag || a.terms.len() != b.terms.len() { return Ok(false); }
        for (ta, tb) in a.terms.iter().zip(b.terms.iter()) {
            eqs.push(Equal { lhs: ta.clone(), rhs: tb.clone() });
        }
    }
    if eqs.is_empty() { return Ok(true); }
    maude.unifiable(&eqs)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{fresh_fact, in_fact, out_fact};
    use tamarin_term::builtin::msg_var;

    #[test]
    fn build_simple_proto_rule_e() {
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Send"),
            vec![fresh_fact(msg_var("k", 0))],
            vec![out_fact(msg_var("k", 0))],
            vec![],
        );
        assert_eq!(r.premises.len(), 1);
        assert_eq!(r.conclusions.len(), 1);
        assert!(matches!(r.info.name, ProtoRuleName::Stand(_)));
    }

    #[test]
    fn rule_indices_lookup() {
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Echo"),
            vec![in_fact(msg_var("m", 0))],
            vec![out_fact(msg_var("m", 0))],
            vec![],
        );
        assert!(r.lookup_premise(PremIdx(0)).is_some());
        assert!(r.lookup_premise(PremIdx(1)).is_none());
        assert!(r.lookup_conclusion(ConcIdx(0)).is_some());
    }

    #[test]
    fn enumerate_yields_indices() {
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("X"),
            vec![in_fact(msg_var("a", 0)), in_fact(msg_var("b", 0))],
            vec![],
            vec![],
        );
        let prems: Vec<PremIdx> = r.enumerate_premises().map(|(i, _)| i).collect();
        assert_eq!(prems, vec![PremIdx(0), PremIdx(1)]);
    }

    #[test]
    fn rule_attributes_merge_prefers_right() {
        let a = RuleAttributes { role: Some("alice".into()), ..Default::default() };
        let b = RuleAttributes { role: Some("bob".into()), is_sapic_rule: true, ..Default::default() };
        let merged = a.merge(b);
        assert_eq!(merged.role, Some("bob".into()));
        assert!(merged.is_sapic_rule);
    }

    #[test]
    fn rule_info_conversion_round_trip() {
        let intr: IntrRuleAC = Rule::new(
            IntrRuleACInfo::Coerce,
            vec![],
            vec![],
            vec![],
        );
        let lifted: RuleAC = rule_ac_intr_to_rule_ac(intr.clone());
        let back = rule_ac_to_intr_rule_ac(lifted).unwrap();
        assert_eq!(back, intr);
    }

    #[test]
    fn intruder_predicates() {
        assert!(is_constr_rule_info(&IntrRuleACInfo::ConstrRule(b"f".to_vec())));
        assert!(is_destr_rule_info(&IntrRuleACInfo::DestrRule(b"f".to_vec(), 0, true, false)));
        assert!(is_coerce_rule_info(&IntrRuleACInfo::Coerce));
        assert!(!is_constr_rule_info(&IntrRuleACInfo::Coerce));
    }

    #[test]
    fn print_extended_position() {
        let ep: ExtendedPosition = (PremIdx(2), 1, vec![0, 1, 0]);
        assert_eq!(print_position(&ep), "2_1_0_1_0_");
        assert_eq!(print_fact_position(&ep), "2");
    }

    #[test]
    fn reserved_names_include_fresh() {
        let r = reserved_rule_names();
        // Matches Haskell reservedRuleNames (Rule.hs):
        // ["Fresh", "irecv", "isend", "coerce", "fresh", "pub", "iequality"].
        assert!(r.contains("Fresh"));
        assert!(r.contains("coerce"));
        assert!(r.contains("iequality"));
        assert!(!r.contains("KU"));
    }

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        for c in ["/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() { return Some(c.to_string()); }
        }
        None
    }

    #[test]
    fn unify_ln_fact_eqs_tag_mismatch_no_unifiers() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let f1 = out_fact(msg_var("x", 0));
        let f2 = in_fact(msg_var("y", 0));
        let res = unify_ln_fact_eqs(&h, &[Equal { lhs: f1, rhs: f2 }]).unwrap();
        assert!(res.is_empty());
    }

    #[test]
    fn unify_ln_fact_eqs_two_vars() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let f1 = out_fact(msg_var("x", 0));
        let f2 = out_fact(msg_var("y", 0));
        let res = unify_ln_fact_eqs(&h, &[Equal { lhs: f1, rhs: f2 }]).unwrap();
        // At least one unifier; mgu binds one of the two vars.
        assert!(!res.is_empty());
        assert!(res.iter().all(|s| !s.is_empty()));
    }

    #[test]
    fn unifiable_ln_facts_yes_no() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let f1 = out_fact(msg_var("x", 0));
        let f2 = out_fact(msg_var("y", 0));
        let f3 = in_fact(msg_var("y", 0));
        assert!(unifiable_ln_facts(&h, &f1, &f2).unwrap());
        assert!(!unifiable_ln_facts(&h, &f1, &f3).unwrap());
    }

    #[test]
    fn unifiable_rule_ac_insts_same_shape() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let r1: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![in_fact(msg_var("a", 0))],
            vec![out_fact(msg_var("a", 0))],
            vec![],
        );
        let r2: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![in_fact(msg_var("b", 0))],
            vec![out_fact(msg_var("b", 0))],
            vec![],
        );
        assert!(unifiable_rule_ac_insts(&h, &r1, &r2).unwrap());
    }

    #[test]
    fn unifiable_rule_ac_insts_different_info_no() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let r1: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![in_fact(msg_var("a", 0))],
            vec![out_fact(msg_var("a", 0))],
            vec![],
        );
        let r2: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::ISend),
            vec![in_fact(msg_var("b", 0))],
            vec![out_fact(msg_var("b", 0))],
            vec![],
        );
        assert!(!unifiable_rule_ac_insts(&h, &r1, &r2).unwrap());
    }

    #[test]
    fn has_frees_for_rule_visits_premise_and_conclusion_vars() {
        use tamarin_term::lterm::{HasFrees, LSort};
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("X"),
            vec![in_fact(msg_var("a", 0))],
            vec![out_fact(msg_var("b", 1))],
            vec![],
        );
        let mut seen: Vec<(String, u64)> = Vec::new();
        r.for_each_free(&mut |v| {
            assert_eq!(v.sort, LSort::Msg);
            seen.push((v.name.to_string(), v.idx));
        });
        assert!(seen.contains(&("a".into(), 0)));
        assert!(seen.contains(&("b".into(), 1)));
    }

    #[test]
    fn d_exp_pmult_emap_rule_classification() {
        let dexp: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(b"_exp".to_vec(), 0, false, false)),
            vec![], vec![], vec![],
        );
        let dpmult: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(b"_pmult".to_vec(), 0, false, false)),
            vec![], vec![], vec![],
        );
        let dem: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(b"_em".to_vec(), 0, false, false)),
            vec![], vec![], vec![],
        );
        let coerce: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![], vec![], vec![],
        );
        assert!(is_d_exp_rule(&dexp));
        assert!(!is_d_exp_rule(&dpmult));
        assert!(is_d_pmult_rule(&dpmult));
        assert!(is_d_emap_rule(&dem));
        assert!(is_coerce_rule_inst(&coerce));
        assert!(is_destr_rule(&dexp));
        assert!(!is_destr_rule(&coerce));
    }

    #[test]
    fn get_remaining_rule_applications_works() {
        let with_budget: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(b"_x".to_vec(), 3, false, false)),
            vec![], vec![], vec![],
        );
        assert_eq!(get_remaining_rule_applications(&with_budget), 3);
        let no_budget: RuleACInst = Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::Coerce),
            vec![], vec![], vec![],
        );
        assert_eq!(get_remaining_rule_applications(&no_budget), 0);
    }

    #[test]
    fn rename_rule_shifts_indices() {
        use tamarin_term::lterm::{HasFrees, LSort};
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("X"),
            vec![in_fact(msg_var("a", 5))],
            vec![out_fact(msg_var("b", 7))],
            vec![],
        );
        // Shift by +10.
        let renamed = r.map_free(&mut |v| LVar { idx: v.idx + 10, ..v });
        let mut idxs = Vec::new();
        renamed.for_each_free(&mut |v| {
            assert_eq!(v.sort, LSort::Msg);
            idxs.push(v.idx);
        });
        assert!(idxs.contains(&15));
        assert!(idxs.contains(&17));
    }
}
