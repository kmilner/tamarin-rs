// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Theory.Model.Rule` from `lib/theory/src/Theory/Model/Rule.hs`.
//!
//! Rewriting rules describing protocol execution and intruder deduction.
//! This file covers the data types, accessors, queries, and basic
//! conversions.  Two related pieces of `Rule.hs` live elsewhere in the
//! crate rather than here:
//! - `someRuleACInst*` (rule instantiation) — in
//!   `constraint::solver::reduction` (`canonical_rule_inst`).
//! - Pretty-printing — `render_rule` in `pretty_theory.rs`; graph/dot
//!   rendering of rule instances lives in `constraint::system::dot`.
//!
//! The Haskell version uses `fclabels` lenses heavily; we replace those
//! with public fields plus accessor methods.

use tamarin_term::function_symbols::{FunSym, NdcState};
use tamarin_term::lterm::{HasFrees, LNTerm, LVar, Name};
use tamarin_term::macro_expand::LNMacro;
use tamarin_utils::color::Rgb;

use crate::fact::{apply_macro_in_fact, pretty_lnfact, LNFact};
use crate::formula::SyntacticLNFormula;
use crate::pretty_hpj::{fsep, operator_, punctuate, sep, Doc};
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
        Rule {
            info,
            premises,
            conclusions,
            actions,
            new_vars: Vec::new(),
        }
    }

    pub fn with_new_vars(mut self, vars: Vec<LNTerm>) -> Self {
        self.new_vars = vars;
        self
    }

    /// Add an action fact, prepended, unless already present. Port of HS
    /// `addAction` (Theory/Model/Rule.hs:1108-1112): `if act elem acts then
    /// unchanged else
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
        self.premises
            .iter()
            .enumerate()
            .map(|(i, f)| (PremIdx(i), f))
    }
    pub fn enumerate_conclusions(&self) -> impl Iterator<Item = (ConcIdx, &LNFact)> {
        self.conclusions
            .iter()
            .enumerate()
            .map(|(i, f)| (ConcIdx(i), f))
    }
}

/// HS `applyMacroInRule` (Theory/Model/Rule.hs:1115-1121): the theory's macros
/// applied to every premise, conclusion and action, `new_vars` recomputed from
/// the rewritten facts (`newVariables mRuPrems (mRuConcs ++ mRuActs)`, :1121)
/// and `info` left as it stands — so a rule's `_restrict` formulas keep their
/// macro calls.  An empty macro list returns the rule untouched, which is the
/// case HS's `closeProtoRule` splits out to keep `new_vars` as the rule holds
/// them (lib/theory/src/Rule.hs:82-85).
pub fn apply_macro_in_rule<I>(macros: &[LNMacro], r: Rule<I>) -> Rule<I> {
    if macros.is_empty() {
        return r;
    }
    let premises: Vec<LNFact> = r
        .premises
        .iter()
        .map(|f| apply_macro_in_fact(macros, f))
        .collect();
    let conclusions: Vec<LNFact> = r
        .conclusions
        .iter()
        .map(|f| apply_macro_in_fact(macros, f))
        .collect();
    let actions: Vec<LNFact> = r
        .actions
        .iter()
        .map(|f| apply_macro_in_fact(macros, f))
        .collect();
    let new_vars = crate::elaborate::compute_new_vars(&premises, &conclusions, &actions);
    Rule {
        info: r.info,
        premises,
        conclusions,
        actions,
        new_vars,
    }
}

// =============================================================================
// HasFrees instance — visit/map over premises, conclusions, actions, new_vars.
// `info` is intentionally skipped here: the generic bound is `Clone`, not
// `HasFrees`, so this impl cannot recurse into it. This is sound because every
// caller operates on `RuleACInst`, whose info (ProtoRuleACInstInfo /
// IntrRuleACInfo) carries no free LVars. Note that Haskell's `HasFrees (Rule i)`
// (Theory/Model/Rule.hs:291-306) DOES fold over `info` first, and
// ProtoRuleEInfo/ProtoRuleACInfo
// info (Theory/Model/Rule.hs:491-498, 503-515) carry frees (restrictions /
// variant keys); callers
// that need those (ProtoRuleE/AC) must walk variants/restrictions separately, as
// rule_variants.rs::rename_precise_rule_with_variants does.
// =============================================================================

impl<I: Clone> HasFrees for Rule<I> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for p in &self.premises {
            p.for_each_free(f);
        }
        for c in &self.conclusions {
            c.for_each_free(f);
        }
        for a in &self.actions {
            a.for_each_free(f);
        }
        for v in &self.new_vars {
            v.for_each_free(f);
        }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        Rule {
            info: self.info,
            premises: self
                .premises
                .into_iter()
                .map(|x| x.map_free_with(f, monotone))
                .collect(),
            conclusions: self
                .conclusions
                .into_iter()
                .map(|x| x.map_free_with(f, monotone))
                .collect(),
            actions: self
                .actions
                .into_iter()
                .map(|x| x.map_free_with(f, monotone))
                .collect(),
            new_vars: self
                .new_vars
                .into_iter()
                .map(|x| x.map_free_with(f, monotone))
                .collect(),
        }
    }
}

/// HS `instance Apply LNSubst i => Apply LNSubst (Rule i)`
/// (Theory/Model/Rule.hs:308-310):
/// a free substitution applied to every fact and new-var term of a rule.
///
/// `info` is carried over untouched, which is what HS's `apply subst i` comes
/// to for the info types this port instantiates: the `Apply` instances for
/// `ProtoRuleEInfo` and `IntrRuleACInfo` are literally `apply _ = id`
/// (Theory/Model/Rule.hs:500-501, 619-620), and `ProtoRuleACInstInfo`'s
/// (Theory/Model/Rule.hs:517-519)
/// maps only its `ProtoRuleName`, whose own instance is `apply _ = id`
/// (Theory/Model/Rule.hs:467-468).  So a refined `ProtoRuleE` keeps its
/// original
/// restriction frees unsubstituted.
pub(crate) fn apply_subst_rule<I: Clone>(
    sigma: &tamarin_term::subst::Subst<Name, LVar>,
    r: &Rule<I>,
) -> Rule<I> {
    let app_facts = |fs: &[LNFact]| -> Vec<LNFact> {
        fs.iter()
            .map(|f| crate::fact::apply_subst_fact(sigma, f))
            .collect()
    };
    Rule {
        info: r.info.clone(),
        premises: app_facts(&r.premises),
        conclusions: app_facts(&r.conclusions),
        actions: app_facts(&r.actions),
        new_vars: r
            .new_vars
            .iter()
            .map(|t| tamarin_term::subst::apply_vterm(sigma, t.clone()))
            .collect(),
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
    pub fn empty() -> Self {
        Self::default()
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProtoRuleName {
    /// The reserved `Fresh` rule.
    Fresh,
    /// A user-defined protocol rule.  Interned `&'static str` (see
    /// `tamarin_term::intern`): pointer-copy clone per rule instantiation.
    Stand(&'static str),
}

/// Information for protocol rules modulo E (the equational theory).
#[derive(Debug, Clone, PartialEq)]
pub struct ProtoRuleEInfo {
    pub name: ProtoRuleName,
    pub attributes: RuleAttributes,
    /// HS `_preRestriction` (Theory/Model/Rule.hs:423): the rule's
    /// `_restrict` formulas as written.  `Apply ProtoRuleEInfo` is the
    /// identity (Theory/Model/Rule.hs:500-501), so they are never
    /// substituted; only their free variables are read.
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
    /// HS `ConstrRule BC.ByteString FunSym` (Theory/Model/Rule.hs:540); `fun`
    /// is the
    /// symbol this construction rule builds.
    ConstrRule {
        name: Vec<u8>,
        fun: FunSym,
    },
    /// HS `DestrRule BC.ByteString Int Bool Bool [FunSym]`
    /// (Theory/Model/Rule.hs:541).
    /// `remaining_applications` of `0` means unbounded; `-1` means not yet
    /// determined. `funs` lists the function symbols this rule's application
    /// corresponds to (head first).
    ///
    /// Field order is load-bearing: the derived `Ord`/`Hash` compare fields
    /// in declaration order, so it must keep matching the positional order of
    /// the HS constructor.
    DestrRule {
        name: Vec<u8>,
        remaining_applications: i64,
        rhs_is_proper_subterm: bool,
        rhs_is_constant: bool,
        funs: Vec<FunSym>,
    },
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
        Some(Rule {
            info: i,
            premises: r.premises,
            conclusions: r.conclusions,
            actions: r.actions,
            new_vars: r.new_vars,
        })
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

// =============================================================================
// Predicates / queries
// =============================================================================

pub fn is_destr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::DestrRule { .. })
}
/// `isSubtermRule`: True iff the rule is a destruction rule whose
/// RHS is a true subterm of the LHS, or the IEquality rule.
/// Mirrors Haskell's `Theory.Model.Rule.isSubtermRule`
/// (`lib/theory/src/Theory/Model/Rule.hs`).
pub fn is_subterm_rule_info(info: &IntrRuleACInfo) -> bool {
    match info {
        IntrRuleACInfo::DestrRule {
            rhs_is_proper_subterm,
            ..
        } => *rhs_is_proper_subterm,
        IntrRuleACInfo::IEquality => true,
        _ => false,
    }
}
pub fn is_constr_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::ConstrRule { .. })
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

/// `isACConstrRule`: the function symbol iff the rule is a construction rule
/// for an AC symbol.
pub fn is_ac_constr_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> Option<FunSym> {
    match &rule.info {
        RuleInfo::Intr(IntrRuleACInfo::ConstrRule {
            fun: fun @ FunSym::Ac(_),
            ..
        }) => Some(*fun),
        _ => None,
    }
}

/// `getDestrRuleFunction`: the function at the root of a deconstruction rule.
pub fn get_destr_rule_function(rule: &IntrRuleAC) -> Option<FunSym> {
    match &rule.info {
        IntrRuleACInfo::DestrRule { funs, .. } => funs.first().copied(),
        _ => None,
    }
}

/// `builtInDestrRule`: name suffixes identifying built-in deconstruction rules.
pub fn built_in_destr_rule() -> [&'static [u8]; 6] {
    [b"exp", b"inv", b"union", b"xor", b"pmult", b"em"]
}

/// `builtInDestrRuleInclPair`: `builtInDestrRule` plus the pair projections.
pub fn built_in_destr_rule_incl_pair() -> [&'static [u8]; 8] {
    [
        b"exp", b"inv", b"union", b"xor", b"pmult", b"em", b"fst", b"snd",
    ]
}

pub(crate) fn has_builtin_suffix(name: &[u8], suffixes: &[&[u8]]) -> bool {
    suffixes.iter().any(|s| name.ends_with(s))
}

/// `isBuiltInIntruderRule`: everything except user-symbol Constr/Destr rules.
pub fn is_built_in_intruder_rule(rule: &IntrRuleAC) -> bool {
    match &rule.info {
        IntrRuleACInfo::ConstrRule { name, .. } | IntrRuleACInfo::DestrRule { name, .. } => {
            has_builtin_suffix(name, &built_in_destr_rule_incl_pair())
        }
        IntrRuleACInfo::Coerce
        | IntrRuleACInfo::IRecv
        | IntrRuleACInfo::ISend
        | IntrRuleACInfo::PubConstr
        | IntrRuleACInfo::NatConstr
        | IntrRuleACInfo::FreshConstr
        | IntrRuleACInfo::IEquality => true,
    }
}

/// The head function of a deconstruction rule, for the `RuleInfo`-wrapped
/// shape ([`get_destr_rule_function`] serves the bare `IntrRuleAC` one).
fn destr_rule_head<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> Option<&FunSym> {
    match &rule.info {
        RuleInfo::Intr(IntrRuleACInfo::DestrRule { funs, .. }) => funs.first(),
        _ => None,
    }
}

/// `isNDCRule`: `Just IsNDC` iff the rule is a deconstruction rule whose head
/// function has the (trace-mode) NDC property.
pub fn is_ndc_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> Option<NdcState> {
    destr_rule_head(rule)
        .is_some_and(FunSym::is_ndc_fun_sym)
        .then_some(NdcState::IsNdc)
}

/// `isNDCDiffRule` (IntruderRules.hs:524-527): `Just IsNDCDiff` iff the head
/// function has the diff-mode NDC property.
///
/// Intentionally retained: faithful mirror of HS `isNDCDiffRule`
/// (IntruderRules.hs:524-527); no caller yet.
pub fn is_ndc_diff_rule<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> Option<NdcState> {
    destr_rule_head(rule)
        .is_some_and(FunSym::is_ndc_diff_fun_sym)
        .then_some(NdcState::IsNdcDiff)
}

/// `getDeconstrRuleKDPrem`: the first premise fact of an intruder rule (the
/// KD fact for a deconstruction rule).
pub fn get_deconstr_rule_kd_prem(rule: &IntrRuleAC) -> &LNFact {
    rule.premises
        .first()
        .expect("getDeconstrRuleKDPrem: deconstruction rules have at least one premise")
}

/// `getDeconstrRulePremsTail`: all premises except the leading KD fact.
pub fn get_deconstr_rule_prems_tail(rule: &IntrRuleAC) -> &[LNFact] {
    match rule.premises.split_first() {
        Some((first, tail)) if first.tag == crate::fact::FactTag::Kd => tail,
        _ => panic!("getDeconstrRulePremsTail: deconstruction rules have a leading KD premise"),
    }
}

/// `getConcFact`: the single conclusion of an intruder rule.
pub fn get_conc_fact(rule: &IntrRuleAC) -> &LNFact {
    match rule.conclusions.as_slice() {
        [fact] => fact,
        _ => panic!("getConcFact: intruder rules have exactly one conclusion"),
    }
}

/// `getRuleName` restricted to intruder-rule infos (used where only an
/// `IntrRuleAC` is at hand).
pub fn intr_rule_name_string(info: &IntrRuleACInfo) -> String {
    match info {
        IntrRuleACInfo::ConstrRule { name, .. } => format!(
            "Constr{}",
            prefix_if_reserved(&format!("c{}", String::from_utf8_lossy(name)))
        ),
        IntrRuleACInfo::DestrRule { name, .. } => format!(
            "Destr{}",
            prefix_if_reserved(&format!("d{}", String::from_utf8_lossy(name)))
        ),
        IntrRuleACInfo::Coerce => "Coerce".to_string(),
        IntrRuleACInfo::IRecv => "Recv".to_string(),
        IntrRuleACInfo::ISend => "Send".to_string(),
        IntrRuleACInfo::PubConstr => "PubConstr".to_string(),
        IntrRuleACInfo::NatConstr => "NatConstr".to_string(),
        IntrRuleACInfo::FreshConstr => "FreshConstr".to_string(),
        IntrRuleACInfo::IEquality => "Equality".to_string(),
    }
}

/// Generic destruction-rule predicate: matches `_<sym>` destructor
/// rules (e.g. `_exp` for `isDExpRule`).
fn is_d_rule_with_sym<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>, sym: &[u8]) -> bool {
    if let RuleInfo::Intr(IntrRuleACInfo::DestrRule { name, .. }) = &rule.info {
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

/// `getRemainingRuleApplications`: returns the chain budget for
/// destruction rules, or `0` for everything else.
pub fn get_remaining_rule_applications<I>(rule: &Rule<RuleInfo<I, IntrRuleACInfo>>) -> i64 {
    match &rule.info {
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            remaining_applications,
            ..
        }) => *remaining_applications,
        _ => 0,
    }
}

/// `setRemainingRuleApplications`: writes a new budget into the
/// `DestrRule::remaining_applications` field.  Non-destr rules are returned
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
) -> Rule<RuleInfo<I, IntrRuleACInfo>> {
    let Rule {
        info,
        premises,
        conclusions,
        actions,
        new_vars,
    } = rule;
    let info = match info {
        RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name,
            rhs_is_proper_subterm,
            rhs_is_constant,
            funs,
            ..
        }) => RuleInfo::Intr(IntrRuleACInfo::DestrRule {
            name,
            remaining_applications: n,
            rhs_is_proper_subterm,
            rhs_is_constant,
            funs,
        }),
        other => other,
    };
    Rule {
        info,
        premises,
        conclusions,
        actions,
        new_vars,
    }
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
pub fn rule_name_string(rule: &RuleACInst) -> String {
    match &rule.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => s.to_string(),
            ProtoRuleName::Fresh => "FreshRule".to_string(),
        },
        RuleInfo::Intr(i) => intr_rule_name_string(i),
    }
}

/// Mirror Haskell `prefixIfReserved` (Theory/Model/Rule.hs):
/// prefixes the name with `_` if it collides with a reserved rule name
/// or already starts with `_`.
pub(crate) fn prefix_if_reserved(s: &str) -> String {
    if RESERVED_RULE_NAMES.contains(&s) || s.starts_with('_') {
        format!("_{}", s)
    } else {
        s.to_string()
    }
}

/// `reservedRuleNames` from Haskell (Theory/Model/Rule.hs).
const RESERVED_RULE_NAMES: [&str; 7] = [
    "Fresh",
    "irecv",
    "isend",
    "coerce",
    "fresh",
    "pub",
    "iequality",
];

// =============================================================================
// Maude-backed unification helpers — port of `unifiableRuleACInsts`,
// `unifyLNFactEqs`, `unifiableLNFacts`.
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
        if e.lhs.tag != e.rhs.tag {
            return Ok(Vec::new());
        }
        if e.lhs.terms.len() != e.rhs.terms.len() {
            return Ok(Vec::new());
        }
        for (a, b) in e.lhs.terms.iter().zip(e.rhs.terms.iter()) {
            term_eqs.push(Equal {
                lhs: a.clone(),
                rhs: b.clone(),
            });
        }
    }
    if term_eqs.is_empty() {
        // No constraints → unique trivial unifier (empty substitution).
        return Ok(vec![Vec::new()]);
    }
    maude.unify(&term_eqs)
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
    if f1.tag != f2.tag {
        return Ok(false);
    }
    if f1.terms.len() != f2.terms.len() {
        return Ok(false);
    }
    let eqs: Vec<Equal<LNTerm>> = f1
        .terms
        .iter()
        .zip(f2.terms.iter())
        .map(|(a, b)| Equal {
            lhs: a.clone(),
            rhs: b.clone(),
        })
        .collect();
    if eqs.is_empty() {
        return Ok(true);
    }
    maude.unifiable(&eqs)
}

/// `unifiableRuleACInsts`: are two rule instances AC-unifiable?
/// Routes through `maude.unifiable` for memoisation; the shape-
/// mismatch fast-path rejects rules whose info, premise count or
/// conclusion count differ before building any equalities.
pub fn unifiable_rule_ac_insts(
    maude: &MaudeHandle,
    r1: &RuleACInst,
    r2: &RuleACInst,
) -> Result<bool, MaudeError> {
    if r1.info != r2.info {
        return Ok(false);
    }
    if r1.premises.len() != r2.premises.len() {
        return Ok(false);
    }
    if r1.conclusions.len() != r2.conclusions.len() {
        return Ok(false);
    }
    let mut eqs: Vec<Equal<LNTerm>> = Vec::new();
    for (a, b) in r1.premises.iter().zip(r2.premises.iter()) {
        if a.tag != b.tag || a.terms.len() != b.terms.len() {
            return Ok(false);
        }
        for (ta, tb) in a.terms.iter().zip(b.terms.iter()) {
            eqs.push(Equal {
                lhs: ta.clone(),
                rhs: tb.clone(),
            });
        }
    }
    for (a, b) in r1.conclusions.iter().zip(r2.conclusions.iter()) {
        if a.tag != b.tag || a.terms.len() != b.terms.len() {
            return Ok(false);
        }
        for (ta, tb) in a.terms.iter().zip(b.terms.iter()) {
            eqs.push(Equal {
                lhs: ta.clone(),
                rhs: tb.clone(),
            });
        }
    }
    if eqs.is_empty() {
        return Ok(true);
    }
    maude.unifiable(&eqs)
}

// =============================================================================
// Pretty printing
// =============================================================================

/// HS `ppList = fsep . punctuate comma` applied to `map ppFact`
/// (Theory/Model/Rule.hs:1379-1380) at `ppFact = prettyLNFact`.
fn pp_list(facts: &[LNFact]) -> Doc {
    fsep(punctuate(
        Doc::char(','),
        facts.iter().map(pretty_lnfact).collect(),
    ))
}

/// HS `ppFactsList list = fsep [operator_ "[", ppFacts' list, operator_ "]"]`
/// (Theory/Model/Rule.hs:1381).
fn pp_facts_list(facts: &[LNFact]) -> Doc {
    fsep(vec![operator_("["), pp_list(facts), operator_("]")])
}

/// HS `prettyRuleRestrGen ppFact ppRestr prems acts concls restr`
/// (Theory/Model/Rule.hs:1366-1382) at `ppFact = prettyLNFact` and an empty
/// restriction list, i.e. HS `prettyRule`
/// (Theory/Model/Rule.hs:1389-1390):
/// `sep [nest 1 (ppFactsList prems), arrow, nest 1 (ppFactsList concls)]`.
///
/// HS takes the bare `-->` arrow when `null acts && null restr`; `restr` is
/// the empty list here, so the arrow turns on `acts` alone.
pub fn pretty_rule_restr_gen(prems: &[LNFact], acts: &[LNFact], concls: &[LNFact]) -> Doc {
    let arrow = if acts.is_empty() {
        operator_("-->")
    } else {
        fsep(vec![operator_("--["), pp_list(acts), operator_("]->")])
    };
    sep(vec![
        pp_facts_list(prems).nest(1),
        arrow,
        pp_facts_list(concls).nest(1),
    ])
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "rule_tests.rs"]
mod tests;
