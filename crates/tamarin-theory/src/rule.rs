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
//! - Graph/dot rendering of rule instances — in `constraint::system::dot`.
//!
//! The Haskell version uses `fclabels` lenses heavily; we replace those
//! with public fields plus accessor methods.

use tamarin_term::apply::Apply;
use tamarin_term::function_symbols::{FunSym, NdcState};
use tamarin_term::lterm::{HasFrees, LNTerm, LVar, Name};
use tamarin_term::macro_expand::LNMacro;
use tamarin_utils::color::Rgb;

use crate::apply::SystemSubst;
use crate::fact::{apply_macro_in_fact, pretty_lnfact, FactTag, LNFact, Multiplicity};
use crate::formula::{formula_frees_list, SyntacticLNFormula};
use crate::pretty_hpj::{
    above_blank, fsep, hcat, kw_rule_modulo, kw_variants, line_comment_, multi_comment,
    multi_comment_, numbered_prime, operator_, punctuate, sep, vcat, Doc,
};
use crate::sapic::SharedProcess;

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
    // HS `newVariables mRuPrems (mRuConcs ++ mRuActs)` (Theory/Model/Rule.hs:1121).
    let new_vars =
        crate::fact::new_variables(&premises, &[&conclusions[..], &actions[..]].concat());
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

/// HS `Apply LNSubst i => Apply LNSubst (Rule i)`
/// (Theory/Model/Rule.hs:308-310).  At `RuleACInst` the info is a
/// `ProtoRuleACInstInfo`, whose instance (Theory/Model/Rule.hs:517-519)
/// rewrites only the rule name, and a rule name is not a variable
/// (Theory/Model/Rule.hs:467-468) — so the info comes through untouched.
impl<I: Clone> Apply<SystemSubst<'_>> for Rule<I> {
    fn apply_changed(&self, subst: &SystemSubst<'_>) -> Option<Self> {
        let premises = self.premises.apply_changed(subst);
        let conclusions = self.conclusions.apply_changed(subst);
        let actions = self.actions.apply_changed(subst);
        let new_vars = self.new_vars.apply_changed(subst);
        if premises.is_none() && conclusions.is_none() && actions.is_none() && new_vars.is_none() {
            return None;
        }
        Some(Rule {
            info: self.info.clone(),
            premises: premises.unwrap_or_else(|| self.premises.clone()),
            conclusions: conclusions.unwrap_or_else(|| self.conclusions.clone()),
            actions: actions.unwrap_or_else(|| self.actions.clone()),
            new_vars: new_vars.unwrap_or_else(|| self.new_vars.clone()),
        })
    }
}

/// HS `frees` at `Rule ProtoRuleEInfo` (Theory/Model/Rule.hs:291-298): the
/// info's free variables, then the premises', conclusions', actions' and new
/// variables', `sortednub`bed (`frees = sortednub . freesList`,
/// Term/LTerm.hs:613-614).  `HasFrees ProtoRuleEInfo`
/// (Theory/Model/Rule.hs:491-494) folds the rule name and the attributes,
/// whose own instances yield nothing (Theory/Model/Rule.hs:462-465, :470-473),
/// so the info contributes exactly the `_restrict` formulas' free variables —
/// the ones the [`HasFrees`] impl above cannot reach.
pub fn proto_rule_e_frees(ru: &ProtoRuleE) -> Vec<LVar> {
    let mut out: Vec<LVar> = Vec::new();
    for r in &ru.info.restrictions {
        out.extend(formula_frees_list(r));
    }
    ru.for_each_free(&mut |v| out.push(*v));
    out.sort();
    out.dedup();
    out
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

/// HS `Apply s PremIdx` (Theory/Model/Rule.hs:475-476) and `Apply s ConcIdx`
/// (Theory/Model/Rule.hs:483-484): an index is not a variable, so a
/// substitution leaves it alone.  The `NodePrem` / `NodeConc` pairs reach
/// these through the pair instance (SubstVFree.hs:316-317).
impl Apply<SystemSubst<'_>> for PremIdx {
    fn apply_changed(&self, _subst: &SystemSubst<'_>) -> Option<Self> {
        None
    }
}

impl Apply<SystemSubst<'_>> for ConcIdx {
    fn apply_changed(&self, _subst: &SystemSubst<'_>) -> Option<Self> {
        None
    }
}

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
    /// Source process — for SAPIC-derived rules (HS `ruleProcess`,
    /// Theory/Model/Rule.hs:367-378).  Shared behind an `Arc` because the
    /// solver clones a rule's attributes once per rule instance it builds and
    /// a SAPIC theory's top-level rules carry the whole process tree, so an
    /// instance points at the process rather than copying it.  See
    /// [`SharedProcess`] for why the rendering travels with it.
    pub process: Option<std::sync::Arc<SharedProcess>>,
    pub ignore_deriv_checks: bool,
    pub is_sapic_rule: bool,
    /// Optional role name.
    pub role: Option<String>,
}

impl Eq for RuleAttributes {}

impl PartialOrd for RuleAttributes {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// HS derives `Ord RuleAttributes` over `ruleColor`, `ruleProcess`,
/// `ignoreDerivChecks`, `isSAPiCRule`, `role` (Theory/Model/Rule.hs:367-379),
/// which is this struct's declaration order.  HS's colour is an
/// `RGB Rational` and totally ordered; [`Rgb`] uses `f64::total_cmp` so the
/// relation remains total even for values public Rust callers construct
/// directly (including NaNs).
impl Ord for RuleAttributes {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        let color = match (&self.color, &other.color) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => a.cmp(b),
        };
        color
            .then_with(|| self.process.cmp(&other.process))
            .then_with(|| self.ignore_deriv_checks.cmp(&other.ignore_deriv_checks))
            .then_with(|| self.is_sapic_rule.cmp(&other.is_sapic_rule))
            .then_with(|| self.role.cmp(&other.role))
    }
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
///
/// HS derives `Ord ProtoRuleACInstInfo` over `_praciName`,
/// `_praciAttributes`, `_praciLoopBreakers` (Theory/Model/Rule.hs:444-449),
/// which is this struct's declaration order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
// Predicates / queries
// =============================================================================

/// HS `isDestrRule` (Model/Rule.hs:694-698): the `_crDestruct` class —
/// a `DestrRule` or the `IEquality` rule.  HS partitions the rules with
/// `isDestrRule` and `isConstrRule` (CloseRule.hs:435-436), so the
/// `IEquality` rule is classified as a destruction rule, not a protocol
/// rule.
pub fn is_destr_rule(info: &IntrRuleACInfo) -> bool {
    matches!(
        info,
        IntrRuleACInfo::DestrRule { .. } | IntrRuleACInfo::IEquality
    )
}

/// HS `isConstrRule` (Model/Rule.hs:707-714): the `_crConstruct` class —
/// a `ConstrRule`, `FreshConstr`, `PubConstr`, `NatConstr` or `Coerce`.
pub fn is_constr_rule(info: &IntrRuleACInfo) -> bool {
    matches!(
        info,
        IntrRuleACInfo::ConstrRule { .. }
            | IntrRuleACInfo::FreshConstr
            | IntrRuleACInfo::PubConstr
            | IntrRuleACInfo::NatConstr
            | IntrRuleACInfo::Coerce
    )
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
pub fn is_irecv_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::IRecv)
}
pub fn is_isend_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::ISend)
}
pub fn is_coerce_rule_info(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::Coerce)
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
pub(crate) fn intr_rule_name_string(info: &IntrRuleACInfo) -> String {
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
// Rule comparison
// =============================================================================

/// HS `equalUpToTerms` (Theory/Model/Rule.hs:958-968): the two rules share a
/// name, have the same number of premises, conclusions and actions, and the
/// facts at each position share a tag.  Terms, fact annotations and the rule
/// infos beyond the name are not compared.
pub fn equal_up_to_terms(ru_ac: &ProtoRuleAC, ru_e: &ProtoRuleE) -> bool {
    let same_tags = |xs: &[LNFact], ys: &[LNFact]| {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(f1, f2)| f1.tag == f2.tag)
    };
    ru_ac.info.name == ru_e.info.name
        && same_tags(&ru_ac.premises, &ru_e.premises)
        && same_tags(&ru_ac.conclusions, &ru_e.conclusions)
        && same_tags(&ru_ac.actions, &ru_e.actions)
}

/// HS `isTrivialProtoVariantAC` (Theory/Model/Rule.hs:789-793): the variant
/// disjunction is the identity substitution alone and the two rule bodies —
/// premises, conclusions, actions and new variables — are equal, facts
/// compared whole (tag, annotations and terms).
pub fn is_trivial_proto_variant_ac(ru_ac: &ProtoRuleAC, ru_e: &ProtoRuleE) -> bool {
    ru_ac.info.variants.len() == 1
        && ru_ac.info.variants[0].is_empty()
        && ru_ac.premises == ru_e.premises
        && ru_ac.conclusions == ru_e.conclusions
        && ru_ac.actions == ru_e.actions
        && ru_ac.new_vars == ru_e.new_vars
}

/// Set-subset check: every distinct element of `a` is `==` to some element of
/// `b`.  Mirrors Haskell's `subsetOf` (Utils/Misc.hs:90-92):
/// `subsetOf xs ys = (S.fromList xs) `S.isSubsetOf` (S.fromList ys)` —
/// `S.fromList` deduplicates BOTH arguments, so multiplicity is ignored on both
/// sides.  This is a SET subset, not a multiset/list subset.
pub(crate) fn is_subset_of(a: &[crate::fact::LNFact], b: &[crate::fact::LNFact]) -> bool {
    a.iter().all(|fa| b.iter().any(|fb| fa == fb))
}

/// `map fst (varOccurences ru)` — a rule's distinct variables, sorted.
fn rule_vars(r: &IntrRuleAC) -> Vec<LVar> {
    use tamarin_term::lterm::HasFrees;
    let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    r.for_each_free(&mut |v| {
        s.insert(*v);
    });
    s.into_iter().collect()
}

/// `rPrems ++ rConcs ++ rActs` — the fact sequence HS's `matchFacts` walks,
/// concatenated across section boundaries.
pub(crate) fn rule_facts(r: &IntrRuleAC) -> impl Iterator<Item = &LNFact> {
    r.premises
        .iter()
        .chain(r.conclusions.iter())
        .chain(r.actions.iter())
}

/// `equalRuleUpToRenamingIgnoringNames` — port of
/// `Theory.Model.Rule.equalRuleUpToRenamingIgnoringNames` (Rule.hs).
///
/// Two rules are equal up to variable renaming (their `info`/names NOT
/// considered) iff:
///   - Zipped (premises ++ concs ++ acts) have matching fact tags, and the
///     element-wise term-equalities admit a unifier that is a renaming
///     when restricted to either rule's variable occurrences (sorted).
///   - `new_vars` are also zipped into equalities (in HS, `nvs1` zipped
///     with `nvs2` start the equation list).
///
/// HS `matchFacts` only fails (`Nothing`) on a fact-TAG mismatch; the
/// `zipWith Equal`/`zip` over `(pr1++co1++ac1)`/`(pr2++co2++ac2)` and over
/// `nvs1`/`nvs2` silently TRUNCATE to the shorter list on a count or arity
/// mismatch (they never force False), and the concatenations are zipped
/// across section boundaries.  We mirror that exactly with truncating
/// `zip`s and no length guards.  (In practice every caller compares
/// variants of the same base rule, so counts/arities always agree.)
///
/// HS:
/// ```haskell
/// equalRuleUpToRenamingIgnoringNames r1 r2 = reader $ \hnd ->
///   case eqs of
///     Nothing   -> False
///     Just eqs' -> any isRenamingPerRule (unifs eqs' hnd)
/// ```
pub fn equal_rule_up_to_renaming_ignoring_names(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    r1: &IntrRuleAC,
    r2: &IntrRuleAC,
) -> bool {
    use tamarin_term::rewriting::Equal;
    use tamarin_term::subst_vfresh::LNSubstVFresh;

    // HS's `eqs` is initialised with `zipWith Equal nvs1 nvs2` (truncating),
    // then each tag-matching fact pair extends it by `zipWith Equal t1 t2`
    // (also truncating).  `matchFacts` only fails on a TAG mismatch — never
    // on a count/arity mismatch — so we use truncating `zip`s with no length
    // guards, and zip the section concatenations across boundaries.
    let mut term_eqs: Vec<Equal<LNTerm>> = Vec::new();
    for (a, b) in r1.new_vars.iter().zip(r2.new_vars.iter()) {
        term_eqs.push(Equal {
            lhs: a.clone(),
            rhs: b.clone(),
        });
    }
    for (f1, f2) in rule_facts(r1).zip(rule_facts(r2)) {
        if f1.tag != f2.tag {
            return false;
        }
        for (a, b) in f1.terms.iter().zip(f2.terms.iter()) {
            term_eqs.push(Equal {
                lhs: a.clone(),
                rhs: b.clone(),
            });
        }
    }

    // Trivial case: no constraints → identity unifier is trivially a
    // renaming (empty), so result is True.
    if term_eqs.is_empty() {
        return true;
    }

    let vars_r1 = rule_vars(r1);
    let vars_r2 = rule_vars(r2);
    let unifs = match maude.unify(&term_eqs) {
        Ok(u) => u,
        Err(_) => return false,
    };
    // For each unifier `subst`: check `isRenaming (restrictVFresh vars_r1 subst)
    //                       && isRenaming (restrictVFresh vars_r2 subst)`.
    // The unifier comes back as `Vec<(LVar, LNTerm)>` — treat as VFresh.
    for u_pairs in &unifs {
        let s_fresh = LNSubstVFresh::from_list(u_pairs.clone());
        let r1_rest = s_fresh.restrict(&vars_r1);
        let r2_rest = s_fresh.restrict(&vars_r2);
        if r1_rest.is_renaming() && r2_rest.is_renaming() {
            return true;
        }
    }
    false
}

/// `equalRuleUpToRenaming` — port of
/// `Theory.Model.Rule.equalRuleUpToRenaming` (Rule.hs):
///
/// ```haskell
/// equalRuleUpToRenaming r1@(Rule rn1 _ _ _ _) r2@(Rule rn2 _ _ _ _) =
///   if rn1 == rn2 then equalRuleUpToRenamingIgnoringNames r1 r2
///                 else return False
/// ```
pub fn equal_rule_up_to_renaming(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    r1: &IntrRuleAC,
    r2: &IntrRuleAC,
) -> bool {
    r1.info == r2.info && equal_rule_up_to_renaming_ignoring_names(maude, r1, r2)
}

/// `equalDuplicateRuleUpToRenaming` — port of
/// `Theory.Model.Rule.equalDuplicateRuleUpToRenaming` (Rule.hs):
///
/// ```haskell
/// equalDuplicateRuleUpToRenaming r1 r2 =
///     equalRuleUpToRenamingIgnoringNames r1 (r2 `renameAvoiding` r1)
/// ```
///
/// `r2` is renamed apart from `r1` first, so rules that merely share
/// variable identities do not compare equal by accident.
pub fn equal_duplicate_rule_up_to_renaming(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    r1: &IntrRuleAC,
    r2: &IntrRuleAC,
) -> bool {
    // Early reject, pure filter: `rename_avoiding` preserves fact tags and
    // section lengths, so the `matchFacts` tag test that
    // `equal_rule_up_to_renaming_ignoring_names` applies to the zipped
    // `(prems++concs++acts)` pairs evaluates identically on the un-renamed
    // rules — any tag mismatch forces that check to `false`.  This skips
    // the rule clone/rename and the Maude round trip for such pairs.
    let tags_match = rule_facts(r1)
        .zip(rule_facts(r2))
        .all(|(f1, f2)| f1.tag == f2.tag);
    if !tags_match {
        return false;
    }
    let r2_apart = tamarin_term::lterm::rename_avoiding(r2.clone(), r1);
    equal_rule_up_to_renaming_ignoring_names(maude, r1, &r2_apart)
}

/// `equalSubsetRuleUpToRenaming` — port of
/// `Theory.Model.Rule.equalSubsetRuleUpToRenaming` (Rule.hs):
///
/// ```haskell
/// equalSubsetRuleUpToRenaming r1@(Rule _ _ co1 _ _) r2@(Rule _ _ co2 _ _) = reader $ \hnd ->
///   case unifyLNFactEqs [Equal (head co2) (head co1)] `runReader` hnd of
///       []    -> False
///       subst -> any (\x -> isRenamingPerRule x && premSubst x) subst
///     where
///       premSubst sub = srpr2 `subsetOf` spr1
///         where
///           (Rule _ spr1 _ _ _, Rule _ srpr2 _ _ _) =
///               evalFreshAvoiding (appSubst sub r1 r2) (r1, r2)
///           appSubst x inst0 inst1 = do
///             s <- freshToFree x
///             return (apply s (inst0, inst1))
/// ```
///
/// True iff the head conclusions unify by a renaming-per-rule AND, after
/// converting that unifier to a free substitution (fresh vars avoiding
/// BOTH rules) and applying it to both rules, `r2`'s premises are a SET
/// subset of `r1`'s premises — i.e. the peer `r2` subsumes `r1`.
pub fn equal_subset_rule_up_to_renaming(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    r1: &IntrRuleAC,
    r2: &IntrRuleAC,
) -> bool {
    use tamarin_term::rewriting::Equal;
    use tamarin_term::subst::apply_vterm;
    use tamarin_term::subst_vfresh::LNSubstVFresh;

    // `unifyLNFactEqs [Equal (head co2) (head co1)]`.  HS's `head` `error`s on
    // a conclusion-free rule; the `false` arm here reads as "not subsumed" and
    // keeps it instead.  `minimize_intruder_rules`, the only non-test caller,
    // states the exactly-one-conclusion precondition in its contract and
    // `debug_assert!`s it, so the arm is unreachable from the production pass.
    let (co1, co2) = match (r1.conclusions.first(), r2.conclusions.first()) {
        (Some(a), Some(b)) => (a, b),
        _ => return false,
    };
    // Early rejects, pure filters:
    //  (a) mirrors the tag/term-count guards `unify_ln_fact_eqs` itself
    //      applies before calling Maude — on a mismatch it yields zero
    //      unifiers, i.e. HS `[] -> False` — evaluated here before the
    //      fact clones are built;
    //  (b) `premSubst` needs `srpr2 `subsetOf` spr1`, and substitution
    //      preserves each fact's tag and term count while fact equality
    //      implies both — so every `r2` premise must have an `r1` premise
    //      with equal tag and term count, checkable before the Maude
    //      round trip.
    if co1.tag != co2.tag || co1.terms.len() != co2.terms.len() {
        return false;
    }
    let prems_coverable = r2.premises.iter().all(|p2| {
        r1.premises
            .iter()
            .any(|p1| p1.tag == p2.tag && p1.terms.len() == p2.terms.len())
    });
    if !prems_coverable {
        return false;
    }
    let unifs = match unify_ln_fact_eqs(
        maude,
        &[Equal {
            lhs: co2.clone(),
            rhs: co1.clone(),
        }],
    ) {
        Ok(u) => u,
        Err(_) => return false,
    };
    if unifs.is_empty() {
        return false;
    }

    let vars_r1 = rule_vars(r1);
    let vars_r2 = rule_vars(r2);

    // `evalFreshAvoiding ... (r1, r2)` — fresh idx allocation starts above
    // the maximum index occurring in either rule.
    let max_idx = vars_r1.iter().chain(vars_r2.iter()).map(|v| v.idx).max();

    for u_pairs in &unifs {
        let s_fresh = LNSubstVFresh::from_list(u_pairs.clone());
        // `isRenamingPerRule`.
        if !(s_fresh.restrict(&vars_r1).is_renaming() && s_fresh.restrict(&vars_r2).is_renaming()) {
            continue;
        }
        // `premSubst`: freshToFree the unifier avoiding (r1, r2), apply to
        // both rules' premises, then `srpr2 `subsetOf` spr1`.
        let mut counter = max_idx.map(|m| m + 1).unwrap_or(0);
        let sigma = s_fresh.fresh_to_free_avoiding(|n| {
            let b = counter;
            counter += n;
            b
        });
        let subst_prems = |fs: &[LNFact]| -> Vec<LNFact> {
            fs.iter()
                .map(|f| {
                    // subst rebuild — frees can change; recompute the bloom.
                    let terms: Vec<LNTerm> = f
                        .terms
                        .iter()
                        .map(|t| apply_vterm(&sigma, t.clone()))
                        .collect();
                    LNFact::fresh_annotated(f.tag, f.annotations.clone(), terms)
                })
                .collect()
        };
        let spr1 = subst_prems(&r1.premises);
        let srpr2 = subst_prems(&r2.premises);
        if is_subset_of(&srpr2, &spr1) {
            return true;
        }
    }
    false
}

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

/// HS `prettyProtoRuleName` (Theory/Model/Rule.hs:1287-1290): the reserved
/// `Fresh` rule prints under its own name, a user rule under
/// [`prefix_if_reserved`].
pub(crate) fn pretty_proto_rule_name(name: &ProtoRuleName) -> Doc {
    match name {
        ProtoRuleName::Fresh => Doc::text("Fresh"),
        ProtoRuleName::Stand(n) => Doc::text(prefix_if_reserved(n)),
    }
}

/// HS `getRuleNameDiff` on a protocol rule (Theory/Model/Rule.hs:812-823):
/// `"Proto"` before the rule name, with the reserved `Fresh` rule spelled
/// `FreshRule`.
fn proto_rule_name_diff(name: &ProtoRuleName) -> String {
    match name {
        ProtoRuleName::Fresh => "ProtoFreshRule".to_string(),
        ProtoRuleName::Stand(n) => format!("Proto{}", n),
    }
}

/// HS `prettyRuleAttribute` (Theory/Model/Rule.hs:1313-1328): the record's set
/// fields as `fsep $ punctuate comma $ catMaybes [color, process,
/// no_derivcheck, issapicrule, role]`.  A `Nothing` field and a `False` flag
/// contribute nothing.
pub fn pretty_rule_attribute(attr: &RuleAttributes) -> Doc {
    let mut parts: Vec<Doc> = Vec::new();
    if let Some(c) = attr.color {
        parts.push(Doc::text("color=").beside(Doc::text(tamarin_utils::color::rgb_to_hex(c))));
    }
    if let Some(proc) = &attr.process {
        // HS `ppProcess p = text "process=" <> text ("\"" ++
        // prettySapicTopLevel' f p ++ "\"")` (Theory/Model/Rule.hs:1324-1327),
        // whose local `f` renders an embedded MSR block through
        // `prettyRuleRestr`.
        parts.push(Doc::text("process=").beside(Doc::text(format!(
            "\"{}\"",
            crate::pretty_sapic::pretty_sapic_top_level_attr(proc)
        ))));
    }
    if attr.ignore_deriv_checks {
        parts.push(Doc::text("no_derivcheck"));
    }
    if attr.is_sapic_rule {
        parts.push(Doc::text("issapicrule"));
    }
    if let Some(r) = &attr.role {
        parts.push(
            Doc::text("role='")
                .beside(Doc::text(r.clone()))
                .beside(Doc::text("'")),
        );
    }
    fsep(punctuate(Doc::char(','), parts))
}

/// HS `prettyRuleAttributes` (Theory/Model/Rule.hs:1330-1334): the attribute
/// list in brackets, or nothing at all when the record equals `mempty`.
pub fn pretty_rule_attributes(attr: &RuleAttributes) -> Doc {
    if *attr == RuleAttributes::empty() {
        Doc::empty()
    } else {
        hcat(vec![
            Doc::text("["),
            pretty_rule_attribute(attr),
            Doc::text("]"),
        ])
    }
}

/// HS `prettyNamedRule prefix ppInfo ru` (Theory/Model/Rule.hs:1393-1405):
///
/// ```text
/// prefix <-> prettyRuleName ru <> prettyRuleAttributes ru <> colon $-$
/// nest 2 (prettyRule prems acts concls) $-$
/// nest 2 (ppInfo (rInfo ru))
/// ```
///
/// `acts` drops the diff annotation `Diff<getRuleNameDiff ru>()` — a nullary
/// linear protocol fact with no annotations — that `addDiffLabel` attaches in
/// diff mode (Theory/Model/Rule.hs:1404).  `info` is the already-rendered
/// `ppInfo` result; the empty doc there leaves the rule at its body.
fn pretty_named_rule<I>(
    prefix: Doc,
    name: &ProtoRuleName,
    attributes: &RuleAttributes,
    ru: &Rule<I>,
    info: Doc,
) -> Doc {
    let diff_label = format!("Diff{}", proto_rule_name_diff(name));
    let is_diff_annotation = |fa: &LNFact| {
        matches!(&fa.tag, FactTag::Proto(Multiplicity::Linear, n, 0) if *n == diff_label)
            && fa.annotations.is_empty()
            && fa.terms.is_empty()
    };
    let filtered: Option<Vec<LNFact>> = ru.actions.iter().any(&is_diff_annotation).then(|| {
        ru.actions
            .iter()
            .filter(|fa| !is_diff_annotation(fa))
            .cloned()
            .collect()
    });
    let acts: &[LNFact] = filtered.as_deref().unwrap_or(&ru.actions);
    prefix
        .beside_sp(pretty_proto_rule_name(name))
        .beside(pretty_rule_attributes(attributes))
        .beside(Doc::char(':'))
        .above_g(pretty_rule_restr_gen(&ru.premises, acts, &ru.conclusions).nest(2))
        .above_g(info.nest(2))
}

/// HS `prettyLoopBreakers` (Theory/Model/Rule.hs:1418-1424): a `// loop
/// breaker: [i]` line comment, plural for more than one, nothing when there
/// are none.  Haskell `show` on `[Int]` puts no space after the commas.
pub fn pretty_loop_breakers(breakers: &[PremIdx]) -> Doc {
    if breakers.is_empty() {
        return Doc::empty();
    }
    let plural = if breakers.len() == 1 { "" } else { "s" };
    let idxs: Vec<String> = breakers.iter().map(|b| b.0.to_string()).collect();
    line_comment_(&format!("loop breaker{}: [{}]", plural, idxs.join(",")))
}

/// HS `prettyDisjLNSubstsVFresh`'s `ppConj`
/// (Term/Substitution/SubstVFresh.hs:223-229): one substitution as a `vcat` of
/// `var $$ nest 6 ("=" <-> term)` bindings.
///
/// The `text ". " <>` of the enclosing `numbered'` is a BESIDE onto this
/// multi-line doc, so HughesPJ measures the ribbon of the wrapped lines from
/// the number's column.  Keep the whole conjunction one doc: rendering each
/// binding standalone measures from the variable's column instead and moves
/// the wrap point of terms close to the boundary (an 11-tuple `<x.16, …,
/// x.26>` in pkcs11-templates `cannot_obtain_key`).
pub(crate) fn pretty_subst_vfresh_conj(subst: &tamarin_term::subst_vfresh::LNSubstVFresh) -> Doc {
    let eqs: Vec<Doc> = subst
        .to_list()
        .iter()
        .map(|(v, t)| {
            // HS `prettyEq (a,b) = prettyNTerm (Var a) $$ nest 6 (text "=" <->
            // prettyNTerm b)` — the `=` is a PLAIN `text`, so it carries no
            // `hl_operator` span.
            let mut var = String::new();
            tamarin_term::pretty::pp_lvar(v, &mut var);
            let rhs = Doc::text("=")
                .beside_sp(tamarin_term::pretty::pretty_nterm(t))
                .nest(6);
            Doc::text(var).above(rhs)
        })
        .collect();
    vcat(eqs)
}

/// HS `prettyDisjLNSubstsVFresh` (Term/Substitution/SubstVFresh.hs:223-229):
/// the disjunction as `numbered'` over the per-substitution conjunctions.
fn pretty_disj_ln_substs_vfresh(substs: &[tamarin_term::subst_vfresh::LNSubstVFresh]) -> Doc {
    numbered_prime(substs.iter().map(pretty_subst_vfresh_conj).collect())
}

/// HS `prettyProtoRuleACInfo` (Theory/Model/Rule.hs:1407-1413): the variant
/// disjunction under a `variants (modulo AC)` keyword, then the loop
/// breakers.  A disjunction holding nothing but the identity substitution
/// prints neither keyword nor block.
fn pretty_proto_rule_ac_info(info: &ProtoRuleACInfo) -> Doc {
    let variants = if info.variants.len() == 1 && info.variants[0].is_empty() {
        Doc::empty()
    } else {
        crate::pretty_hpj::kw_modulo("variants", "AC")
            .above_g(pretty_disj_ln_substs_vfresh(&info.variants))
    };
    variants.above_g(pretty_loop_breakers(&info.loop_breakers))
}

/// HS `prettyProtoRuleE` (Theory/Model/Rule.hs:1434-1435): the rule under the
/// `rule (modulo E)` prefix, with no trailing info block.
pub fn pretty_proto_rule_e(ru: &ProtoRuleE) -> Doc {
    pretty_named_rule(
        kw_rule_modulo("E"),
        &ru.info.name,
        &ru.info.attributes,
        ru,
        Doc::empty(),
    )
}

/// HS `prettyProtoRuleACasE` (Theory/Model/Rule.hs:1442-1444): an AC rule
/// printed under the `rule (modulo E)` prefix, its variant disjunction and
/// loop breakers left out.
pub fn pretty_proto_rule_ac_as_e(ru: &ProtoRuleAC) -> Doc {
    pretty_named_rule(
        kw_rule_modulo("E"),
        &ru.info.name,
        &ru.info.attributes,
        ru,
        Doc::empty(),
    )
}

/// HS `prettyProtoRuleAC` (Theory/Model/Rule.hs:1458-1459): the rule under the
/// `rule (modulo AC)` prefix followed by its `ProtoRuleACInfo`.
pub fn pretty_proto_rule_ac(ru: &ProtoRuleAC) -> Doc {
    pretty_named_rule(
        kw_rule_modulo("AC"),
        &ru.info.name,
        &ru.info.attributes,
        ru,
        pretty_proto_rule_ac_info(&ru.info),
    )
}

/// HS `multiComment_ ["has exactly the trivial AC variant"]`, the annotation
/// both closed-rule printers put under a rule whose AC form says nothing the
/// E form does not (ClosedTheory.hs:335-339, OpenTheory.hs:833-834).
fn trivial_ac_variant_comment() -> Doc {
    multi_comment_(&["has exactly the trivial AC variant"])
}

/// HS `prettyClosedProtoRule` (ClosedTheory.hs:331-366#prettyClosedProtoRule):
/// four shapes, keyed on the AC rule's relation to the E rule.  A trivial AC
/// variant prints the E rule with the annotation; an AC rule that carries
/// added actions prints as if it were modulo E; an AC rule that only narrowed
/// the terms prints the E rule with the AC rule quoted in a comment; and a
/// rule whose AC name differs — one variant of a rule split into several —
/// prints as modulo AC with the E rule quoted under it.
pub fn pretty_closed_proto_rule(ru_ac: &ProtoRuleAC, ru_e: &ProtoRuleE) -> Doc {
    let breakers = || pretty_loop_breakers(&ru_ac.info.loop_breakers);
    if is_trivial_proto_variant_ac(ru_ac, ru_e) {
        above_blank(
            pretty_proto_rule_e(ru_e),
            breakers().above_g(trivial_ac_variant_comment()).nest(2),
        )
    } else if ru_ac.info.name == ru_e.info.name {
        if !equal_up_to_terms(ru_ac, ru_e) {
            above_blank(
                pretty_proto_rule_ac_as_e(ru_ac),
                breakers().above_g(trivial_ac_variant_comment()).nest(2),
            )
        } else {
            above_blank(
                pretty_proto_rule_e(ru_e),
                breakers()
                    .above_g(multi_comment(pretty_proto_rule_ac(ru_ac)))
                    .nest(2),
            )
        }
    } else {
        above_blank(
            pretty_proto_rule_ac(ru_ac),
            breakers()
                .above_g(multi_comment_(&["variant of"]))
                .above_g(multi_comment(pretty_proto_rule_e(ru_e)))
                .nest(3),
        )
    }
}

/// HS `ppList` (OpenTheory.hs:822-824): the AC rules of a merged rule item,
/// one `prettyProtoRuleAC` each, separated by a `,` line.
fn pretty_proto_rule_ac_list(variants: &[ProtoRuleAC]) -> Doc {
    match variants {
        [] => Doc::empty(),
        [x] => pretty_proto_rule_ac(x),
        [x, rest @ ..] => pretty_proto_rule_ac(x)
            .above_g(Doc::char(','))
            .above_g(pretty_proto_rule_ac_list(rest)),
    }
}

/// HS `prettyOpenProtoRule`
/// (OpenTheory.hs:814-824#prettyOpenProtoRule): the printer of an open
/// theory's rule item.  A rule with no manual `variants (modulo AC)` block is
/// its E rule; one manual variant stands in for the E rule and prints under
/// the `rule (modulo E)` prefix; several are listed under a `variants` block
/// below the E rule.
pub fn pretty_open_proto_rule(r: &crate::theory::OpenProtoRule) -> Doc {
    let variants = crate::theory::manual_rule_variants(r);
    match variants.as_slice() {
        [] => pretty_proto_rule_e(r.rule_e()),
        [ru_ac] => pretty_proto_rule_ac_as_e(ru_ac),
        vs => pretty_proto_rule_e(r.rule_e()).above_g(
            kw_variants()
                .above_g(pretty_proto_rule_ac_list(vs).nest(1))
                .nest(1),
        ),
    }
}

/// HS `prettyOpenProtoRuleAsClosedRule`
/// (OpenTheory.hs:826-850#prettyOpenProtoRuleAsClosedRule): the printer
/// `prettyClosedTheory` switches the whole theory to when some rule item
/// carries an AC rule of its own.  With no AC rule the loop breakers are
/// unavailable and only the annotation is printed; with one the AC rule
/// stands in for the E rule; with several the E rule is followed by a
/// `variants` block listing them.
pub fn pretty_open_proto_rule_as_closed_rule(r: &crate::theory::MergedProtoRule) -> Doc {
    match r.rule_ac.as_slice() {
        [] => above_blank(
            pretty_proto_rule_e(&r.rule_e),
            Doc::empty().above_g(trivial_ac_variant_comment()).nest(2),
        ),
        [ru_ac] => above_blank(
            pretty_proto_rule_ac_as_e(ru_ac),
            pretty_loop_breakers(&ru_ac.info.loop_breakers)
                .above_g(if ru_ac.info.variants.len() == 1 {
                    trivial_ac_variant_comment()
                } else {
                    multi_comment(pretty_proto_rule_ac(ru_ac))
                })
                .nest(2),
        ),
        variants => pretty_proto_rule_e(&r.rule_e).above_g(
            kw_variants()
                .above_g(pretty_proto_rule_ac_list(variants).nest(1))
                .nest(1),
        ),
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
#[path = "rule_tests.rs"]
mod tests;
