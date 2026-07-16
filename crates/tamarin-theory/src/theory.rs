//! Top-level `Theory` data type — port of `TheoryObject.Theory` and
//! `Items.TheoryItem.TheoryItem`.
//!
//! In Haskell, `Theory sig c r p s` is parameterised over five type
//! variables (signature / cache / rule type / proof type / translation
//! element). Here we use concrete types in most slots since the Rust
//! port currently has just one rule representation; the few places
//! where polymorphism actually matters (open vs closed, diff vs trace)
//! we model with explicit enums or distinct types.

use tamarin_term::lterm::LVar;

use crate::predicate::Predicate;
use crate::restriction::ProtoRestriction;
use crate::rule::{ProtoRuleAC, ProtoRuleE};
use crate::sapic::PlainProcess;
use crate::signature::SignaturePure;

/// Restriction over the surface formula, used in `OpenTheory`. After
/// elaboration this becomes [`crate::restriction::Restriction`] which
/// carries an `LNFormula`.
pub type OpenRestriction = ProtoRestriction<tamarin_parser::ast::Formula>;

/// `OpenProtoRule = (ProtoRuleE, [ProtoRuleAC])` — a protocol rule
/// modulo E together with its precomputed AC variants. Mirrors
/// Haskell's `OpenProtoRule` newtype.
#[derive(Debug, Clone, PartialEq)]
pub struct OpenProtoRule {
    pub rule: ProtoRuleE,
    /// Pre-applied variant rules — each entry is a fully-narrowed
    /// `ProtoRuleAC` with its variant subst applied.  Populated by
    /// `ProofContext::new` (context.rs) for rules with reducible-headed
    /// sub-terms and still read by live code: `intruder_variants`
    /// asserts intruder rules carry none, and `context.rs` short-circuits
    /// (constraint/solver/context.rs:636 `if !o.variants.is_empty()`)
    /// when this field is already filled.
    /// The SplitG-based solving path uses `variant_substs` instead.
    pub variants: Vec<ProtoRuleAC>,
    /// Variant substitutions as a disjunction (`RuleACConstrs` in
    /// Haskell — `Disj LNSubstVFresh`).  The canonical rule (`rule`)
    /// represents the un-narrowed E-rule; when this disjunction is
    /// non-empty, `solve_rule_constraints` adds it as a SplitG goal
    /// in the eq-store so the variant choice is enumerated lazily
    /// per Haskell's `solveRuleConstraints` (Reduction.hs:766-774).
    /// Mirrors `RuleACConstrs = Disj LNSubstVFresh` (Rule.hs:926).
    pub variant_substs: Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    /// The abstracted form of `rule` for the SplitG path (Haskell
    /// `variantsProtoRule` returns this in the `ProtoRuleAC`'s
    /// prems/concs/acts/nvs).  Every reducible-headed sub-term in
    /// the rule's terms is replaced by a fresh `LVar`; the
    /// `variant_substs` disjunction is keyed by those fresh vars,
    /// so applying any picked variant subst yields a fully-narrowed
    /// rule.  `None` when no reducible-headed sub-terms exist
    /// (canonical rule equals raw rule).  Populated by
    /// `ProofContext::new` for every rule with reducible-headed
    /// conclusions — this is the Haskell-faithful `someRuleACInst`
    /// path (always on).
    pub abstracted_rule: Option<ProtoRuleE>,
    /// Premise indices marked as loop breakers by the dataflow
    /// analysis (`useAutoLoopBreakersAC`).  In Haskell these live on
    /// `praciLoopBreakers` of `ProtoRuleACInfo`; we attach them to
    /// the parent `OpenProtoRule` so both the E-rule and any AC
    /// variants share a single source of truth.  The field is
    /// populated by `ProofContext::new`'s `annotate_loop_breakers`
    /// pass.
    pub loop_breakers: Vec<crate::rule::PremIdx>,
}

impl OpenProtoRule {
    pub fn new(rule: ProtoRuleE) -> Self {
        OpenProtoRule {
            rule,
            variants: Vec::new(),
            variant_substs: Vec::new(),
            abstracted_rule: None,
            loop_breakers: Vec::new(),
        }
    }

    pub fn name(&self) -> &str {
        match &self.rule.info.name {
            crate::rule::ProtoRuleName::Stand(n) => n,
            crate::rule::ProtoRuleName::Fresh => "Fresh",
        }
    }
}

/// Lightweight placeholder for `Theory.Sapic.ProcessDef`, populated
/// by the SAPIC translation pass. We carry just enough to round-trip
/// through pretty-printing. Backs the not-yet-produced
/// `TranslationElement::ProcessDef` variant — kept for the HS port.
#[derive(Debug, Clone, PartialEq)]
pub struct ProcessDef {
    pub name: String,
    pub vars: Option<Vec<crate::sapic::SapicLVar>>,
    pub body: PlainProcess,
}

/// Lightweight placeholder for `Theory.Sapic.SapicFunSym` —
/// `((NoEqSym), [SapicType], SapicType)`. Backs the not-yet-produced
/// `TranslationElement::FunctionTypingInfo` variant — kept for the HS port.
#[derive(Debug, Clone, PartialEq)]
pub struct SapicFunSym {
    pub sym: tamarin_term::function_symbols::NoEqSym,
    pub arg_types: Vec<crate::sapic::SapicType>,
    pub out_type: crate::sapic::SapicType,
}

// =============================================================================
// Items
// =============================================================================

/// `(header, body)` formal comment, e.g. `text{* hello *}`.
pub type FormalComment = (String, String);

/// Free-text configuration block.
pub type ConfigBlock = String;

/// `TranslationElement` — items produced during SAPIC / accountability
/// translation that aren't first-class top-level constructs in the
/// surface syntax.
///
/// Mirrors the full HS `TranslationElement` surface. Only
/// `SignatureBuiltin`, `AccLemma`, `CaseTest`, and `ExportInfo` are
/// currently produced by elaboration; the remaining variants
/// (`Process`, `ProcessDef`, `FunctionTypingInfo`, `DiffEquivLemma`,
/// `EquivLemma`) are not yet produced — kept for the faithful HS port.
#[derive(Debug, Clone, PartialEq)]
pub enum TranslationElement {
    Process(PlainProcess),
    ProcessDef(ProcessDef),
    SignatureBuiltin(String),
    FunctionTypingInfo(SapicFunSym),
    DiffEquivLemma(PlainProcess),
    EquivLemma(PlainProcess, PlainProcess),
    AccLemma(AccLemma),
    CaseTest(CaseTest),
    /// Foreign-language export block (Tamarin's `export X: "..."`).
    ExportInfo { tag: String, body: String },
}

/// Trace quantifier on lemmas.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceQuantifier { AllTraces, ExistsTrace }

/// Attribute on a lemma.
#[derive(Debug, Clone, PartialEq)]
pub enum LemmaAttr {
    Sources,
    Reuse,
    DiffReuse,
    UseInduction,
    HideLemma(String),
    Heuristic(String),
    Output(Vec<String>),
    Left,
    Right,
    /// Free-form attribute we don't recognize.
    Hint(String),
}

/// A typed lemma. `proof` is a proof skeleton the prover may attempt
/// to discharge.
#[derive(Debug, Clone, PartialEq)]
pub struct Lemma<P = ProofSkeleton> {
    pub name: String,
    pub modulo: Option<String>,
    pub attributes: Vec<LemmaAttr>,
    pub trace_quantifier: TraceQuantifier,
    /// The lemma's formula. We store as the parser's `Formula` for now;
    /// once we have a typed formula AST we'll narrow this.
    pub formula: tamarin_parser::ast::Formula,
    pub proof: P,
    /// Verbatim source text (comments stripped) — HS `_lPlaintext`
    /// (`Items/LemmaItem.hs:50`).  Carried through elaboration for the
    /// interactive web server's Edit-lemma form; never used by `--prove`.
    pub plaintext: String,
}

// Not yet ported: diff theories (needs `ClosedDiffTheory`). `DiffLemma`,
// `DiffTheoryItem`, `Side`, and `DiffTheory` below model the HS diff-theory
// surface but are not yet produced by elaboration or consumed by the prover.
#[derive(Debug, Clone, PartialEq)]
pub struct DiffLemma<P = ProofSkeleton> {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub proof: P,
}

/// Accountability lemma — names a list of case-test identifiers and
/// the property the case-tests collectively account for.
#[derive(Debug, Clone, PartialEq)]
pub struct AccLemma {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub formula: tamarin_parser::ast::Formula,
    pub case_test_idents: Vec<String>,
}

/// Case test referenced by an accountability lemma.
#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: String,
    pub formula: tamarin_parser::ast::Formula,
}

/// Macro definition (`name(args) = body`).
#[derive(Debug, Clone, PartialEq)]
pub struct LNMacro {
    pub name: String,
    pub args: Vec<LVar>,
    pub body: tamarin_term::lterm::LNTerm,
}

/// Stored proof: either an unproven skeleton (raw text) or a
/// completed proof tree. We keep this opaque in the typed AST.
///
/// `tree` is the structured parse of `raw`, produced by
/// [`tamarin_parser::parse_proof_tree`].  Used by
/// `prove::replace_sorry_prove` (the HS `replaceSorryProver` analogue,
/// HS: Theory/Proof.hs:642-650) to walk the skeleton at proof-replay
/// time and invoke the auto-prover only at `by sorry` leaves.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofSkeleton {
    pub raw: String,
    pub tree: Option<tamarin_parser::ast::ParsedProofTree>,
}

impl ProofSkeleton {
    pub fn unproven() -> Self { ProofSkeleton { raw: String::new(), tree: None } }
}

/// `TheoryItem` — one top-level construct in a (non-diff) theory.
#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem<R = OpenProtoRule, P = ProofSkeleton, S = TranslationElement> {
    Rule(R),
    Lemma(Lemma<P>),
    Restriction(OpenRestriction),
    Text(FormalComment),
    ConfigBlock(ConfigBlock),
    Predicate(Predicate),
    Macros(Vec<LNMacro>),
    Translation(S),
}

/// `DiffTheoryItem` — one top-level construct in a diff theory.
#[derive(Debug, Clone, PartialEq)]
pub enum DiffTheoryItem<R = OpenProtoRule, R2 = OpenProtoRule, P = ProofSkeleton, P2 = ProofSkeleton> {
    DiffRule(R),
    EitherRule(Side, R2),
    DiffLemma(DiffLemma<P>),
    EitherLemma(Side, Lemma<P2>),
    EitherRestriction(Side, OpenRestriction),
    DiffMacros(Vec<LNMacro>),
    DiffText(FormalComment),
    DiffConfigBlock(ConfigBlock),
}

/// Side of a diff theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Side { LHS, RHS }

// =============================================================================
// Top-level Theory
// =============================================================================

/// `Option` block — translation/proof-driver options set per theory.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Options {
    pub trans_progress: bool,
    pub trans_report: bool,
    pub trans_reliable: bool,
    pub trans_allow_pattern_matching_in_lookup: bool,
    pub state_channel_opt: bool,
    pub asynchronous_channels: bool,
    pub compress_events: bool,
    /// Auto-generated `default` heuristic used to discharge proofs when
    /// no explicit heuristic is supplied.
    pub default_heuristic: Option<String>,
    /// Lemmas the user requested to prove via `--prove=NAME`.
    pub lemmas_to_prove: Vec<String>,
}

/// Top-level theory containing rules, lemmas, restrictions, etc.
///
/// Most operations are convenience accessors over `items`; the
/// underlying storage is order-preserving so pretty-printing matches
/// Haskell's output (which preserves source order).
#[derive(Debug, Clone, PartialEq)]
pub struct Theory<R = OpenProtoRule, P = ProofSkeleton, S = TranslationElement> {
    pub name: String,
    pub in_file: String,
    pub heuristic: Vec<String>,
    pub tactic: Vec<crate::tactic::Tactic>,
    pub signature: SignaturePure,
    pub items: Vec<TheoryItem<R, P, S>>,
    pub options: Options,
    pub is_sapic: bool,
}

impl<R, P, S> Theory<R, P, S> {
    pub fn new(name: impl Into<String>, signature: SignaturePure) -> Self {
        Theory {
            name: name.into(),
            in_file: String::new(),
            heuristic: Vec::new(),
            tactic: Vec::new(),
            signature,
            items: Vec::new(),
            options: Options::default(),
            is_sapic: false,
        }
    }

    /// Builder helper to append an item. Currently no callers inside the
    /// port (elaboration pushes to `items` directly); retained as public
    /// builder API.
    pub fn add_item(&mut self, item: TheoryItem<R, P, S>) -> &mut Self {
        self.items.push(item);
        self
    }
}

impl<R, P, S> Theory<R, P, S> {
    /// Iterate every rule item. Returns references so callers can
    /// further specialise on the rule type.
    pub fn rules(&self) -> impl Iterator<Item = &R> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r), _ => None,
        })
    }

    pub fn lemmas(&self) -> impl Iterator<Item = &Lemma<P>> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Lemma(l) => Some(l), _ => None,
        })
    }

    pub fn restrictions(&self) -> impl Iterator<Item = &OpenRestriction> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Restriction(r) => Some(r), _ => None,
        })
    }

    pub fn predicates(&self) -> impl Iterator<Item = &Predicate> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Predicate(p) => Some(p), _ => None,
        })
    }

    pub fn macros(&self) -> impl Iterator<Item = &LNMacro> {
        self.items.iter().flat_map(|i| match i {
            TheoryItem::Macros(ms) => ms.as_slice(),
            _ => &[],
        })
    }

    /// Look up a lemma by name.
    pub fn lookup_lemma(&self, name: &str) -> Option<&Lemma<P>> {
        self.lemmas().find(|l| l.name == name)
    }

}

// =============================================================================
// Diff theory
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct DiffTheory<R = OpenProtoRule, R2 = OpenProtoRule, P = ProofSkeleton, P2 = ProofSkeleton> {
    pub name: String,
    pub in_file: String,
    pub heuristic: Vec<String>,
    pub tactic: Vec<crate::tactic::Tactic>,
    pub signature: SignaturePure,
    pub items: Vec<DiffTheoryItem<R, R2, P, P2>>,
    pub options: Options,
    pub is_sapic: bool,
}

impl<R, R2, P, P2> DiffTheory<R, R2, P, P2> {
    pub fn new(name: impl Into<String>, signature: SignaturePure) -> Self {
        DiffTheory {
            name: name.into(),
            in_file: String::new(),
            heuristic: Vec::new(),
            tactic: Vec::new(),
            signature,
            items: Vec::new(),
            options: Options::default(),
            is_sapic: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_theory_has_no_items() {
        let s = SignaturePure::empty(false);
        let t: Theory = Theory::new("Foo", s);
        assert_eq!(t.name, "Foo");
        assert_eq!(t.items.len(), 0);
        assert_eq!(t.rules().count(), 0);
        assert_eq!(t.lemmas().count(), 0);
    }

    #[test]
    fn options_default_is_all_false() {
        let o = Options::default();
        assert!(!o.trans_progress);
        assert!(!o.compress_events);
        assert!(o.lemmas_to_prove.is_empty());
    }

    #[test]
    fn proof_skeleton_unproven_is_empty() {
        let p = ProofSkeleton::unproven();
        assert!(p.raw.is_empty());
    }
}
