// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Top-level `Theory` data type — port of `TheoryObject.Theory` and
//! `Items.TheoryItem.TheoryItem`.
//!
//! In Haskell, `Theory sig c r p s` is parameterised over five type
//! variables (signature / cache / rule type / proof type / translation
//! element). Here we use concrete types in most slots since the Rust
//! port currently has just one rule representation; the few places
//! where polymorphism actually matters (open vs closed, diff vs trace)
//! we model with explicit enums or distinct types.

use crate::formula::{LNFormula, SyntacticLNFormula};
use crate::predicate::Predicate;
use crate::restriction::Restriction;
use crate::rule::ProtoRuleE;
use crate::sapic::PlainProcess;
use crate::signature::SignaturePure;

/// A protocol rule modulo E with its variant machinery.  Mirrors the
/// `ProtoRuleE` half of HS's `OpenProtoRule = (ProtoRuleE, [ProtoRuleAC])`;
/// the port never materialises the `[ProtoRuleAC]` half — variants are
/// enumerated lazily through `variant_substs` + `abstracted_rule` (the
/// SplitG route).
#[derive(Debug, Clone, PartialEq)]
pub struct OpenProtoRule {
    pub rule: ProtoRuleE,
    /// Variant substitutions as a disjunction (`RuleACConstrs` in
    /// Haskell — `Disj LNSubstVFresh`).  The canonical rule (`rule`)
    /// represents the un-narrowed E-rule; when this disjunction is
    /// non-empty, `solve_rule_constraints` adds it as a SplitG goal
    /// in the eq-store so the variant choice is enumerated lazily
    /// per Haskell's `solveRuleConstraints` (Reduction.hs:789-797).
    /// Mirrors `RuleACConstrs = Disj LNSubstVFresh`
    /// (Theory/Model/Rule.hs:1009).
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
    /// This rule is a product of the `--auto-sources` variant unfold
    /// (`unfoldRuleVariants`, lib/theory/src/Rule.hs:63-79): `rule` holds one
    /// AC variant named `<orig>___VARIANT_<i>` while HS's `cprRuleE` half
    /// keeps the ORIGINAL rule, so the two names differ and
    /// `equalUpToTerms` (Theory/Model/Rule.hs:960-968) is False on the name
    /// alone — `openProtoRule` (lib/theory/src/Rule.hs:52-59) then always
    /// yields its non-empty `[ruAC]` branch for such a rule.  The renderer
    /// reads this flag where it mirrors that branch choice
    /// (`pretty_theory::rule_open_ac_nonempty`).
    pub unfolded_variant: bool,
    /// HS's `cprRuleE` half (`ClosedProtoRule`, Items/RuleItem.hs:56-59),
    /// stored only where it differs from `rule`: **`None` iff `rule` IS that
    /// half**.  Three steps drive them apart.  `elaborate_items` applies the
    /// theory's macros to `rule` alone, because `closeProtoRule` narrows
    /// `applyMacroInRule macros ruE` and keeps the unexpanded `ruE`
    /// (lib/theory/src/Rule.hs:82-86).  `addActionClosedProtoRule` adds AUTO
    /// actions to `cprRuleAC` only (lib/theory/src/Rule.hs:95-99).
    /// `unfoldRuleVariants` carries the ORIGINAL rule as every variant's
    /// `cprRuleE` (lib/theory/src/Rule.hs:63-79, see line 76).  Consumers of
    /// HS's `getProtoRuleEs` (`S.toList . S.fromList . map oprRuleE`,
    /// ClosedTheory.hs:87-89) — partial evaluation — must read this half
    /// through [`OpenProtoRule::rule_e`]: it is macro-unexpanded, carries no
    /// AUTO actions, and the Set round-trip collapses the per-variant
    /// duplicates.
    pub rule_e: Option<Box<ProtoRuleE>>,
    /// HS's `_oprRuleAC` (Items/RuleItem.hs:34-36): the `variants (modulo
    /// AC)` blocks the source writes out, parsed by `protoRuleAC` and
    /// collected by `protoRule` (Theory/Text/Parser/Rule.hs:126-135, see line
    /// 134).  A rule that declares them is closed by mapping `ClosedProtoRule
    /// ruE` over the list rather than by computing variants, so neither the
    /// macros nor Maude ever touch them (lib/theory/src/Rule.hs:82-86, see
    /// line 86).  HS types them `ProtoRuleAC`; the parser fills that info's
    /// variant and loop-breaker slots with `Disj [emptySubstVFresh]` and `[]`
    /// (`protoRuleACInfo`, Theory/Text/Parser/Rule.hs:138-143, see line 142),
    /// so a [`ProtoRuleE`] holds everything a parsed block carries.
    pub rule_ac: Vec<ProtoRuleE>,
}

impl OpenProtoRule {
    pub fn new(rule: ProtoRuleE) -> Self {
        OpenProtoRule {
            rule,
            variant_substs: Vec::new(),
            abstracted_rule: None,
            loop_breakers: Vec::new(),
            unfolded_variant: false,
            rule_e: None,
            rule_ac: Vec::new(),
        }
    }

    /// HS's `cprRuleE` — the rule as the source writes it, before the macros
    /// and before an `--auto-sources` close annotates or unfolds it.
    /// `getProtoRuleEs` (ClosedTheory.hs:87-89) reads exactly this.
    pub fn rule_e(&self) -> &ProtoRuleE {
        self.rule_e.as_deref().unwrap_or(&self.rule)
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
/// `(UserDefinedSym, [SapicType], SapicType)` (Theory/Sapic/Term.hs:78), so a
/// typing declaration can name a free OR a user-defined AC symbol. Backs the
/// not-yet-produced `TranslationElement::FunctionTypingInfo` variant — kept for
/// the HS port.
#[derive(Debug, Clone, PartialEq)]
pub struct SapicFunSym {
    pub sym: tamarin_term::function_symbols::UserDefinedSym,
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
    ExportInfo {
        tag: String,
        body: String,
    },
}

/// Trace quantifier on lemmas.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceQuantifier {
    AllTraces,
    ExistsTrace,
}

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
    /// `_lFormula` (Items/LemmaItem.hs:53) — the macro- and predicate-expanded
    /// formula, which the solver converts to a guarded formula and the printer
    /// shows in the `guarded formula characterizing ...` block.
    pub formula: LNFormula,
    /// `_lOriginalFormula` (Items/LemmaItem.hs:54) — the same formula before
    /// macro application, which the printer quotes on the header line.  HS's
    /// `applyMacroInLemma` fills it for every lemma of a closed theory, macros
    /// or none (lib/theory/src/Lemma.hs:83-88, CloseRule.hs:85).
    pub original_formula: Option<LNFormula>,
    pub proof: P,
    /// Verbatim source text (comments stripped) — HS `_lPlaintext`
    /// (`Items/LemmaItem.hs:48-58, see line 50`).  Carried through elaboration for the
    /// interactive web server's Edit-lemma form; never used by `--prove`.
    pub plaintext: String,
}

/// HS `applyMacroInLemma` (lib/theory/src/Lemma.hs:83-88): the theory's macros
/// applied to the formula, with the formula as it stood recorded as the
/// original one.  HS runs it over every lemma of a closed theory
/// (`closeTheoryItem`, CloseRule.hs:85), macros or none, so
/// `original_formula` ends up filled either way.
pub fn apply_macro_in_lemma<P>(macros: &[LNMacro], lemma: Lemma<P>) -> Lemma<P> {
    let original_formula = lemma.formula.clone();
    Lemma {
        formula: crate::formula::apply_macro_in_formula(macros, lemma.formula),
        original_formula: Some(original_formula),
        ..lemma
    }
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
    /// HS `_aFormula` (Items/AccLemmaItem.hs:32).  The `Pred` sugar stays:
    /// `liftedAddAccLemma` adds the lemma verbatim
    /// (Theory/Text/Parser.hs:153-157), with neither predicate nor macro
    /// expansion.
    pub formula: SyntacticLNFormula,
    pub case_test_idents: Vec<String>,
}

/// Case test referenced by an accountability lemma.
#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: String,
    /// HS `_cFormula` (Items/CaseTestItem.hs:27).  The `Pred` sugar stays:
    /// `liftedAddCaseTest` adds the case test verbatim
    /// (Theory/Text/Parser.hs:159-163), and `caseTestToPredicate` strips it
    /// with `toLNFormula` at accountability-translation time
    /// (Items/CaseTestItem.hs:33-37).
    pub formula: SyntacticLNFormula,
}

/// HS `LNMacro` (Term/Macro.hs:24): one `macros:` declaration, `name(params)
/// = body`.
pub use tamarin_term::macro_expand::LNMacro;

/// One node of a lemma's stored proof — HS `ProofSkeleton = Proof ()`, i.e.
/// `LTree CaseName (ProofStep ())` (Theory/ProofSkeleton.hs:30,
/// Theory/Proof.hs:187-192,238).
///
/// `cases` keeps the source order of the `case` blocks; the printer sorts by
/// name (HS stores them in an `M.fromList`, Theory/Text/Parser/Proof.hs:113)
/// and replay looks each case up by name.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofTree {
    pub method: crate::constraint::solver::proof_method::ProofMethod,
    pub cases: Vec<(String, ProofTree)>,
}

/// A lemma's stored proof.  `None` is a lemma written without one, which HS
/// gives the one-node `unproven ()` skeleton
/// (Theory/ProofSkeleton.hs:59-61); `prove::replace_sorry_prove` (HS
/// `replaceSorryProver`, Theory/Proof.hs:641-650) walks the tree at
/// proof-replay time and invokes the auto-prover only at `sorry` leaves.
pub type ProofSkeleton = Option<ProofTree>;

/// `TheoryItem` — one top-level construct in a (non-diff) theory.
#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem<R = OpenProtoRule, P = ProofSkeleton, S = TranslationElement> {
    Rule(R),
    Lemma(Lemma<P>),
    Restriction(Restriction),
    Text(FormalComment),
    ConfigBlock(ConfigBlock),
    Predicate(Predicate),
    Macros(Vec<LNMacro>),
    Translation(S),
}

/// `DiffTheoryItem` — one top-level construct in a diff theory.
#[derive(Debug, Clone, PartialEq)]
pub enum DiffTheoryItem<
    R = OpenProtoRule,
    R2 = OpenProtoRule,
    P = ProofSkeleton,
    P2 = ProofSkeleton,
> {
    DiffRule(R),
    EitherRule(Side, R2),
    DiffLemma(DiffLemma<P>),
    EitherLemma(Side, Lemma<P2>),
    EitherRestriction(Side, Restriction),
    DiffMacros(Vec<LNMacro>),
    DiffText(FormalComment),
    DiffConfigBlock(ConfigBlock),
}

/// Side of a diff theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Side {
    LHS,
    RHS,
}

// =============================================================================
// Top-level Theory
// =============================================================================

/// `Option` block — translation/proof-driver options set per theory.
#[derive(Debug, Clone, PartialEq)]
pub struct Options {
    pub trans_progress: bool,
    pub trans_report: bool,
    pub trans_reliable: bool,
    pub trans_allow_pattern_matching_in_lookup: bool,
    pub state_channel_opt: bool,
    pub asynchronous_channels: bool,
    pub compress_events: bool,
    /// HS `_deductionChainCheck`: run the no-deconstruction-chain (NDC)
    /// check at theory load. Enabled by default; `--no-ndc` disables it.
    /// Consulted by the load paths that run the once-per-theory
    /// `close_rule::check_close_intr_rule` pass.
    pub deduction_chain_check: bool,
    /// HS `_lemmasToProve`: lemma names the user requested via `--prove=NAME`.
    pub lemmas_to_prove: Vec<String>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            trans_progress: false,
            trans_report: false,
            trans_reliable: false,
            trans_allow_pattern_matching_in_lookup: false,
            state_channel_opt: false,
            asynchronous_channels: false,
            compress_events: false,
            deduction_chain_check: true,
            lemmas_to_prove: Vec::new(),
        }
    }
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
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
    }

    pub fn lemmas(&self) -> impl Iterator<Item = &Lemma<P>> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Lemma(l) => Some(l),
            _ => None,
        })
    }

    pub fn restrictions(&self) -> impl Iterator<Item = &Restriction> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Restriction(r) => Some(r),
            _ => None,
        })
    }

    pub fn predicates(&self) -> impl Iterator<Item = &Predicate> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Predicate(p) => Some(p),
            _ => None,
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

    /// Look up a restriction by name (HS `lookupRestriction`,
    /// TheoryObject.hs:671-672).
    ///
    /// The closed printer's restriction renderer resolves the parsed item to
    /// its elaborated twin through this (`pretty_theory::render_parsed_restriction`),
    /// and [`Theory::add_restriction`] uses it as the duplicate-name guard.
    pub fn lookup_restriction(&self, name: &str) -> Option<&Restriction> {
        self.restrictions().find(|r| r.name == name)
    }

    /// HS `addRules` (TheoryObject.hs:470-471): append rule items, in order.
    ///
    /// Intentionally retained: faithful mirror of HS `addRules`
    /// (TheoryObject.hs:470-471); no caller yet.
    pub fn add_rules(&mut self, rules: impl IntoIterator<Item = R>) -> &mut Self {
        self.items.extend(rules.into_iter().map(TheoryItem::Rule));
        self
    }

    /// HS `addLemma` (TheoryObject.hs:462-465): append the lemma unless one of
    /// that name is already present.  Returns whether it was added.
    ///
    /// HS returns `Maybe (Theory ...)`; the `bool` here is that `Just`/`Nothing`
    /// distinction on an in-place update.
    ///
    /// Intentionally retained: faithful mirror of HS `addLemma`
    /// (TheoryObject.hs:462-465); its only caller is the equally caller-less
    /// [`Theory::add_lemmas`].
    pub fn add_lemma(&mut self, l: Lemma<P>) -> bool {
        if self.lookup_lemma(&l.name).is_some() {
            return false;
        }
        self.items.push(TheoryItem::Lemma(l));
        true
    }

    /// HS `addLemmas` (TheoryObject.hs:467-468): add each lemma in turn.  HS
    /// folds `addLemma` through a `Maybe` and `fromJust`s it, so a name clash
    /// leaves the theory as it was (and, mid-list, is a hard error); here a
    /// clashing lemma is simply skipped.
    ///
    /// Intentionally retained: faithful mirror of HS `addLemmas`
    /// (TheoryObject.hs:467-468); no caller yet.
    pub fn add_lemmas(&mut self, lemmas: impl IntoIterator<Item = Lemma<P>>) -> &mut Self {
        for l in lemmas {
            self.add_lemma(l);
        }
        self
    }

    /// HS `addRestriction` (TheoryObject.hs:453-456): append the restriction
    /// unless one of that name is already present.  Returns whether it was
    /// added.
    ///
    /// Intentionally retained: faithful mirror of HS `addRestriction`
    /// (TheoryObject.hs:453-456); its only caller is the equally caller-less
    /// [`Theory::add_restrictions`].
    pub fn add_restriction(&mut self, r: Restriction) -> bool {
        if self.lookup_restriction(&r.name).is_some() {
            return false;
        }
        self.items.push(TheoryItem::Restriction(r));
        true
    }

    /// HS `addRestrictions` (TheoryObject.hs:458-459): add each restriction in
    /// turn, skipping name clashes (see [`Theory::add_lemmas`]).
    ///
    /// Intentionally retained: faithful mirror of HS `addRestrictions`
    /// (TheoryObject.hs:458-459); no caller yet.
    pub fn add_restrictions(
        &mut self,
        restrictions: impl IntoIterator<Item = Restriction>,
    ) -> &mut Self {
        for r in restrictions {
            self.add_restriction(r);
        }
        self
    }
}

// =============================================================================
// Diff theory
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct DiffTheory<R = OpenProtoRule, R2 = OpenProtoRule, P = ProofSkeleton, P2 = ProofSkeleton>
{
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

    /// A theory over simple stand-in type parameters.  The accessors are
    /// generic over `R`/`P`/`S`.  The item payloads therefore do not have to
    /// be real rules or proofs.
    type TestTheory = Theory<i32, (), char>;

    fn lemma(name: &str) -> Lemma<()> {
        Lemma {
            name: name.to_string(),
            modulo: None,
            attributes: Vec::new(),
            trace_quantifier: TraceQuantifier::AllTraces,
            formula: crate::formula::ProtoFormula::ltrue(),
            original_formula: None,
            proof: (),
            plaintext: String::new(),
        }
    }

    fn restriction(name: &str) -> Restriction {
        Restriction {
            name: name.to_string(),
            formula: crate::formula::ProtoFormula::ltrue(),
            original_formula: None,
        }
    }

    fn lnmacro(name: &str) -> LNMacro {
        LNMacro::new(
            name.as_bytes().to_vec(),
            Vec::new(),
            tamarin_term::vterm::var_term(tamarin_term::lterm::LVar::new(
                "x",
                tamarin_term::lterm::LSort::Msg,
                0,
            )),
        )
    }

    /// Every accessor is a `filter_map` over one `TheoryItem` arm.  A
    /// copy-pasted arm makes one accessor return another accessor's items,
    /// and nothing reports the mistake.  The `items` vector below holds one
    /// item of each kind and keeps their order.  Each accessor must therefore
    /// return exactly its own items.  `macros()` must also flatten its item's
    /// list and not count the item.
    #[test]
    fn accessors_select_only_their_own_item_kind() {
        let mut t: TestTheory = Theory::new("Foo", SignaturePure::empty(false));
        assert_eq!(t.name, "Foo");
        assert_eq!(t.items.len(), 0);
        assert_eq!(t.rules().count(), 0);

        t.add_item(TheoryItem::Rule(7))
            .add_item(TheoryItem::Lemma(lemma("L")))
            .add_item(TheoryItem::Restriction(restriction("R")))
            .add_item(TheoryItem::Macros(vec![lnmacro("m1"), lnmacro("m2")]))
            .add_item(TheoryItem::Translation('t'));

        assert_eq!(t.rules().copied().collect::<Vec<_>>(), vec![7]);
        assert_eq!(
            t.lemmas().map(|l| l.name.as_str()).collect::<Vec<_>>(),
            vec!["L"]
        );
        assert_eq!(
            t.restrictions()
                .map(|r| r.name.as_str())
                .collect::<Vec<_>>(),
            vec!["R"]
        );
        assert_eq!(t.predicates().count(), 0);
        assert_eq!(
            t.macros().map(|m| m.name.as_slice()).collect::<Vec<_>>(),
            vec![b"m1".as_slice(), b"m2".as_slice()],
            "`macros()` flattens the item's macro list"
        );
        assert_eq!(t.lookup_lemma("L").map(|l| l.name.as_str()), Some("L"));
        assert_eq!(t.lookup_lemma("R"), None, "a restriction is not a lemma");
        assert_eq!(
            t.lookup_restriction("R").map(|r| r.name.as_str()),
            Some("R")
        );
        assert_eq!(t.lookup_restriction("L"), None);
    }

    /// HS `addLemma` and `addRestriction` (TheoryObject.hs:453-465) refuse a
    /// name that is already present, and they report the refusal.  `addRules`
    /// has no such check.  It always appends.
    #[test]
    fn add_lemma_and_add_restriction_refuse_a_duplicate_name() {
        let mut t: TestTheory = Theory::new("Foo", SignaturePure::empty(false));
        assert!(t.add_lemma(lemma("L")));
        assert!(!t.add_lemma(lemma("L")), "second `L` must be refused");
        assert!(t.add_lemma(lemma("L2")));
        assert!(t.add_restriction(restriction("R")));
        assert!(!t.add_restriction(restriction("R")));

        // `add_lemmas` and `add_restrictions` fold the singular form.  They
        // skip the entries whose names clash.  They add the new entries in
        // order.
        t.add_lemmas([lemma("L"), lemma("L3")]);
        t.add_restrictions([restriction("R"), restriction("R2")]);
        assert_eq!(
            t.lemmas().map(|l| l.name.as_str()).collect::<Vec<_>>(),
            vec!["L", "L2", "L3"]
        );
        assert_eq!(
            t.restrictions()
                .map(|r| r.name.as_str())
                .collect::<Vec<_>>(),
            vec!["R", "R2"]
        );

        // `add_rules` removes no duplicates.  It adds both copies after the
        // items that are already present.
        t.add_rules([7, 7]);
        assert_eq!(t.rules().copied().collect::<Vec<_>>(), vec![7, 7]);
    }

    #[test]
    fn options_default_flags() {
        let o = Options::default();
        assert!(!o.trans_progress);
        assert!(!o.compress_events);
        // `--no-ndc` opts out; the check is on by default.
        assert!(o.deduction_chain_check);
        assert!(o.lemmas_to_prove.is_empty());
    }
}

#[cfg(test)]
#[path = "stored_proof_corpus_tests.rs"]
mod stored_proof_corpus_tests;
