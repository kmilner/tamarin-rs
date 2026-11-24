// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Top-level `Theory` data type — port of `TheoryObject.Theory` and
//! `Items.TheoryItem.TheoryItem`.
//!
//! In Haskell, `Theory sig c r p s` is parameterised over five type
//! variables (signature / cache / rule type / proof type / translation
//! element). Here we use concrete types in most slots since the Rust
//! port currently has just one rule representation; the few places
//! where polymorphism actually matters (open vs closed, diff vs trace)
//! we model with explicit enums or distinct types.

use tamarin_term::maude_sig::MaudeSig;
pub use tamarin_term::tags::{LemmaAttr, TraceQuantifier};

use crate::formula::{LNFormula, SyntacticLNFormula};
use crate::predicate::Predicate;
use crate::restriction::Restriction;
use crate::rule::ProtoRuleE;
use crate::sapic::PlainProcess;

/// HS `variantsProtoRule`'s result for a rule's executable body
/// (Theory/Tools/RuleVariants.hs).
#[derive(Debug, Clone, PartialEq)]
pub enum RuleVariants {
    /// Not computed yet.
    Unprepared,
    /// `Nothing`: every variant is fresh-redundant.
    NoVariants,
    /// `Just ruAC`: the AC body, after reducible-term abstraction and precise
    /// renaming, with its variant disjunction (`RuleACConstrs`, Rule.hs).
    /// `solve_rule_constraints` adds a nonempty disjunction to the equation
    /// store as a SplitG goal, deferring the variant choice to proof search.
    Closed {
        body: ProtoRuleE,
        variants: Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    },
}

/// A protocol rule family with its original E rule, explicit AC members,
/// and the executable body and variant machinery prepared during closing.
/// [`closed_rules_ac`] exposes the family's compiled members.
#[derive(Debug, Clone, PartialEq)]
pub struct OpenProtoRule {
    /// Working body: it may be macro-expanded, unfolded, or auto-source annotated.
    pub rule: ProtoRuleE,
    /// The variants of `rule`, computed while closing or, by standalone proof
    /// contexts, on demand.
    pub variants: RuleVariants,
    /// Premise indices marked as loop breakers by the dataflow
    /// analysis (`useAutoLoopBreakersAC`).  In Haskell these live on
    /// `praciLoopBreakers` of `ProtoRuleACInfo`; we attach them to
    /// the parent `OpenProtoRule` so both the E-rule and any AC
    /// variants share a single source of truth.  The field is
    /// populated while closing the theory, or by a standalone
    /// `ProofContext` on demand.
    pub loop_breakers: Vec<crate::rule::PremIdx>,
    /// Saved original E rule (`cprRuleE`, Items/RuleItem.hs). `None` makes
    /// [`OpenProtoRule::rule_e`] fall back to `rule`; a saved copy may equal it.
    /// Macro expansion, auto-source annotation and unfolding preserve this
    /// half for original-family consumers such as partial evaluation and
    /// injectivity analysis. Closing leaves this saved body unchanged;
    /// generated AUTO annotations belong to the executable bodies.
    pub rule_e: Option<Box<ProtoRuleE>>,
    /// Explicit `variants (modulo AC)` members (`_oprRuleAC`, Items/RuleItem.hs).
    /// Open theories preserve source macros. Closing expands the members while
    /// preserving declared new variables, without computing Maude variants
    /// (`closeProtoRule`, lib/theory/src/Rule.hs).
    ///
    /// Parsed members have a trivial variant disjunction and no loop breakers,
    /// so a [`ProtoRuleE`] holds everything a parsed block carries.
    pub rule_ac: Vec<ProtoRuleE>,
}

impl OpenProtoRule {
    pub fn new(rule: ProtoRuleE) -> Self {
        OpenProtoRule {
            rule,
            variants: RuleVariants::Unprepared,
            loop_breakers: Vec::new(),
            rule_e: None,
            rule_ac: Vec::new(),
        }
    }

    /// HS's `cprRuleE` — the rule as the source writes it, before the macros
    /// and before an `--auto-sources` close annotates or unfolds it.
    /// `getProtoRuleEs` (ClosedTheory.hs) reads exactly this.
    pub fn rule_e(&self) -> &ProtoRuleE {
        self.rule_e.as_deref().unwrap_or(&self.rule)
    }

    /// The executable body: the closed AC body, else `rule`.
    pub fn ac_body(&self) -> &ProtoRuleE {
        match &self.variants {
            RuleVariants::Closed { body, .. } => body,
            RuleVariants::Unprepared | RuleVariants::NoVariants => &self.rule,
        }
    }

    /// The closed body's variant disjunction; empty when there is none.
    pub fn variant_substs(&self) -> &[tamarin_term::subst_vfresh::LNSubstVFresh] {
        match &self.variants {
            RuleVariants::Closed { variants, .. } => variants,
            RuleVariants::Unprepared | RuleVariants::NoVariants => &[],
        }
    }

    /// Expand explicit members at the executable-rule boundary. Open printers
    /// retain their source spelling until this step.
    pub(crate) fn expand_variant_macros(&mut self, macros: &[LNMacro]) {
        for member in &mut self.rule_ac {
            *member = crate::rule::apply_macro_in_rule_preserving_new_vars(macros, member.clone());
        }
    }

    pub fn name(&self) -> &str {
        match &self.rule.info.name {
            crate::rule::ProtoRuleName::Stand(n) => n,
            crate::rule::ProtoRuleName::Fresh => "Fresh",
        }
    }
}

/// HS `ProcessDef` (Items/ProcessItem.hs): the payload of a
/// `let P (v1,…,vn) = …` declaration.  `vars` is `None` for a definition
/// written without a parameter list; the SAPIC typing pass replaces it with
/// the inferred formals (`typeAndRenameProcessDef`, Typing.hs).
#[derive(Debug, Clone, PartialEq)]
pub struct ProcessDef {
    pub name: String,
    pub vars: Option<Vec<crate::sapic::SapicLVar>>,
    pub body: PlainProcess,
}

/// `Theory.Sapic.SapicFunSym` — `(UserDefinedSym, [SapicType], SapicType)`
/// (Theory/Sapic/Term.hs), so a typing declaration can name a free OR a
/// user-defined AC symbol. Payload of `TranslationElement::FunctionTypingInfo`.
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
/// Mirrors the full HS `TranslationElement` surface (Items/TheoryItem.hs); elaboration produces every variant.
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

/// A typed lemma. `proof` is a proof skeleton the prover may attempt
/// to discharge.
#[derive(Debug, Clone, PartialEq)]
pub struct Lemma {
    pub name: String,
    /// File whose parser context supplied a lemma-local heuristic. Empty for
    /// generated lemmas and lemmas without such an attribute.
    pub heuristic_in_file: Option<String>,
    pub attributes: Vec<LemmaAttr>,
    pub trace_quantifier: TraceQuantifier,
    /// `_lFormula` (Items/LemmaItem.hs) — the macro- and predicate-expanded
    /// formula, which the solver converts to a guarded formula and the printer
    /// shows in the `guarded formula characterizing ...` block.
    pub formula: LNFormula,
    /// `_lOriginalFormula` (Items/LemmaItem.hs) — the same formula before
    /// macro application, which the printer quotes on the header line.  HS's
    /// `applyMacroInLemma` fills it for every lemma of a closed theory, macros
    /// or none (lib/theory/src/Lemma.hs, CloseRule.hs).
    pub original_formula: Option<LNFormula>,
    pub proof: ProofSkeleton,
    /// Verbatim source text (comments stripped) — HS `_lPlaintext`
    /// (`Items/LemmaItem.hs`).  Carried through elaboration for the
    /// interactive web server's Edit-lemma form; never used by `--prove`.
    pub plaintext: String,
}

impl Lemma {
    /// Only universal source lemmas can refine source cases.
    pub(crate) fn is_source_assumption(&self) -> bool {
        self.trace_quantifier == TraceQuantifier::AllTraces
            && self
                .attributes
                .iter()
                .any(|attr| matches!(attr, LemmaAttr::Sources))
    }
}

/// HS `applyMacroInLemma` (lib/theory/src/Lemma.hs): the theory's macros
/// applied to the formula, with the formula as it stood recorded as the
/// original one.  HS runs it over every lemma of a closed theory
/// (`closeTheoryItem`, CloseRule.hs), macros or none, so
/// `original_formula` ends up filled either way.
pub fn apply_macro_in_lemma(macros: &[LNMacro], lemma: Lemma) -> Lemma {
    let original_formula = lemma.formula.clone();
    Lemma {
        formula: crate::formula::apply_macro_in_formula(macros, lemma.formula),
        original_formula: Some(original_formula),
        ..lemma
    }
}

/// Accountability lemma — names a list of case-test identifiers and
/// the property the case-tests collectively account for.
#[derive(Debug, Clone, PartialEq)]
pub struct AccLemma {
    pub name: String,
    /// File whose parser context supplied an accountability heuristic.
    pub heuristic_in_file: Option<String>,
    pub attributes: Vec<LemmaAttr>,
    /// HS `_aFormula` (Items/AccLemmaItem.hs).  The `Pred` sugar stays:
    /// `liftedAddAccLemma` adds the lemma verbatim
    /// (Theory/Text/Parser.hs), with neither predicate nor macro
    /// expansion.
    pub formula: SyntacticLNFormula,
    pub case_test_idents: Vec<String>,
}

/// Case test referenced by an accountability lemma.
#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: String,
    /// HS `_cFormula` (Items/CaseTestItem.hs).  The `Pred` sugar stays:
    /// `liftedAddCaseTest` adds the case test verbatim
    /// (Theory/Text/Parser.hs), and `caseTestToPredicate` strips it
    /// with `toLNFormula` at accountability-translation time
    /// (Items/CaseTestItem.hs).
    pub formula: SyntacticLNFormula,
}

/// HS `LNMacro` (Term/Macro.hs): one `macros:` declaration, `name(params)
/// = body`.
pub use tamarin_term::macro_expand::LNMacro;

/// One node of a lemma's stored proof — HS `ProofSkeleton = Proof ()`, i.e.
/// `LTree CaseName (ProofStep ())` (Theory/ProofSkeleton.hs,
/// Theory/Proof.hs).
///
/// `cases` keeps the source order of the `case` blocks; the printer sorts by
/// name (HS stores them in an `M.fromList`, Theory/Text/Parser/Proof.hs)
/// and replay looks each case up by name.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofTree {
    pub method: crate::constraint::solver::proof_method::ProofMethod,
    pub cases: Vec<(String, ProofTree)>,
}

/// A lemma's stored proof.  `None` is a lemma written without one, which HS
/// gives the one-node `unproven ()` skeleton
/// (Theory/ProofSkeleton.hs); `prove::replace_sorry_prove` (HS
/// `replaceSorryProver`, Theory/Proof.hs) walks the tree at
/// proof-replay time and invokes the auto-prover only at `sorry` leaves.
pub type ProofSkeleton = Option<ProofTree>;

/// `TheoryItem` — one top-level construct in a (non-diff) theory.
#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem<R = OpenProtoRule> {
    Rule(R),
    Lemma(Lemma),
    Restriction(Restriction),
    Text(FormalComment),
    ConfigBlock(ConfigBlock),
    Predicate(Predicate),
    Macros(Vec<LNMacro>),
    Translation(TranslationElement),
}

impl<R> TheoryItem<R> {
    /// The non-rule half of HS `mapTheoryItem f id` (TheoryObject.hs):
    /// a rule item hands its payload back as `Err`, every other item is cloned
    /// into the target rule type at its position.  Callers supply the rule arm,
    /// which may yield one item or several.
    pub fn split_rule<R2>(&self) -> Result<TheoryItem<R2>, &R> {
        match self {
            TheoryItem::Rule(r) => Err(r),
            TheoryItem::Lemma(x) => Ok(TheoryItem::Lemma(x.clone())),
            TheoryItem::Restriction(x) => Ok(TheoryItem::Restriction(x.clone())),
            TheoryItem::Text(x) => Ok(TheoryItem::Text(x.clone())),
            TheoryItem::ConfigBlock(x) => Ok(TheoryItem::ConfigBlock(x.clone())),
            TheoryItem::Predicate(x) => Ok(TheoryItem::Predicate(x.clone())),
            TheoryItem::Macros(x) => Ok(TheoryItem::Macros(x.clone())),
            TheoryItem::Translation(x) => Ok(TheoryItem::Translation(x.clone())),
        }
    }
}

// =============================================================================
// Top-level Theory
// =============================================================================

/// `Option` block — translation/proof-driver options set per theory.
///
/// HS `Option` (Items/OptionItem.hs) declares fourteen fields in another
/// order and derives `Ord` over them.  Only equality is derived here, and it
/// is order-insensitive, so an ordering for this struct has to be written out
/// rather than derived.
#[derive(Debug, Clone, PartialEq)]
pub struct Options {
    declarable: [bool; tamarin_parser::DeclarableOption::ALL.len()],
    /// HS `_deductionChainCheck`: run the no-deconstruction-chain (NDC)
    /// check at theory load. Enabled by default; `--no-ndc` disables it.
    /// Consulted by the load paths that run the once-per-theory
    /// `close_rule::check_close_intr_rule` pass.
    pub deduction_chain_check: bool,
    /// HS `_lemmasToProve`: lemma names the user requested via `--prove=NAME`.
    pub lemmas_to_prove: Vec<String>,
}

/// HS `defaultOption` (OpenTheory.hs), whose tenth field is the
/// `True` of `_deductionChainCheck`.
impl Default for Options {
    fn default() -> Self {
        Options {
            declarable: [false; tamarin_parser::DeclarableOption::ALL.len()],
            deduction_chain_check: true,
            lemmas_to_prove: Vec::new(),
        }
    }
}

impl Options {
    /// Record an option already validated by the surface parser.
    pub(crate) fn set_declarable(&mut self, name: &str) -> bool {
        let Some(option) = tamarin_parser::DeclarableOption::parse(name) else {
            return false;
        };
        self.declarable[option as usize] = true;
        true
    }

    pub(crate) fn declared(&self) -> Vec<&'static str> {
        tamarin_parser::DeclarableOption::ALL
            .into_iter()
            .filter(|option| self.declarable[*option as usize])
            .map(tamarin_parser::DeclarableOption::as_str)
            .collect()
    }

    pub fn trans_progress(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationProgress as usize]
    }

    pub fn state_channel_opt(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationStateOptimisation as usize]
    }

    pub fn asynchronous_channels(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationAsynchronousChannels as usize]
    }

    pub fn compress_events(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationCompressEvents as usize]
    }
}

/// Top-level theory containing rules, lemmas, restrictions, etc.
///
/// Most operations are convenience accessors over `items`; the
/// underlying storage is order-preserving so pretty-printing matches
/// Haskell's output (which preserves source order).
#[derive(Debug, Clone, PartialEq)]
pub struct Theory<R = OpenProtoRule> {
    pub name: String,
    pub in_file: String,
    /// The `heuristic:` header's goal rankings (HS `_thyHeuristic ::
    /// [GoalRanking ProofContext]`, TheoryObject.hs), parsed when the
    /// theory is built.
    pub heuristic: Vec<crate::constraint::solver::goals::GoalRanking>,
    /// File whose parser context supplied the top-level heuristic header.
    pub heuristic_in_file: Option<String>,
    pub tactic: Vec<crate::tactic::Tactic>,
    pub signature: MaudeSig,
    /// Intruder rules declared as top-level `rule (modulo AC)` blocks. HS
    /// keeps these in `_thyCache`, outside the printable item stream.
    pub intruder_rules: Vec<crate::rule::IntrRuleAC>,
    pub items: Vec<TheoryItem<R>>,
    pub options: Options,
}

impl<R> Theory<R> {
    pub fn new(name: impl Into<String>, signature: MaudeSig) -> Self {
        Theory {
            name: name.into(),
            in_file: String::new(),
            heuristic: Vec::new(),
            heuristic_in_file: None,
            tactic: Vec::new(),
            signature,
            intruder_rules: Vec::new(),
            items: Vec::new(),
            options: Options::default(),
        }
    }
}

impl<R> Theory<R> {
    /// Iterate every rule item. Returns references so callers can
    /// further specialise on the rule type.
    pub fn rules(&self) -> impl Iterator<Item = &R> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r),
            _ => None,
        })
    }

    pub fn lemmas(&self) -> impl Iterator<Item = &Lemma> {
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
    pub fn lookup_lemma(&self, name: &str) -> Option<&Lemma> {
        self.lemmas().find(|l| l.name == name)
    }

    /// Remove the named lemma while preserving the order of every other item.
    pub fn remove_lemma(&mut self, name: &str) -> bool {
        let len = self.items.len();
        self.items
            .retain(|item| !matches!(item, TheoryItem::Lemma(lemma) if lemma.name == name));
        self.items.len() != len
    }

    /// Look up a restriction by name (HS `lookupRestriction`,
    /// TheoryObject.hs).
    pub fn lookup_restriction(&self, name: &str) -> Option<&Restriction> {
        self.restrictions().find(|r| r.name == name)
    }

    /// Whether the theory contains exactly one top-level process.
    pub fn is_sapic(&self) -> bool {
        let mut processes = self.processes();
        processes.next().is_some() && processes.next().is_none()
    }

    /// Whether a `builtins:` declaration contains `name`.
    pub fn has_signature_builtin(&self, name: &str) -> bool {
        self.items.iter().any(|item| {
            matches!(item,
                TheoryItem::Translation(TranslationElement::SignatureBuiltin(builtin))
                    if builtin == name)
        })
    }
}

impl<R> Theory<R> {
    /// HS `theoryFunctionTypingInfos` (TheoryObject.hs): the
    /// `SapicFunSym` of every `functions:` declaration, in source order.
    pub fn function_typing_infos(&self) -> impl Iterator<Item = &SapicFunSym> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::FunctionTypingInfo(f)) => Some(f),
            _ => None,
        })
    }

    /// HS `theoryProcesses` (TheoryObject.hs): the body of every
    /// top-level `process:` item, in source order.  `equivLemma` and
    /// `diffEquivLemma` processes are NOT included, matching the comprehension
    /// over `ProcessItem` alone.
    pub fn processes(&self) -> impl Iterator<Item = &PlainProcess> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::Process(pr)) => Some(pr),
            _ => None,
        })
    }

    /// HS `theoryProcessDefs` (TheoryObject.hs): every `let P = …`
    /// definition, in source order.
    pub fn process_defs(&self) -> impl Iterator<Item = &ProcessDef> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::ProcessDef(d)) => Some(d),
            _ => None,
        })
    }
}

// =============================================================================
// The render-time view of a rule item
// =============================================================================

/// HS `OpenProtoRule` (Items/RuleItem.hs): a rule modulo E together with
/// the rules modulo AC that differ from it.  [`open_proto_rule`] builds one
/// per rule item and [`merge_open_proto_rules`] concatenates the AC halves of
/// consecutive items that share an E rule.
#[derive(Debug, Clone, PartialEq)]
pub struct MergedProtoRule {
    pub rule_e: ProtoRuleE,
    pub rule_ac: Vec<crate::rule::ProtoRuleAC>,
}

/// HS `cprRuleAC` (Items/RuleItem.hs) rebuilt from the split
/// representation: the `variants (modulo AC)` blocks the source writes, which
/// `closeProtoRule` turns into one closed rule each (lib/theory/src/Rule.hs),
/// otherwise the single narrowed form — the abstracted body when Maude found
/// reducible sub-terms, else the rule itself.  The info carries the rule's own
/// name and attributes, the variant disjunction and the loop breakers.
///
/// `closeProtoRule` reaches `variantsProtoRule` only for a rule that writes no
/// `variants (modulo AC)` block (lib/theory/src/Rule.hs), so a written
/// block keeps the disjunction its parser gave it — `Disj [emptySubstVFresh]`
/// (`protoRuleACInfo`, Theory/Text/Parser/Rule.hs) —
/// and the narrowing [`crate::tools::rule_variants::populate_rule_variants`]
/// ran on the E rule stays out of it.  A rule without closed variants gets
/// that same trivial disjunction.
pub fn closed_rules_ac(r: &OpenProtoRule) -> Vec<crate::rule::ProtoRuleAC> {
    if !r.rule_ac.is_empty() {
        return written_rules_ac(r, &r.loop_breakers);
    }
    let variants = match &r.variants {
        RuleVariants::Closed { variants, .. } => variants.clone(),
        RuleVariants::Unprepared | RuleVariants::NoVariants => {
            vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()]
        }
    };
    let info = crate::rule::ProtoRuleACInfo {
        name: r.rule.info.name,
        attributes: r.rule.info.attributes.clone(),
        variants,
        loop_breakers: r.loop_breakers.clone(),
    };
    vec![rule_ac_under(r.ac_body(), info)]
}

/// The written `variants (modulo AC)` members as `ProtoRuleAC`s: each keeps
/// its own name and attributes, has the identity substitution as its
/// variant disjunction (`protoRuleACInfo`, Theory/Text/Parser/Rule.hs) and
/// carries `loop_breakers`.
fn written_rules_ac(
    r: &OpenProtoRule,
    loop_breakers: &[crate::rule::PremIdx],
) -> Vec<crate::rule::ProtoRuleAC> {
    r.rule_ac
        .iter()
        .map(|ac| {
            let info = crate::rule::ProtoRuleACInfo {
                name: ac.info.name,
                attributes: ac.info.attributes.clone(),
                variants: vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()],
                loop_breakers: loop_breakers.to_vec(),
            };
            rule_ac_under(ac, info)
        })
        .collect()
}

/// A rule's facts under a `ProtoRuleAC` info.  HS types both halves as one
/// `Rule` over two infos (Theory/Model/Rule.hs), so only the info
/// changes.
fn rule_ac_under(e: &ProtoRuleE, info: crate::rule::ProtoRuleACInfo) -> crate::rule::ProtoRuleAC {
    crate::rule::Rule {
        info,
        premises: e.premises.clone(),
        conclusions: e.conclusions.clone(),
        actions: e.actions.clone(),
        new_vars: e.new_vars.clone(),
    }
}

/// HS `openProtoRule` (lib/theory/src/Rule.hs): the E rule with the AC
/// rules that `equal_up_to_terms` cannot identify with it; an AC rule that
/// differs from the E rule only in its terms is dropped.
pub fn open_proto_rule(r: &OpenProtoRule) -> MergedProtoRule {
    let rule_e = r.rule_e().clone();
    let rule_ac = closed_rules_ac(r)
        .into_iter()
        .filter(|ac| !crate::rule::equal_up_to_terms(ac, &rule_e))
        .collect();
    MergedProtoRule { rule_e, rule_ac }
}

/// HS `ClosedProtoRule` (Items/RuleItem.hs): the rule as the source
/// writes it beside the one rule modulo AC `closeProtoRule` narrows it to.
#[derive(Debug, Clone, PartialEq)]
pub struct ClosedProtoRule {
    pub rule_e: ProtoRuleE,
    pub rule_ac: crate::rule::ProtoRuleAC,
}

/// HS `closeTheoryItem`'s rule arm followed by `unfoldClosedRules`
/// (CloseRule.hs#unfoldClosedRules) over `closeProtoRule`
/// (lib/theory/src/Rule.hs): a rule item becomes one closed rule per AC
/// rule it closes into — one for a computed narrowing, one per `variants
/// (modulo AC)` block the source writes — each carrying the item's E half.
/// Every other item passes through at its position.
pub fn close_proto_rules(items: &[TheoryItem<OpenProtoRule>]) -> Vec<TheoryItem<ClosedProtoRule>> {
    let mut out: Vec<TheoryItem<ClosedProtoRule>> = Vec::new();
    for item in items {
        match item.split_rule() {
            Ok(other) => out.push(other),
            Err(r) => out.extend(closed_rules_ac(r).into_iter().map(|ac| {
                TheoryItem::Rule(ClosedProtoRule {
                    rule_e: r.rule_e().clone(),
                    rule_ac: ac,
                })
            })),
        }
    }
    out
}

/// HS `mergeOpenProtoRules . map (mapTheoryItem openProtoRule id)`
/// (ClosedTheory.hs, OpenTheory.hs): every rule item opened, then
/// runs of consecutive rule items sharing an E rule collapsed into one item
/// whose AC list is their concatenation.  Every other item passes through at
/// its position.
pub fn merge_open_proto_rules(
    items: &[TheoryItem<OpenProtoRule>],
) -> Vec<TheoryItem<MergedProtoRule>> {
    let mut out: Vec<TheoryItem<MergedProtoRule>> = Vec::new();
    for item in items {
        let mut opened = match item.split_rule() {
            Ok(other) => {
                out.push(other);
                continue;
            }
            Err(r) => open_proto_rule(r),
        };
        // `groupBy comp` compares each element against the group's FIRST, and
        // the fold leaves that element's E rule in place, so the accumulated
        // item is what the next one is compared against.
        match out.last_mut() {
            Some(TheoryItem::Rule(prev)) if prev.rule_e == opened.rule_e => {
                prev.rule_ac =
                    tamarin_utils::prelude_ext::nub(prev.rule_ac.drain(..).chain(opened.rule_ac));
            }
            _ => {
                opened.rule_ac = tamarin_utils::prelude_ext::nub(opened.rule_ac);
                out.push(TheoryItem::Rule(opened));
            }
        }
    }
    out
}

/// HS `_oprRuleAC` (Items/RuleItem.hs) as `prettyOpenProtoRule` reads
/// it: the `variants (modulo AC)` blocks the source writes, typed as the
/// `ProtoRuleAC`s the parser builds.  `protoRuleACInfo` gives each of them the
/// rule's own name and attributes, the identity substitution as its variant
/// disjunction and an empty loop-breaker list
/// (Theory/Text/Parser/Rule.hs).
pub(crate) fn manual_rule_variants(r: &OpenProtoRule) -> Vec<crate::rule::ProtoRuleAC> {
    written_rules_ac(r, &[])
}

/// HS `clearFunctionTypingInfos` (TheoryObject.hs): drop every
/// source-positioned `FunctionTypingInfo` item.
pub fn clear_function_typing_infos<R>(thy: &mut Theory<R>) {
    thy.items.retain(|i| {
        !matches!(
            i,
            TheoryItem::Translation(TranslationElement::FunctionTypingInfo(_))
        )
    });
}

/// HS `containsManualRuleVariants` (OpenTheory.hs): whether any rule
/// item carries an AC rule of its own.
pub fn contains_manual_rule_variants(items: &[TheoryItem<MergedProtoRule>]) -> bool {
    items
        .iter()
        .any(|i| matches!(i, TheoryItem::Rule(r) if !r.rule_ac.is_empty()))
}

/// [`contains_manual_rule_variants`] of [`merge_open_proto_rules`]`(items)`,
/// without building the merged items: a merged item's AC rules are the union
/// of those its rules open with ([`open_proto_rule`]), so it carries one
/// exactly when one of its rules opens with one.  It compares what
/// [`closed_rules_ac`] would build, without building it: each written member
/// under its own name, else the AC body under the rule's name.
pub fn merged_contain_manual_rule_variants(items: &[TheoryItem<OpenProtoRule>]) -> bool {
    use crate::rule::same_fact_tags;
    items.iter().any(|i| {
        let TheoryItem::Rule(r) = i else {
            return false;
        };
        let e = r.rule_e();
        if r.rule_ac.is_empty() {
            r.rule.info.name != e.info.name || !same_fact_tags(r.ac_body(), e)
        } else {
            r.rule_ac
                .iter()
                .any(|ac| ac.info.name != e.info.name || !same_fact_tags(ac, e))
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A theory over simple stand-in type parameters.  The accessors are
    /// generic over `R`, so the item payload does not have to be a real rule.
    type TestTheory = Theory<i32>;

    fn lemma(name: &str) -> Lemma {
        Lemma {
            name: name.to_string(),
            heuristic_in_file: None,
            attributes: Vec::new(),
            trace_quantifier: TraceQuantifier::AllTraces,
            formula: crate::formula::ProtoFormula::ltrue(),
            original_formula: None,
            proof: None,
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
        let mut t: TestTheory =
            Theory::new("Foo", tamarin_term::maude_sig::minimal_maude_sig(false));
        assert_eq!(t.name, "Foo");
        assert_eq!(t.items.len(), 0);
        assert_eq!(t.rules().count(), 0);

        t.items = vec![
            TheoryItem::Rule(7),
            TheoryItem::Lemma(lemma("L")),
            TheoryItem::Restriction(restriction("R")),
            TheoryItem::Macros(vec![lnmacro("m1"), lnmacro("m2")]),
            TheoryItem::Translation(TranslationElement::SignatureBuiltin("t".to_string())),
        ];

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

    #[test]
    fn options_default_flags() {
        let o = Options::default();
        assert!(!o.trans_progress());
        assert!(!o.compress_events());
        // `--no-ndc` opts out; the check is on by default.
        assert!(o.deduction_chain_check);
        assert!(o.lemmas_to_prove.is_empty());
    }
}

#[cfg(test)]
#[path = "stored_proof_corpus_tests.rs"]
mod stored_proof_corpus_tests;
