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

use tamarin_term::maude_sig::MaudeSig;
pub use tamarin_term::tags::{LemmaAttr, TraceQuantifier};

use crate::formula::{LNFormula, SyntacticLNFormula};
use crate::predicate::Predicate;
use crate::restriction::Restriction;
use crate::rule::ProtoRuleE;
use crate::sapic::PlainProcess;

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

/// HS `ProcessDef` (Items/ProcessItem.hs:23-28): the payload of a
/// `let P (v1,…,vn) = …` declaration.  `vars` is `None` for a definition
/// written without a parameter list; the SAPIC typing pass replaces it with
/// the inferred formals (`typeAndRenameProcessDef`, Typing.hs:217-225).
#[derive(Debug, Clone, PartialEq)]
pub struct ProcessDef {
    pub name: String,
    pub vars: Option<Vec<crate::sapic::SapicLVar>>,
    pub body: PlainProcess,
}

/// `Theory.Sapic.SapicFunSym` — `(UserDefinedSym, [SapicType], SapicType)`
/// (Theory/Sapic/Term.hs:78), so a typing declaration can name a free OR a
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
/// Mirrors the full HS `TranslationElement` surface (Items/TheoryItem.hs:
/// 43-53); elaboration produces every variant.
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
    pub proof: ProofSkeleton,
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
    /// The non-rule half of HS `mapTheoryItem f id` (TheoryObject.hs:269-271):
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
/// HS `Option` (Items/OptionItem.hs:21-38) declares fourteen fields in another
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

/// HS `defaultOption` (OpenTheory.hs:546-547), whose tenth field is the
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

    pub fn trans_progress(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationProgress as usize]
    }

    pub fn trans_allow_pattern_matching_in_lookup(&self) -> bool {
        self.declarable[tamarin_parser::DeclarableOption::TranslationAllowPatternLookups as usize]
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
    /// [GoalRanking ProofContext]`, TheoryObject.hs:185), parsed when the
    /// theory is built.
    pub heuristic: Vec<crate::constraint::solver::goals::GoalRanking>,
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

    /// Look up a restriction by name (HS `lookupRestriction`,
    /// TheoryObject.hs:671-672).
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
    /// HS `theoryFunctionTypingInfos` (TheoryObject.hs:368-369): the
    /// `SapicFunSym` of every `functions:` declaration, in source order.
    pub fn function_typing_infos(&self) -> impl Iterator<Item = &SapicFunSym> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::FunctionTypingInfo(f)) => Some(f),
            _ => None,
        })
    }

    /// HS `theoryProcesses` (TheoryObject.hs:360-361): the body of every
    /// top-level `process:` item, in source order.  `equivLemma` and
    /// `diffEquivLemma` processes are NOT included, matching the comprehension
    /// over `ProcessItem` alone.
    pub fn processes(&self) -> impl Iterator<Item = &PlainProcess> {
        self.items.iter().filter_map(|i| match i {
            TheoryItem::Translation(TranslationElement::Process(pr)) => Some(pr),
            _ => None,
        })
    }

    /// HS `theoryProcessDefs` (TheoryObject.hs:364-365): every `let P = …`
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

/// HS `OpenProtoRule` (Items/RuleItem.hs:34-37): a rule modulo E together with
/// the rules modulo AC that differ from it.  [`open_proto_rule`] builds one
/// per rule item and [`merge_open_proto_rules`] concatenates the AC halves of
/// consecutive items that share an E rule.
#[derive(Debug, Clone, PartialEq)]
pub struct MergedProtoRule {
    pub rule_e: ProtoRuleE,
    pub rule_ac: Vec<crate::rule::ProtoRuleAC>,
}

/// HS `cprRuleAC` (Items/RuleItem.hs:56-59) rebuilt from the split
/// representation: the `variants (modulo AC)` blocks the source writes, which
/// `closeProtoRule` turns into one closed rule each (lib/theory/src/Rule.hs:86),
/// otherwise the single narrowed form — the abstracted body when Maude found
/// reducible sub-terms, else the rule itself.  The info carries the rule's own
/// name and attributes, the variant disjunction and the loop breakers.
///
/// `closeProtoRule` reaches `variantsProtoRule` only for a rule that writes no
/// `variants (modulo AC)` block (lib/theory/src/Rule.hs:82-86), so a written
/// block keeps the disjunction its parser gave it — `Disj [emptySubstVFresh]`
/// (`protoRuleACInfo`, Theory/Text/Parser/Rule.hs:138-143, see line 142) —
/// and the narrowing [`crate::tools::rule_variants::populate_rule_variants`]
/// ran on the E rule stays out of it.  For every other rule an empty
/// `variant_substs` stands for that same trivial disjunction.
pub fn closed_rules_ac(r: &OpenProtoRule) -> Vec<crate::rule::ProtoRuleAC> {
    let info = |e: &ProtoRuleE, variants: Vec<tamarin_term::subst_vfresh::LNSubstVFresh>| {
        crate::rule::ProtoRuleACInfo {
            name: e.info.name,
            attributes: e.info.attributes.clone(),
            variants,
            loop_breakers: r.loop_breakers.clone(),
        }
    };
    let trivial = || vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()];
    if r.rule_ac.is_empty() {
        let variants = if r.variant_substs.is_empty() {
            trivial()
        } else {
            r.variant_substs.clone()
        };
        let ac = r.abstracted_rule.as_ref().unwrap_or(&r.rule);
        vec![rule_ac_under(ac, info(&r.rule, variants))]
    } else {
        r.rule_ac
            .iter()
            .map(|ac| rule_ac_under(ac, info(ac, trivial())))
            .collect()
    }
}

/// A rule's facts under a `ProtoRuleAC` info.  HS types both halves as one
/// `Rule` over two infos (Theory/Model/Rule.hs:635-638), so only the info
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

/// HS `openProtoRule` (lib/theory/src/Rule.hs:51-59): the E rule with the AC
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

/// HS `ClosedProtoRule` (Items/RuleItem.hs:50-59): the rule as the source
/// writes it beside the one rule modulo AC `closeProtoRule` narrows it to.
#[derive(Debug, Clone, PartialEq)]
pub struct ClosedProtoRule {
    pub rule_e: ProtoRuleE,
    pub rule_ac: crate::rule::ProtoRuleAC,
}

/// HS `closeTheoryItem`'s rule arm followed by `unfoldClosedRules`
/// (CloseRule.hs:82-93#unfoldClosedRules) over `closeProtoRule`
/// (lib/theory/src/Rule.hs:82-86): a rule item becomes one closed rule per AC
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
/// (ClosedTheory.hs:402, OpenTheory.hs:592-603): every rule item opened, then
/// runs of consecutive rule items sharing an E rule collapsed into one item
/// whose AC list is their concatenation.  Every other item passes through at
/// its position.
pub fn merge_open_proto_rules(
    items: &[TheoryItem<OpenProtoRule>],
) -> Vec<TheoryItem<MergedProtoRule>> {
    let mut out: Vec<TheoryItem<MergedProtoRule>> = Vec::new();
    for item in items {
        let opened = match item.split_rule() {
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
                prev.rule_ac.extend(opened.rule_ac)
            }
            _ => out.push(TheoryItem::Rule(opened)),
        }
    }
    out
}

/// HS `_oprRuleAC` (Items/RuleItem.hs:34-36) as `prettyOpenProtoRule` reads
/// it: the `variants (modulo AC)` blocks the source writes, typed as the
/// `ProtoRuleAC`s the parser builds.  `protoRuleACInfo` gives each of them the
/// rule's own name and attributes, the identity substitution as its variant
/// disjunction and an empty loop-breaker list
/// (Theory/Text/Parser/Rule.hs:137-143, see line 142).
pub(crate) fn manual_rule_variants(r: &OpenProtoRule) -> Vec<crate::rule::ProtoRuleAC> {
    r.rule_ac
        .iter()
        .map(|v| {
            rule_ac_under(
                v,
                crate::rule::ProtoRuleACInfo {
                    name: v.info.name,
                    attributes: v.info.attributes.clone(),
                    variants: vec![tamarin_term::subst_vfresh::LNSubstVFresh::empty()],
                    loop_breakers: Vec::new(),
                },
            )
        })
        .collect()
}

/// HS `clearFunctionTypingInfos` (TheoryObject.hs:504-508): drop every
/// source-positioned `FunctionTypingInfo` item.
pub fn clear_function_typing_infos<R>(thy: &mut Theory<R>) {
    thy.items.retain(|i| {
        !matches!(
            i,
            TheoryItem::Translation(TranslationElement::FunctionTypingInfo(_))
        )
    });
}

/// HS `containsManualRuleVariants` (OpenTheory.hs:584-589): whether any rule
/// item carries an AC rule of its own.
pub fn contains_manual_rule_variants(items: &[TheoryItem<MergedProtoRule>]) -> bool {
    items
        .iter()
        .any(|i| matches!(i, TheoryItem::Rule(r) if !r.rule_ac.is_empty()))
}

/// Whether opening any stored rule would retain an AC half. This is the
/// allocation-free gate for [`merge_open_proto_rules`]: `equalUpToTerms`
/// compares only the rule name and the fact-tag shapes, so constructing and
/// cloning the closed AC rules is unnecessary merely to choose a printer.
pub fn contains_open_rule_variants(items: &[TheoryItem<OpenProtoRule>]) -> bool {
    fn same_tags(xs: &[crate::fact::LNFact], ys: &[crate::fact::LNFact]) -> bool {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| x.tag == y.tag)
    }
    fn differs(ac: &ProtoRuleE, e: &ProtoRuleE) -> bool {
        ac.info.name != e.info.name
            || !same_tags(&ac.premises, &e.premises)
            || !same_tags(&ac.conclusions, &e.conclusions)
            || !same_tags(&ac.actions, &e.actions)
    }

    items.iter().any(|item| {
        let TheoryItem::Rule(rule) = item else {
            return false;
        };
        let e = rule.rule_e();
        if rule.rule_ac.is_empty() {
            differs(rule.abstracted_rule.as_ref().unwrap_or(&rule.rule), e)
        } else {
            rule.rule_ac.iter().any(|ac| differs(ac, e))
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
