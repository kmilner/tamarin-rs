// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, beschmi, meiersi, PhilipLukertWork, felixlinker, rkunnema,
//   BTom-GH, rsasse, and other minor contributors (see upstream git
//   history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Term.hs, lib/theory/src/Items/LemmaItem.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Text/Parser/Lemma.hs,
//   lib/theory/src/Theory/Text/Parser/Proof.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Signature.hs

//! Surface-syntax AST for `.spthy` files: the loose tree [`crate::parser`]
//! produces and [`crate::wf`] (plus, downstream, `tamarin-theory`'s
//! elaboration) consumes.
//!
//! Nodes mirror Tamarin's concrete syntax rather than any single Haskell type —
//! the HS parser builds straight into the semantic `Theory`, so this is a
//! syntax-level staging form that a later elaboration pass lowers. [`Theory`] is
//! the root; every other type hangs off its [`TheoryItem`] stream.

// =============================================================================
// Top-level theory
// =============================================================================

use std::ops::Deref;

use crate::parser::Location;

#[derive(Debug, Clone, PartialEq)]
pub struct Theory {
    pub is_diff: bool,
    pub name: String,
    pub configuration: Option<String>,
    pub items: Vec<TheoryItem>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem {
    Builtins(Vec<Builtin>),
    Functions(Vec<FunctionDecl>),
    Equations {
        convergent: bool,
        eqs: Vec<Equation>,
    },
    Macros(Vec<Macro>),
    Predicates(Vec<Predicate>),
    Options(Vec<String>),
    Heuristic(String),
    Tactic(Tactic),
    Restriction(Restriction),
    LegacyAxiom(Restriction),
    Rule(Rule),
    IntrRule(Rule),
    Lemma(Lemma),
    DiffLemma(DiffLemma),
    AccLemma(AccLemma),
    CaseTest(CaseTest),
    ProcessDef(ProcessDef),
    TopLevelProcess(Process),
    EquivLemma(Process, Process),
    DiffEquivLemma(Process),
    Export {
        tag: String,
        body: String,
    },
    FormalComment {
        header: String,
        body: String,
    },
    // `#ifdef` never yields an item: the parser evaluates the flag formula
    // and splices the live branch's items into the surrounding stream
    // (parser.rs `expand_ifdef`), matching HS's parse-time preprocessing —
    // so `items` is always the flat post-preprocessor stream.
    Define(String),
    Include(String),
}

// =============================================================================
// Functions / equations / macros / predicates / restrictions
// =============================================================================

#[derive(Debug, Clone)]
pub struct Builtin {
    pub kind: BuiltinKind,
    pub location: Location,
}

impl PartialEq for Builtin {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            kind: _,
            location: _,
        } = self;
        let Self {
            kind: _,
            location: _,
        } = other;
        // Everything but location
        self.kind == other.kind
    }
}

impl Eq for Builtin {}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BuiltinKind {
    LocationsReport,
    DestAsymmetricEncryption,
    AsymmetricEncryption,
    DestSymmetricEncryption,
    SymmetricEncryption,
    DestSigning,
    Signing,
    RevealingSigning,
    Hashing,
    DestPairing,
    Pairing,
    DiffieHellman,
    BilinearPairing,
    Multiset,
    Xor,
    NaturalNumbers,
    ReliableChannel,
}

impl std::fmt::Display for BuiltinKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl BuiltinKind {
    pub fn from_str(name: &str) -> Option<Self> {
        match name {
            "locations-report" => Some(Self::LocationsReport),
            "dest-asymmetric-encryption" => Some(Self::DestAsymmetricEncryption),
            "asymmetric-encryption" => Some(Self::AsymmetricEncryption),
            "dest-symmetric-encryption" => Some(Self::DestSymmetricEncryption),
            "symmetric-encryption" => Some(Self::SymmetricEncryption),
            "dest-signing" => Some(Self::DestSigning),
            "signing" => Some(Self::Signing),
            "revealing-signing" => Some(Self::RevealingSigning),
            "hashing" => Some(Self::Hashing),
            "dest-pairing" => Some(Self::DestPairing),
            "pairing" => Some(Self::Pairing),
            "diffie-hellman" => Some(Self::DiffieHellman),
            "bilinear-pairing" => Some(Self::BilinearPairing),
            "multiset" => Some(Self::Multiset),
            "xor" => Some(Self::Xor),
            "natural-numbers" => Some(Self::NaturalNumbers),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::LocationsReport => "locations-report",
            Self::DestAsymmetricEncryption => "dest-asymmetric-encryption",
            Self::AsymmetricEncryption => "asymmetric-encryption",
            Self::DestSymmetricEncryption => "dest-symmetric-encryption",
            Self::SymmetricEncryption => "symmetric-encryption",
            Self::DestSigning => "dest-signing",
            Self::Signing => "signing",
            Self::RevealingSigning => "revealing-signing",
            Self::Hashing => "hashing",
            Self::DestPairing => "dest-pairing",
            Self::Pairing => "pairing",
            Self::DiffieHellman => "diffie-hellman",
            Self::BilinearPairing => "bilinear-pairing",
            Self::Multiset => "multiset",
            Self::Xor => "xor",
            Self::NaturalNumbers => "natural-numbers",
            Self::ReliableChannel => "reliable-channel",
        }
    }

    pub fn iter() -> impl Iterator<Item = Self> {
        const BUILTINKINDS: [BuiltinKind; 16] = [
            BuiltinKind::LocationsReport,
            BuiltinKind::DiffieHellman,
            BuiltinKind::BilinearPairing,
            BuiltinKind::Multiset,
            BuiltinKind::Xor,
            BuiltinKind::SymmetricEncryption,
            BuiltinKind::AsymmetricEncryption,
            BuiltinKind::Signing,
            BuiltinKind::DestPairing,
            BuiltinKind::DestSymmetricEncryption,
            BuiltinKind::DestAsymmetricEncryption,
            BuiltinKind::DestSigning,
            BuiltinKind::RevealingSigning,
            BuiltinKind::Hashing,
            BuiltinKind::NaturalNumbers,
            BuiltinKind::ReliableChannel,
        ];
        BUILTINKINDS.iter().copied()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
    pub name: String,
    pub arg_types: Vec<Option<String>>,
    pub out_type: Option<String>,
    pub private: bool,
    pub destructor: bool,
    /// `[AC]`: the symbol is a user-defined associative-commutative operator
    /// (HS `ACstate IsAC`).  HS requires such a symbol to be binary and
    /// registers it as an `ACfctUser` rather than a `NoEqUser` symbol; a binary
    /// one is additionally usable in infix notation (`Parser::acterm`).
    pub ac: bool,
    /// `[NDC]`: the "no deconstruction chain" property is asserted for the
    /// trace intruder rules (HS `NDCstate IsNDC`).
    pub ndc: bool,
    /// `[NDC-diff]`: the "no deconstruction chain" property is asserted for the
    /// diff-mode intruder rules (HS `NDCstate IsNDCDiff`).
    ///
    /// The symbol's NDC state is the join of the two flags (HS `function`,
    /// Theory/Text/Parser/Signature.hs:183-225): neither = `NotNDC`, `ndc`
    /// alone = `IsNDC`, `ndc_diff` alone = `IsNDCDiff`, both = `IsNDCBoth`.
    pub ndc_diff: bool,
    pub location: Location,
}

impl PartialEq for FunctionDecl {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            name: _,
            arg_types: _,
            out_type: _,
            private: _,
            destructor: _,
            ac: _,
            ndc: _,
            ndc_diff: _,
            location: _,
        } = self;
        let Self {
            name: _,
            arg_types: _,
            out_type: _,
            private: _,
            destructor: _,
            ac: _,
            ndc: _,
            ndc_diff: _,
            location: _,
        } = other;
        // Everything but location
        self.name == other.name
            && self.arg_types == other.arg_types
            && self.out_type == other.out_type
            && self.private == other.private
            && self.destructor == other.destructor
            && self.ac == other.ac
            && self.ndc == other.ndc
            && self.ndc_diff == other.ndc_diff
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    pub name: String,
    pub args: Vec<VarSpec>,
    pub body: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Predicate {
    pub fact: Fact,
    pub formula: Formula,
}

#[derive(Debug, Clone)]
pub struct Restriction {
    pub name: String,
    pub formula: Formula,
    pub attributes: Vec<RestrictionAttr>,
    pub location: Location,
}

impl PartialEq for Restriction {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            name: _,
            formula: _,
            attributes: _,
            location: _,
        } = self;
        let Self {
            name: _,
            formula: _,
            attributes: _,
            location: _,
        } = other;
        // Everything but location
        self.name == other.name
            && self.formula == other.formula
            && self.attributes == other.attributes
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RestrictionAttr {
    Left,
    Right,
}

impl RestrictionAttr {
    pub fn iter() -> impl Iterator<Item = Self> {
        const RESTRICTION_ATTRS: [RestrictionAttr; 2] =
            [RestrictionAttr::Left, RestrictionAttr::Right];
        RESTRICTION_ATTRS.iter().copied()
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Left => "left",
            Self::Right => "right",
        }
    }
}

// =============================================================================
// Rules
// =============================================================================

#[derive(Debug, Clone)]
pub struct Rule {
    pub name: String,
    pub modulo: Option<String>, // E or AC
    pub attributes: Vec<RuleAttr>,
    pub let_block: Vec<LetBinding>,
    pub premises: Vec<Fact>,
    pub actions: Vec<Fact>,
    pub conclusions: Vec<Fact>,
    pub embedded_restrictions: Vec<Formula>,
    pub variants: Vec<Rule>,
    pub left_right: Option<(Box<Rule>, Box<Rule>)>,
    pub location: Location,
}

impl PartialEq for Rule {
    fn eq(&self, other: &Self) -> bool {
        // Compilation error once we add new fields
        let Rule {
            name: _,
            modulo: _,
            attributes: _,
            let_block: _,
            premises: _,
            actions: _,
            conclusions: _,
            embedded_restrictions: _,
            variants: _,
            left_right: _,
            location: _,
        } = self;
        let Rule {
            name: _,
            modulo: _,
            attributes: _,
            let_block: _,
            premises: _,
            actions: _,
            conclusions: _,
            embedded_restrictions: _,
            variants: _,
            left_right: _,
            location: _,
        } = other;
        // Everything but the location
        self.name == other.name
            && self.modulo == other.modulo
            && self.attributes == other.attributes
            && self.let_block == other.let_block
            && self.premises == other.premises
            && self.actions == other.actions
            && self.conclusions == other.conclusions
            && self.embedded_restrictions == other.embedded_restrictions
            && self.variants == other.variants
            && self.left_right == other.left_right
    }
}

#[derive(Debug, Clone)]
pub struct RuleAttr {
    pub kind: RuleAttrKind,
    pub location: Location,
}

impl PartialEq for RuleAttr {
    fn eq(&self, other: &Self) -> bool {
        // Compilation error once we add new fields
        let RuleAttr {
            kind: _,
            location: _,
        } = self;
        let RuleAttr {
            kind: _,
            location: _,
        } = other;
        // Everything but the location
        self.kind == other.kind
    }
}

impl RuleAttr {
    pub fn expected() -> Vec<&'static str> {
        vec![
            "color",
            "colour",
            "no_derivcheck",
            "role",
            "issapicrule",
            "process",
            "external attribute",
        ]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RuleAttrKind {
    Color(String),
    NoDerivCheck,
    Role(String),
    IsSapicRule,
    /// `process="..."` — the rendered `prettySapicTopLevel'` of a
    /// SAPIC-generated rule's subprocess.  HS's rule-attribute PARSER ignores
    /// a user-written `process=` (`parseAndIgnore`, Parser/Rule.hs:68-93, see line 72), so this
    /// variant is never produced by the parser; it is synthesised only by the
    /// SAPIC translation when it injects generated rules into the parsed theory
    /// (so the pretty-printer renders the `process="..."` attribute).
    Process(String),
    External(String, Option<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetBinding {
    pub var: Term, // pattern
    pub value: Term,
}

// =============================================================================
// Lemmas / accountability / case tests / proof skeletons
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Lemma {
    pub name: String,
    pub modulo: Option<String>,
    pub attributes: Vec<LemmaAttr>,
    pub trace_quantifier: TraceQuantifier,
    pub formula: Formula,
    pub proof: Option<ProofSkeleton>,
    /// The verbatim source text of the lemma (from the `lemma` keyword up to
    /// and including the trailing whitespace/comments after its proof
    /// skeleton), with comments stripped.  Mirrors HS `_lPlaintext`
    /// (`ProtoLemma`, `Items/LemmaItem.hs:48-58, see line 50`), which the parser fills from
    /// `removeComments $ take (length start - length end) start`
    /// (`Theory/Text/Parser/Lemma.hs:78-88, see line 87`).  Used only by the interactive web
    /// server's Edit-lemma form (never rendered by `--prove`).
    pub plaintext: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DiffLemma {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub proof: Option<ProofSkeleton>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AccLemma {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub formula: Formula,
    pub case_test_idents: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: String,
    pub formula: Formula,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TraceQuantifier {
    AllTraces,
    ExistsTrace,
}

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
    Hint(String),
}

impl LemmaAttr {
    pub fn expected() -> Vec<&'static str> {
        vec![
            "sources",
            "reuse",
            "diff_reuse",
            "use_induction",
            "hide_lemma",
            "heuristic",
            "output",
            "left",
            "right",
        ]
    }
}

/// Structured skeleton parse — mirrors HS's
/// `LTree (ProofStep ProofMethod (Maybe System))` produced by
/// `Theory.Text.Parser.Proof.startProofSkeleton`
/// (lib/theory/src/Theory/Text/Parser/Proof.hs:90-115).
///
/// The skeleton is the *static* tree as written in the `.spthy` source,
/// before any prover is run; `by sorry` leaves are the placeholders
/// `replaceSorryProver` (HS: Theory/Proof.hs:642-651) replaces with
/// auto-prover output at proof-replay time.
#[derive(Debug, Clone, PartialEq)]
pub struct ProofSkeleton {
    /// Raw source text of the proof skeleton (used for diagnostics/logging and
    /// propagated into theory.rs's `ProofSkeleton` during elaboration).
    pub raw: String,
    /// Structured parse of `raw`.  `None` only if `try_proof_skeleton`
    /// failed to interpret the token stream (we always set this for
    /// well-formed proofs).
    pub tree: Option<ParsedProofTree>,
}

/// One node of the parsed proof skeleton.
///
/// Mirrors HS's `LNode (ProofStep ProofMethod ()) (Map CaseName ProofSkeleton)`
/// from lib/theory/src/Theory/Text/Parser/Proof.hs:98-115:
///
/// ```haskell
/// proofSkeleton =
///     solvedProof <|> finalProof <|> interProof
///   where
///     solvedProof = symbol "SOLVED" *> pure (LNode (ProofStep (Finished Solved) ()) M.empty)
///     finalProof = do
///         method <- symbol "by" *> proofMethod
///         return (LNode (ProofStep method ()) M.empty)
///     interProof = do
///         method <- proofMethod
///         cases  <- (sepBy oneCase (symbol "next") <* symbol "qed") <|>
///                   ((return . (,) "") <$> proofSkeleton          )
///         return (LNode (ProofStep method ()) (M.fromList cases))
///     oneCase = (,) <$> (symbol "case" *> identifier) <*> proofSkeleton
/// ```
///
/// `cases` retains the source ordering (HS uses `M.fromList` which is
/// alphabetical, but at replay time the order doesn't matter — we look
/// each case up by name).
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedProofTree {
    pub method: ParsedMethod,
    pub cases: Vec<(String, ParsedProofTree)>,
}

/// Parsed proof method.  Mirrors HS's `ProofMethod` enum (matched by
/// `Theory.Text.Parser.Proof.proofMethod`, Proof.hs:76-85).  Plus
/// `Solved` for the `SOLVED` keyword leaf and `Other` for any token
/// pattern intentionally left to the auto-prover fallback.
#[derive(Debug, Clone, PartialEq)]
pub enum ParsedMethod {
    /// `by sorry` or `sorry` (HS: `Sorry Nothing`).  This is the
    /// placeholder `replaceSorryProver` replaces.
    Sorry,
    /// `by contradiction` (HS: `Finished (Contradictory Nothing)`).
    Contradiction,
    /// `simplify` (HS: `Simplify`).
    Simplify,
    /// `induction` (HS: `Induction`).
    Induction,
    /// `solve( <goal-text> )` (HS: `SolveGoal <parsed-goal>`).  We
    /// capture the raw inner text plus a best-effort parsed `GoalSpec`.
    /// The String is the raw text inside `solve( ... )`, preserved for
    /// HS-faithful unannotated subtree display (see `replay.rs`).
    SolveGoal(GoalSpec, String),
    /// `SOLVED` (HS: `Finished Solved`).
    SolvedLeaf,
    /// `UNFINISHABLE` (HS: `Finished Unfinishable`).
    Unfinishable,
    /// `INVALIDATED` (HS: `Invalidated`).
    Invalidated,
    /// Any proof-method token not matched by a structural variant;
    /// intentionally replayed via the auto-prover.
    Other(String),
}

/// Best-effort parse of the formula inside `solve( ... )`.
///
/// The text inside `solve(...)` is one of HS's `goal` parses
/// (Theory/Text/Parser/Proof.hs:38-72):
///
///   - `Fact( ... ) @ #var`        →  ActionG
///   - `Fact( ... ) ▶<n> #var`     →  PremiseG (subscript-digit shows
///     the premise index)
///   - `gf1 ∥ gf2 ∥ ...`           →  DisjG (Disj [guardedFormula])
///   - chain / subterm / splitEqs  →  Chain/Subterm/Split
///
/// We build the cheap-to-recognise variants (Action, Premise, Disj);
/// everything else lands in `Raw` and the replay walker falls back to
/// the auto-prover.
#[derive(Debug, Clone, PartialEq)]
pub enum GoalSpec {
    /// `Fact( args... ) @ #ivar` — action goal.
    Action {
        fact: Fact,
        /// Timepoint variable ROOT name (sigil/idx stripped), e.g. `vk`
        /// from `#vk.6`.
        time_var: String,
        /// Timepoint variable index (the `N` in `#vk.N`; `0` when absent).
        /// HS's `ActionG i fa` carries the full LVar incl. idx, so this is
        /// needed to re-render the goal head faithfully (`#vk.6`, not `#vk`)
        /// and for exact goal-key matching at replay time.
        time_idx: u32,
    },
    /// `Fact( args... ) ▶<idx> #ivar` — premise goal.  The premise
    /// index is the digit after `▶` (UTF-8 ▶₀..▶₉).
    Premise {
        fact: Fact,
        prem_idx: usize,
        /// Node variable ROOT name (sigil/idx stripped).
        time_var: String,
        /// Node variable index (the `N` in `#i.N`; `0` when absent).
        time_idx: u32,
    },
    /// `gf1 ∥ gf2 ∥ ...` — disjunction-split goal.  Mirrors HS
    /// `disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula
    /// (symbol "∥")` (Theory/Text/Parser/Proof.hs:39-72, see line 61).
    ///
    /// HS parses each disjunct as a full `Guarded` value bearing
    /// concrete LVar identities, then matches by structural equality
    /// against the open `Goal::Disj(...)` in `sys.goals` (HS
    /// ProofMethod.hs:254-274, see line 259 `SolveGoal goal -> guard (goal `M.member`
    /// L.get sGoals sys)`).
    ///
    /// We can't reconstruct skeleton-text LVar indices reliably (they
    /// differ from runtime indices), so we capture each disjunct's
    /// STRUCTURAL signature (its top-level shape: quantified or not,
    /// and the number of bound vars).  The replay matcher then looks
    /// for an open `Goal::Disj` whose `d.0` list has the same length
    /// and whose entries share the same per-alt shape.  At the points
    /// where the HS-parsed disjunction would be matched, only ONE open
    /// `Goal::Disj` typically lives in `sys.goals`, so the shape
    /// signature is a sufficient discriminator.
    Disj {
        alts: Vec<DisjAlt>,
        alt_texts: Vec<String>,
    },
    /// `(#i, n) ~~> (#j, m)` — chain-split goal.  Mirrors HS
    /// `chainGoal = ChainG <$> (try (nodeConc <* opChain)) <*> nodePrem`
    /// (Theory/Text/Parser/Proof.hs:39-72, see line 59).  `nodeConc`/`nodePrem` parse
    /// `(<nodevar>, <natural>)` and the operator is `~~>` (HS
    /// `prettyGoal (ChainG c p)` Constraints.hs:269-270).
    ///
    /// We capture the time-var names (e.g. `i`, `j` from `#i`/`#j`)
    /// and the conclusion / premise indices.  The replay matcher
    /// disambiguates by these idxs and the time-var ROOT name; LVar
    /// suffix-idxs are intentionally ignored (skeleton-text indices
    /// differ from runtime LVar indices — same pattern as Action /
    /// Premise).
    Chain {
        src_var: String,
        conc_idx: u32,
        tgt_var: String,
        prem_idx: u32,
    },
    /// `<small> ⊏ <big>` — subterm-split goal.  Mirrors HS
    /// `stSplitGoal` (Theory/Text/Parser/Proof.hs:63-66):
    /// ```haskell
    /// stSplitGoal = do
    ///   a <- try (termp <* opSubterm)
    ///   b <- termp
    ///   return $ SubtermG (a, b)
    /// ```
    /// and the pretty-printer at Constraints.hs:281-282 emits
    /// `<term> ⊏ <term>` (U+228F).
    ///
    /// We keep both sides as raw text trimmed of outer whitespace; the
    /// matcher compares against open `Goal::Subterm((l, r))` by canonical
    /// pretty-printed text equality.
    Subterm { small_raw: String, big_raw: String },
    /// `splitEqs(N)` — equation-split goal.  Mirrors HS `eqSplitGoal`
    /// (Theory/Text/Parser/Proof.hs:70-72):
    /// ```haskell
    /// eqSplitGoal = try $ do
    ///   symbol_ "splitEqs"
    ///   parens $ (SplitG . SplitId . fromIntegral) <$> natural
    /// ```
    /// and the pretty-printer at Constraints.hs:279-280 emits
    /// `splitEqs(<i64>)`.  The matcher looks up `Goal::Split(SplitId(N))`
    /// by exact id — split ids are stable identifiers minted by the
    /// equation store, not subject to LVar-style renaming.
    Split { split_id: i64 },
    /// Anything we didn't structurally recognise.  Kept as raw text so
    /// the walker can choose to either (a) fall back to auto-prover or
    /// (b) be extended later to handle it.
    Raw(String),
}

/// Structural signature of one alt inside a `solve( a ∥ b ∥ … )` text.
/// See [`GoalSpec::Disj`] for context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisjAlt {
    /// `∀ x1 .. xN. …`  — universally quantified alt with `n_vars`
    /// bound names.
    All { n_vars: usize },
    /// `∃ x1 .. xN. …`  — existentially quantified alt with `n_vars`
    /// bound names.
    Ex { n_vars: usize },
    /// Atom, conjunction of atoms, or negated atom — anything that
    /// does NOT begin with a top-level quantifier.  We don't try to
    /// match deeper here; the count + shape mix is enough to
    /// distinguish disjs that co-exist in `sys.goals` at any replay
    /// point.
    NonQuant,
}

// =============================================================================
// Tactics
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Tactic {
    pub name: String,
    pub raw: String,
}

// =============================================================================
// Processes (SAPIC)
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct ProcessDef {
    pub name: String,
    pub vars: Option<Vec<VarSpec>>,
    pub body: Process,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Process {
    Null,
    Action {
        action: SapicAction,
        body: Box<Process>,
    },
    Comb {
        comb: ProcessComb,
        left: Box<Process>,
        right: Box<Process>,
    },
    Replication(Box<Process>),
    /// Process called by name (with optional argument list).
    Call {
        name: String,
        args: Vec<Term>,
    },
    /// (...) @ term — annotation
    AtAnnotation(Box<Process>, Term),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SapicAction {
    New(VarSpec),
    Insert(Term, Term),
    Delete(Term),
    ChIn {
        chan: Option<Term>,
        msg: Term,
    },
    ChOut {
        chan: Option<Term>,
        msg: Term,
    },
    Lock(Term),
    Unlock(Term),
    Event(Fact),
    /// embedded MSR rule
    Msr {
        prems: Vec<Fact>,
        acts: Vec<Fact>,
        concs: Vec<Fact>,
        restrictions: Vec<Formula>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProcessComb {
    Parallel,
    Ndc,
    /// `if cond then ... else ...`
    Cond(Condition),
    /// `lookup t as v in ... else ...`
    Lookup(Term, VarSpec),
    /// `let pat = t in ... else ...`
    Let {
        pat: Term,
        value: Term,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Condition {
    Eq(Term, Term),
    Formula(Formula),
}

// =============================================================================
// Facts
// =============================================================================

#[derive(Debug, Clone)]
pub struct Fact {
    pub persistent: bool,
    pub name: String,
    pub args: Vec<Term>,
    pub annotations: Vec<FactAnnotation>,
    pub location: Location,
}

impl PartialEq for Fact {
    fn eq(&self, other: &Self) -> bool {
        // Compilation error once we add new fields
        let Fact {
            persistent: _,
            name: _,
            args: _,
            annotations: _,
            location: _,
        } = self;
        let Fact {
            persistent: _,
            name: _,
            args: _,
            annotations: _,
            location: _,
        } = other;
        // Everything but the location
        self.persistent == other.persistent
            && self.name == other.name
            && self.args == other.args
            && self.annotations == other.annotations
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}

// =============================================================================
// Formulas
// =============================================================================

#[derive(Debug, Clone)]
pub struct Formula {
    pub kind: FormulaKind,
    pub location: Location,
}

impl Formula {
    pub fn new(kind: FormulaKind, location: Location) -> Self {
        Self { kind, location }
    }

    pub fn and(self, other: Formula) -> Self {
        let new_loc = Location::from_locations(self.location, other.location);
        Formula::new(FormulaKind::And(Box::new(self), Box::new(other)), new_loc)
    }

    pub fn or(self, other: Formula) -> Self {
        let new_loc = Location::from_locations(self.location, other.location);
        Formula::new(FormulaKind::Or(Box::new(self), Box::new(other)), new_loc)
    }

    pub fn implies(self, other: Formula) -> Self {
        let new_loc = Location::from_locations(self.location, other.location);
        Formula::new(
            FormulaKind::Implies(Box::new(self), Box::new(other)),
            new_loc,
        )
    }

    pub fn iff(self, other: Formula) -> Self {
        let new_loc = Location::from_locations(self.location, other.location);
        Formula::new(FormulaKind::Iff(Box::new(self), Box::new(other)), new_loc)
    }

    pub fn not(inner: Formula, start: Location) -> Self {
        let new_loc = Location::from_locations(start, inner.location);
        Formula::new(FormulaKind::Not(Box::new(inner)), new_loc)
    }

    pub fn forall(vars: Vec<VarSpec>, body: Formula, start: Location) -> Self {
        let new_loc = Location::from_locations(start, body.location);
        Formula::new(FormulaKind::Forall(vars, Box::new(body)), new_loc)
    }

    pub fn exists(vars: Vec<VarSpec>, body: Formula, start: Location) -> Self {
        let new_loc = Location::from_locations(start, body.location);
        Formula::new(FormulaKind::Exists(vars, Box::new(body)), new_loc)
    }

    pub fn atom(atom: Atom, location: Location) -> Self {
        Formula::new(FormulaKind::Atom(atom), location)
    }

    pub fn r#false(location: Location) -> Self {
        Formula::new(FormulaKind::False, location)
    }

    pub fn r#true(location: Location) -> Self {
        Formula::new(FormulaKind::True, location)
    }
}

impl Deref for Formula {
    type Target = FormulaKind;

    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        // Compilation error once we add new fields
        let Formula {
            kind: _,
            location: _,
        } = self;
        let Formula {
            kind: _,
            location: _,
        } = other;
        // Everything but the location
        self.kind == other.kind
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FormulaKind {
    False,
    True,
    Atom(Atom),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(Vec<VarSpec>, Box<Formula>),
    Exists(Vec<VarSpec>, Box<Formula>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    Eq(Term, Term),
    Less(Term, Term),     // tp < tp
    LessMset(Term, Term), // t (<) t
    Subterm(Term, Term),
    /// `F @ t`
    Action(Fact, Term),
    /// `last(t)`
    Last(Term),
    /// predicate (parsed as fact)
    Pred(Fact),
}

// =============================================================================
// Terms
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Var(VarSpec),
    PubLit(String),   // 'foo'
    FreshLit(String), // ~'n'
    NatLit(String),   // %'n'
    Number(u64),      // bare integer literal (e.g. for %+)
    NumberOne,        // 1
    NatOne,           // 1:nat / %1
    DhNeutral,
    /// Function or operator application by name.
    App(String, Vec<Term>),
    /// `op{arg1}arg2` algebraic syntax.
    AlgApp(String, Box<Term>, Box<Term>),
    /// Pair / tuple `<a, b, c>` (right-associative).
    Pair(Vec<Term>),
    /// `diff(a, b)`
    Diff(Box<Term>, Box<Term>),
    /// AC binary operations (left-associative).
    BinOp(BinOp, Box<Term>, Box<Term>),
    /// SAPIC pattern-match syntax `=t`: literal-match the inner term rather
    /// than bind it.
    PatMatch(Box<Term>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Exp,     // ^
    Mult,    // *
    Union,   // + or ++
    Xor,     // XOR or ⊕
    NatPlus, // %+
    /// A user-declared `[AC]` function symbol, applied infix (`(x add y)`).
    /// Carries the bare symbol name; the rendered separator is the name
    /// surrounded by spaces.  The name is interned, which is what lets the
    /// variant borrow it for `'static` and keep the enum `Copy`.
    AcFct(&'static str),
}

impl BinOp {
    /// The string HS `prettyTerm` puts between the operands of this operator.
    ///
    /// The five builtin operators are the literal separators of `prettyTerm`'s
    /// `ppTerms`/`exp` arms (`*`, `⊕`, `++`, `%+`, `^`; Term/Term.hs:306-310).
    /// A user-declared `[AC]` symbol is separated by `" " ++ BC.unpack f ++ " "`
    /// (Term/Term.hs:305), i.e. its name with the spaces included, so that one
    /// arm owns a `String`.
    ///
    /// This is the single separator table: printers that need a `&'static str`
    /// (the `LNTerm` printer hands separators to a `Doc`) intern the owned arm.
    pub fn separator(&self) -> std::borrow::Cow<'static, str> {
        use std::borrow::Cow;
        match self {
            BinOp::Exp => Cow::Borrowed("^"),
            BinOp::Mult => Cow::Borrowed("*"),
            BinOp::Union => Cow::Borrowed("++"),
            BinOp::Xor => Cow::Borrowed("\u{2295}"),
            BinOp::NatPlus => Cow::Borrowed("%+"),
            BinOp::AcFct(name) => Cow::Owned(format!(" {name} ")),
        }
    }
}

#[derive(Debug, Clone)]
pub struct VarSpec {
    pub name: String,
    pub idx: u64,
    pub sort: SortHint,
    pub typ: Option<String>, // SAPIC type annotation
    pub location: Location,
}

impl PartialEq for VarSpec {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            name: _,
            idx: _,
            sort: _,
            typ: _,
            location: _,
        } = self;
        let Self {
            name: _,
            idx: _,
            sort: _,
            typ: _,
            location: _,
        } = other;
        // Everything but location
        self.name == other.name
            && self.idx == other.idx
            && self.sort == other.sort
            && self.typ == other.typ
    }
}

impl Eq for VarSpec {}

impl std::hash::Hash for VarSpec {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let Self {
            name: _,
            idx: _,
            sort: _,
            typ: _,
            location: _,
        } = self;
        // Everything but location
        self.name.hash(state);
        self.idx.hash(state);
        self.sort.hash(state);
        self.typ.hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SortHint {
    Msg,
    Pub,   // $x
    Fresh, // ~x
    Node,  // #x
    Nat,   // %x
    /// Sort given by suffix `: msg | : pub | : fresh | : node | : nat`.
    Suffix(SuffixSort),
    /// No sort hint: bare identifier, sort to be inferred.
    #[default]
    Untagged,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuffixSort {
    Msg,
    Pub,
    Fresh,
    Node,
    Nat,
}

impl SuffixSort {
    fn as_str(&self) -> &'static str {
        match self {
            SuffixSort::Msg => "msg",
            SuffixSort::Pub => "pub",
            SuffixSort::Fresh => "fresh",
            SuffixSort::Node => "node",
            SuffixSort::Nat => "nat",
        }
    }
}

impl std::fmt::Display for VarSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.sort {
            SortHint::Fresh => write!(f, "~{}", self.name)?,
            SortHint::Pub => write!(f, "${}", self.name)?,
            SortHint::Node => write!(f, "#{}", self.name)?,
            SortHint::Nat => write!(f, "%{}", self.name)?,
            SortHint::Msg | SortHint::Untagged => write!(f, "{}", self.name)?,
            SortHint::Suffix(s) => write!(f, "{}:{}", self.name, s.as_str())?,
        }
        if self.idx != 0 {
            write!(f, ".{}", self.idx)?;
        }
        if let Some(typ) = &self.typ {
            write!(f, ":{typ}")?;
        }
        Ok(())
    }
}

// =============================================================================
// Flag formulas (for #ifdef)
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum FlagFormula {
    Atom(String),
    Not(Box<FlagFormula>),
    And(Box<FlagFormula>, Box<FlagFormula>),
    Or(Box<FlagFormula>, Box<FlagFormula>),
}

#[cfg(test)]
mod tests {
    use super::BinOp;

    /// The separator strings HS `prettyTerm` puts between operands
    /// (Term/Term.hs:305-310).  Every printer of a `BinOp` reads them from
    /// here, so a typo would move in lockstep across all of them — pin the
    /// table itself.
    #[test]
    fn separator_table_matches_prettyterm() {
        assert_eq!(BinOp::Exp.separator(), "^");
        assert_eq!(BinOp::Mult.separator(), "*");
        assert_eq!(BinOp::Union.separator(), "++");
        assert_eq!(BinOp::Xor.separator(), "\u{2295}");
        assert_eq!(BinOp::NatPlus.separator(), "%+");
        // A user-declared `[AC]` symbol keeps the surrounding spaces.
        assert_eq!(BinOp::AcFct("add").separator(), " add ");
        // Only that arm needs to own its string.
        assert!(matches!(
            BinOp::Exp.separator(),
            std::borrow::Cow::Borrowed(_)
        ));
        assert!(matches!(
            BinOp::AcFct("add").separator(),
            std::borrow::Cow::Owned(_)
        ));
    }
}
