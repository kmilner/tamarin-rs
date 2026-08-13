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

use std::{borrow::Borrow, ops::Deref};

use crate::parser::Location;

#[derive(Debug, Clone, PartialEq)]
pub struct Theory {
    pub is_diff: bool,
    pub name: SpannedStr,
    pub configuration: Option<SpannedStr>,
    pub items: Vec<TheoryItem>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem {
    Builtins(Vec<SpannedStr>),
    Functions(Vec<FunctionDecl>),
    Equations {
        convergent: bool,
        eqs: Vec<Equation>,
    },
    Macros(Vec<Macro>),
    Predicates(Vec<Predicate>),
    Options(Vec<SpannedStr>),
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
    Define(SpannedStr),
    Include(SpannedStr),
}

#[derive(Debug, Clone)]
/// A string with a source location.
pub struct SpannedStr {
    pub content: String,
    pub location: Location,
}

impl SpannedStr {
    /// Create a new identifier with the given name and location.
    pub fn new(name: impl Into<String>, location: Location) -> Self {
        Self {
            content: name.into(),
            location,
        }
    }

    /// Create a synthetic identifier with the given name and a dummy location.
    pub fn synthetic(name: impl Into<String>) -> Self {
        Self {
            content: name.into(),
            location: Location {
                line: 0,
                col: 0,
                start: 0,
                end: 0,
            },
        }
    }
}

impl std::hash::Hash for SpannedStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.content.hash(state);
    }
}

impl From<SpannedStr> for String {
    fn from(id: SpannedStr) -> Self {
        id.content
    }
}

impl<S> PartialEq<S> for SpannedStr
where
    S: AsRef<str>,
{
    fn eq(&self, other: &S) -> bool {
        self.content == other.as_ref()
    }
}

impl Eq for SpannedStr {}

impl PartialEq<SpannedStr> for String {
    fn eq(&self, other: &SpannedStr) -> bool {
        self == &other.content
    }
}

impl PartialEq<SpannedStr> for &str {
    fn eq(&self, other: &SpannedStr) -> bool {
        self == &other.content
    }
}

impl<S> PartialOrd<S> for SpannedStr
where
    S: AsRef<str>,
{
    fn partial_cmp(&self, other: &S) -> Option<std::cmp::Ordering> {
        self.content.as_str().partial_cmp(other.as_ref())
    }
}

impl Ord for SpannedStr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let SpannedStr { content: a, .. } = self;
        let SpannedStr { content: b, .. } = other;
        a.cmp(b)
    }
}

impl Deref for SpannedStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.content
    }
}

impl AsRef<str> for SpannedStr {
    fn as_ref(&self) -> &str {
        &self.content
    }
}

impl Borrow<str> for SpannedStr {
    fn borrow(&self) -> &str {
        &self.content
    }
}

impl Borrow<String> for SpannedStr {
    fn borrow(&self) -> &String {
        &self.content
    }
}

impl std::fmt::Display for SpannedStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.content)
    }
}

// =============================================================================
// Functions / equations / macros / predicates / restrictions
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDecl {
    pub name: SpannedStr,
    pub arg_types: Vec<Option<SpannedStr>>,
    pub out_type: Option<SpannedStr>,
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    pub name: SpannedStr,
    pub args: Vec<VarSpec>,
    pub body: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Predicate {
    pub fact: Fact,
    pub formula: Formula,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Restriction {
    pub name: SpannedStr,
    pub formula: Formula,
    pub attributes: Vec<RestrictionAttr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RestrictionAttr {
    LeftRestriction,
    RightRestriction,
}

// =============================================================================
// Rules
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Rule {
    pub name: SpannedStr,
    pub modulo: Option<SpannedStr>, // E or AC
    pub attributes: Vec<RuleAttr>,
    pub let_block: Vec<LetBinding>,
    pub premises: Vec<Fact>,
    pub actions: Vec<Fact>,
    pub conclusions: Vec<Fact>,
    pub embedded_restrictions: Vec<Formula>,
    pub variants: Vec<Rule>,
    pub left_right: Option<(Box<Rule>, Box<Rule>)>,
}

impl Rule {
    pub fn name(&self) -> &str {
        &self.name.content
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RuleAttr {
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
    pub name: SpannedStr,
    pub modulo: Option<SpannedStr>,
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
    pub name: SpannedStr,
    pub attributes: Vec<LemmaAttr>,
    pub proof: Option<ProofSkeleton>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AccLemma {
    pub name: SpannedStr,
    pub attributes: Vec<LemmaAttr>,
    pub formula: Formula,
    pub case_test_idents: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: SpannedStr,
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
    pub name: SpannedStr,
    pub raw: SpannedStr,
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

#[derive(Debug, Clone, PartialEq)]
pub struct Fact {
    pub persistent: bool,
    pub name: SpannedStr,
    pub args: Vec<Term>,
    pub annotations: Vec<FactAnnotation>,
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

#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarSpec {
    pub name: String,
    pub idx: u64,
    pub sort: SortHint,
    pub typ: Option<String>, // SAPIC type annotation
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
