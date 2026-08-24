// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Surface-syntax AST for `.spthy` files: the loose tree [`crate::parser`]
//! produces and [`crate::wf`] (plus, downstream, `tamarin-theory`'s
//! elaboration) consumes.
//!
//! Nodes mirror Tamarin's concrete syntax rather than any single Haskell type —
//! the HS parser builds straight into the semantic `Theory`, so this is a
//! syntax-level staging form that a later elaboration pass lowers. [`Theory`] is
//! the root; every other type hangs off its [`TheoryItem`] stream.

use tamarin_term::lterm::LSort;

// =============================================================================
// Top-level theory
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Theory {
    pub is_diff: bool,
    pub name: String,
    pub configuration: Option<String>,
    pub items: Vec<TheoryItem>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem {
    Builtins(Vec<String>),
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

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct Restriction {
    pub name: String,
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

/// Parsed proof method.  Mirrors the `ProofMethod` values HS's
/// `proofMethod` (Theory/Text/Parser/Proof.hs:75-85) produces, plus
/// `SolvedLeaf` for the `SOLVED` keyword, which HS reads at the skeleton
/// level (`solvedProof`, Theory/Text/Parser/Proof.hs:102-103).
#[derive(Debug, Clone, PartialEq)]
pub enum ParsedMethod {
    /// `sorry` (HS `Sorry Nothing`).  This is the placeholder
    /// `replaceSorryProver` replaces.
    Sorry,
    /// `contradiction` (HS `Finished (Contradictory Nothing)`).
    Contradiction,
    /// `simplify` (HS `Simplify`).
    Simplify,
    /// `induction` (HS `Induction`).
    Induction,
    /// `solve( <goal> )` (HS `SolveGoal <goal>`).
    SolveGoal(GoalSpec),
    /// `SOLVED` (HS `Finished Solved`).
    SolvedLeaf,
    /// `UNFINISHABLE` (HS `Finished Unfinishable`).
    Unfinishable,
    /// `INVALIDATED` (HS `Invalidated`).
    Invalidated,
}

/// The goal of a stored `solve( ... )` step.
///
/// [`crate::parser::parse_goal_str`] builds these from HS's `goal` grammar
/// (Theory/Text/Parser/Proof.hs:38-72); they mirror the HS `Goal`
/// constructors (Constraints.hs:159-171) over surface terms and formulas
/// instead of `LNTerm`s and `LNGuarded`s.
#[derive(Debug, Clone, PartialEq)]
pub enum GoalSpec {
    /// `Fact( args... ) @ #i` — HS `ActionG LVar LNFact`.
    Action(VarSpec, Fact),
    /// `(#i, n) ~~> (#j, m)` — HS `ChainG NodeConc NodePrem`.  Both node
    /// variables carry their index, and both natural indices are kept.
    Chain((VarSpec, u64), (VarSpec, u64)),
    /// `Fact( args... ) ▶<n> #i` — HS `PremiseG NodePrem LNFact`.  The
    /// premise index is the subscript after `▶`.
    Premise((VarSpec, u64), Fact),
    /// `splitEqs(N)` — HS `SplitG SplitId`.
    Split(i64),
    /// `gf1 ∥ gf2 ∥ ...` — HS `DisjG (Disj LNGuarded)`.  Each disjunct is a
    /// `plainFormula`; HS's `guardedFormula`
    /// (Theory/Text/Parser/Formula.hs:122-127) turns it into an `LNGuarded`,
    /// which `tamarin_theory::elaborate::goal_from_parsed` does here.
    Disj(Vec<Formula>),
    /// `<small> ⊏ <big>` — HS `SubtermG (LNTerm, LNTerm)`.
    Subterm(Term, Term),
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

#[derive(Debug, Clone, PartialEq)]
pub struct Fact {
    pub persistent: bool,
    pub name: String,
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

/// A variable occurrence: HS `LVar` plus the SAPIC type annotation HS keeps
/// beside it in `SapicLVar` (Theory/Sapic/Term.hs:64-65).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarSpec {
    pub name: String,
    pub idx: u64,
    pub sort: LSort,
    pub typ: Option<String>, // SAPIC type annotation
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
