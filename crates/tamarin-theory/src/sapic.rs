// Currently GPL 3.0 until granted permission by the following authors:
//   Robert Künnemann, Charlie Jacomme, Artur Cygan, Kevin Morio, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Basetranslation.hs, lib/sapic/src/Sapic/Bindings.hs,
//   lib/sapic/src/Sapic/ProcessUtils.hs, lib/sapic/src/Sapic/Typing.hs,
//   lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Sapic/Term.hs

//! Port of `Theory.Sapic.{Position, Term, Annotation, Process}` from
//! `lib/theory/src/Theory/Sapic/`.
//!
//! Foundational SAPIC types: positions, sorted variables, processes.
//! These live in `tamarin-theory` (not `tamarin-sapic`) because Haskell
//! places them in `lib/theory/src/Theory/Sapic/`.
//!
//! Coverage:
//! - `Theory.Sapic.Position` — full
//! - `Theory.Sapic.Term` — `SapicType`, `SapicLVar` data types and
//!   defaults; pretty-printing (`pretty_sapic.rs`) and `to_lvar` ported.
//!   The `toLNTerm` converter is not ported yet.
//! - `Theory.Sapic.Annotation` — `ProcessParsedAnnotation` and the
//!   `GoodAnnotation` trait
//! - `Theory.Sapic.Process` — the `Process<Ann, V>` data type and
//!   `SapicAction`/`ProcessCombinator`. The Haskell traversal helpers
//!   (`foldProcess`, `traverseTermsAction`, etc.) are not ported.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LSort, LVar, Name};
use tamarin_term::subst::Subst;
use tamarin_term::vterm::VTerm;

use crate::fact::Fact;
use crate::formula::ProtoFormula;
use crate::atom::SyntacticSugar;

// =============================================================================
// Position
// =============================================================================

pub type ProcessPosition = Vec<i64>;

/// `lhsP p`: append `1` to `p` (left branch).
// Intentionally retained: faithful HS port; exercised only by tests so far.
pub fn lhs_position(mut p: ProcessPosition) -> ProcessPosition {
    p.push(1);
    p
}

/// `rhsP p`: append `2` to `p` (right branch).
// Intentionally retained: faithful HS port; exercised only by tests so far.
pub fn rhs_position(mut p: ProcessPosition) -> ProcessPosition {
    p.push(2);
    p
}

/// `descendant child parent`: whether `parent` is a prefix of `child`.
pub fn descendant<T: PartialEq>(child: &[T], parent: &[T]) -> bool {
    if parent.len() > child.len() { return false; }
    parent.iter().zip(child.iter()).all(|(a, b)| a == b)
}

pub fn pretty_position(p: &ProcessPosition) -> String {
    p.iter().map(|n| n.to_string()).collect()
}

// =============================================================================
// SapicType / SapicLVar
// =============================================================================

/// SAPIC variables carry an optional type tag (`Some("node")`, `Some("Any")`, …).
pub type SapicType = Option<String>;

// Intentionally retained: faithful HS port; no caller yet.
pub fn default_sapic_type_string() -> String { "Any".to_string() }
pub fn default_sapic_type() -> SapicType { None }
pub fn default_sapic_node_type() -> SapicType { Some("node".to_string()) }

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SapicLVar {
    pub var: LVar,
    pub stype: SapicType,
}

impl SapicLVar {
    pub fn new(var: LVar, stype: SapicType) -> Self { SapicLVar { var, stype } }
    pub fn untyped(var: LVar) -> Self { SapicLVar { var, stype: None } }
    pub fn to_lvar(&self) -> LVar { self.var.clone() }
}

/// `SapicNTerm<V>` ≡ `VTerm<Name, V>` — SAPIC terms carry `Name` constants.
pub type SapicNTerm<V> = VTerm<Name, V>;
pub type SapicTerm = SapicNTerm<SapicLVar>;
pub type SapicNFact<V> = Fact<SapicNTerm<V>>;
pub type SapicLNFact = Fact<SapicTerm>;
pub type SapicNFormula<V> =
    ProtoFormula<SyntacticSugar<SapicNTerm<V>>, (String, LSort), Name, V>;
pub type SapicFormula =
    ProtoFormula<SyntacticSugar<SapicNTerm<SapicLVar>>, (String, LSort), Name, SapicLVar>;

// =============================================================================
// Annotation
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProcessParsedAnnotation {
    /// Identifiers that produced this subprocess via inlined `let`-bindings.
    pub process_names: Vec<String>,
    /// Optional location for Isolated Execution Environments.
    pub location: Option<SapicTerm>,
    /// Substitution that maps renamed variables back to the user's
    /// original names. Empty until uniqueness renaming has run.
    pub back_substitution: Subst<Name, LVar>,
}

impl Default for ProcessParsedAnnotation {
    fn default() -> Self {
        ProcessParsedAnnotation {
            process_names: Vec::new(),
            location: None,
            back_substitution: Subst::empty(),
        }
    }
}

impl ProcessParsedAnnotation {
    pub fn empty() -> Self { Self::default() }
    pub fn append(self, other: Self) -> Self {
        let mut names = self.process_names;
        names.extend(other.process_names);
        let location = match (self.location, other.location) {
            (_, Some(l2)) => Some(l2),
            (l1, None) => l1,
        };
        let back_substitution = self.back_substitution.compose(&other.back_substitution);
        ProcessParsedAnnotation { process_names: names, location, back_substitution }
    }
}

/// `GoodAnnotation`: any annotation that can recover the parsed-stage info.
pub trait GoodAnnotation: Sized {
    fn parsed(&self) -> &ProcessParsedAnnotation;
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self;
    fn default_annotation() -> Self;
}

impl GoodAnnotation for ProcessParsedAnnotation {
    fn parsed(&self) -> &ProcessParsedAnnotation { self }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self { p }
    fn default_annotation() -> Self { Self::default() }
}

// =============================================================================
// Process
// =============================================================================

// Note: only `PartialEq` (not `Eq`) — the `Msr` variant carries a
// `tamarin_parser::ast::Formula` in its `rest` (embedded-restriction) field,
// which is `PartialEq` but not `Eq` (mirrors `ProcessCombinator::Cond`).
#[derive(Debug, Clone, PartialEq)]
pub enum SapicAction<V> {
    Rep,
    New(V),
    ChIn {
        chan: Option<SapicNTerm<V>>,
        msg: SapicNTerm<V>,
        match_vars: BTreeSet<V>,
    },
    ChOut {
        chan: Option<SapicNTerm<V>>,
        msg: SapicNTerm<V>,
    },
    Insert(SapicNTerm<V>, SapicNTerm<V>),
    Delete(SapicNTerm<V>),
    Lock(SapicNTerm<V>),
    Unlock(SapicNTerm<V>),
    Event(SapicNFact<V>),
    ProcessCall(String, Vec<SapicNTerm<V>>),
    Msr {
        prems: Vec<SapicNFact<V>>,
        acts: Vec<SapicNFact<V>>,
        concs: Vec<SapicNFact<V>>,
        /// Embedded `_restrict(...)` formulas attached to the MSR's action row
        /// (`[l]--[a restricting φ]->[r]`).  HS stores these as
        /// `SapicNFormula v` (Process.hs:88); the RS port carries the
        /// un-expanded parser-AST [`tamarin_parser::ast::Formula`] directly,
        /// exactly as `ProcessCombinator::Cond` does — the base translation
        /// (`baseTransAction` MSR, Basetranslation.hs:200-203) keeps them as the
        /// rule's 4th (restriction) component, which then flows through
        /// `lift_rule_restrictions` (HS `liftedAddProtoRule`) unchanged, so a
        /// `SapicNFormula` round-trip would be lossy with no consumer.
        rest: Vec<tamarin_parser::ast::Formula>,
        match_vars: BTreeSet<V>,
    },
}

// Note: only `PartialEq` (not `Eq`) — the `Cond` variant carries a
// `tamarin_parser::ast::Formula`, which is `PartialEq` but not `Eq`.
#[derive(Debug, Clone, PartialEq)]
pub enum ProcessCombinator<V> {
    Parallel,
    /// Non-deterministic choice.
    Ndc,
    /// `if <formula> then .. else ..`.  HS stores this as a
    /// `Cond (SapicNFormula v)` (a `ProtoFormula`/`SyntacticSugar` formula),
    /// `lib/theory/src/Theory/Sapic/Process.hs:94`.  The RS port carries the
    /// (un-expanded) parser-AST [`tamarin_parser::ast::Formula`] instead: every
    /// downstream use is parser-AST based — the `process="if .."` attribute
    /// renders it flat (mirroring `prettySyntacticSapicFormula`), and the
    /// embedded `_restrict` expansion (`rule_restriction::lift_rule_restrictions`,
    /// HS `liftedAddProtoRule`) consumes a parser-AST `Formula` — so storing the
    /// parser formula avoids a lossy DeBruijn round-trip with no consumer of the
    /// elaborated form.  Variable renaming (`renameUnique`) and the WFUnbound
    /// check operate on its `VarSpec`s directly.
    Cond(tamarin_parser::ast::Formula),
    CondEq(SapicNTerm<V>, SapicNTerm<V>),
    Lookup(SapicNTerm<V>, V),
    Let {
        left: SapicNTerm<V>,
        right: SapicNTerm<V>,
        match_vars: BTreeSet<V>,
    },
}

// Note: only `PartialEq` (not `Eq`) — a `Comb` may carry a `Cond` formula
// (`tamarin_parser::ast::Formula`), which is `PartialEq` but not `Eq`.
#[derive(Debug, Clone, PartialEq)]
pub enum Process<Ann, V> {
    Null(Ann),
    Comb(ProcessCombinator<V>, Ann, Box<Process<Ann, V>>, Box<Process<Ann, V>>),
    Action(SapicAction<V>, Ann, Box<Process<Ann, V>>),
}

pub type LSapicAction = SapicAction<SapicLVar>;
pub type LProcessCombinator = ProcessCombinator<SapicLVar>;
pub type LProcess<Ann> = Process<Ann, SapicLVar>;
pub type PlainProcess = LProcess<ProcessParsedAnnotation>;

impl<Ann, V> Process<Ann, V> {
    pub fn null(ann: Ann) -> Self { Process::Null(ann) }
    pub fn annotation(&self) -> &Ann {
        match self {
            Process::Null(a) | Process::Comb(_, a, _, _) | Process::Action(_, a, _) => a,
        }
    }
}

/// `pfoldMap`: visit every node in the process tree calling `f`,
/// concatenating outputs. Traversal order matches Haskell
/// `pfoldMap` (Process.hs:285-296):
/// - `Null`: just `f(self)`.
/// - `Action`: self first, then the body (`f self <> pfoldMap body`).
/// - `Comb`: in-order — left subtree, then self, then right subtree
///   (`pfoldMap pl <> f self <> pfoldMap pr`).
pub fn pfold_map<Ann, V, T, F: FnMut(&Process<Ann, V>) -> Vec<T>>(
    p: &Process<Ann, V>,
    f: &mut F,
) -> Vec<T> {
    match p {
        Process::Null(_) => f(p),
        Process::Action(_, _, body) => {
            let mut out = f(p);
            out.extend(pfold_map(body, f));
            out
        }
        Process::Comb(_, _, l, r) => {
            let mut out = pfold_map(l, f);
            out.extend(f(p));
            out.extend(pfold_map(r, f));
            out
        }
    }
}

/// `processContains`: any node in `p` for which `f` returns true.
pub fn process_contains<Ann, V, F: FnMut(&Process<Ann, V>) -> bool>(
    p: &Process<Ann, V>,
    mut f: F,
) -> bool {
    let mut found = false;
    fn walk<Ann, V, F: FnMut(&Process<Ann, V>) -> bool>(
        p: &Process<Ann, V>,
        f: &mut F,
        found: &mut bool,
    ) {
        if *found { return; }
        if f(p) { *found = true; return; }
        match p {
            Process::Null(_) => {}
            Process::Action(_, _, body) => walk(body, f, found),
            Process::Comb(_, _, l, r) => {
                walk(l, f, found);
                walk(r, f, found);
            }
        }
    }
    walk(p, &mut f, &mut found);
    found
}

/// `processAt p pos`: subprocess at position `pos`. Returns `None` if the
/// position is invalid.
pub fn process_at<'a, Ann, V>(
    p: &'a Process<Ann, V>,
    pos: &[i64],
) -> Option<&'a Process<Ann, V>> {
    if pos.is_empty() { return Some(p); }
    match (p, pos[0]) {
        (Process::Null(_), _) => None,
        (Process::Action(_, _, body), 1) => process_at(body, &pos[1..]),
        (Process::Comb(_, _, l, _), 1) => process_at(l, &pos[1..]),
        (Process::Comb(_, _, _, r), 2) => process_at(r, &pos[1..]),
        _ => None,
    }
}

/// `PatternSapicLVar`: pattern variables either bind a new variable
/// (`PatternBind`) or match an existing one (`PatternMatch`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PatternSapicLVar {
    Bind(SapicLVar),
    Match(SapicLVar),
}

impl PatternSapicLVar {
    pub fn into_var(self) -> SapicLVar {
        match self {
            PatternSapicLVar::Bind(v) | PatternSapicLVar::Match(v) => v,
        }
    }
    pub fn as_var(&self) -> &SapicLVar {
        match self {
            PatternSapicLVar::Bind(v) | PatternSapicLVar::Match(v) => v,
        }
    }
}

/// `unpatternVar`: drop the bind/match tag.
// Intentionally retained: faithful HS port; exercised only by tests so far.
pub fn unpattern_var(p: PatternSapicLVar) -> SapicLVar { p.into_var() }

/// `freesSapicTerm`: free variables of a SAPIC term, in source order, with
/// duplicates (HS Sapic/Term.hs:131-132, `freesSapicTerm = foldMap (: [])` —
/// a plain in-order traversal, neither sorted nor deduplicated).
///
/// Order and duplicates are load-bearing: `bindingsAct`/`bindingsComb`
/// (Sapic/Bindings.hs:22-33) apply `nub` (first-occurrence dedup) to this
/// list, and that ordered list flows into the not-yet-ported
/// `Typing.mkSubst`, where `mapM freshLVar bvars` (Sapic/Typing.hs:267-269)
/// assigns fresh indices in binding-list order. Do not sort/dedup here.
pub fn frees_sapic_term(t: &SapicTerm) -> Vec<SapicLVar> {
    tamarin_term::vterm::vars_vterm_in_order(t)
}

/// `freesSapicFact`: free variables of a SAPIC fact, in source order, with
/// duplicates (HS Sapic/Term.hs:136-137, `freesSapicFact = foldMap
/// freesSapicTerm` — a plain `concatMap` over the fact's terms; no sort, no
/// dedup). See [`frees_sapic_term`] for why order/duplicates matter.
pub fn frees_sapic_fact(f: &Fact<SapicTerm>) -> Vec<SapicLVar> {
    let mut out = Vec::new();
    for t in &f.terms {
        out.extend(frees_sapic_term(t));
    }
    out
}

// =============================================================================
// Action / combinator predicates (mirroring Sapic.ProcessUtils)
//
// `is_lock`/`is_unlock`/`is_ch_in`/`is_ch_out`/`is_eq` are faithful ports of
// the corresponding HS predicates (ProcessUtils.hs:54-72), which are generic
// over the annotation and inspect only the action/combinator shape.
//
// `is_delete`/`is_lookup` are an INTENTIONALLY INCOMPLETE mirror: HS
// `isDelete`/`isLookup` (ProcessUtils.hs:46-52) are specialised to
// `Process (ProcessAnnotation LVar) v` and additionally require
// `pureState=False`, i.e. they exclude optimized pure-state states. That
// guard cannot be expressed here — these functions are generic over `Ann`,
// and `tamarin-theory` cannot reference `ProcessAnnotation`'s `pure_state`
// field without a dependency cycle (that type lives downstream in
// `tamarin-sapic`). Callers that need the HS `pureState=False` semantics
// (e.g. a future Sapic.Basetranslation port) MUST re-check `pure_state`
// themselves rather than relying on these predicates alone.
// =============================================================================

pub fn is_lock<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::Lock(_), _, _))
}
pub fn is_unlock<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::Unlock(_), _, _))
}
pub fn is_ch_in<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::ChIn { .. }, _, _))
}
pub fn is_ch_out<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::ChOut { .. }, _, _))
}
/// Incomplete mirror of HS `isDelete`: matches the `Delete` action shape but
/// omits the HS `pureState=False` guard (see module section note above).
pub fn is_delete<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::Delete(_), _, _))
}
pub fn is_eq<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Comb(ProcessCombinator::CondEq(_, _), _, _, _))
}
/// Incomplete mirror of HS `isLookup`: matches the `Lookup` combinator shape
/// but omits the HS `pureState=False` guard (see module section note above).
pub fn is_lookup<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Comb(ProcessCombinator::Lookup(_, _), _, _, _))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn position_helpers() {
        assert_eq!(lhs_position(vec![1, 2]), vec![1, 2, 1]);
        assert_eq!(rhs_position(vec![1, 2]), vec![1, 2, 2]);
        assert!(descendant(&[1, 2, 3], &[1, 2]));
        assert!(!descendant(&[1, 2], &[1, 2, 3]));
        assert_eq!(pretty_position(&vec![1, 2, 1]), "121");
    }

    #[test]
    fn sapic_lvar_round_trip() {
        let v = LVar::new("x", LSort::Msg, 0);
        let sv = SapicLVar::untyped(v.clone());
        assert_eq!(sv.to_lvar(), v);
    }

    #[test]
    fn parsed_annotation_append() {
        let mut a = ProcessParsedAnnotation::empty();
        a.process_names.push("A".into());
        let mut b = ProcessParsedAnnotation::empty();
        b.process_names.push("B".into());
        let merged = a.append(b);
        assert_eq!(merged.process_names, vec!["A", "B"]);
    }

    #[test]
    fn build_a_simple_null_process() {
        let p: PlainProcess = Process::null(ProcessParsedAnnotation::empty());
        assert!(matches!(p, Process::Null(_)));
    }

    fn null_proc() -> PlainProcess {
        Process::null(ProcessParsedAnnotation::empty())
    }

    fn lock_action(v: &str) -> PlainProcess {
        let term = tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(
            v,
            LSort::Msg,
            0,
        )));
        Process::Action(
            SapicAction::Lock(term),
            ProcessParsedAnnotation::empty(),
            Box::new(null_proc()),
        )
    }

    #[test]
    fn predicate_helpers() {
        assert!(is_lock(&lock_action("k")));
        assert!(!is_unlock(&lock_action("k")));
        assert!(!is_lock(&null_proc()));
    }

    #[test]
    fn process_at_returns_root_and_navigates() {
        let p = lock_action("k");
        assert!(process_at(&p, &[]).is_some());
        // Position [1] selects the action body (a Null).
        assert!(matches!(process_at(&p, &[1]), Some(Process::Null(_))));
        // Going further than the body fails.
        assert!(process_at(&p, &[1, 1]).is_none());
    }

    #[test]
    fn process_contains_finds_locks() {
        let p = lock_action("k");
        assert!(process_contains(&p, is_lock));
        assert!(!process_contains(&null_proc(), is_lock));
    }

    #[test]
    fn pattern_var_round_trip() {
        let v = SapicLVar::untyped(LVar::new("x", LSort::Msg, 0));
        let pb = PatternSapicLVar::Bind(v.clone());
        let pm = PatternSapicLVar::Match(v.clone());
        assert_eq!(unpattern_var(pb), v);
        assert_eq!(unpattern_var(pm), v);
    }
}
