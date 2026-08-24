// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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

use tamarin_term::lterm::{BVar, LVar, Name};
use tamarin_term::subst::Subst;
use tamarin_term::term::map_lits;
use tamarin_term::vterm::{Lit, VTerm};

use crate::atom::map_atom;
use crate::fact::Fact;
use crate::formula::{map_atoms, SyntacticLNFormula, SyntacticNFormula};

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
    if parent.len() > child.len() {
        return false;
    }
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

/// HS `defaultSapicTypeS` (Theory/Sapic/Term.hs:94-95) — the type printed for an
/// undeclared argument / return type (see
/// `pretty_theory::pretty_function_typing_info`).
pub fn default_sapic_type_string() -> String {
    "Any".to_string()
}
pub fn default_sapic_type() -> SapicType {
    None
}
pub fn default_sapic_node_type() -> SapicType {
    Some("node".to_string())
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SapicLVar {
    pub var: LVar,
    pub stype: SapicType,
}

impl SapicLVar {
    pub fn new(var: LVar, stype: SapicType) -> Self {
        SapicLVar { var, stype }
    }
    pub fn untyped(var: LVar) -> Self {
        SapicLVar { var, stype: None }
    }
    pub fn to_lvar(&self) -> LVar {
        self.var
    }
}

/// `SapicNTerm<V>` ≡ `VTerm<Name, V>` — SAPIC terms carry `Name` constants.
pub type SapicNTerm<V> = VTerm<Name, V>;
pub type SapicTerm = SapicNTerm<SapicLVar>;
pub type SapicNFact<V> = Fact<SapicNTerm<V>>;
pub type SapicLNFact = Fact<SapicTerm>;
/// HS `SapicNFormula v` (Theory/Sapic/Term.hs:73) — the same declaration as
/// HS `SyntacticNFormula v` (Theory/Model/Formula.hs:264).
pub type SapicNFormula<V> = SyntacticNFormula<V>;
/// HS `SapicFormula` (Theory/Sapic/Term.hs:74).
pub type SapicFormula = SapicNFormula<SapicLVar>;

/// HS `toLFormula` (Theory/Sapic/Term.hs:152-154): replace each free
/// variable by its `LVar`, dropping the type tag.  The four nested `fmap`s
/// under `mapAtoms` reach the atom's terms, each term's literals, each
/// literal's variable and the `BVar` inside it, so a bound De Bruijn index
/// and the binder hints cross unchanged.
pub fn to_lformula(f: &SapicFormula) -> SyntacticLNFormula {
    map_atoms(f.clone(), &mut |_, a| {
        map_atom(a, &mut |t| {
            map_lits(t, &mut |l| match l {
                Lit::Con(c) => Lit::Con(*c),
                Lit::Var(BVar::Bound(i)) => Lit::Var(BVar::Bound(*i)),
                Lit::Var(BVar::Free(v)) => Lit::Var(BVar::Free(v.to_lvar())),
            })
        })
    })
}

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
    pub fn empty() -> Self {
        Self::default()
    }
    pub fn append(self, other: Self) -> Self {
        let mut names = self.process_names;
        names.extend(other.process_names);
        let location = match (self.location, other.location) {
            (_, Some(l2)) => Some(l2),
            (l1, None) => l1,
        };
        let back_substitution = self.back_substitution.compose(&other.back_substitution);
        ProcessParsedAnnotation {
            process_names: names,
            location,
            back_substitution,
        }
    }
}

/// `GoodAnnotation`: any annotation that can recover the parsed-stage info.
pub trait GoodAnnotation: Sized {
    fn parsed(&self) -> &ProcessParsedAnnotation;
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self;
    fn default_annotation() -> Self;
}

impl GoodAnnotation for ProcessParsedAnnotation {
    fn parsed(&self) -> &ProcessParsedAnnotation {
        self
    }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self {
        p
    }
    fn default_annotation() -> Self {
        Self::default()
    }
}

// =============================================================================
// Process
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
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
        /// (`[l]--[a restricting φ]->[r]`).  HS `iRest :: [SapicNFormula v]`
        /// (Theory/Sapic/Process.hs:81): each is a locally-nameless formula
        /// over the process's own variable type, with the parser's `Pred`
        /// sugar left un-expanded — the base translation (`baseTransAction`
        /// MSR, Basetranslation.hs:200-203) hands them to the rule's 4th
        /// (restriction) component, where `lift_rule_restrictions`
        /// (HS `liftedAddProtoRule`) expands the predicates.
        rest: Vec<SapicNFormula<V>>,
        match_vars: BTreeSet<V>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcessCombinator<V> {
    Parallel,
    /// Non-deterministic choice.
    Ndc,
    /// `if <formula> then .. else ..`.  HS `Cond (SapicNFormula v)`
    /// (Theory/Sapic/Process.hs:94): the condition is a
    /// locally-nameless formula over the process's own variable type, with
    /// the parser's `Pred` sugar left un-expanded — `lift_rule_restrictions`
    /// (HS `liftedAddProtoRule`) expands it once the base translation has
    /// made it a rule's restriction.
    Cond(SapicNFormula<V>),
    CondEq(SapicNTerm<V>, SapicNTerm<V>),
    Lookup(SapicNTerm<V>, V),
    Let {
        left: SapicNTerm<V>,
        right: SapicNTerm<V>,
        match_vars: BTreeSet<V>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Process<Ann, V> {
    Null(Ann),
    Comb(
        ProcessCombinator<V>,
        Ann,
        Box<Process<Ann, V>>,
        Box<Process<Ann, V>>,
    ),
    Action(SapicAction<V>, Ann, Box<Process<Ann, V>>),
}

pub type LSapicAction = SapicAction<SapicLVar>;
pub type LProcessCombinator = ProcessCombinator<SapicLVar>;
pub type LProcess<Ann> = Process<Ann, SapicLVar>;
pub type PlainProcess = LProcess<ProcessParsedAnnotation>;

impl<Ann, V> Process<Ann, V> {
    pub fn null(ann: Ann) -> Self {
        Process::Null(ann)
    }
    pub fn annotation(&self) -> &Ann {
        match self {
            Process::Null(a) | Process::Comb(_, a, _, _) | Process::Action(_, a, _) => a,
        }
    }
}

/// `pfoldMap`: visit every node in the process tree calling `f`,
/// concatenating outputs. Traversal order matches Haskell
/// `pfoldMap` (Theory/Sapic/Process.hs:285-296):
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
        if *found {
            return;
        }
        if f(p) {
            *found = true;
            return;
        }
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
pub fn process_at<'a, Ann, V>(p: &'a Process<Ann, V>, pos: &[i64]) -> Option<&'a Process<Ann, V>> {
    if pos.is_empty() {
        return Some(p);
    }
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
pub fn unpattern_var(p: PatternSapicLVar) -> SapicLVar {
    p.into_var()
}

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
    for t in f.terms.iter() {
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
    use tamarin_term::lterm::LSort;

    #[test]
    fn position_helpers() {
        assert_eq!(lhs_position(vec![1, 2]), vec![1, 2, 1]);
        assert_eq!(rhs_position(vec![1, 2]), vec![1, 2, 2]);
        assert!(descendant(&[1, 2, 3], &[1, 2]));
        assert!(!descendant(&[1, 2], &[1, 2, 3]));
        assert_eq!(pretty_position(&vec![1, 2, 1]), "121");
    }

    /// `untyped` is HS `SapicLVar v Nothing`. The type tag is absent. It does
    /// not hold the spelling of the default type. The difference is visible in
    /// two places. `pretty_function_typing_info` prints `defaultSapicTypeS`
    /// ("Any") for a `None`. The SAPIC typing pass treats a `Some` as a user
    /// declaration that it must respect. `to_lvar` drops whichever tag is
    /// present and returns the `LVar` unchanged.
    #[test]
    fn sapic_lvar_untyped_has_no_type_tag_and_to_lvar_drops_it() {
        let v = LVar::new("x", LSort::Msg, 0);
        let sv = SapicLVar::untyped(v);
        assert_eq!(sv.stype, None);
        assert_eq!(sv.stype, default_sapic_type());
        assert_eq!(sv.to_lvar(), v);
        // A tagged variable keeps its tag. `to_lvar` still returns the `LVar`
        // without the tag.
        let typed = SapicLVar::new(v, default_sapic_node_type());
        assert_eq!(typed.stype, Some("node".to_string()));
        assert_eq!(typed.to_lvar(), v);
        assert_ne!(typed, sv, "the type tag is part of the variable's identity");
    }

    /// `toLFormula` maps each free variable to its `LVar` through the atom,
    /// the term, the literal and the `BVar`, so a tag disappears wherever it
    /// sits, a bound index and its binder hint cross unchanged, and the
    /// sugar's fact is reached like any other atom.
    #[test]
    fn to_lformula_drops_type_tags_and_keeps_bound_indices() {
        use crate::atom::{ProtoAtom, SyntacticSugar};
        use crate::fact::{Fact, FactTag};
        use crate::formula::ProtoFormula;
        use tamarin_term::vterm::var_term;

        let y = LVar::new("y", LSort::Msg, 0);
        let tagged = var_term(BVar::Free(SapicLVar::new(y, Some("foo".to_string()))));
        fn pred<V>(t: VTerm<Name, BVar<V>>) -> SyntacticNFormula<V> {
            ProtoFormula::Atom(ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::new(
                FactTag::Term,
                vec![t],
            ))))
        }
        let hint = ("x".to_string(), LSort::Msg);
        let fm: SapicFormula = ProtoFormula::exists(
            hint.clone(),
            ProtoFormula::Atom(ProtoAtom::EqE(var_term(BVar::Bound(0)), tagged.clone()))
                .and(pred(tagged)),
        );

        let free = var_term(BVar::Free(y));
        let want: SyntacticLNFormula = ProtoFormula::exists(
            hint,
            ProtoFormula::Atom(ProtoAtom::EqE(var_term(BVar::Bound(0)), free.clone()))
                .and(pred(free)),
        );
        assert_eq!(to_lformula(&fm), want);
    }

    /// `<>` on the annotation works field by field, but each field behaves
    /// differently. The names concatenate from left to right. The location
    /// comes from the right side. An inner `at`-location therefore overrides
    /// an outer one. Only a `None` on the right keeps the location of the
    /// left. The back-substitutions compose.
    #[test]
    fn parsed_annotation_append_concats_names_and_right_biases_location() {
        let loc = |n: &str| {
            tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(n, LSort::Msg, 0)))
        };
        let ann = |name: &str, location: Option<SapicTerm>, sub: Subst<Name, LVar>| {
            ProcessParsedAnnotation {
                process_names: vec![name.to_string()],
                location,
                back_substitution: sub,
            }
        };
        let sub = |from: &str, to: &str| {
            Subst::from_list([(
                LVar::new(from, LSort::Msg, 0),
                tamarin_term::vterm::var_term(LVar::new(to, LSort::Msg, 0)),
            )])
        };

        let merged = ann("A", Some(loc("l1")), sub("y", "z")).append(ann(
            "B",
            Some(loc("l2")),
            sub("x", "y"),
        ));
        assert_eq!(merged.process_names, vec!["A", "B"]);
        assert_eq!(merged.location, Some(loc("l2")), "location is right-biased");
        // The operation is `compose` (`self . other`), not a union. The left
        // `y ~> z` rewrites the range of the right side, so `x ~> y` becomes
        // `x ~> z`. A union keeps `x ~> y`.
        assert_eq!(
            merged
                .back_substitution
                .image_of(&LVar::new("x", LSort::Msg, 0)),
            Some(&tamarin_term::vterm::var_term(LVar::new(
                "z",
                LSort::Msg,
                0
            )))
        );

        // A `None` on the right keeps the location of the left. A `Some` on
        // the right wins even when the left has no location.
        assert_eq!(
            ann("A", Some(loc("l1")), Subst::empty())
                .append(ann("B", None, Subst::empty()))
                .location,
            Some(loc("l1"))
        );
        assert_eq!(
            ann("A", None, Subst::empty())
                .append(ann("B", Some(loc("l2")), Subst::empty()))
                .location,
            Some(loc("l2"))
        );
        assert_eq!(ProcessParsedAnnotation::empty(), ann_empty());
    }

    /// `empty()` and `Default` must stay the same value.
    /// `GoodAnnotation::default_annotation` goes through `Default`. The
    /// `Process::null` call sites go through `empty()`.
    fn ann_empty() -> ProcessParsedAnnotation {
        <ProcessParsedAnnotation as GoodAnnotation>::default_annotation()
    }

    fn null_proc() -> PlainProcess {
        Process::null(ProcessParsedAnnotation::empty())
    }

    fn lock_action(v: &str) -> PlainProcess {
        let term = tamarin_term::vterm::var_term(SapicLVar::untyped(LVar::new(v, LSort::Msg, 0)));
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

    /// A process tree is `Eq`, and the comparison descends into the formulas
    /// a conditional and an embedded MSR's restrictions carry: two trees built
    /// from equal formulas are equal, and one changed atom separates them.
    #[test]
    fn process_equality_is_structural_over_condition_formulas() {
        use crate::atom::ProtoAtom;
        use crate::formula::ProtoFormula;
        use tamarin_term::vterm::var_term;

        fn requires_eq<T: Eq>(_: &T) {}

        let v = |n: &str| var_term(BVar::Free(SapicLVar::untyped(LVar::new(n, LSort::Msg, 0))));
        let eq =
            |l: &str, r: &str| -> SapicFormula { ProtoFormula::Atom(ProtoAtom::EqE(v(l), v(r))) };
        let proc = |cond: SapicFormula, rest: SapicFormula| -> PlainProcess {
            Process::Action(
                SapicAction::Msr {
                    prems: Vec::new(),
                    acts: Vec::new(),
                    concs: Vec::new(),
                    rest: vec![rest],
                    match_vars: BTreeSet::new(),
                },
                ann_empty(),
                Box::new(Process::Comb(
                    ProcessCombinator::Cond(cond),
                    ann_empty(),
                    Box::new(null_proc()),
                    Box::new(null_proc()),
                )),
            )
        };

        let p = proc(eq("x", "y"), eq("a", "b"));
        requires_eq(&p);
        assert_eq!(p, proc(eq("x", "y"), eq("a", "b")));
        assert_ne!(p, proc(eq("x", "z"), eq("a", "b")));
        assert_ne!(p, proc(eq("x", "y"), eq("a", "c")));
    }
}
