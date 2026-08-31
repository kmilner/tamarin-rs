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
//! - `Theory.Sapic.Process` — the `Process<Ann, V>` data type,
//!   `SapicAction`/`ProcessCombinator`, the term traversals
//!   (`mapTermsAction`/`mapTermsComb` and their `traverse` twins),
//!   `pfoldMap` and the `applyMatchVars` pair. `mapTerms`, `foldProcess`,
//!   `foldMProcess` and `traverseProcess` are not ported.

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

/// HS `defaultSapicTypeS` (Theory/Sapic/Term.hs:94-95).
pub(crate) const DEFAULT_SAPIC_TYPE: &str = "Any";

pub(crate) fn default_sapic_node_type() -> SapicType {
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

/// HS `instance Show SapicLVar` (Theory/Sapic/Term.hs:108-110): the variable's
/// own `Show LVar` (Term/LTerm.hs:550-557), followed by `":" ++ t` when the
/// variable carries a type tag.
impl std::fmt::Display for SapicLVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.var)?;
        match &self.stype {
            Some(t) => write!(f, ":{t}"),
            None => Ok(()),
        }
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

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProcessParsedAnnotation {
    /// Identifiers that produced this subprocess via inlined `let`-bindings.
    pub process_names: Vec<String>,
    /// Optional location for Isolated Execution Environments.
    pub location: Option<SapicTerm>,
    /// Substitution that maps renamed variables back to the user's
    /// original names. Empty until uniqueness renaming has run.
    pub back_substitution: Subst<Name, LVar>,
}

impl ProcessParsedAnnotation {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn map_location(mut self, f: impl FnOnce(SapicTerm) -> SapicTerm) -> Self {
        self.location = self.location.map(f);
        self
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
}

impl GoodAnnotation for ProcessParsedAnnotation {
    fn parsed(&self) -> &ProcessParsedAnnotation {
        self
    }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self {
        p
    }
}

// =============================================================================
// Process
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
        /// (restriction) component, where the SAPIC rule injection
        /// (`tamarin_sapic::apply`, HS `liftedAddProtoRule`) expands the
        /// predicates.
        rest: Vec<SapicNFormula<V>>,
        match_vars: BTreeSet<V>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProcessCombinator<V> {
    Parallel,
    /// Non-deterministic choice.
    Ndc,
    /// `if <formula> then .. else ..`.  HS `Cond (SapicNFormula v)`
    /// (Theory/Sapic/Process.hs:94): the condition is a
    /// locally-nameless formula over the process's own variable type, with
    /// the parser's `Pred` sugar left un-expanded — the SAPIC rule injection
    /// (`tamarin_sapic::apply`, HS `liftedAddProtoRule`) expands it once the
    /// base translation has made it a rule's restriction.
    Cond(SapicNFormula<V>),
    CondEq(SapicNTerm<V>, SapicNTerm<V>),
    Lookup(SapicNTerm<V>, V),
    Let {
        left: SapicNTerm<V>,
        right: SapicNTerm<V>,
        match_vars: BTreeSet<V>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

/// Rebuild a process while transforming every action, combinator and
/// annotation. The process shape and left-to-right traversal order are fixed;
/// passes only supply the payload transformations.
pub fn try_map_process<Ann, V, Ann2, V2, E>(
    p: &Process<Ann, V>,
    map_action: &mut impl FnMut(&SapicAction<V>) -> Result<SapicAction<V2>, E>,
    map_comb: &mut impl FnMut(&ProcessCombinator<V>) -> Result<ProcessCombinator<V2>, E>,
    map_ann: &mut impl FnMut(&Ann) -> Result<Ann2, E>,
) -> Result<Process<Ann2, V2>, E> {
    match p {
        Process::Null(ann) => Ok(Process::Null(map_ann(ann)?)),
        Process::Action(action, ann, body) => {
            let action = map_action(action)?;
            let body = try_map_process(body, map_action, map_comb, map_ann)?;
            Ok(Process::Action(action, map_ann(ann)?, Box::new(body)))
        }
        Process::Comb(comb, ann, left, right) => {
            let comb = map_comb(comb)?;
            let left = try_map_process(left, map_action, map_comb, map_ann)?;
            let right = try_map_process(right, map_action, map_comb, map_ann)?;
            Ok(Process::Comb(
                comb,
                map_ann(ann)?,
                Box::new(left),
                Box::new(right),
            ))
        }
    }
}

/// Infallible form of [`try_map_process`].
pub fn map_process<Ann, V, Ann2, V2>(
    p: &Process<Ann, V>,
    map_action: &mut impl FnMut(&SapicAction<V>) -> SapicAction<V2>,
    map_comb: &mut impl FnMut(&ProcessCombinator<V>) -> ProcessCombinator<V2>,
    map_ann: &mut impl FnMut(&Ann) -> Ann2,
) -> Process<Ann2, V2> {
    let mut action = |a: &SapicAction<V>| Ok::<_, std::convert::Infallible>(map_action(a));
    let mut comb = |c: &ProcessCombinator<V>| Ok::<_, std::convert::Infallible>(map_comb(c));
    let mut ann = |a: &Ann| Ok::<_, std::convert::Infallible>(map_ann(a));
    match try_map_process(p, &mut action, &mut comb, &mut ann) {
        Ok(mapped) => mapped,
        Err(never) => match never {},
    }
}

pub type LProcess<Ann> = Process<Ann, SapicLVar>;
pub type PlainProcess = LProcess<ProcessParsedAnnotation>;

/// A [`PlainProcess`] together with its `{:?}` rendering.
///
/// A SAPIC-generated rule carries the process it was generated from
/// ([`crate::rule::RuleAttributes::process`]), and the solver renders a rule's
/// info into an occurrence path once per node of every candidate system.  The
/// rendering here is the process's derived
/// `Debug` output, so [`Debug`](std::fmt::Debug) writes those bytes instead of
/// walking the tree again, and [`Deref`](std::ops::Deref) hands out the process
/// itself to the wellformedness pass and the printers.
pub struct SharedProcess {
    process: PlainProcess,
    debug: String,
}

impl SharedProcess {
    pub fn new(process: PlainProcess) -> Self {
        let debug = format!("{:?}", process);
        SharedProcess { process, debug }
    }
}

impl std::fmt::Debug for SharedProcess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.debug)
    }
}

impl std::ops::Deref for SharedProcess {
    type Target = PlainProcess;

    fn deref(&self) -> &PlainProcess {
        &self.process
    }
}

impl PartialEq for SharedProcess {
    fn eq(&self, other: &Self) -> bool {
        self.process == other.process
    }
}

impl Eq for SharedProcess {}

impl PartialOrd for SharedProcess {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SharedProcess {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.process.cmp(&other.process)
    }
}

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

#[cfg(test)]
mod shared_process_order_tests {
    use super::*;

    fn ann(name: &str) -> ProcessParsedAnnotation {
        ProcessParsedAnnotation {
            process_names: vec![name.to_string()],
            ..ProcessParsedAnnotation::empty()
        }
    }

    #[test]
    fn shared_process_uses_haskell_constructor_order() {
        let null = SharedProcess::new(Process::Null(ann("z")));
        let comb = SharedProcess::new(Process::Comb(
            ProcessCombinator::Parallel,
            ann("a"),
            Box::new(Process::Null(ann("a"))),
            Box::new(Process::Null(ann("a"))),
        ));
        let action = SharedProcess::new(Process::Action(
            SapicAction::Rep,
            ann("a"),
            Box::new(Process::Null(ann("a"))),
        ));

        // Haskell derives Ord from declaration order:
        // ProcessNull < ProcessComb < ProcessAction. Debug text has a
        // different lexical order, so this also guards against regressing to
        // comparison of the cached rendering.
        assert!(null < comb);
        assert!(comb < action);
    }
}

// =============================================================================
// Term traversals
// =============================================================================

/// `mapTermsAction ft ff fv ac` (Theory/Sapic/Process.hs:140-157): rebuild an
/// action, sending every term through `ft`, every embedded formula through
/// `ff` and every variable the action carries on its own through `fv`.
pub fn map_terms_action<T, V>(
    mut ft: impl FnMut(&SapicNTerm<T>) -> SapicNTerm<V>,
    mut ff: impl FnMut(&SapicNFormula<T>) -> SapicNFormula<V>,
    mut fv: impl FnMut(&T) -> V,
    ac: &SapicAction<T>,
) -> SapicAction<V>
where
    V: Ord,
{
    let mut try_term = |t: &SapicNTerm<T>| Ok::<_, std::convert::Infallible>(ft(t));
    let mut try_formula = |f: &SapicNFormula<T>| Ok::<_, std::convert::Infallible>(ff(f));
    let mut try_var = |v: &T| Ok::<_, std::convert::Infallible>(fv(v));
    match traverse_terms_action(&mut try_term, &mut try_formula, &mut try_var, ac) {
        Ok(mapped) => mapped,
        Err(never) => match never {},
    }
}

/// `mapTermsComb ft ff fv c` (Theory/Sapic/Process.hs:159-170): the
/// [`map_terms_action`] counterpart for a process combinator.
pub fn map_terms_comb<T, V>(
    mut ft: impl FnMut(&SapicNTerm<T>) -> SapicNTerm<V>,
    mut ff: impl FnMut(&SapicNFormula<T>) -> SapicNFormula<V>,
    mut fv: impl FnMut(&T) -> V,
    c: &ProcessCombinator<T>,
) -> ProcessCombinator<V>
where
    V: Ord,
{
    let mut try_term = |t: &SapicNTerm<T>| Ok::<_, std::convert::Infallible>(ft(t));
    let mut try_formula = |f: &SapicNFormula<T>| Ok::<_, std::convert::Infallible>(ff(f));
    let mut try_var = |v: &T| Ok::<_, std::convert::Infallible>(fv(v));
    match traverse_terms_comb(&mut try_term, &mut try_formula, &mut try_var, c) {
        Ok(mapped) => mapped,
        Err(never) => match never {},
    }
}

/// `traverseTermsAction ft ff fv ac` (Theory/Sapic/Process.hs:242-268) over the
/// `Either` applicative: [`map_terms_action`] with fallible handlers, stopping
/// at the first error in the visit order HS's `<*>` chain fixes.
pub fn traverse_terms_action<T, V, E>(
    mut ft: impl FnMut(&SapicNTerm<T>) -> Result<SapicNTerm<V>, E>,
    mut ff: impl FnMut(&SapicNFormula<T>) -> Result<SapicNFormula<V>, E>,
    mut fv: impl FnMut(&T) -> Result<V, E>,
    ac: &SapicAction<T>,
) -> Result<SapicAction<V>, E>
where
    V: Ord,
{
    Ok(match ac {
        SapicAction::New(v) => SapicAction::New(fv(v)?),
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => SapicAction::ChIn {
            chan: chan.as_ref().map(&mut ft).transpose()?,
            msg: ft(msg)?,
            match_vars: match_vars.iter().map(&mut fv).collect::<Result<_, _>>()?,
        },
        SapicAction::ChOut { chan, msg } => SapicAction::ChOut {
            chan: chan.as_ref().map(&mut ft).transpose()?,
            msg: ft(msg)?,
        },
        SapicAction::Insert(t1, t2) => SapicAction::Insert(ft(t1)?, ft(t2)?),
        SapicAction::Delete(t) => SapicAction::Delete(ft(t)?),
        SapicAction::Lock(t) => SapicAction::Lock(ft(t)?),
        SapicAction::Unlock(t) => SapicAction::Unlock(ft(t)?),
        SapicAction::Event(fa) => SapicAction::Event(fa.try_map_ref(&mut ft)?),
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            match_vars,
        } => SapicAction::Msr {
            prems: prems
                .iter()
                .map(|fa| fa.try_map_ref(&mut ft))
                .collect::<Result<_, _>>()?,
            acts: acts
                .iter()
                .map(|fa| fa.try_map_ref(&mut ft))
                .collect::<Result<_, _>>()?,
            concs: concs
                .iter()
                .map(|fa| fa.try_map_ref(&mut ft))
                .collect::<Result<_, _>>()?,
            rest: rest.iter().map(&mut ff).collect::<Result<_, _>>()?,
            match_vars: match_vars.iter().map(&mut fv).collect::<Result<_, _>>()?,
        },
        SapicAction::Rep => SapicAction::Rep,
        SapicAction::ProcessCall(s, ts) => {
            SapicAction::ProcessCall(s.clone(), ts.iter().map(&mut ft).collect::<Result<_, _>>()?)
        }
    })
}

/// `traverseTermsComb ft ff fv c` (Theory/Sapic/Process.hs:270-283) over the
/// `Either` applicative: the [`traverse_terms_action`] counterpart for a
/// process combinator.
pub fn traverse_terms_comb<T, V, E>(
    mut ft: impl FnMut(&SapicNTerm<T>) -> Result<SapicNTerm<V>, E>,
    mut ff: impl FnMut(&SapicNFormula<T>) -> Result<SapicNFormula<V>, E>,
    mut fv: impl FnMut(&T) -> Result<V, E>,
    c: &ProcessCombinator<T>,
) -> Result<ProcessCombinator<V>, E>
where
    V: Ord,
{
    Ok(match c {
        ProcessCombinator::Cond(fa) => ProcessCombinator::Cond(ff(fa)?),
        ProcessCombinator::CondEq(t1, t2) => ProcessCombinator::CondEq(ft(t1)?, ft(t2)?),
        ProcessCombinator::Let {
            left,
            right,
            match_vars,
        } => ProcessCombinator::Let {
            left: ft(left)?,
            right: ft(right)?,
            match_vars: match_vars.iter().map(&mut fv).collect::<Result<_, _>>()?,
        },
        ProcessCombinator::Lookup(t, v) => ProcessCombinator::Lookup(ft(t)?, fv(v)?),
        ProcessCombinator::Parallel => ProcessCombinator::Parallel,
        ProcessCombinator::Ndc => ProcessCombinator::Ndc,
    })
}

/// Visit every node in the process tree. Traversal order matches Haskell
/// `pfoldMap` (Theory/Sapic/Process.hs:285-296):
/// - `Null`: just the node itself.
/// - `Action`: self first, then the body.
/// - `Comb`: in-order — left subtree, then self, then right subtree
///   (`pfoldMap pl <> f self <> pfoldMap pr` in HS).
pub fn for_each_process<Ann, V>(p: &Process<Ann, V>, f: &mut impl FnMut(&Process<Ann, V>)) {
    match p {
        Process::Null(_) => f(p),
        Process::Action(_, _, body) => {
            f(p);
            for_each_process(body, f);
        }
        Process::Comb(_, _, l, r) => {
            for_each_process(l, f);
            f(p);
            for_each_process(r, f);
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
    pub fn as_var(&self) -> &SapicLVar {
        match self {
            PatternSapicLVar::Bind(v) | PatternSapicLVar::Match(v) => v,
        }
    }
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

/// A substitution mapping SAPIC variables to SAPIC terms.
pub type SapicSubst = Subst<Name, SapicLVar>;

/// Apply a SAPIC substitution to a SAPIC term.
pub fn subst_term(subst: &SapicSubst, t: &SapicTerm) -> SapicTerm {
    tamarin_term::subst::apply_vterm(subst, t.clone())
}

/// Apply a SAPIC substitution to a SAPIC fact (tag and annotations kept).
pub fn subst_fact(subst: &SapicSubst, f: &SapicLNFact) -> SapicLNFact {
    f.map_ref(|t| subst_term(subst, t))
}

/// `applyMatchVars subst vs` (Theory/Sapic/Process.hs:304-309): a match
/// variable is replaced by every variable of its image under `subst`, and kept
/// as it is when `subst` does not define it.  Matching `=t` against a
/// substituted compound term binds the term's own variables instead of the
/// match variable that no longer occurs.
pub fn apply_match_vars<C, V>(subst: &Subst<C, V>, vs: &BTreeSet<V>) -> BTreeSet<V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    let mut out = BTreeSet::new();
    for v in vs {
        match subst.image_of(v) {
            Some(img) => out.extend(tamarin_term::vterm::vars_vterm_in_order(img)),
            None => {
                out.insert(v.clone());
            }
        }
    }
    out
}

/// `applyMatchVars' f vs` (Theory/Sapic/Process.hs:313-317): the same rewrite
/// driven by a caller-supplied rewrite instead of a substitution.  HS applies
/// `f` to `varTerm v` and keeps the variables of the result, so the parameter
/// here is that composite `f . varTerm`.
pub fn apply_match_vars_with<C, V>(
    mut f: impl FnMut(&V) -> VTerm<C, V>,
    vs: &BTreeSet<V>,
) -> BTreeSet<V>
where
    V: Ord + Clone,
{
    let mut out = BTreeSet::new();
    for v in vs {
        out.extend(tamarin_term::vterm::vars_vterm_in_order(&f(v)));
    }
    out
}

// =============================================================================
// Action / combinator predicates (mirroring Sapic.ProcessUtils)
//
// `is_lock`/`is_unlock`/`is_eq` are faithful ports of the corresponding HS
// predicates (ProcessUtils.hs:54-60,70-72), which are generic over the
// annotation and inspect only the action/combinator shape.
// =============================================================================

pub fn is_lock<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::Lock(_), _, _))
}
pub fn is_unlock<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Action(SapicAction::Unlock(_), _, _))
}
pub fn is_eq<Ann, V>(p: &Process<Ann, V>) -> bool {
    matches!(p, Process::Comb(ProcessCombinator::CondEq(_, _), _, _, _))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    /// The whole point of [`SharedProcess`] is that its `Debug` writes what
    /// the process's own derived `Debug` writes: the occurrence paths the
    /// solver builds from a rule's info embed that rendering, so a different
    /// spelling would reorder them.
    #[test]
    fn shared_process_debug_is_the_process_debug() {
        let inner = Process::Action(
            SapicAction::New(SapicLVar::untyped(LVar::new("x", LSort::Msg, 0))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let shared = SharedProcess::new(inner.clone());
        assert_eq!(format!("{:?}", shared), format!("{:?}", inner));
        // The occurrence path embeds the rule attributes' derived `Debug`,
        // which reaches the process as `Option<Arc<SharedProcess>>` — the
        // same `Some(…)` bytes the bare process writes.
        assert_eq!(
            format!("{:?}", Some(std::sync::Arc::new(shared))),
            format!("{:?}", Some(&inner))
        );
    }

    #[test]
    fn position_relations_and_rendering() {
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
        assert_eq!(ProcessParsedAnnotation::empty(), Default::default());
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

    /// A match variable stands for whatever its image binds: a compound image
    /// contributes all of its variables, and an image that is itself a
    /// variable contributes that one. A variable the substitution does not
    /// define survives. `apply_match_vars_with` reaches the same result
    /// through a caller-supplied rewrite, which is what lets a caller resolve
    /// a variable against a key spelling of its own.
    #[test]
    fn apply_match_vars_replaces_a_variable_by_the_variables_of_its_image() {
        use tamarin_term::term::f_app_list;
        use tamarin_term::vterm::var_term;

        let v = |n: &str| SapicLVar::untyped(LVar::new(n, LSort::Msg, 0));
        let pair: SapicTerm = f_app_list(vec![var_term(v("a")), var_term(v("b"))]);
        let subst = SapicSubst::from_list([(v("x"), pair), (v("y"), var_term(v("c")))]);
        let vs: BTreeSet<SapicLVar> = [v("x"), v("y"), v("z")].into_iter().collect();
        let want: BTreeSet<SapicLVar> = [v("a"), v("b"), v("c"), v("z")].into_iter().collect();

        assert_eq!(apply_match_vars(&subst, &vs), want);
        assert_eq!(
            apply_match_vars_with(
                |w| subst
                    .image_of(w)
                    .cloned()
                    .unwrap_or_else(|| var_term(w.clone())),
                &vs
            ),
            want
        );
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
                ProcessParsedAnnotation::empty(),
                Box::new(Process::Comb(
                    ProcessCombinator::Cond(cond),
                    ProcessParsedAnnotation::empty(),
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
