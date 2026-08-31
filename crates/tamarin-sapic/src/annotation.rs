// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Annotation` from `lib/sapic/src/Sapic/Annotation.hs`.
//!
//! Translation-time process annotation. Wraps the `ProcessParsedAnnotation`
//! from `tamarin_theory::sapic` with extra fields used by the various
//! analysis passes (lock variables, secret-channel variables, etc.).

use tamarin_term::lterm::LNTerm;
use tamarin_theory::sapic::{
    map_process, GoodAnnotation, Process, ProcessParsedAnnotation, SapicLVar, SapicTerm,
};

/// Variable annotation wrapper. Semantics: when combined with itself the
/// rightmost wins (matches Haskell `instance Semigroup AnVar`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AnVar<V>(pub V);

/// Annotations attached to a process during translation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ProcessAnnotation<V> {
    /// Original parsed annotation (carries process names, location,
    /// back-substitution).
    pub parsing_ann: ProcessParsedAnnotation,
    /// Fresh variable annotating a `lock` action.
    pub lock: Option<AnVar<V>>,
    /// Fresh variable annotating an `unlock` action; should match the
    /// corresponding `lock`.
    pub unlock: Option<AnVar<V>>,
    /// Variable annotating a channel known to be secret.
    pub secret_channel: Option<AnVar<V>>,
    /// Two terms used to model a `let`-binding with a destructor RHS.
    pub destructor_equation: Option<(LNTerm, LNTerm)>,
    /// Whether this process has a non-zero else branch (relevant for
    /// `let` translation).
    pub else_branch: bool,
    /// Whether this lock/insert/lookup is part of a "pure state" pattern
    /// that the optimiser can elide.
    pub pure_state: bool,
    /// Variable identifying the state cell associated with this op.
    pub state_channel: Option<AnVar<V>>,
    /// Term marking the binding of a state-channel.  HS `isStateChannel ::
    /// Maybe SapicTerm` (sapic/src/Sapic/Annotation.hs:48-60, see line 59): the
    /// cell identifier this fresh `new StateChannel:channel` was introduced for.
    pub is_state_channel: Option<SapicTerm>,
}

/// HS `instance Monoid (ProcessAnnotation v)` sets `elseBranch` to `True` in
/// `mempty` (sapic/src/Sapic/Annotation.hs:73-74), which no derive can
/// express, and a derive would also demand `V: Default`.
impl<V> Default for ProcessAnnotation<V> {
    fn default() -> Self {
        ProcessAnnotation {
            parsing_ann: ProcessParsedAnnotation::default(),
            lock: None,
            unlock: None,
            secret_channel: None,
            destructor_equation: None,
            else_branch: true,
            pure_state: false,
            state_channel: None,
            is_state_channel: None,
        }
    }
}

impl<V> ProcessAnnotation<V> {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn with_lock(v: V) -> Self {
        Self {
            lock: Some(AnVar(v)),
            ..Default::default()
        }
    }
    pub(crate) fn with_unlock(v: V) -> Self {
        Self {
            unlock: Some(AnVar(v)),
            ..Default::default()
        }
    }
    pub(crate) fn with_secret_channel(v: V) -> Self {
        Self {
            secret_channel: Some(AnVar(v)),
            ..Default::default()
        }
    }
    pub(crate) fn with_destructor_equation(t1: LNTerm, t2: LNTerm, else_branch: bool) -> Self {
        Self {
            destructor_equation: Some((t1, t2)),
            else_branch,
            ..Default::default()
        }
    }
    pub(crate) fn with_else_branch(b: bool) -> Self {
        Self {
            else_branch: b,
            ..Default::default()
        }
    }

    /// Combine two annotations, matching Haskell's
    /// `Semigroup (ProcessAnnotation v)` (sapic/src/Sapic/Annotation.hs:76-86).
    ///
    /// The `AnVar` fields (`lock`, `unlock`, `secret_channel`,
    /// `state_channel`) are combined via `Maybe`'s `<>`, whose inner `AnVar`
    /// `<>` is right-biased (`(<>) _ b = b`, sapic/src/Sapic/Annotation.hs:43-44),
    /// so when both are `Some` the *right* value wins (`other.X.or(self.X)`).
    /// `destructor_equation`/`is_state_channel` use Haskell `mayMerge`
    /// (left-biased on `Just`/`Just`), so they keep the *left* value
    /// (`self.X.or(other.X)`). `pure_state` is OR'ed; `else_branch` is taken
    /// from the right operand.
    pub(crate) fn append(self, other: Self) -> Self {
        ProcessAnnotation {
            parsing_ann: self.parsing_ann.append(other.parsing_ann),
            lock: other.lock.or(self.lock),
            unlock: other.unlock.or(self.unlock),
            secret_channel: other.secret_channel.or(self.secret_channel),
            destructor_equation: self.destructor_equation.or(other.destructor_equation),
            else_branch: other.else_branch,
            pure_state: self.pure_state || other.pure_state,
            state_channel: other.state_channel.or(self.state_channel),
            is_state_channel: self.is_state_channel.or(other.is_state_channel),
        }
    }
}

impl<V> GoodAnnotation for ProcessAnnotation<V> {
    fn parsed(&self) -> &ProcessParsedAnnotation {
        &self.parsing_ann
    }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self {
        ProcessAnnotation {
            parsing_ann: p,
            ..self
        }
    }
}

/// `AnnotatedProcess`: SAPIC process post-translation, parameterised over
/// `V` (typically `tamarin_term::lterm::LVar`).
pub(crate) type AnnotatedProcess<V> = Process<ProcessAnnotation<V>, SapicLVar>;

/// `toAnProcess` (sapic/src/Sapic/Annotation.hs:136-140): lift a parsed process into a
/// translation annotation by wrapping the parsed annotation in
/// `ProcessAnnotation`.
pub(crate) fn to_annotated<V>(
    p: &Process<ProcessParsedAnnotation, SapicLVar>,
) -> Process<ProcessAnnotation<V>, SapicLVar> {
    map_process(p, &mut Clone::clone, &mut Clone::clone, &mut |ann| {
        ProcessAnnotation {
            parsing_ann: ann.clone(),
            ..Default::default()
        }
    })
}

/// `toProcess` (sapic/src/Sapic/Annotation.hs:142-145): drop the translation
/// annotations and recover the parsed-stage form — the inverse of
/// [`to_annotated`].  `facts::to_rule` erases with it for the rule name and
/// the `process=` attribute (Facts.hs:391).
pub(crate) fn to_parsed<Ann: GoodAnnotation>(
    p: &Process<Ann, SapicLVar>,
) -> Process<ProcessParsedAnnotation, SapicLVar> {
    map_process(p, &mut Clone::clone, &mut Clone::clone, &mut |ann| {
        ann.parsed().clone()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};

    type V = LVar;

    #[test]
    fn empty_annotation_default_else_branch_is_true() {
        let a: ProcessAnnotation<V> = ProcessAnnotation::empty();
        assert!(a.else_branch);
        assert!(a.lock.is_none());
    }

    #[test]
    fn append_anvar_field_is_right_biased() {
        let v1 = LVar::new("a", LSort::Msg, 0);
        let v2 = LVar::new("b", LSort::Msg, 0);
        let a = ProcessAnnotation::<V>::with_lock(v1);
        let b = ProcessAnnotation::<V>::with_lock(v2);
        let c = a.append(b);
        // `AnVar` `<>` is right-biased (`(<>) _ b = b`), so combining two
        // `Just` lock annotations keeps the right (`b`) value.
        assert_eq!(c.lock.map(|AnVar(v)| v), Some(v2));
    }

    /// `toAnProcess` / `toProcess` must carry the parsed annotation at every
    /// node kind.  They must not set it back to the default.  Each node here
    /// holds a distinct `ProcessParsedAnnotation` that is not the default
    /// value.  A lift that dropped `parsing_ann` therefore shows up as an
    /// inequality.  A `to_parsed` that read the annotation of the wrong node
    /// shows up the same way.  Neither one can default to a match.
    #[test]
    fn round_trip_to_annotated_and_back() {
        let named = |n: &str| ProcessParsedAnnotation {
            process_names: vec![n.to_string()],
            location: Some(tamarin_term::lterm::pub_term(n)),
            ..Default::default()
        };
        let parsed: Process<ProcessParsedAnnotation, SapicLVar> = Process::Comb(
            tamarin_theory::sapic::ProcessCombinator::Parallel,
            named("comb"),
            Box::new(Process::Action(
                tamarin_theory::sapic::SapicAction::Rep,
                named("act"),
                Box::new(Process::Null(named("left"))),
            )),
            Box::new(Process::Null(named("right"))),
        );
        let annotated: Process<ProcessAnnotation<V>, SapicLVar> = to_annotated(&parsed);
        // The lift wraps the parsed annotation, and does not replace it.  The
        // parsed part is reachable unchanged at the root.  The translation
        // fields start at their default values.
        assert_eq!(annotated.annotation().parsing_ann, named("comb"));
        assert!(annotated.annotation().lock.is_none());
        assert_eq!(to_parsed(&annotated), parsed);
    }
}
