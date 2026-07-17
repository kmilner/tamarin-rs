// Currently GPL 3.0 until granted permission by the following authors:
//   Robert Künnemann, Artur Cygan, Charlie Jacomme, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Annotation.hs

//! Port of `Sapic.Annotation` from `lib/sapic/src/Sapic/Annotation.hs`.
//!
//! Translation-time process annotation. Wraps the `ProcessParsedAnnotation`
//! from `tamarin_theory::sapic` with extra fields used by the various
//! analysis passes (lock variables, secret-channel variables, etc.).

use tamarin_theory::sapic::{
    GoodAnnotation, Process, ProcessParsedAnnotation, SapicLVar, SapicTerm,
};
use tamarin_term::lterm::LNTerm;

/// Variable annotation wrapper. Semantics: when combined with itself the
/// rightmost wins (matches Haskell `instance Semigroup AnVar`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AnVar<V>(pub V);

/// Annotations attached to a process during translation.
#[derive(Debug, Clone, PartialEq)]
pub struct ProcessAnnotation<V> {
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
    /// Maybe SapicTerm` (Annotation.hs:59): the cell identifier this fresh
    /// `new StateChannel:channel` was introduced for.
    pub is_state_channel: Option<SapicTerm>,
}

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

impl<V: Clone> ProcessAnnotation<V> {
    pub fn empty() -> Self { Self::default() }

    pub fn with_lock(v: V) -> Self {
        Self { lock: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_unlock(v: V) -> Self {
        Self { unlock: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_secret_channel(v: V) -> Self {
        Self { secret_channel: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_destructor_equation(t1: LNTerm, t2: LNTerm, else_branch: bool) -> Self {
        Self {
            destructor_equation: Some((t1, t2)),
            else_branch,
            ..Default::default()
        }
    }
    pub fn with_else_branch(b: bool) -> Self {
        Self { else_branch: b, ..Default::default() }
    }

    /// Combine two annotations, matching Haskell's
    /// `Semigroup (ProcessAnnotation v)` (Annotation.hs:76-86).
    ///
    /// The `AnVar` fields (`lock`, `unlock`, `secret_channel`,
    /// `state_channel`) are combined via `Maybe`'s `<>`, whose inner `AnVar`
    /// `<>` is right-biased (`(<>) _ b = b`, Annotation.hs:43-44), so when
    /// both are `Some` the *right* value wins (`other.X.or(self.X)`).
    /// `destructor_equation`/`is_state_channel` use Haskell `mayMerge`
    /// (left-biased on `Just`/`Just`), so they keep the *left* value
    /// (`self.X.or(other.X)`). `pure_state` is OR'ed; `else_branch` is taken
    /// from the right operand.
    pub fn append(self, other: Self) -> Self {
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

impl<V: Clone> GoodAnnotation for ProcessAnnotation<V> {
    fn parsed(&self) -> &ProcessParsedAnnotation { &self.parsing_ann }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self {
        ProcessAnnotation { parsing_ann: p, ..self }
    }
    fn default_annotation() -> Self { Self::default() }
}

/// `AnnotatedProcess`: SAPIC process post-translation, parameterised over
/// `V` (typically `tamarin_term::lterm::LVar`).
pub type AnnotatedProcess<V> = Process<ProcessAnnotation<V>, SapicLVar>;

/// `toAnProcess`: lift a parsed process into a translation annotation by
/// wrapping the parsed annotation in `ProcessAnnotation`.
pub fn to_annotated<V: Clone>(
    p: Process<ProcessParsedAnnotation, SapicLVar>,
) -> Process<ProcessAnnotation<V>, SapicLVar> {
    fn go<V: Clone>(
        p: Process<ProcessParsedAnnotation, SapicLVar>,
    ) -> Process<ProcessAnnotation<V>, SapicLVar> {
        match p {
            Process::Null(ann) => Process::Null(ProcessAnnotation {
                parsing_ann: ann,
                ..Default::default()
            }),
            Process::Action(a, ann, body) => Process::Action(
                a,
                ProcessAnnotation { parsing_ann: ann, ..Default::default() },
                Box::new(go(*body)),
            ),
            Process::Comb(c, ann, l, r) => Process::Comb(
                c,
                ProcessAnnotation { parsing_ann: ann, ..Default::default() },
                Box::new(go(*l)),
                Box::new(go(*r)),
            ),
        }
    }
    go(p)
}

/// Drop the translation annotations and recover the parsed-stage form.
// Intentionally retained: faithful HS port of `toProcess`; the symmetric
// inverse of `to_annotated`, no non-test caller yet.
pub fn to_parsed<V>(
    p: Process<ProcessAnnotation<V>, SapicLVar>,
) -> Process<ProcessParsedAnnotation, SapicLVar> {
    match p {
        Process::Null(ann) => Process::Null(ann.parsing_ann),
        Process::Action(a, ann, body) => {
            Process::Action(a, ann.parsing_ann, Box::new(to_parsed(*body)))
        }
        Process::Comb(c, ann, l, r) => Process::Comb(
            c,
            ann.parsing_ann,
            Box::new(to_parsed(*l)),
            Box::new(to_parsed(*r)),
        ),
    }
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
        let b = ProcessAnnotation::<V>::with_lock(v2.clone());
        let c = a.append(b);
        // `AnVar` `<>` is right-biased (`(<>) _ b = b`), so combining two
        // `Just` lock annotations keeps the right (`b`) value.
        assert_eq!(c.lock.map(|AnVar(v)| v), Some(v2));
    }

    #[test]
    fn round_trip_to_annotated_and_back() {
        let parsed: Process<ProcessParsedAnnotation, SapicLVar> = Process::Null(
            ProcessParsedAnnotation::default(),
        );
        let annotated: Process<ProcessAnnotation<V>, SapicLVar> = to_annotated(parsed.clone());
        let back = to_parsed(annotated);
        assert_eq!(parsed, back);
    }
}
