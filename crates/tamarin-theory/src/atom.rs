// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, PhilipLukertWork, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/theory/src/Theory/Model/Atom.hs

//! Port of `Theory.Model.Atom` from `lib/theory/src/Theory/Model/Atom.hs`.
//!
//! Atoms of trace formulas. A `ProtoAtom<S, T>` is parameterised over a
//! syntactic-sugar wrapper `S` and a term type `T`. Stripping the sugar
//! (`Atom<T>` ≡ `ProtoAtom<Unit, T>`) yields the form used after parsing.

use crate::fact::Fact;

/// Marker type with no fields — Haskell's `Unit2 t = Unit2`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Unit2;

/// Syntactic sugar wrapper used during parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntacticSugar<T> {
    Pred(Fact<T>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoAtom<S, T> {
    Action(T, Fact<T>),
    EqE(T, T),
    Subterm(T, T),
    Less(T, T),
    Last(T),
    Syntactic(S),
}

/// `Atom<T>` ≡ `ProtoAtom<Unit2, T>` — the post-parsing form.
pub type Atom<T> = ProtoAtom<Unit2, T>;
pub type SyntacticAtom<T> = ProtoAtom<SyntacticSugar<T>, T>;

/// Strip syntactic sugar, replacing it with `Unit2`.
///
/// No production caller; kept as parity/API surface.
pub fn to_atom<S, T>(a: ProtoAtom<S, T>) -> Atom<T> {
    match a {
        ProtoAtom::Action(t, fa) => ProtoAtom::Action(t, fa),
        ProtoAtom::EqE(l, r) => ProtoAtom::EqE(l, r),
        ProtoAtom::Subterm(l, r) => ProtoAtom::Subterm(l, r),
        ProtoAtom::Less(l, r) => ProtoAtom::Less(l, r),
        ProtoAtom::Last(t) => ProtoAtom::Last(t),
        ProtoAtom::Syntactic(_) => ProtoAtom::Syntactic(Unit2),
    }
}

// -- Predicates ---------------------------------------------------------------
//
// Kept for parity with the exported API of Haskell's `Theory.Model.Atom`; no
// current Rust caller exercises these on an `Atom<T>` value (the live
// `is_action`/`is_eq`/`is_subterm` elsewhere are on `Goal`/`Process`/`Term`,
// not `Atom`).

impl<T> Atom<T> {
    pub fn is_action(&self) -> bool { matches!(self, ProtoAtom::Action(_, _)) }
    pub fn is_eq(&self) -> bool { matches!(self, ProtoAtom::EqE(_, _)) }
    pub fn is_subterm(&self) -> bool { matches!(self, ProtoAtom::Subterm(_, _)) }
    pub fn is_less(&self) -> bool { matches!(self, ProtoAtom::Less(_, _)) }
    pub fn is_last(&self) -> bool { matches!(self, ProtoAtom::Last(_)) }
    /// Retained for parity with Haskell's exported `isSyntacticSugar`; no Rust
    /// call site currently uses it.
    #[allow(dead_code)]
    pub fn is_syntactic_sugar(&self) -> bool { matches!(self, ProtoAtom::Syntactic(_)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{fresh_fact, FactTag};
    use tamarin_term::builtin::msg_var;
    use tamarin_term::lterm::LNTerm;

    #[test]
    fn atom_predicates() {
        let a: Atom<LNTerm> = ProtoAtom::Less(msg_var("x", 0), msg_var("y", 0));
        assert!(a.is_less());
        assert!(!a.is_eq());

        let b: Atom<LNTerm> = ProtoAtom::Action(
            msg_var("t", 0),
            fresh_fact(msg_var("k", 0)),
        );
        assert!(b.is_action());
    }

    #[test]
    fn to_atom_strips_sugar() {
        let s: SyntacticAtom<LNTerm> = ProtoAtom::Syntactic(SyntacticSugar::Pred(
            Fact::fresh(FactTag::Term, vec![msg_var("x", 0)]),
        ));
        let a = to_atom(s);
        assert!(matches!(a, ProtoAtom::Syntactic(Unit2)));
    }
}
