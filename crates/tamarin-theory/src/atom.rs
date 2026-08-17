// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

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
    pub fn is_action(&self) -> bool {
        matches!(self, ProtoAtom::Action(_, _))
    }
    pub fn is_eq(&self) -> bool {
        matches!(self, ProtoAtom::EqE(_, _))
    }
    pub fn is_subterm(&self) -> bool {
        matches!(self, ProtoAtom::Subterm(_, _))
    }
    pub fn is_less(&self) -> bool {
        matches!(self, ProtoAtom::Less(_, _))
    }
    pub fn is_last(&self) -> bool {
        matches!(self, ProtoAtom::Last(_))
    }
    /// Retained for parity with Haskell's exported `isSyntacticSugar`; no Rust
    /// call site currently uses it.
    pub fn is_syntactic_sugar(&self) -> bool {
        matches!(self, ProtoAtom::Syntactic(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fact::{fresh_fact, FactTag};
    use tamarin_term::builtin::msg_var;
    use tamarin_term::lterm::LNTerm;

    fn x() -> LNTerm {
        msg_var("x", 0)
    }
    fn y() -> LNTerm {
        msg_var("y", 0)
    }

    /// Every predicate matches exactly its own variant.  The test asserts the
    /// full variant × predicate diagonal.  This catches a predicate that is
    /// wired to the wrong constructor.  It also catches a predicate that
    /// degenerates to a constant.
    #[test]
    fn atom_predicates() {
        let atoms: Vec<Atom<LNTerm>> = vec![
            ProtoAtom::Action(x(), fresh_fact(y())),
            ProtoAtom::EqE(x(), y()),
            ProtoAtom::Subterm(x(), y()),
            ProtoAtom::Less(x(), y()),
            ProtoAtom::Last(x()),
            ProtoAtom::Syntactic(Unit2),
        ];
        for (i, a) in atoms.iter().enumerate() {
            let row = [
                a.is_action(),
                a.is_eq(),
                a.is_subterm(),
                a.is_less(),
                a.is_last(),
                a.is_syntactic_sugar(),
            ];
            for (j, hit) in row.iter().enumerate() {
                assert_eq!(*hit, i == j, "predicate {j} on {a:?}");
            }
        }
    }

    /// `to_atom` replaces the sugar payload with the field-less `Unit2`.  It
    /// carries every other variant across unchanged.  This includes the
    /// constructor of the variant.  A check that uses `matches!` on one
    /// variant cannot see that constructor.
    #[test]
    fn to_atom_strips_sugar() {
        let s: SyntacticAtom<LNTerm> =
            ProtoAtom::Syntactic(SyntacticSugar::Pred(Fact::fresh(FactTag::Term, vec![x()])));
        assert_eq!(to_atom(s), ProtoAtom::Syntactic(Unit2));

        let cases: Vec<(SyntacticAtom<LNTerm>, Atom<LNTerm>)> = vec![
            (
                ProtoAtom::Action(x(), fresh_fact(y())),
                ProtoAtom::Action(x(), fresh_fact(y())),
            ),
            (ProtoAtom::EqE(x(), y()), ProtoAtom::EqE(x(), y())),
            (ProtoAtom::Subterm(x(), y()), ProtoAtom::Subterm(x(), y())),
            (ProtoAtom::Less(x(), y()), ProtoAtom::Less(x(), y())),
            (ProtoAtom::Last(x()), ProtoAtom::Last(x())),
        ];
        for (input, expected) in cases {
            assert_eq!(to_atom(input), expected);
        }
    }
}
