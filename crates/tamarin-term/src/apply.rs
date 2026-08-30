// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `class Apply` (SubstVFree.hs:267-268), the class of types a
//! substitution can be applied to.
//!
//! Haskell's class has one method, `apply`.  The primitive here is
//! [`Apply::apply_changed`], which answers `None` when the substitution
//! leaves the value structurally unchanged so the caller keeps the original:
//! the solver applies the equation-store substitution across the whole
//! constraint system after every solving step, that substitution is
//! idempotent, and most of the system is untouched by it.  [`Apply::apply`]
//! is Haskell's method, recovered by substituting the original for `None`.
//!
//! An instance reads a substitution only through [`LeafSubst`] — the image of
//! one variable — so the same instance runs against a [`Subst`], against its
//! raw map, and against the hashed [`SubstView`] a whole-system pass builds
//! over one.

use std::collections::BTreeMap;

use tamarin_utils::cow::{cow_map_vec, cow_pair};

use crate::function_symbols::FunSym;
use crate::lterm::LVar;
use crate::subst::{Subst, SubstView};
use crate::term::{f_app_ac, f_app_c, f_app_list, f_app_no_eq, Term};
use crate::vterm::{Lit, VTerm};

/// What an [`Apply`] instance reads from a substitution: HS's `imageOf`
/// (SubstVFree.hs:240-241), plus the empty test that lets a whole-value walk
/// return immediately.
pub trait LeafSubst {
    /// The constant type of the substitution's range terms.
    type Const;
    /// The variable type the substitution binds.
    type Var;

    /// HS `imageOf` (SubstVFree.hs:240-241).
    fn image_of(&self, v: &Self::Var) -> Option<&VTerm<Self::Const, Self::Var>>;

    /// Whether the substitution binds nothing, in which case it is the
    /// identity on every value.
    fn is_empty(&self) -> bool;
}

impl<C: Ord + Clone, V: Ord + Clone> LeafSubst for BTreeMap<V, VTerm<C, V>> {
    type Const = C;
    type Var = V;

    fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> {
        self.get(v)
    }

    fn is_empty(&self) -> bool {
        BTreeMap::is_empty(self)
    }
}

impl<C: Ord + Clone, V: Ord + Clone> LeafSubst for Subst<C, V> {
    type Const = C;
    type Var = V;

    fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> {
        Subst::image_of(self, v)
    }

    fn is_empty(&self) -> bool {
        Subst::is_empty(self)
    }
}

impl<C: Ord + Clone, V: Ord + Clone + std::hash::Hash> LeafSubst for SubstView<'_, C, V> {
    type Const = C;
    type Var = V;

    fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> {
        SubstView::image_of(self, v)
    }

    fn is_empty(&self) -> bool {
        SubstView::is_empty(self)
    }
}

/// HS `class Apply t' t` (SubstVFree.hs:267-268).
pub trait Apply<S>: Sized {
    /// The image of `self` under `subst`, or `None` when `subst` leaves
    /// `self` structurally unchanged and the caller may keep the original.
    fn apply_changed(&self, subst: &S) -> Option<Self>;

    /// HS `apply` (SubstVFree.hs:268).
    fn apply(self, subst: &S) -> Self {
        match self.apply_changed(subst) {
            Some(v) => v,
            None => self,
        }
    }
}

/// HS's overlapping `Apply (Subst c v) v` (SubstVFree.hs:279-285): a variable
/// is replaced by the variable its image is.  Haskell errors on an image that
/// is not a variable; the fields carrying a bare variable here are node ids,
/// which the equation store only ever binds to another node id.
impl<S: LeafSubst<Var = LVar>> Apply<S> for LVar {
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        match subst.image_of(self) {
            Some(Term::Lit(Lit::Var(w))) if w != self => Some(*w),
            Some(Term::Lit(Lit::Var(_))) | None => None,
            Some(_) => {
                debug_assert!(false, "bare variable mapped to a non-variable term");
                None
            }
        }
    }
}

/// HS's overlapping `Apply (Subst c v) (VTerm c v)` (SubstVFree.hs:287-288),
/// i.e. `applyVTerm`: replace every domain variable by its image and rebuild
/// through the smart constructors, so AC and `C` argument lists come back
/// normalised under the images.
impl<C, V, S> Apply<S> for VTerm<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
    S: LeafSubst<Const = C, Var = V>,
{
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        if subst.is_empty() {
            return None;
        }
        apply_term(self, subst)
    }
}

/// The recursion behind [`Apply`] for a term, with the empty-substitution
/// test hoisted to the entry point.  An `App` node is rebuilt — and
/// re-normalised through the smart constructors — only when at least one
/// child changed; an untouched subtree is already normal, so reusing it gives
/// the same value the full rebuild would.
fn apply_term<C, V, S>(t: &VTerm<C, V>, subst: &S) -> Option<VTerm<C, V>>
where
    C: Ord + Clone,
    V: Ord + Clone,
    S: LeafSubst<Const = C, Var = V>,
{
    match t {
        Term::Lit(Lit::Var(v)) => subst.image_of(v).cloned(),
        Term::Lit(Lit::Con(_)) => None,
        Term::App(fsym, args) => {
            cow_map_vec(&args[..], |a| apply_term(a, subst)).map(|mapped| match fsym {
                FunSym::Ac(o) => f_app_ac(*o, mapped),
                FunSym::C(o) => f_app_c(*o, mapped),
                FunSym::NoEq(o) => f_app_no_eq(*o, mapped),
                FunSym::List => f_app_list(mapped),
            })
        }
    }
}

/// HS `Apply s a => Apply s [a]` (SubstVFree.hs:331-332).
impl<S, T: Apply<S> + Clone> Apply<S> for Vec<T> {
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        cow_map_vec(&self[..], |x| x.apply_changed(subst))
    }
}

/// HS `Apply s a => Apply s (Maybe a)` (SubstVFree.hs:325-326).
impl<S, T: Apply<S>> Apply<S> for Option<T> {
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        self.as_ref()?.apply_changed(subst).map(Some)
    }
}

/// HS `(Apply s a, Apply s b) => Apply s (a, b)` (SubstVFree.hs:316-317).
impl<S, A: Apply<S> + Clone, B: Apply<S> + Clone> Apply<S> for (A, B) {
    fn apply_changed(&self, subst: &S) -> Option<Self> {
        cow_pair(
            &self.0,
            self.0.apply_changed(subst),
            &self.1,
            self.1.apply_changed(subst),
        )
    }
}
