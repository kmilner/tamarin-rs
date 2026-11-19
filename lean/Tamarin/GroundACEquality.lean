import Tamarin.FlatAC

namespace Tamarin

inductive Head (sig : Signature) where
  | var (v : Variable)
  | atom (a : sig.Atom)
  | free (f : sig.FreeSym)
  | comm (f : sig.CSym)
  | ac (f : sig.ACSym)

def headModel (sig : Signature) : Model sig where
  Carrier := Head sig
  atom := Head.atom
  free := fun f _ => .free f
  comm := fun f _ _ => .comm f
  ac := fun f _ _ => .ac f
  comm_swap := by intros; rfl
  ac_swap := by intros; rfl
  ac_assoc := by intros; rfl

/-- B never changes a term's outer constructor, even through transitive
sequences of equations in subterms. Useful for matching and branch joins. -/
theorem EquivB.head_eq {sig : Signature} {a b : Term sig} (h : EquivB a b) :
    (headModel sig).eval Head.var a = (headModel sig).eval Head.var b :=
  h.eval_eq _ _

namespace GroundACEquality
variable {sig : Signature}

inductive Value (sig : Signature) where
  | atom (a : sig.Atom)
  | product (f : sig.ACSym) (a b : sig.Atom) (rest : List sig.Atom)

def Value.term : Value sig → Term sig
  | .atom a => .atom a
  | .product f a b rest => FlatAC.term f (a :: b :: rest)

def Equivalent : Value sig → Value sig → Prop
  | .atom a, .atom b => a = b
  | .product f a b as, .product g c d bs => f = g ∧ (a :: b :: as).Perm (c :: d :: bs)
  | _, _ => False

/-- The exact comparison used for merging flat ground bindings: full atom
identity, distinct-root rejection, and multiset equality at a shared AC root. -/
theorem equivalent_iff [DecidableEq sig.Atom] (a b : Value sig) :
    Equivalent a b ↔ EquivB a.term b.term := by
  cases a <;> cases b
  · constructor
    · intro h; cases h; exact .refl _
    · intro h; exact Head.atom.inj h.head_eq
  · constructor
    · exact False.elim
    · intro h; cases h.head_eq
  · constructor
    · exact False.elim
    · intro h; cases h.head_eq
  · rename_i f a b as g c d bs
    constructor
    · rintro ⟨rfl, hp⟩; exact FlatAC.perm_equiv _ hp
    · intro h
      have he : f = g := Head.ac.inj h.head_eq
      subst g
      exact ⟨rfl, FlatAC.equiv_perm _ h⟩

end GroundACEquality
end Tamarin
