import Tamarin.DHCanonical
import Tamarin.Models

/-! The carrier for the DH normal-form algebra consists of all normal terms
modulo the structural C/AC laws, including terms at the common kind. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open Cancellation
variable {sig : Signature} {R : Root sig}

private theorem exists_rep (q : Class sig) : ∃ t, classOf t = q := by
  induction q using Quotient.inductionOn with
  | h t => exact ⟨t,rfl⟩

noncomputable def representative (q : Class sig) : Term sig := (exists_rep q).choose

theorem representative_class (q : Class sig) : classOf (representative q) = q := (exists_rep q).choose_spec

abbrev Value (R : Root sig) := {q : Class sig // Normal R (representative q)}

noncomputable abbrev Value.rep (x : Value R) : Term sig := representative x.val

theorem Value.normal (x : Value R) : Normal R x.rep := x.property

theorem Value.class_rep (x : Value R) : classOf x.rep = x.val := representative_class _

theorem Value.eq_of_rep {x y : Value R} (e : EquivB x.rep y.rep) : x = y :=
  Subtype.ext (x.class_rep.symm.trans ((Quotient.sound e).trans y.class_rep))

noncomputable def value (t : Term sig) (h : Normal R t) : Value R :=
  ⟨classOf t,(normal_equiv R (Quotient.exact (representative_class (classOf t))).symm).mp h⟩

theorem value_rep (t : Term sig) (h : Normal R t) : EquivB t (value t h).rep :=
  (Quotient.exact (representative_class (classOf t))).symm

/-- A simultaneous choice of reachable normal forms for a binary AC head.
The carrier already identifies structurally equivalent representatives. -/
structure Product (s : Symbols sig) (R : Root sig) where
  mul : Value R → Value R → Value R
  reaches : ∀ a b, Reduces R (s.product.mul a.rep b.rep) (mul a b).rep
  comm : ∀ a b, mul a b = mul b a
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

end Tamarin.Rewriting.DHPeer.ChurchRosser
