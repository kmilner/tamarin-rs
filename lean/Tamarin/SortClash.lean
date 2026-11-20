import Tamarin.ACRepresentation
import Tamarin.Unification

/-! Equivalence modulo free, C and AC symbols preserves every sort check. -/
namespace Tamarin.SortClash
variable {sig : Signature}

theorem check_equiv {a b : Term sig} (h : EquivB a b) :
    ∀ s, a.checkSort s = b.checkSort s := by
  induction h with
  | refl => intros; rfl
  | symm _ ih => exact fun s => (ih s).symm
  | trans _ _ ih ik => exact fun s => (ih s).trans (ik s)
  | free f a b _ ih => intro s; simp only [Term.checkSort, ih]
  | comm_congr _ _ _ ia ib | ac_congr _ _ _ ia ib =>
    intro s; simp only [Term.checkSort, ia, ib]
  | comm_swap | ac_swap => intro s; simp only [Term.checkSort]; grind
  | ac_assoc f =>
    intro s
    simp only [Term.checkSort, (Subsort.check_iff _ _).mpr (.refl (sig.acSort f))]
    grind

end Tamarin.SortClash
