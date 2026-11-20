import Tamarin.BilinearRoots

/-! Read the bilinear rule inventory on the same table as the scalar group.
Only the two operator declarations and the local variable slots are needed
to reconstruct the oriented rules. -/
namespace Tamarin.BilinearTable
open Rewriting DHPeer Bilinear ConstructorVariants
variable {sig : Signature}

structure Schema (sig : Signature) where
  ops : Operators sig
  keys : Bilinear.Rule → Fin 3 → Variable
  typed : ∀ r i, (keys r i).sort = .msg
  distinct : ∀ r, Function.Injective (keys r)

namespace Schema
variable (a : Schema sig)

def row (s : Symbols sig) (r : Bilinear.Rule) : Equation sig :=
  r.equation s a.ops fun i => .var (a.keys r i)

def rows (s : Symbols sig) : Problem sig := [a.row s .one, a.row s .nested, a.row s .extract]

def owns [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] : Head sig → Bool
  | .free g => g == a.ops.pmult
  | .comm g => g == a.ops.emap
  | _ => false

theorem row_mem (s : Symbols sig) (r : Bilinear.Rule) : a.row s r ∈ a.rows s := by
  cases r <;> simp [rows]

theorem mem_rows {s : Symbols sig} {r : Equation sig} :
    r ∈ a.rows s ↔ ∃ k, r = a.row s k := by
  constructor
  · intro h
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h
    · exact ⟨.one,h⟩
    · exact ⟨.nested,h⟩
    · exact ⟨.extract,h⟩
  · rintro ⟨k,rfl⟩; exact a.row_mem s k

theorem owns_row [DecidableEq sig.FreeSym] [DecidableEq sig.CSym]
    {s : Symbols sig} {r : Equation sig} (h : r ∈ a.rows s) : a.owns (head r.lhs) := by
  obtain ⟨k,rfl⟩ := a.mem_rows.mp h
  cases k <;> simp [row,Bilinear.Rule.equation,Operators.point,head,headModel,Model.eval,owns]

def inventory [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] (s : Symbols sig) (rs : Problem sig)
    (present : ∀ r ∈ a.rows s, r ∈ rs)
    (only : ∀ r ∈ rs, a.owns (head r.lhs) → r ∈ a.rows s)
    (apps : ∀ r ∈ rs, Application r.lhs) : Bilinear.Inventory s a.ops rs where
  keys := a.keys
  typed := a.typed
  distinct := a.distinct
  present r := present _ (a.row_mem s r)
  apps := apps
  onlyPoint r hr hd := by
    obtain ⟨k,rfl⟩ := a.mem_rows.mp (only r hr (by simp [hd,owns]))
    cases k with
    | one => exact ⟨.one,.inl rfl,rfl⟩
    | nested => exact ⟨.nested,.inr rfl,rfl⟩
    | extract => cases hd
  onlyMap r hr hd := by
    obtain ⟨k,rfl⟩ := a.mem_rows.mp (only r hr (by simp [hd,owns]))
    cases k with
    | one | nested => cases hd
    | extract => rfl

end Schema
end Tamarin.BilinearTable
