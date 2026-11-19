import TamarinCI
import Tamarin.ACResidual

namespace Tamarin.CommonCancellationTests
open Pairing (signature PTerm PSubst)

private abbrev x : Variable := ⟨1, .msg⟩
private abbrev y : Variable := ⟨2, .msg⟩
private abbrev c : Variable := ⟨3, .msg⟩
private def lit : PTerm := .atom (0, .msg)
private def repeated (t : PTerm) : PTerm := .free (.other 80 2) (fun _ => t)

private def reduced : Equation signature := ⟨.var x, .var y⟩
private def original : Equation signature :=
  ⟨.ac 0 (.var x) (repeated (.var c)), .ac 0 (.var y) (repeated (.var c))⟩
private def alias : PSubst := Pairing.parameters x y (.var c) (.var c) (.var _) (.var _)

-- A substitution can be sound and complete on residual variables x,y, yet
-- accidentally reuse a name whose only original occurrences were canceled.
private theorem alias_complete_residual : CompleteSet [reduced] [alias] := by
  constructor
  · intro s hs e he; obtain rfl := List.mem_singleton.mp hs; obtain rfl := List.mem_singleton.mp he
    exact .refl _
  · intro ρ solved
    let δ := Substitution.binding c (ρ.image x) (ρ.sorted x)
    have val : δ.image c = ρ.image x := Substitution.binding_image_self ..
    have both : EquivB (ρ.image x) (ρ.image y) := solved reduced (by simp)
    refine ⟨alias, by simp, δ, ?_⟩
    intro v ⟨e, he, hv⟩; obtain rfl := List.mem_singleton.mp he
    change v = x ∨ v = y at hv
    rcases hv with rfl | rfl
    · change EquivB (ρ.image x) (δ.image c); rw [val]; exact .refl _
    · change EquivB (ρ.image y) (δ.image c); rw [val]; exact both.symm

example : ¬ FreshFor [reduced] [c] alias := by
  intro h
  apply h x ⟨reduced, by simp, Or.inl rfl⟩ c rfl _ (by simp)
  rintro ⟨e, he, h⟩; obtain rfl := List.mem_singleton.mp he
  change c = x ∨ c = y at h
  revert h; decide

example : ¬ CompleteSet [original] [alias] := by
  let ρ := Pairing.parameters x y lit lit (HasSort.atom _) (HasSort.atom _)
  intro h
  have solved : Problem.Solves [original] ρ := by
    intro e he; obtain rfl := List.mem_singleton.mp he; exact .refl _
  obtain ⟨s, hs, δ, agree⟩ := h.covers ρ solved
  obtain rfl := List.mem_singleton.mp hs
  have hx := agree x ⟨original, by simp, Or.inl (Or.inl rfl)⟩
  have hc := agree c ⟨original, by simp, Or.inl (Or.inr ⟨0, rfl⟩)⟩
  change EquivB lit (δ.image c) at hx
  change EquivB (.var c) (δ.image c) at hc
  exact nomatch (hx.trans hc.symm).head_eq

private theorem original_iff (σ : PSubst) :
    EquivB (σ.apply original.lhs) (σ.apply original.rhs) ↔ EquivB (σ.image x) (σ.image y) :=
  ⟨EquivB.ac_cancel_right (sig := signature) 0, fun h => EquivB.ac_congr (sig := signature) 0 h (.refl _)⟩

-- The exact exported rows preserve unifiers even when substitution changes
-- the internal structure of the repeated compound that disappeared.
example : ∃ l r : List UInt64, Executable.cancelCommon #[0,42] #[1,42] = #[l.toArray, r.toArray] ∧
    let word := fun (id : UInt64) => if id = 0 then (.var x : PTerm) else
      if id = 1 then .var y else repeated (.var c)
    ∀ σ, ACResidual.Holds (sig := signature) 0 σ (l.map word) (r.map word) ↔ EquivB (σ.image x) (σ.image y) := by
  let word := fun (id : UInt64) => if id = 0 then (.var x : PTerm) else
    if id = 1 then .var y else repeated (.var c)
  obtain ⟨l, r, packet, equiv⟩ := ACResidual.run_correct exportedCancelCommon_correct word 0 #[0,42] #[1,42]
  exact ⟨l, r, packet, fun σ => (equiv σ).symm.trans (original_iff σ)⟩

-- The residual answer x↦y leaves c free and extends to
-- a complete answer in every caller context, including one that reserves c.
example (context : List Variable) :
    (Outcome.complete [Substitution.binding x (.var y : PTerm) (HasSort.var y)]).CorrectIn
      [original] context := by
  apply ACResidual.lift_complete [original] [reduced] context [c]
  · intro σ
    constructor
    · intro h e he; obtain rfl := List.mem_singleton.mp he; exact (original_iff σ).mp (h _ (by simp))
    · intro h e he; obtain rfl := List.mem_singleton.mp he; exact (original_iff σ).mpr (h reduced (by simp))
  · rintro v ⟨e, he, hv⟩; obtain rfl := List.mem_singleton.mp he
    rcases hv with hx | hy
    · exact ⟨original, by simp, Or.inl (Or.inl hx)⟩
    · exact ⟨original, by simp, Or.inr (Or.inl hy)⟩
  · rintro v ⟨e, he, hv⟩ missing; obtain rfl := List.mem_singleton.mp he
    rcases hv with (h | ⟨i, h⟩) | (h | ⟨i, h⟩)
    · exact False.elim (missing ⟨reduced, by simp, Or.inl h⟩)
    · exact List.mem_singleton.mpr h
    · exact False.elim (missing ⟨reduced, by simp, Or.inr h⟩)
    · exact List.mem_singleton.mpr h
  · constructor
    · exact VariableElimination.binding_complete x _ _ (show x ≠ y by decide)
    · intro σ h; obtain rfl := List.mem_singleton.mp h; exact VariableElimination.binding_domain x _ _
    · intro σ h; obtain rfl := List.mem_singleton.mp h; exact VariableElimination.binding_fresh x _ _ _

-- No finite nonempty AC term supplies a unit, even when the unmatched
-- occurrence can itself be instantiated by an arbitrary nonground term.
example {sig : Signature} (f : sig.ACSym) (a b : Term sig) (σ : Substitution sig) :
    ¬ EquivB (σ.apply (.ac f a b)) (σ.apply b) := by
  intro equal
  have perm := Cancellation.flatten_equiv f equal
  change (Cancellation.flatten f (.ac f (σ.apply a) (σ.apply b))).Perm _ at perm
  rw [Cancellation.flatten_ac] at perm
  have eq := perm.length_eq
  rw [List.length_append] at eq
  have empty : Cancellation.flatten f (σ.apply a) = [] := List.length_eq_zero_iff.mp (by omega)
  have folded := Cancellation.fold_flatten f (σ.apply a)
  rw [empty] at folded
  cases folded

-- Complete cancellation leaves two empty inventories and still allows the
-- identity solution in any caller context.
example {sig : Signature} (t : Term sig) (avoid : List Variable) :
    (Outcome.complete [Substitution.identity]).CorrectIn [⟨t,t⟩] avoid := by
  constructor
  · constructor
    · intro _ _ e hm; obtain rfl := List.mem_singleton.mp hm; exact .refl _
    · intro ρ _; exact ⟨Substitution.identity, by simp, ρ, fun _ _ => .refl _⟩
  · intro σ h v _; obtain rfl := List.mem_singleton.mp h; rfl
  · intro σ h v observed w occurs outside; obtain rfl := List.mem_singleton.mp h
    exact False.elim (outside (occurs ▸ observed))

private def alphabet : List UInt64 := [0,7,18446744073709551615]

private def words : Nat → List (List UInt64)
  | 0 => [[]]
  | n+1 => [] :: alphabet.flatMap (fun x => (words n).map (x :: ·))

/-- Histogram oracle independent of the export's algorithm and of row order. -/
def stress : IO Unit := do
  let inputs := words 4
  let mut count := 0
  for lhs in inputs do
    for rhs in inputs do
      let packet := (Executable.cancelCommon lhs.toArray rhs.toArray).toList
      let [left, right] := packet | throw (IO.userError s!"expected two rows: {packet}")
      let left := left.toList
      let right := right.toList
      unless (left ++ right).all (fun x => alphabet.contains x) && alphabet.all (fun x =>
        left.count x == lhs.count x - rhs.count x && right.count x == rhs.count x - lhs.count x) do
        throw (IO.userError s!"cancel {lhs} against {rhs}: got {packet}")
      count := count + 1
  unless count == 14641 do throw (IO.userError s!"unexpected corpus size {count}")
  IO.println s!"{count} AC cancellation cases through the exported function"

end Tamarin.CommonCancellationTests

def main : IO Unit := Tamarin.CommonCancellationTests.stress
