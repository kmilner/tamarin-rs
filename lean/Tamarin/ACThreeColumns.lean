import TamarinRuntime.ACThreeColumns
import Tamarin.ACLowRank

namespace Tamarin.ACFeasibility.ThreeColumns
open ACBasis RowReduction.Reference

theorem within_of_feasible {rows : List (Row 3)} (h : Feasible rows) : LowRank.Within rows := by
  obtain ⟨x,sol,pos⟩ := h
  let a : Fin 3 → Int := fun i => if i = 0 then x 2 else if i = 1 then 0 else -(x 0 : Int)
  let b : Fin 3 → Int := fun i => if i = 0 then 0 else if i = 1 then x 2 else -(x 1 : Int)
  apply LowRank.Within.of_span rows a b
  intro r hr
  have sum := sol r hr
  change dot r.pos x = dot r.neg x at sum
  simp only [dot,total,List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,Nat.add_zero] at sum
  have zero : signed r 0 * (x 0 : Int) + signed r 1 * (x 1 : Int) + signed r 2 * (x 2 : Int) = 0 := by
    have e := congrArg (fun n : Nat => (n : Int)) sum
    simp only [Int.natCast_add,Int.natCast_mul] at e
    unfold signed
    grind
  refine ⟨x 2,signed r 0,signed r 1,by have := pos 2; omega,?_⟩
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> simp [a,b] <;> grind

theorem decide_iff (rows : List (Row 3)) : decide rows = true ↔ Feasible rows := by
  cases ran : LowRank.run rows with
  | some b => simpa [decide,ran] using LowRank.run_sound ran
  | none =>
    simp only [decide,ran,Option.getD_none,Bool.false_eq_true,false_iff]
    intro h
    have completes := LowRank.run_complete rows (within_of_feasible h)
    simp [ran] at completes

theorem run_sound {n : Nat} (rows : List (Row n)) (b : Bool) (hit : run rows = some b) :
    b = true ↔ Feasible rows := by
  by_cases h : n = 3
  · subst n
    obtain rfl : decide rows = b := by simpa [run] using hit
    exact decide_iff rows
  · simp [run,h] at hit

end Tamarin.ACFeasibility.ThreeColumns
