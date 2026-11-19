import Tamarin.ACCoverage

namespace Tamarin.Homogeneous
open ACBasis

/-- An arm has an array of rows. Each row has a column tag and one word per
witness occurrence. Count a word for each row and each arm as well. -/
def selectionWords {n} (gs : List (Vec n)) (js : List (Fin gs.length)) : Nat :=
  1 + 2*n + (js.map fun j => total (gs.get j)).sum

namespace Coverage
private def spend (budget cost : Nat) : Option Nat :=
  if cost ≤ budget then some (budget - cost) else none

private theorem spend_add (budget a b : Nat) :
    ((spend budget a).bind fun rest => spend rest b) = spend budget (a+b) := by
  by_cases ha : a ≤ budget
  · by_cases hb : b ≤ budget-a
    · simp [spend,ha,hb,show a+b ≤ budget by omega,Nat.sub_sub]
    · simp [spend,ha,hb,show ¬a+b ≤ budget by omega]
  · simp [spend,ha,show ¬a+b ≤ budget by omega]

private theorem remaining_eq {α n} (w : α → Nat) (full : BitVec n) (plan : Plan α n)
    (seen : BitVec n) (cost budget : Nat) :
    remainingBudget w full plan seen cost budget =
      spend budget (((enumerate full plan seen).map (fun js => cost + (js.map w).sum)).sum) := by
  induction plan generalizing seen cost budget with
  | done =>
    by_cases h : seen = full <;> simp [remainingBudget,enumerate,h,spend]
  | step x support remaining tail ih =>
    by_cases h : seen ||| remaining = full
    · simp only [remainingBudget,enumerate,h,ne_eq,not_true_eq_false,ite_false,ite_true,ih,
        Option.bind_eq_bind,List.map_append,List.sum_append,List.map_map,Function.comp_def,
        List.map_cons,List.sum_cons,Nat.add_assoc,spend_add]
    · simp [remainingBudget,enumerate,h,spend]

theorem packetFits_iff {n} (gs : List (Vec n)) (budget : Nat) :
    packetFits gs budget = true ↔ ((selections gs).map (selectionWords gs)).sum ≤ budget := by
  have weight (j : Fin gs.length) : (Vector.ofFn fun k => total (gs.get k))[j] = total (gs.get j) := by simp
  simp only [packetFits,remaining_eq,weight]
  change (spend budget (((coveringSelections gs).map (selectionWords gs)).sum)).isSome = true ↔ _
  rw [coveringSelections_eq]
  simp [spend]

end Coverage
end Tamarin.Homogeneous
