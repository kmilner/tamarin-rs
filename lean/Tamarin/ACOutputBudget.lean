import Tamarin.ACCoverage

namespace Tamarin.Homogeneous
open ACBasis

/-- An arm has an array of rows. Each row has a column tag and one word per
witness occurrence. Count a word for each row and each arm as well. -/
def selectionWords {n} (gs : List (Vec n)) (js : List (Fin gs.length)) : Nat :=
  1 + 2*n + (js.map fun j => total (gs.get j)).sum

private def subsetSum {α : Type} (w : List α → Nat) (xs : List α) :=
  ((FlatMatchSearch.sublists xs).map w).sum

private theorem subsetSum_cons {α : Type} (w : List α → Nat) (a : α) (xs : List α) :
    subsetSum w (a::xs) = subsetSum w xs + subsetSum (fun ys => w (a::ys)) xs := by
  simp [subsetSum,FlatMatchSearch.sublists,List.map_append,List.map_map,Function.comp_def]

private theorem subsetSum_perm {α : Type} {xs ys : List α} (p : xs.Perm ys)
    (w : List α → Nat) (respect : ∀ {a b}, List.Perm a b → w a = w b) : subsetSum w xs = subsetSum w ys := by
  induction p generalizing w with
  | nil => rfl
  | cons a _ ih => simp only [subsetSum_cons]; rw [ih w respect,ih _ (fun p => respect (p.cons a))]
  | swap a b xs =>
    simp only [subsetSum_cons]
    have eq : (fun ys => w (b::a::ys)) = fun ys => w (a::b::ys) :=
      funext fun ys => respect (.swap a b ys)
    rw [eq]; omega
  | trans _ _ ih₁ ih₂ => exact (ih₁ w respect).trans (ih₂ w respect)

private def selectedWords {n} (gs : List (Vec n)) : Nat :=
  if ∀ i, ∃ g ∈ gs, 0 < g i then 1+2*n+(gs.map total).sum else 0

private theorem selectionWords_sum {n} (gs : List (Vec n)) :
    ((selections gs).map (selectionWords gs)).sum = subsetSum selectedWords gs := by
  have filtered (xss : List (List (Fin gs.length))) :
      ((xss.filter (covers gs)).map (selectionWords gs)).sum =
        (xss.map (fun js => selectedWords (js.map gs.get))).sum := by
    induction xss with
    | nil => rfl
    | cons js xss ih =>
      have equal : (∀ i, ∃ g ∈ js.map gs.get, 0 < g i) ↔ ∀ i, ∃ j ∈ js, 0 < gs.get j i := by
        apply forall_congr'; intro i; constructor
        · rintro ⟨g,m,pos⟩
          obtain ⟨j,mem,rfl⟩ := List.mem_map.mp m
          exact ⟨j,mem,pos⟩
        · rintro ⟨j,mem,pos⟩; exact ⟨_,List.mem_map_of_mem mem,pos⟩
      have weight : selectedWords (js.map gs.get) = if covers gs js then selectionWords gs js else 0 := by
        simp only [selectedWords,equal,covers,decide_eq_true_eq,selectionWords,List.map_map]
        rfl
      cases ok : covers gs js <;>
        simp only [List.filter_cons,ok,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.sum_cons,
          weight,Nat.zero_add,ih]
  have ids : (List.finRange gs.length).map gs.get = gs := by
    apply List.ext_getElem <;> simp [List.get_eq_getElem]
  rw [selections,filtered,subsetSum]
  conv => rhs; rw [←ids,FlatMatchSearch.sublists_map,List.map_map]
  rfl

/-- Permuting the generator IDs gives the same total packet cost even
when individual covering selections move to different answer positions. -/
theorem outputWords_perm {n} {xs ys : List (Vec n)} (p : xs.Perm ys) :
    ((selections xs).map (selectionWords xs)).sum = ((selections ys).map (selectionWords ys)).sum := by
  rw [selectionWords_sum,selectionWords_sum]
  apply subsetSum_perm p
  intro a b perm
  have covered : (∀ i, ∃ g ∈ a, 0 < g i) ↔ ∀ i, ∃ g ∈ b, 0 < g i := by
    simp only [perm.mem_iff]
  simp only [selectedWords,covered,(perm.map total).sum_nat]

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
