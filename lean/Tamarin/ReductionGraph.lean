import Tamarin.ContextualReduction
import TamarinRuntime.ReductionGraph

namespace Tamarin.ReductionGraph
open Rewriting ACSubproductReduction

abbrev Graph := Array (Array UInt64)

/-- A nonempty finite graph in postorder, with at most one terminal.
Strict descent entails closure and guarantees that a terminal exists.
IDs refer to states local to one ordinary reduction query. -/
structure Certificate (g : Graph) : Prop where
  nonempty : 0 < g.size
  earlier : ∀ i : Fin g.size, ∀ w ∈ g[i], w.toNat < i.val
  unique : ∀ i j : Fin g.size, g[i] = #[] → g[j] = #[] → i = j

def Correct (check : Graph → Bool) := ∀ g, check g = true ↔ Certificate g

private theorem zero_empty {g : Graph} (nonempty : 0 < g.size)
    (earlier : ∀ i : Fin g.size, ∀ w ∈ g[i], w.toNat < i.val) : g[0] = #[] := by
  apply Classical.byContradiction
  intro ne
  obtain ⟨w,mem⟩ := Array.exists_mem_of_ne_empty _ ne
  exact Nat.not_lt_zero _ (earlier ⟨0,nonempty⟩ w mem)

theorem correct : Correct run := by
  intro g
  simp only [run,Nat.all_eq_finRange_all,Bool.and_eq_true,List.all_eq_true,List.mem_finRange,
    forall_const,Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true',Array.isEmpty_eq_false_iff,
    decide_eq_true_eq,Array.all_eq_true_iff_forall_mem]
  constructor
  · rintro ⟨hn,rows⟩
    refine ⟨hn,fun i => (rows i).2,?_⟩
    intro i j ei ej
    exact Fin.ext (((rows i).1.resolve_right (fun ne => ne ei)).trans
      ((rows j).1.resolve_right (fun ne => ne ej)).symm)
  · intro h
    refine ⟨h.nonempty,fun i => ⟨?_,h.earlier i⟩⟩
    by_cases ei : g[i] = #[]
    · exact .inl (congrArg Fin.val (h.unique i ⟨0,h.nonempty⟩ ei (zero_empty h.nonempty h.earlier)))
    · exact .inr ei

/-- Reading the graph's integer rows as completed ordinary rewrite steps
gives a reachable unique normal form at state zero. The start can be any
encoded state, including the final row representing the caller's input. -/
def Semantic (check : Graph → Bool) : Prop :=
  ∀ {g : Graph}, check g = true → ∀ {s : Signature} {R : Root s}
    (read : Nat → Term s) (start : Fin g.size) (next : Term s → List (Term s)),
    (∀ i : Fin g.size, next (read i) = g[i].toList.map (fun w => read w.toNat)) →
    (∀ i : Fin g.size, ∀ b, StepModulo R (read i) b ↔ ∃ v ∈ next (read i), EquivB v b) →
    (∀ k, HasSort (read start) k → HasSort (read 0) k) →
    NormalForm R (read start) (read 0) ∧ ∀ u, NormalForm R (read start) u → EquivB u (read 0)

theorem completed {check : Graph → Bool} (ok : Correct check) : Semantic check := by
  intro g accepted s R read start next decode edges sorts
  have cert := (ok g).mp accepted
  let states := (List.finRange g.size).map (fun i => read i.val)
  have member (i : Fin g.size) : read i ∈ states := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  have leaf : next (read 0) = [] := by
    rw [decode ⟨0,cert.nonempty⟩]
    simp [zero_empty cert.nonempty cert.earlier]
  have reach (i : Nat) (hi : i < g.size) (path : Visited next (read start) (read i)) :
      Visited next (read start) (read 0) := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      by_cases e : i = 0
      · exact e ▸ path
      · have nonempty : g[i] ≠ #[] := fun empty => e (congrArg Fin.val
          (cert.unique ⟨i,hi⟩ ⟨0,cert.nonempty⟩ empty (zero_empty cert.nonempty cert.earlier)))
        obtain ⟨w,hw⟩ := Array.exists_mem_of_ne_empty _ nonempty
        have earlier := cert.earlier ⟨i,hi⟩ w hw
        apply ih w.toNat earlier (Nat.lt_trans earlier hi) (path.follow ?_)
        rw [decode ⟨i,hi⟩]
        exact List.mem_map_of_mem (by simpa using hw)
  apply ACSubproductReduction.completed states next (read start) (read 0) (member start)
  · rintro _ mem b
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
    exact edges i b
  · rintro _ mem b hb
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
    rw [decode i] at hb
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    exact member ⟨w.toNat,Nat.lt_trans (cert.earlier i w (by simpa using hw)) i.isLt⟩
  · rintro _ mem he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
    rw [decode i] at he
    have noEdges : g[i] = #[] := by simpa using he
    have e := congrArg Fin.val (cert.unique i ⟨0,cert.nonempty⟩ noEdges (zero_empty cert.nonempty cert.earlier))
    exact e ▸ EquivB.refl _
  · exact reach start start.isLt .seed
  · exact leaf
  · exact sorts

end Tamarin.ReductionGraph
