import Tamarin.MixedCombination

/-! Unconditional finite complete sets of unifiers for simultaneous free/C/AC
equations. Guess equalities only among original slots. Check all candidate
valuations against the original equations before accepting them. -/
namespace Tamarin.MixedUnification.Total
open LocalAnswers
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def coordinates (p : Problem s) (q : System s) :=
  ((p.variables.map (fun v => q.slot (.var v))) ++ q.constraints.flatMap Constraint.slots).eraseDups

private def templates (q : System s) (k : Nat → Nat) :=
  (Combination.candidates (q.constraints.map (Constraint.rename k))).map fun θ =>
    project q (θ ∘ ref ∘ k)

def solve (p : Problem s) : List (UnifierSorts.Template s) :=
  let q := purify p
  (SlotPartitions.choices (coordinates p q)).flatMap fun k =>
    (templates q k).filter fun θ => p.all fun e => ReferenceMatching.equal (e.lhs.subst θ) (e.rhs.subst θ)

theorem correct (p : Problem s) : UnifierSorts.CompleteTemplates p (solve p) := by
  let q := purify p
  let is := coordinates p q
  constructor
  · intro θ h e he
    obtain ⟨_,_,m⟩ := List.mem_flatMap.mp h
    exact (ReferenceMatching.equal_iff ..).mp (List.all_eq_true.mp (List.mem_filter.mp m).2 e he)
  · intro ρ sol
    obtain ⟨V,model,values⟩ := extend_solution p ρ.image sol
    obtain ⟨k,hk,reps,identifies⟩ := SlotPartitions.covers is (Matching.ACBagSearch.dedup_distinct _) V
    let cs := q.constraints.map (Constraint.rename k)
    have inside {c : Constraint s} (hc : c ∈ q.constraints) {i} (hi : i ∈ c.slots) : i ∈ is :=
      List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,hc,hi⟩))
    have renamed : ∀ c ∈ cs, c.Holds V := by
      intro d hd
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
      exact (c.rename_holds ..).mpr (c.holds_congr (fun i hi => (reps i (inside hc hi)).2.2) (model c hc))
    have rep {i} (hi : i ∈ cs.flatMap Constraint.slots) : i ∈ is ∧ k i = i := by
      obtain ⟨_,hm,hd⟩ := List.mem_flatMap.mp hi
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
      rw [Constraint.slots_rename] at hd
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
      have h := reps j (inside hc hj)
      exact ⟨h.1,h.2.1⟩
    have sep : RigidGraph.Separated cs V := by
      intro i hi j hj eq
      have h := identifies i (rep hi).1 j (rep hj).1 eq
      simpa only [(rep hi).2,(rep hj).2] using h
    obtain ⟨θ,hθ,hsol,W,fac⟩ := Combination.covers cs V renamed sep
    have orig : q.Model (θ ∘ ref ∘ k) := fun c hc =>
      (c.rename_holds ..).mp (hsol _ (List.mem_map_of_mem hc))
    have sound := project_solves p orig
    refine ⟨_,List.mem_flatMap.mpr ⟨k,hk,List.mem_filter.mpr ⟨List.mem_map_of_mem hθ,
      List.all_eq_true.mpr (fun e he => (ReferenceMatching.equal_iff ..).mpr (sound e he))⟩⟩,W,?_⟩
    intro v hv
    let i := q.slot (.var v)
    have hi : i ∈ is := List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map_of_mem
      (f := fun v => q.slot (.var v)) ((p.mem_variables _).mpr hv)))
    exact (values v hv).trans ((reps i hi).2.2.trans (fac (k i)))

end Tamarin.MixedUnification.Total
