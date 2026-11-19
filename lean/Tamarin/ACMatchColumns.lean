import Std
import Tamarin.ACMatchBags

/-! Counts of each frozen factor can be chosen independently across all equations.
Their supports must together give a nonempty image to each observed key. -/
namespace Tamarin.Matching.ACBags
variable {κ α : Type} [DecidableEq α]

def Balanced (rows : List (List κ × List α)) (a : α) (w : κ → Nat) :=
  ∀ r ∈ rows, (r.1.map w).sum = r.2.count a

private theorem countExpanded (ks : List κ) (image : κ → List α) (a : α) :
    (ks.flatMap image).count a = (ks.map fun k => (image k).count a).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [List.count_append,ih]

private theorem countBag (w : α → Nat) (a : α) (as : List α) (nd : as.Nodup) :
    (as.flatMap fun b => List.replicate (w b) b).count a = if a ∈ as then w a else 0 := by
  induction as with
  | nil => simp
  | cons b bs ih =>
    rw [List.flatMap_cons,List.count_append,ih nd.tail,List.count_replicate]
    by_cases h : b = a
    · subst b; simp [(List.nodup_cons.mp nd).1]
    · simp [h,Ne.symm h]

theorem feasible_columns (rows : List (List κ × List α)) (atoms : List α) (distinct : atoms.Nodup)
    (observed : ∀ a, a ∈ atoms ↔ ∃ r ∈ rows, a ∈ r.2) :
    Feasible rows ↔ ∃ w : α → κ → Nat, (∀ a ∈ atoms, Balanced rows a (w a)) ∧
      ∀ r ∈ rows, ∀ k ∈ r.1, ∃ a ∈ atoms, 0 < w a k := by
  constructor
  · rintro ⟨image,nz,ok⟩
    refine ⟨fun a k => (image k).count a,?_,?_⟩
    · intro a _ r hr
      exact (countExpanded r.1 image a).symm.trans ((ok r hr).count_eq a)
    · intro r hr k hk
      obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ (nz r hr k hk)
      exact ⟨a,(observed a).2 ⟨r,hr,(ok r hr).subset (List.mem_flatMap.mpr ⟨k,hk,ha⟩)⟩,
        List.count_pos_iff.mpr ha⟩
  · rintro ⟨w,ok,nz⟩
    let image k := atoms.flatMap fun a => List.replicate (w a k) a
    have count (k a) : (image k).count a = if a ∈ atoms then w a k else 0 :=
      countBag _ _ _ distinct
    refine ⟨image,?_,?_⟩
    · intro r hr k hk empty
      obtain ⟨a,ha,pos⟩ := nz r hr k hk
      have h := count k a
      simp [empty,ha] at h
      omega
    · intro r hr
      apply List.perm_iff_count.mpr
      intro a
      rw [countExpanded]
      by_cases ha : a ∈ atoms
      · simp only [count,ite_eq_left ha]
        exact ok a ha r hr
      · have absent : a ∉ r.2 := fun h => ha ((observed a).2 ⟨r,hr,h⟩)
        simp only [count,ite_eq_right ha,List.count_eq_zero.mpr absent]
        generalize r.1 = ks
        induction ks with
        | nil => rfl
        | cons _ _ ih => simpa only [List.map_cons,List.sum_cons,Nat.zero_add] using ih

end Tamarin.Matching.ACBags
