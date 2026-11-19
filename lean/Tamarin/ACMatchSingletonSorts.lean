import Tamarin.ACMatchSortedBags

namespace Tamarin.Matching.ACBags
variable {sig : Signature} {κ α : Type} [DecidableEq sig.ACSym]
  {f : sig.ACSym} {problem : Problem sig} {row : Equation sig → List κ × List α}
  {name : κ → Variable} {term : α → Term sig} {fixed : Equation sig → List (Term sig)}

/-- Restrictions need describe only the used keys and the factors occurring
in these subjects. Several lists for the same key denote their intersection. -/
structure SortLists (f : sig.ACSym) (rows : List (List κ × List α))
    (name : κ → Variable) (term : α → Term sig) (limits : List (κ × List α)) : Prop where
  restricted : ∀ r ∈ rows, ∀ k ∈ r.1, (∃ l ∈ limits, l.1 = k) ↔ ¬ Subsort (sig.acSort f) (name k).sort
  allowed : ∀ r ∈ rows, ∀ k ∈ r.1, ¬ Subsort (sig.acSort f) (name k).sort → ∀ a ∈ r.2,
    (∀ l ∈ limits, l.1 = k → a ∈ l.2) ↔ Subsort (term a).rootSort (name k).sort

/-- For strict captures only a singleton of a permitted sort can match.
Unrestricted captures may take any nonempty bag of the row's frozen terms. -/
theorem Presentation.fits_iff (p : Presentation f problem row name term fixed) {im : κ → List α}
    (sol : Solution (problem.map row) im) {limits} (sorts : SortLists f (problem.map row) name term limits) :
    Fits f (problem.map row) name term im ↔
      ∀ r ∈ problem.map row, ∀ k ∈ r.1, ∀ l ∈ limits, l.1 = k → ∃ a ∈ l.2, im k = [a] := by
  constructor
  · intro fits r hr k hk l hl key
    have narrow := (sorts.restricted r hr k hk).1 ⟨l,hl,key⟩
    cases h : im k with
    | nil => exact False.elim (sol.1 r hr k hk h)
    | cons a tail =>
      have ok := fits r hr k hk a tail h
      cases tail with
      | nil =>
        have member := (sol.2 r hr).subset (List.mem_flatMap.mpr ⟨k,hk,show a ∈ im k by simp [h]⟩)
        exact ⟨a,(sorts.allowed r hr k hk narrow a member).2 ok l hl key,rfl⟩
      | cons b rest => exact False.elim (narrow ok)
  · intro restricted r hr k hk a tail h
    by_cases wide : Subsort (sig.acSort f) (name k).sort
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
      exact (Term.rootSort_le (p.fold_sorted sol he hk h)).trans wide
    · obtain ⟨l,hl,key⟩ := (sorts.restricted r hr k hk).2 wide
      obtain ⟨b,_,eq⟩ := restricted r hr k hk l hl key
      rw [h] at eq
      obtain ⟨rfl,rfl⟩ := List.cons.inj eq
      have member := (sol.2 r hr).subset (List.mem_flatMap.mpr ⟨k,hk,show a ∈ im k by simp [h]⟩)
      apply (sorts.allowed r hr k hk wide a member).1
      intro l hl key
      obtain ⟨b,mem,eq⟩ := restricted r hr k hk l hl key
      simpa [List.singleton_inj.mp (h.symm.trans eq)] using mem

end Tamarin.Matching.ACBags
