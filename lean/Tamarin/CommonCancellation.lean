import Std

/-! Full cancellation for a request-local alphabet of AC-child identities.
The residue pair represents inventories and may contain empty rows. -/
namespace Tamarin.CommonCancellation

def Correct (run : Array UInt64 → Array UInt64 → Array (Array UInt64)) : Prop :=
  ∀ lhs rhs, ∃ common left right : List UInt64,
    run lhs rhs = #[left.toArray, right.toArray] ∧
    lhs.toList.Perm (common ++ left) ∧ rhs.toList.Perm (common ++ right) ∧
    ∀ w ∈ left, w ∉ right

/-- Reordering the occurrences within the output rows preserves the contract.
Canonical sorting is an implementation choice. -/
theorem Correct.reorder {run} (ok : Correct run) (order : List UInt64 → List UInt64)
    (perm : ∀ xs, (order xs).Perm xs) :
    Correct (fun lhs rhs => (run lhs rhs).map fun row => (order row.toList).toArray) := by
  intro lhs rhs
  obtain ⟨c, l, r, he, hl, hr, hd⟩ := ok lhs rhs
  refine ⟨c, order l, order r, ?_, hl.trans ((perm l).symm.append_left c),
    hr.trans ((perm r).symm.append_left c), ?_⟩
  · simp [he, Array.map]
  · intro w hw hrw
    exact hd w ((perm l).mem_iff.mp hw) ((perm r).mem_iff.mp hrw)

end Tamarin.CommonCancellation
