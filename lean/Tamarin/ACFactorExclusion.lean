import TamarinRuntime.Candidate

namespace Tamarin.Rewriting.ACFactorExclusion

/-- Every rule needs a rigid factor absent from the whole subject. Zero
stands for a pattern without a required application head. -/
def Correct (run : Array (Array UInt64) → Array UInt64 → Bool) : Prop :=
  ∀ rows heads, run rows heads = true ↔
    ∀ row ∈ rows, ∃ k ∈ row, k ≠ 0 ∧ k ∉ heads

theorem correct : Correct RuntimeCandidate.excludeACFactors := by
  intro rows heads
  simp only [RuntimeCandidate.excludeACFactors, Array.all_eq_true_iff_forall_mem,
    Array.any_eq_true', Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
    Bool.eq_false_iff, ← Array.contains_iff_mem]

end Tamarin.Rewriting.ACFactorExclusion
