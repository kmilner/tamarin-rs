import Tamarin.Commutative
import TamarinRuntime.Candidate

namespace Tamarin.CommutativeCandidateProofs

theorem correct : Commutative.Correct RuntimeCandidate.commOrientations := by
  intro a b c d priority
  unfold RuntimeCandidate.commOrientations
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  split <;> rename_i direct
  · split <;> rename_i first
    · constructor
      · decide
      · intro P Q hp hq dom _
        simp [Commutative.Selected]; grind [Commutative.Viable]
    · split <;> rename_i pref
      · constructor
        · decide
        · intro P Q hp hq _ dom
          simp [Commutative.Selected]; grind
      · simp [Commutative.Selected]
  · split <;> rename_i crossed
    · constructor
      · decide
      · intro P Q hp hq _ _
        simp [Commutative.Selected]; grind [Commutative.Viable]
    · constructor
      · decide
      · intro P Q hp hq _ _
        simp [Commutative.Selected]; grind [Commutative.Viable]

theorem bound : Commutative.BranchBound RuntimeCandidate.commOrientations := by
  intro a b c d priority
  simp only [RuntimeCandidate.commOrientations, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', Commutative.Selected, Commutative.Viable, ↓reduceIte]
  split <;> split <;> try split <;> grind

end Tamarin.CommutativeCandidateProofs
