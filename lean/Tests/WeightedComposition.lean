import Tamarin.ACWeightedBudget

namespace Tamarin.ACBasis.WeightedComposition.Tests

private def row4 (a b : Nat) : Row 4 := .ofWeights
  (fun i => if i.val % 2 = 0 then a else 0) (fun i => if i.val % 2 = 1 then b else 0)

private def mixed := row4 31 37
-- Two slots on each side. Splitting quotas 37 and 31 requires 38×32 rows.
private theorem mixed_required : Within mixed := by
  simp only [Within,Uniform]
  decide
-- Regressing the classifier to reject every row violates completion even
-- if the candidate continues to compile and never returns an invalid row.
example : ¬ (∀ r : Row 4, Within r → (none : Option (List (Vec 4))).isSome) :=
  fun h => by simpa using h mixed mixed_required

#guard !(mixed.sparseFits mixed.primitive.cap 16384)
#guard ((candidate mixed).map List.length) == some 1216

-- Verify ascending coordinates, merged neutral singleton position, and
-- the gcd reduction against independent sparse enumeration on a small row.
private def interleaved : Row 5 := .ofWeights
  (fun i => if i.val = 1 ∨ i.val = 3 then 4 else 0)
  (fun i => if i.val = 0 ∨ i.val = 4 then 6 else 0)
private def words {n} (xs : List (Vec n)) := xs.map List.ofFn
#guard ((candidate interleaved).map words) ==
  some (words (minimize (interleaved.sparseGenerators interleaved.primitive.cap)))
#guard ((candidate interleaved).map List.length) == some 13

private def wideQuota (q : Nat) : Row 3 := .ofWeights
  (fun i => if i.val < 2 then 1 else 0) (fun i => if i.val = 2 then q else 0)
#guard ((candidate (wideQuota 2047)).map List.length) == some 2048
#guard (candidate (wideQuota 2048)).isNone

private def forced (q : Nat) : Row 2 := .ofWeights
  (fun i => if i.val = 0 then 1 else 0) (fun i => if i.val = 1 then q else 0)
#guard ((candidate (forced (2^100))).map words) == some [[2^100,1]]
#guard (candidate (forced (2^128))).isNone
#guard (candidate (Row.ofWeights (fun i : Fin 3 => i.val) (fun i => if i.val = 0 then 1 else 0))).isNone

end Tamarin.ACBasis.WeightedComposition.Tests
