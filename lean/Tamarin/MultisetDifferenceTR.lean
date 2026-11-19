import Tamarin.MultisetDifference
import TamarinRuntime.Algorithm

namespace Tamarin.Executable

/-- The accumulator only prepends skipped atoms; it cannot alter failure or
the multiset difference produced by the specification implementation. -/
theorem subtractSortedTRGo_eq (need available skippedRev : List UInt64) :
    subtractSortedTRGo need available skippedRev =
      (subtractSorted need available).map (skippedRev.reverse ++ ·) := by
  induction available generalizing need skippedRev with
  | nil =>
    cases need <;> simp [subtractSortedTRGo, subtractSorted]
  | cons y ys ih =>
    cases need with
    | nil => simp [subtractSortedTRGo, subtractSorted]
    | cons x xs =>
      simp only [subtractSortedTRGo, subtractSorted]
      split
      · exact ih xs skippedRev
      · split
        · rw [ih]
          simp only [List.reverse_cons, Option.map_map, List.append_assoc, List.singleton_append]
          rfl
        · rfl

theorem subtractSortedTR_eq (need available : List UInt64) :
    subtractSortedTR need available = subtractSorted need available := by
  simpa [subtractSortedTR] using subtractSortedTRGo_eq need available []

end Tamarin.Executable
