import TamarinRuntime.ACReducedFeasibility
import Tamarin.ACRowReduction
import Tamarin.ACDirectFeasibility

namespace Tamarin.ACFeasibility
open ACBasis
variable {n : Nat}

theorem positiveCertificate_iff (rs : List (Row n)) (x : Vector Nat n) :
    positiveCertificate rs x = true ↔ (∀ i : Fin n, 0 < x[i]) ∧ SystemHolds rs (fun i => x[i]) := by
  simp [positiveCertificate,Vector.all_eq_true,Row.Holds,SystemHolds]
  intro _
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i,hi⟩⟩

theorem reducedFeasible_sound (rs : List (Row n)) (b : Bool) (result : reducedFeasible rs = some b) :
    b = true ↔ Feasible rs := by
  by_cases room : n*rs.length*rs.length ≤ 524288
  · cases done : RowReduction.echelon rs.length rs with
    | none => simp [reducedFeasible,room,done,guard] at result
    | some out =>
      cases quick : direct out with
      | some answer =>
        obtain rfl : answer = b := by simpa [reducedFeasible,room,done,guard,quick] using result
        apply (direct_sound out answer quick).trans
        exact exists_congr (fun x => and_congr_left (fun _ => RowReduction.echelon_iff _ _ _ done x))
      | none =>
        simp [reducedFeasible,room,done,guard,quick,Option.bind_eq_some_iff] at result
        obtain ⟨x,_,verified,rfl⟩ := result
        obtain ⟨positive,balanced⟩ := (positiveCertificate_iff _ _).mp verified
        exact iff_of_true rfl ⟨_,balanced,positive⟩
  · simp [reducedFeasible,room,guard,failure] at result

end Tamarin.ACFeasibility
