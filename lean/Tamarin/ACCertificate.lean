import TamarinRuntime.ACCertificate
import Tamarin.ACReducedFeasibility
import Tamarin.ACAlternative

namespace Tamarin.ACFeasibility
open ACBasis
variable {n : Nat}

theorem check_primal_iff (rows : List (Row n)) (xs : Array Nat) :
    checkCertificate rows (.primal xs) = some true ↔
      ∃ size : xs.size = n, let x : Vector Nat n := ⟨xs,size⟩
        (∀ i : Fin n, 0 < x[i]) ∧ SystemHolds rows (fun i => x[i]) := by
  by_cases h : xs.size = n <;> simp [checkCertificate,h,positiveCertificate_iff]

theorem check_dual_iff (rows : List (Row n)) (ys : Array Int) :
    checkCertificate rows (.dual ys) = some false ↔ Separation.Certificate rows ys.toList := by
  simp [checkCertificate,Separation.separates_iff]

/-- The two accepted verdicts have disjoint mathematical meanings. Any
candidate generator can use this interface, including an incomplete search. -/
theorem checkCertificate_sound (rows : List (Row n)) (c : Simplex.Certificate) {b}
    (checked : checkCertificate rows c = some b) : b = true ↔ Feasible rows := by
  cases c with
  | primal x =>
    dsimp only [checkCertificate] at checked
    split at checked <;> try contradiction
    split at checked <;> try contradiction
    rename_i h
    cases checked
    obtain ⟨pos,sol⟩ := (positiveCertificate_iff _ _).mp h
    exact iff_of_true rfl ⟨_,sol,pos⟩
  | dual y =>
    dsimp only [checkCertificate] at checked
    split at checked <;> try contradiction
    rename_i h
    cases checked
    exact iff_of_false (by decide) (Separation.separates_refutes h)

/-- The checker accepts a witness for every true answer, including refutations.
This quantifies over the arrays the runtime consumes and makes no assumption
about tableau size, rank, resource limits or how a witness was found. -/
theorem certificate_iff (rows : List (Row n)) (b : Bool) :
    (∃ c, checkCertificate rows c = some b) ↔ (b = true ↔ Feasible rows) := by
  constructor
  · rintro ⟨c,ok⟩
    exact checkCertificate_sound rows c ok
  · intro verdict
    cases b with
    | true =>
      obtain ⟨x,sol,pos⟩ := verdict.mp rfl
      refine ⟨.primal (Vector.ofFn x).toArray,(check_primal_iff ..).mpr ?_⟩
      exact ⟨by simp,by simpa using And.intro pos sol⟩
    | false =>
      have no : ¬Feasible rows := fun h => Bool.noConfusion (verdict.mpr h)
      obtain ⟨ys,sep⟩ := (Alternative.separator_iff_infeasible rows).mpr no
      exact ⟨.dual ys.toArray,(check_dual_iff ..).mpr (by simpa using sep)⟩

theorem certifiedSearch_sound (rows : List (Row n)) {b} (done : certifiedSearch rows = some b) :
    b = true ↔ Feasible rows := by
  obtain ⟨c,_,ok⟩ := Option.bind_eq_some_iff.mp done
  exact checkCertificate_sound rows c ok

end Tamarin.ACFeasibility
