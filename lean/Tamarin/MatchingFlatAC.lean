import Tamarin.Matching
import Tamarin.BackendContract
import Tamarin.SortCheck

namespace Tamarin.Matching
variable {sig : Signature}

theorem residual_complete {backend : FlatACBackend} (correct : backend.Correct)
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (_ht : tail.toList ≠ []) (hr : rhs.toList ≠ [])
    (h : backend.residual tail rhs = (2 :: rest).toArray)
    (hs : HasSort (FlatAC.term f (rest.map decode)) v.sort) :
    Complete (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      (fun _ => True) [Substitution.binding v (FlatAC.term f (rest.map decode)) hs] := by
  apply of_ground_subjects
  · intro e he
    have heq : e = ⟨.ac f (.var v) (FlatAC.term f (tail.toList.map decode)),
        FlatAC.term f (rhs.toList.map decode)⟩ := by
      simpa [FlatAC.variableProblem] using he
    subst e
    exact FlatAC.term_not_occurs f _ (by simpa using hr)
  · exact correct.residual_success decode v f tail rhs rest h hs
  · intro σ hσ
    have he := List.mem_singleton.mp hσ; subst σ
    exact FlatAC.variable_difference_domain v f _ _ _ hs

/-- A forced residual whose root sort cannot inhabit the variable excludes
even nonground solutions, by cancellation and invariance of the root sort. -/
theorem residual_wrong_sort {backend : FlatACBackend} (correct : backend.Correct)
    (decode : UInt64 → sig.Atom) (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (rest : List UInt64)
    (ht : tail.toList ≠ []) (hr : rhs.toList ≠ [])
    (h : backend.residual tail rhs = (2 :: rest).toArray)
    (wrong : ¬ Subsort (FlatAC.term f (rest.map decode)).rootSort v.sort) :
    CompleteSet (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode)) [] := by
  apply (complete_empty_iff _).mpr
  rintro ⟨σ, hσ⟩
  have perm := (correct.residual_difference tail rhs rest h).map decode
  have forced := (FlatAC.variable_solves_iff v f _ _ (rest.map decode)
    (by simpa using ht) (by simpa using hr)
    (by simpa using correct.residual_nonempty tail rhs rest h)
    (by simpa only [List.map_append] using perm) σ).mp hσ
  exact wrong ((Term.rootSort_equiv forced) ▸ Term.rootSort_le (σ.sorted v))

theorem residual_failure {backend : FlatACBackend} (correct : backend.Correct)
    [DecidableEq sig.Atom] (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (v : Variable) (f : sig.ACSym)
    (tail rhs : Array UInt64) (live : ∀ a ∈ tail.toList ++ rhs.toList, encode (decode a) = some a)
    (hr : rhs.toList ≠ [])
    (h : backend.residual tail rhs = #[1]) :
    Complete (FlatAC.variableProblem v f (tail.toList.map decode) (rhs.toList.map decode))
      (fun _ => True) [] := by
  apply of_ground_subjects
  · intro e he
    have heq : e = ⟨.ac f (.var v) (FlatAC.term f (tail.toList.map decode)),
        FlatAC.term f (rhs.toList.map decode)⟩ := by
      simpa [FlatAC.variableProblem] using he
    subst e
    exact FlatAC.term_not_occurs f _ (by simpa using hr)
  · exact correct.residual_failure decode encode v f tail rhs live h
  · simp
end Tamarin.Matching
