import Tamarin.ACBasisComplete
import Tamarin.VariablePermutation
import Tamarin.ACBagSearch

/-! A terminating reference for simultaneous homogeneous equations at one
ordinary AC head. Inputs and answer indices use natural numbers throughout. -/
namespace Tamarin.ACSystem.Reference
open VariablePermutation
variable {sig : Signature}

/-- Build the coordinate table from the source variable occurrences. -/
private def frame (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) :
    Frame f rows (variables rows).eraseDups.length := by
  let vs := (variables rows).eraseDups
  let idx (v : Variable) : Option (Fin vs.length) :=
    if h : v ∈ vs then some ⟨vs.idxOf v, List.idxOf_lt_length_of_mem h⟩ else none
  refine ⟨vs.get, idx, ?_, ?_, ?_, ?_⟩
  · intro i
    have distinct : vs.Nodup := Matching.ACBagSearch.dedup_distinct _
    simp [idx, List.get_eq_getElem, distinct.idxOf_getElem]
  · intro v hv
    have h : v ∈ vs := List.mem_eraseDups.mpr hv
    exact ⟨⟨_, List.idxOf_lt_length_of_mem h⟩, List.getElem_idxOf _⟩
  · intro i
    exact List.mem_eraseDups.mp (List.getElem_mem i.isLt)
  · intro i
    exact sorted _ (List.mem_eraseDups.mp (List.getElem_mem i.isLt))

private def witness (f : sig.ACSym) (used : List Variable) (j : Nat) : Variable :=
  ⟨freshBound used + j, sig.acSort f⟩

private theorem unused (f : sig.ACSym) (used : List Variable) (j : Nat) :
    witness f used j ∉ used := by
  intro h
  have lt := lt_freshBound used _ h
  change freshBound used + j < freshBound used at lt
  omega

private def branches {f : sig.ACSym} {rows : List Row} {n} (fr : Frame f rows n)
    (avoid : List Variable) : List (Branch f rows avoid) :=
  let matrix := rows.map (ACBasis.encode fr.names)
  let gs := ACBasis.generate matrix
  (Homogeneous.selections gs).attach.map fun js =>
    selectedBranch fr gs (ACBasis.generate_correct matrix)
      (fun j => witness f (variables rows ++ avoid) j.val) (fun _ => rfl)
      (fun j => unused _ _ j.val) js

/-- No precomputed basis, witness assignment, search budget, or success
hypothesis is required of the caller. -/
def solve (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) (avoid : List Variable) :
    List (Substitution sig) :=
  (branches (frame f rows sorted) avoid).map Branch.answer

theorem correct (f : sig.ACSym) (rows : List Row)
    (sorted : ∀ v ∈ variables rows, v.sort = sig.acSort f) (avoid : List Variable) :
    (Outcome.complete (solve f rows sorted avoid)).CorrectIn (problem f rows) avoid := by
  let fr := frame f rows sorted
  have inject {k : Nat} : Function.Injective (fun j : Fin k => witness f (variables rows ++ avoid) j.val) :=
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Variable.id h))
  simpa only [solve, branches, List.map_map, Function.comp_def] using
    basis_answers_correct fr _ (ACBasis.generate_correct _) _ inject
      (fun _ => rfl) (fun j => unused f (variables rows ++ avoid) j.val)

theorem range_fresh {f : sig.ACSym} {rows : List Row} {sorted avoid σ}
    (returned : σ ∈ solve f rows sorted avoid) {v w}
    (live : (problem f rows).Occurs v) (occ : (σ.image v).Occurs w) :
    w ∉ variables rows ++ avoid := by
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp returned
  exact b.range_fresh live occ

end Tamarin.ACSystem.Reference
