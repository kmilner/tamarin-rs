import Tamarin.SortedFlatMatching
import Tamarin.SortedMatch
import Tamarin.WholeProblem

namespace Tamarin.SortedMatchSorts
open FlatMatching SortedMatch WholeProblem
variable {sig : Signature}

theorem subsort_iff (a b : SortId) :
    Whole.subsort (sortWord a) (sortWord b) = true ↔ Subsort a b := by
  rw [← Subsort.check_iff]
  cases a <;> cases b <;> rfl

private theorem row_iff (f : sig.ACSym) (v : Variable) (ats : Array UInt64)
    (d : UInt64 → sig.Atom) (row : List UInt64) (full : row ≠ [])
    (live : ∀ j ∈ row, ats[j.toNat]? = some (sortWord (sig.atomSort (d j)))) :
    RowFits (sortWord (sig.acSort f)) (sortWord v.sort) ats row ↔
      Subsort (FlatAC.term f (row.map d)).rootSort v.sort := by
  cases row with
  | nil => contradiction
  | cons j js =>
    cases js with
    | nil => simpa only [RowFits, live j (by simp), Option.some.injEq, exists_eq_left', List.map_cons, List.map_nil, FlatAC.term, Term.rootSort] using
               subsort_iff (sig.atomSort (d j)) v.sort
    | cons k ks => exact subsort_iff _ _

/-- Word-level sort checks are precisely sortedness of the decoded AC images.
Only IDs in the subject need to round-trip through the atom-sort table. -/
theorem fits_iff (vs : Array UInt64) (vars : Fin vs.size → Variable) (f : sig.ACSym)
    (ats : Array UInt64) (decode : UInt64 → sig.Atom) (rhs : Array UInt64) (arm : Array (Array UInt64))
    (varWords : ∀ i, vs[i] = sortWord (vars i).sort)
    (atomWords : ∀ a ∈ rhs.toList, ats[a.toNat]? = some (sortWord (sig.atomSort (decode a))))
    (valid : (arm.toList.map Array.toList).length = vs.size ∧
      ∀ row ∈ arm.toList.map Array.toList, row ≠ [] ∧ List.Sublist row rhs.toList) :
    Fits (sortWord (sig.acSort f)) vs ats arm ↔
      SortedFlatMatching.Typed f vars (arm.toList.map (fun r => r.toList.map decode)) := by
  have len : arm.size = vs.size := by simpa using valid.1
  have decodeLen : (arm.toList.map (fun r => r.toList.map decode)).length = vs.size := by simpa
  have each (i : Fin vs.size) :
      let row := arm[i.val]'(by omega)
      RowFits (sortWord (sig.acSort f)) vs[i] ats row.toList ↔
        Subsort (FlatAC.term f (rowVector _ decodeLen i)).rootSort (vars i).sort := by
    let row := arm[i.val]'(by omega)
    have hm : row.toList ∈ arm.toList.map Array.toList := List.mem_map_of_mem
      (f := Array.toList) (Array.mem_def.mp (Array.getElem_mem (by omega)))
    obtain ⟨full,sub⟩ := valid.2 _ hm
    simpa only [row, varWords, rowVector, List.getElem_map, Array.getElem_toList] using
      row_iff f (vars i) ats decode row.toList full (fun j hj => atomWords j (sub.subset hj))
  constructor
  · rintro ⟨_,fits⟩
    refine ⟨decodeLen,fun i => (each i).mp ?_⟩
    obtain ⟨row,hr,hfit⟩ := fits i
    rw [Array.getElem?_eq_getElem (show i.val < arm.size by omega)] at hr
    cases hr
    exact hfit
  · rintro ⟨_,typed⟩
    refine ⟨len, fun i => ⟨_, Array.getElem?_eq_getElem (show i.val < arm.size by omega), (each i).mpr (typed i)⟩⟩

end Tamarin.SortedMatchSorts
