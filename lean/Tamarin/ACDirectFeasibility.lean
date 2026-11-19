import TamarinRuntime.ACDirectFeasibility
import Tamarin.ACPositiveWitness

namespace Tamarin.ACFeasibility
open ACBasis

def Feasible {n} (rs : List (Row n)) : Prop := ∃ x, SystemHolds rs x ∧ ∀ i, 0 < x i

private theorem total_pos {n} (v : Vec n) : 0 < total v ↔ ∃ i, 0 < v i := by
  simp [total,List.sum_pos_iff_exists_pos_nat]; grind

private theorem side_iff {n} (r : Row n) :
    oneSided r = false ↔ (total r.pos = 0 ↔ total r.neg = 0) := by
  by_cases p : total r.pos = 0 <;> by_cases q : total r.neg = 0 <;> simp [oneSided,p,q]

private theorem row_live {n} (r : Row n) (x : Vec n) (positive : ∀ i, 0 < x i)
    (balanced : r.Holds x) : oneSided r = false := by
  have pos (v : Vec n) : 0 < dot v x ↔ 0 < total v := by
    unfold dot
    rw [total_pos,total_pos]
    exact exists_congr (fun i => ⟨Nat.pos_of_mul_pos_right,fun h => Nat.mul_pos h (positive i)⟩)
  have both := (pos r.pos).symm.trans ((show dot r.pos x = dot r.neg x from balanced) ▸ (pos r.neg))
  apply (side_iff r).mpr
  omega

private theorem witness_pos {n} (r : Row n) (ok : oneSided r = false) :
    ∀ i, 0 < PositiveWitness.witness r i := by
  intro i
  apply (PositiveWitness.positive_iff_enabled r i).mpr
  by_cases neutral : r.pos i = 0 ∧ r.neg i = 0
  · exact .inr neutral
  have nz : 0 < total r.pos ∨ 0 < total r.neg := by
    by_cases h : r.pos i = 0
    · exact .inr ((total_pos _).mpr ⟨i,by omega⟩)
    · exact .inl ((total_pos _).mpr ⟨i,by omega⟩)
  have eq := (side_iff r).mp ok
  exact .inl ⟨(total_pos _).mp (by omega),(total_pos _).mp (by omega)⟩

theorem direct_sound {n} (rs : List (Row n)) (b : Bool) (h : direct rs = some b) :
    b = true ↔ Feasible rs := by
  by_cases bad : rs.any oneSided = true
  · obtain rfl : false = b := by simpa [direct,bad] using h
    obtain ⟨r,hr,unbalanced⟩ := List.any_eq_true.mp bad
    simp only [Bool.false_eq_true,false_iff]
    rintro ⟨x,sol,live⟩
    rw [row_live r x live (sol r hr)] at unbalanced
    contradiction
  cases find : rs.find? (fun r => total r.pos != total r.neg) with
  | none =>
    obtain rfl : true = b := by simpa [direct,bad,find] using h
    refine iff_of_true rfl ⟨fun _ => 1,?_,by simp⟩
    intro r hr
    have sum := List.find?_eq_none.mp find r hr
    simpa [Row.Holds,dot] using sum
  | some r =>
    let x := PositiveWitness.witness r
    simp [direct,bad,find] at h
    obtain ⟨holds,rfl⟩ := h
    refine iff_of_true rfl ⟨x,holds,witness_pos r ?_⟩
    · exact Bool.eq_false_iff.mpr (fun pos => bad (List.any_eq_true.mpr ⟨r,List.mem_of_find?_eq_some find,pos⟩))

/-- These guarantees refer only to input coefficients. Other conjunctions
may also finish when a shared positive witness satisfies every row. -/
def DirectWithin {n} (rs : List (Row n)) : Prop :=
  rs.length ≤ 1 ∨ (∃ r ∈ rs, ¬ (total r.pos = 0 ↔ total r.neg = 0)) ∨
    ∀ r ∈ rs, total r.pos = total r.neg

theorem direct_complete {n} (rs : List (Row n)) (domain : DirectWithin rs) : (direct rs).isSome := by
  by_cases bad : rs.any oneSided = true
  · simp [direct,bad]
  rcases domain with few | ⟨r,hr,side⟩ | balanced
  · cases rs with
    | nil => simp [direct]
    | cons r rest =>
      obtain rfl : rest = [] := by simpa using few
      by_cases eq : total r.pos = total r.neg <;>
        simp_all [direct]
      exact PositiveWitness.witness_holds r
  · exfalso
    apply bad
    apply List.any_eq_true.mpr
    refine ⟨r,hr,?_⟩
    cases h : oneSided r with
    | true => rfl
    | false => exact False.elim (side ((side_iff r).mp h))
  · have find : rs.find? (fun r => total r.pos != total r.neg) = none :=
      List.find?_eq_none.mpr (fun r hr => by simp [balanced r hr])
    simp [direct,bad,find]

end Tamarin.ACFeasibility
