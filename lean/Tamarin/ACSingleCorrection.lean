import TamarinRuntime.ACSingleCorrection
import Tamarin.ACDirectFeasibility

namespace Tamarin.ACFeasibility.SingleCorrection
open ACBasis
variable {n : Nat}

namespace Ratio

def Holds (rs : Constraints) (a b : Nat) : Prop :=
  ∀ r ∈ rs, r.1 * (a : Int) = (r.1-r.2) * (b : Int)

theorem test_iff {p : Int × Int} {rs : Constraints} (hp : p ∈ rs) (nz : p.2 ≠ 0) :
    test p rs = true ↔ ∃ a b : Nat, 0 < a ∧ 0 < b ∧ Holds rs a b := by
  let a' := (p.1-p.2).natAbs
  let b' := p.1.natAbs
  change (decide (0 < a') && decide (0 < b') && rs.all (fun r => balanced r a' b')) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, balanced, beq_iff_eq]
  constructor
  · rintro ⟨⟨ha,hb⟩,holds⟩
    exact ⟨a',b',ha,hb,holds⟩
  · rintro ⟨a,b,ha,hb,holds⟩
    have eq := holds p hp
    have az : (a : Int) ≠ 0 := by omega
    have bz : (b : Int) ≠ 0 := by omega
    have left : p.1 ≠ 0 := by
      intro z
      rw [z,Int.zero_mul] at eq
      have zero := (Int.mul_eq_zero.mp eq.symm).resolve_right bz
      omega
    have right : p.1-p.2 ≠ 0 := by
      intro z
      rw [z,Int.zero_mul] at eq
      exact left ((Int.mul_eq_zero.mp eq).resolve_right az)
    have scale : b' * a = a' * b := by
      simpa [a',b',Int.natAbs_mul] using congrArg Int.natAbs eq
    have scaleZ : (a' : Int)*(b : Int) = (a : Int)*(b' : Int) := by
      exact_mod_cast scale.symm.trans (Nat.mul_comm _ _)
    refine ⟨⟨Int.natAbs_pos.mpr right,Int.natAbs_pos.mpr left⟩,?_⟩
    intro r hr
    have h := holds r hr
    have cancel : (r.1*(a' : Int))*(b : Int) = ((r.1-r.2)*(b' : Int))*(b : Int) := by
      calc
        _ = r.1 * ((a' : Int) * (b : Int)) := Int.mul_assoc ..
        _ = (r.1 * (a : Int)) * (b' : Int) := by rw [scaleZ,Int.mul_assoc]
        _ = _ := by rw [h,Int.mul_right_comm]
    exact Int.eq_of_mul_eq_mul_right bz cancel

theorem run_iff (rs : Constraints) :
    run rs = true ↔ ∃ a b : Nat, 0 < a ∧ 0 < b ∧ Holds rs a b := by
  cases found : rs.find? (fun r => r.2 != 0) with
  | none =>
    simp only [run,found,true_iff]
    refine ⟨1,1,by decide,by decide,?_⟩
    intro r hr
    have h := List.find?_eq_none.mp found r hr
    simp_all
  | some p =>
    have mem := List.mem_of_find?_eq_some found
    have nz := List.find?_some found
    simpa [run,found] using (test_iff mem (by simpa using nz))

end Ratio

def correction (j : Fin n) (a b : Nat) : Vec n := fun i => if i = j then a else b

/-- A positive solution has a common size on every coordinate except possibly j. -/
def Within (rs : List (Row n)) : Prop :=
  ∃ (j : Fin n) (a b : Nat), 0 < a ∧ 0 < b ∧ SystemHolds rs (correction j a b)

private theorem dot_const (v : Vec n) (b : Nat) : dot v (fun _ => b) = total v * b := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    simpa [dot,total,List.ofFn_succ,Nat.add_mul] using
      congrArg (v 0 * b + ·) (ih (fun i => v i.succ))

private theorem dot_correction (v : Vec n) (j : Fin n) (a b : Nat) :
    dot v (correction j a b) + v j*b = total v*b + v j*a := by
  have split : (fun i => correction j a b i + spike j b i) = fun i => b + spike j a i := by
    funext i
    by_cases h : i = j <;> simp [correction,spike,h,Nat.add_comm]
  rw [← dot_spike v j b, ← dot_spike v j a, ← dot_const v b]
  simpa only [dot,Nat.mul_add,total_add] using congrArg (dot v) split

private theorem holds_iff (r : Row n) (j : Fin n) (a b : Nat) :
    r.Holds (correction j a b) ↔
      (signed r j)*(a : Int) = (signed r j - (prepare r).2)*(b : Int) := by
  have cast (v : Vec n) :
      (dot v (correction j a b) : Int) + (v j : Int)*b = (total v : Int)*b + (v j : Int)*a := by
    exact_mod_cast dot_correction v j a b
  have p := cast r.pos
  have q := cast r.neg
  simp only [Row.Holds,signed,prepare,Int.sub_mul]
  omega

private theorem column_iff (rs : List (Row n)) (j : Fin n) (a b : Nat) :
    Ratio.Holds ((rs.map prepare).map (column j)) a b ↔ SystemHolds rs (correction j a b) := by
  simp [Ratio.Holds,SystemHolds,column,holds_iff,prepare]

private theorem any_iff {rs : List (Row n)} {p : Row n × Int}
    (hp : p ∈ rs.map prepare) (nz : p.2 ≠ 0) :
    (List.finRange n).any (fun j => Ratio.test (column j p) ((rs.map prepare).map (column j))) = true
      ↔ Within rs := by
  simp only [List.any_eq_true, List.mem_finRange, true_and, Within]
  apply exists_congr
  intro j
  rw [Ratio.test_iff (List.mem_map_of_mem hp) nz]
  simp only [column_iff]

theorem run_sound (rs : List (Row n)) (b : Bool) (h : run rs = some b) : b = true ↔ Feasible rs := by
  cases find : (rs.map prepare).find? (fun r => r.2 != 0) with
  | none =>
    have eq : true = b := by simpa [run,find] using h
    refine iff_of_true eq.symm ⟨fun _ => 1,?_,by simp⟩
    intro r hr
    have zero := List.find?_eq_none.mp find (prepare r) (List.mem_map_of_mem hr)
    simp [prepare] at zero
    simp [Row.Holds,dot,show total r.pos = total r.neg by omega]
  | some p =>
    have nz := List.find?_some find
    simp only [run,find] at h
    split at h
    · rename_i yes
      obtain ⟨j,a,b,ha,hb,sol⟩ := (any_iff (List.mem_of_find?_eq_some find) (by simpa using nz)).mp yes
      refine iff_of_true (by simpa using h.symm) ⟨_,sol,?_⟩
      intro i
      simp only [correction]
      split <;> assumption
    · contradiction

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  cases find : (rs.map prepare).find? (fun r => r.2 != 0) with
  | none => simp [run,find]
  | some p =>
    have nz := List.find?_some find
    have yes := (any_iff (List.mem_of_find?_eq_some find) (by simpa using nz)).mpr within
    simp only [run,find,yes,ite_true,Option.isSome_some]

end Tamarin.ACFeasibility.SingleCorrection
