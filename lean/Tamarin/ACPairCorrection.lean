import TamarinRuntime.ACPairCorrection
import Tamarin.ACThreeColumns

namespace Tamarin.ACFeasibility.PairCorrection
open ACBasis
variable {n : Nat}

/-- The original system has a positive solution agreeing with a single
positive value outside at most two coordinates. The exceptional coordinates
can take independently chosen natural values. -/
def Within (rs : List (Row n)) : Prop :=
  n*n*max 1 rs.length ≤ 200000 ∧
    ∃ x : Vec n, SystemHolds rs x ∧ (∀ i, 0 < x i) ∧ ∃ b : Nat, 0 < b ∧
      ∃ exceptional : List (Fin n), exceptional.length ≤ 2 ∧ ∀ i ∉ exceptional, x i = b

private def group (j k i : Fin n) : Fin 3 := if i = j then 0 else if i = k then 1 else 2

private def frame (j k : Fin n) (g : Fin 3) : Vec n :=
  fun i => if group j k i = g then 1 else 0

private theorem partition (v : Vec n) (j k : Fin n) :
    total v = dot v (frame j k 0) + dot v (frame j k 1) + dot v (frame j k 2) := by
  have split : v = fun i => v i * frame j k 0 i + v i * frame j k 1 i + v i * frame j k 2 i := by
    funext i
    by_cases hj : i = j <;> by_cases hk : i = k <;> simp_all [frame,group]
  exact (congrArg total split).trans (by simp only [total_add,dot])

private theorem counts_dot (v : Vec n) (j k : Fin n) :
    ∀ i : Fin 3, (counts v (total v) j k)[i] = dot v (frame j k i) := by
  have zeroFrame : frame j k 0 = spike j 1 := by
    funext i; by_cases hj : i = j <;> by_cases hk : i = k <;> simp [frame,group,spike,hj,hk]
  have first : dot v (frame j k 0) = v j := by simp [zeroFrame,dot_spike]
  have second : dot v (frame j k 1) = if j = k then 0 else v k := by
    by_cases same : j = k
    · subst k
      have empty : frame j j 1 = (fun _ => 0) := by
        funext i; by_cases eq : i = j <;> simp [frame,group,eq]
      simp [empty,dot,total,List.sum_eq_zero_iff_forall_eq_nat]
    · have oneFrame : frame j k 1 = spike k 1 := by
        funext i; by_cases hj : i = j <;> by_cases hk : i = k <;> simp_all [frame,group,spike]
      simp [oneFrame,same,dot_spike]
  have parts := partition v j k
  rw [first,second] at parts
  intro i
  have cases3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases3 with rfl|rfl|rfl
  · exact first.symm
  · exact second.symm
  · change total v - v j - _ = _
    omega

private theorem project_pullback (j k : Fin n) (r : Row n) :
    project j k (prepare r) = r.pullback (frame j k) := by
  dsimp only [project,Row.pullback,prepare]
  rw [funext (counts_dot r.pos j k),funext (counts_dot r.neg j k)]

private theorem mix_frame (j k : Fin n) (y : Vec 3) (i : Fin n) :
    mix (frame j k) y i = y (group j k i) := by
  change total (fun g => frame j k g i * y g) = _
  have same : (fun g => frame j k g i * y g) = fun g => y g * spike (group j k i) 1 g := by
    funext g
    by_cases eq : group j k i = g <;> simp [frame,spike,eq,Ne.symm]
  rw [same,←show dot y (spike (group j k i) 1) = total (fun g => y g * spike (group j k i) 1 g) from rfl,
      dot_spike,Nat.mul_one]

private theorem project_holds (rs : List (Row n)) (j k : Fin n) (y : Vec 3) :
    SystemHolds ((rs.map prepare).map (project j k)) y ↔
      SystemHolds rs (fun i => y (group j k i)) := by
  have eq := funext (mix_frame j k y)
  simp only [SystemHolds,List.forall_mem_map,project_pullback,Row.pullback_iff,eq]

private theorem pair_iff (rs : List (Row n)) :
    ((List.finRange n).any (fun j => (List.finRange n).any (fun k =>
      j ≤ k && ThreeColumns.decide ((rs.map prepare).map (project j k))))) = true ↔
    ∃ j k : Fin n, j ≤ k ∧ ∃ y : Vec 3, SystemHolds rs (fun i => y (group j k i)) ∧ ∀ g, 0 < y g := by
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,decide_eq_true_eq,
    ThreeColumns.decide_iff,Feasible,project_holds]

private theorem zero_feasible (rs : List (Row 0)) : Feasible rs := by
  refine ⟨fun _ => 1,?_,by simp⟩
  intro r _
  simp [Row.Holds,dot,total]

theorem run_sound (rs : List (Row n)) (b : Bool) (returned : run rs = some b) :
    b = true ↔ Feasible rs := by
  unfold run at returned
  split at returned <;> try contradiction
  split at returned
  · rename_i zero
    subst n
    exact iff_of_true (Option.some.inj returned).symm (zero_feasible rs)
  · dsimp only at returned
    split at returned
    · rename_i found
      obtain ⟨j,k,_,y,good,positive⟩ := (pair_iff _).mp found
      exact iff_of_true (Option.some.inj returned).symm ⟨_,good,fun i => positive (group j k i)⟩
    · contradiction

private theorem pad {x : Vec n} (b : Nat) (nonempty : 0 < n) (exc : List (Fin n))
    (small : exc.length ≤ 2) (common : ∀ i ∉ exc, x i = b) :
    ∃ j k : Fin n, j ≤ k ∧ ∀ i, i ≠ j → i ≠ k → x i = b := by
  let first : Fin n := ⟨0,nonempty⟩
  match exc with
  | [] => exact ⟨first,first,Fin.le_refl _,fun i _ _ => common i (by simp)⟩
  | [j] => exact ⟨j,j,Fin.le_refl _,fun i h _ => common i (by simpa using h)⟩
  | [j,k] =>
    by_cases order : j ≤ k
    · exact ⟨j,k,order,fun i h g => common i (by simp [h,g])⟩
    · exact ⟨k,j,by omega,fun i h g => common i (by simp [h,g])⟩
  | _ :: _ :: _ :: _ => simp at small

theorem run_complete (rs : List (Row n)) (within : Within rs) : (run rs).isSome := by
  obtain ⟨room,x,sol,positive,b,base,exc,small,common⟩ := within
  by_cases zero : n = 0
  · simp [run,zero]
  · obtain ⟨j,k,order,padded⟩ := pad b (Nat.pos_of_ne_zero zero) exc small common
    let y : Vec 3 := fun g => if g = 0 then x j else if g = 1 then x k else b
    have lift : (fun i => y (group j k i)) = x := by
      funext i
      by_cases first : i = j
      · simp [group,first,y]
      · by_cases second : i = k
        · rw [group,ite_eq_right first,ite_eq_left second]
          simp [y,second]
        · simp [group,first,second,y,padded i first second]
    have found := (pair_iff rs).mpr ⟨j,k,order,y,lift ▸ sol,fun g => by
      dsimp only [y]; (repeat' split) <;> first | exact positive _ | exact base⟩
    simp only [run,Nat.not_lt.mpr room,↓reduceIte,zero,found,Option.isSome_some]

/-- The current probe exhausts exactly the budgeted two-exception family.
In particular, a missed family says nothing about solutions with more sizes. -/
theorem run_iff (rs : List (Row n)) : run rs = some true ↔ Within rs := by
  constructor
  · intro h
    unfold run at h
    split at h <;> try contradiction
    rename_i cap
    refine ⟨Nat.le_of_not_gt cap,?_⟩
    split at h
    · rename_i z
      subst n
      obtain ⟨x,holds,pos⟩ := zero_feasible rs
      exact ⟨x,holds,pos,1,by decide,[],by decide,fun i => i.elim0⟩
    · dsimp only at h
      split at h <;> try contradiction
      rename_i found
      obtain ⟨j,k,_,y,holds,pos⟩ := (pair_iff _).mp found
      refine ⟨_,holds,fun i => pos (group j k i),y 2,pos _,[j,k],by simp,?_⟩
      intro i missing
      simp at missing
      simp [group,missing.1,missing.2]
  · intro within
    obtain ⟨b,got⟩ := Option.isSome_iff_exists.mp (run_complete _ within)
    obtain ⟨_,x,holds,pos,_⟩ := within
    exact ((run_sound _ b got).mpr ⟨x,holds,pos⟩) ▸ got

section
private def equation (width p q scale : Nat) : Row width :=
  Row.ofWeights (fun i => if i.val = p then 1 else 0) (fun i => if i.val = q then scale else 0)

private def fourRows (width : Nat) : List (Row width) :=
  [equation width 7 0 3,equation width 13 1 5,equation width 0 1 1,equation width 1 2 1]

-- A width-47, rank-four system with two distinct exceptional sizes.
-- The mathematical input witness pins an affirmative completion obligation.
private theorem explicit_sizes : Within (fourRows 47) := by
  let x : Vec 47 := fun i => if i = 7 then 3 else if i = 13 then 5 else 1
  refine ⟨by decide,x,?_,?_,1,by decide,[7,13],by decide,?_⟩
  · simp only [fourRows,SystemHolds,List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true,Row.Holds]
    decide
  · decide
  · intro i absent
    simp at absent
    simp [x,absent.1,absent.2]

#guard run (fourRows 47) == some true
#guard run (fourRows 224) == none
#guard run (n := 0) [] == some true
#guard run [equation 1 0 0 2] == none
#guard run [equation 2 0 1 7] == some true
-- The system is feasible with values (2,3,4,1), but every solution uses
-- four distinct sizes, so the three-group probe must defer.
#guard run [equation 4 0 3 2,equation 4 1 3 3,equation 4 2 3 4] == none
end

end Tamarin.ACFeasibility.PairCorrection
