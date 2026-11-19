import Tamarin.ACDirectFeasibility
import Tamarin.ACRationalCone

/-! A strictly positive solution can be scaled to include all columns of any
complete rational generating family with strictly positive coefficients. -/
namespace Tamarin.ACFeasibility.PositivePullback
open ACBasis

private theorem add_dot {n} (v x y : Vec n) :
    dot v (fun i => x i + y i) = dot v x + dot v y := by
  simp only [dot,Nat.mul_add,total_add]

private theorem bounded {n} (v : Vec n) (i : Fin n) : v i ≤ total v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [total,List.ofFn_succ,List.sum_cons]
    exact Fin.cases (by omega) (fun j => Nat.le_trans (ih (fun k => v k.succ) j) (Nat.le_add_left ..)) i

private theorem scale_holds {n} {r : Row n} {x : Vec n} (a : Nat) (h : r.Holds x) :
    r.Holds (Cone.scale a x) := by
  unfold Row.Holds at h ⊢; simp only [Cone.dot_scale,h]

theorem interior {n} {rs : List (Row n)} {gs : List (Vec n)} (basis : Cone.ScaleCorrect rs gs)
    (x : Vec n) (closed : SystemHolds rs x) (pos : ∀ i, 0 < x i) :
    ∃ a > 0, ∃ c : Vec gs.length, (∀ j, 0 < c j) ∧ mix gs.get c = Cone.scale a x := by
  let ones : Vec gs.length := fun _ => 1
  let all := mix gs.get ones
  let d := total all + 1
  let residue := fun i => d * x i - all i
  have whole : (fun i => residue i + all i) = Cone.scale d x := by
    funext i; change d*x i - all i + all i = d*x i
    have enough := Nat.le_trans (Nat.le_succ_of_le (bounded all i)) (Nat.le_mul_of_pos_right d (pos i))
    omega
  have allClosed := basis.sound all ⟨ones,rfl⟩
  have remaining : SystemHolds rs residue := by
    intro r hr
    have same := scale_holds d (closed r hr)
    rw [←whole] at same
    have first := allClosed r hr
    simp only [Row.Holds,add_dot] at first same ⊢
    omega
  obtain ⟨a,ha,c,rep⟩ := basis.complete residue remaining
  refine ⟨a*d,Nat.mul_pos ha (by simp [d]),fun j => c j + a*ones j,by intro j; simp [ones]; omega,?_⟩
  funext i
  change dot (fun j => gs.get j i) (fun j => c j + Cone.scale a ones j) = a*d*x i
  rw [add_dot,Cone.dot_scale]
  change mix gs.get c i + a * all i = a*d*x i
  rw [rep]; change a*residue i + a*all i = a*d*x i
  have eq := congrFun whole i
  change residue i + all i = d*x i at eq
  rw [←Nat.mul_add,eq,Nat.mul_assoc]

/-- Under joint strict positivity one can check subsequent balance equations
on the generator coefficients using the same strict-positivity predicate. -/
theorem feasible_iff {n} (base more : List (Row n)) (gs : List (Vec n))
    (basis : Cone.ScaleCorrect base gs) :
    Feasible (more ++ base) ↔ Feasible base ∧ Feasible (more.map (·.pullback gs.get)) := by
  constructor
  · rintro ⟨x,all,pos⟩
    have hbase : SystemHolds base x := fun r hr => all r (List.mem_append_right _ hr)
    obtain ⟨a,_,c,hc,eq⟩ := interior basis x hbase pos
    refine ⟨⟨x,hbase,pos⟩,c,?_,hc⟩
    intro r hr; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    apply (s.pullback_iff _ _).mpr
    rw [eq]; exact scale_holds a (all s (List.mem_append_left _ hs))
  · rintro ⟨⟨x,bx,px⟩,c,closed,live⟩
    refine ⟨mix gs.get c,?_,?_⟩
    · intro r hr; rcases List.mem_append.mp hr with m|b
      · exact (r.pullback_iff ..).mp (closed _ (List.mem_map.mpr ⟨_,m,rfl⟩))
      · exact basis.sound _ ⟨c,rfl⟩ r b
    · intro i
      obtain ⟨a,ha,w,eq⟩ := basis.complete x bx
      have p : 0 < mix gs.get w i := by rw [eq]; exact Nat.mul_pos ha (px i)
      obtain ⟨t,mem,positive⟩ := List.sum_pos_iff_exists_pos_nat.mp p
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,
        Nat.mul_pos (Nat.pos_of_mul_pos_right positive) (live j)⟩

theorem one_iff {n} (r : Row n) :
    Feasible [r] ↔ ((∃ i, 0 < r.pos i) ↔ (∃ j, 0 < r.neg j)) := by
  constructor
  · rintro ⟨v,h,pos⟩
    have eq := h r List.mem_cons_self
    have sign (a : Vec n) : 0 < dot a v ↔ ∃ i, 0 < a i := by
      rw [dot,total,List.sum_pos_iff_exists_pos_nat]
      constructor
      · rintro ⟨t,ht,gt⟩; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
        exact ⟨i,Nat.pos_of_mul_pos_right gt⟩
      · rintro ⟨i,hi⟩; exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,Nat.mul_pos hi (pos i)⟩
    exact (sign _).symm.trans (eq ▸ sign _)
  · intro eq
    refine ⟨PositiveWitness.witness r,?_,?_⟩
    · simpa [SystemHolds] using PositiveWitness.witness_holds r
    · intro i; apply (PositiveWitness.positive_iff_enabled r i).mpr
      by_cases p : ∃ j, 0 < r.pos j
      · exact .inl ⟨p,eq.mp p⟩
      · have g := fun (j : Fin n) (h : 0 < r.neg j) => p (eq.mpr ⟨j,h⟩)
        exact .inr ⟨Nat.eq_zero_of_not_pos (fun h => p ⟨i,h⟩),Nat.eq_zero_of_not_pos (g i)⟩

end Tamarin.ACFeasibility.PositivePullback
