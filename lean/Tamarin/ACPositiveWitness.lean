import Tamarin.ACBasis

namespace Tamarin.ACBasis.PositiveWitness

variable {k n : Nat}

def enabled (p : Row k) (j : Fin k) : Prop :=
  ((∃ i, 0 < p.pos i) ∧ (∃ i, 0 < p.neg i)) ∨ (p.pos j = 0 ∧ p.neg j = 0)

def witness (p : Row k) : Vec k := fun i =>
  if 0 < p.pos i then total p.neg else if 0 < p.neg i then total p.pos else 1

private theorem total_scale (v : Vec k) (a : Nat) :
    total (fun i => v i * a) = total v * a := by
  induction k with
  | zero => simp [total]
  | succ k ih =>
    simp only [total,List.ofFn_succ,List.sum_cons,Nat.add_mul]
    exact congrArg (v 0 * a + ·) (ih (fun i => v i.succ))


theorem witness_holds (p : Row k) : p.Holds (witness p) := by
  have pos : (fun i => p.pos i * witness p i) = fun i => p.pos i * total p.neg := by
    funext i
    by_cases hp : 0 < p.pos i
    · simp [witness,hp]
    · simp [Nat.eq_zero_of_not_pos hp]
  have neg : (fun i => p.neg i * witness p i) = fun i => p.neg i * total p.pos := by
    funext i
    by_cases hn : 0 < p.neg i
    · have hp := (p.disjoint i).resolve_right (Nat.ne_of_gt hn)
      simp [witness,hp,hn]
    · simp [Nat.eq_zero_of_not_pos hn]
  unfold Row.Holds dot
  rw [pos,neg,total_scale,total_scale,Nat.mul_comm]

private theorem total_pos (v : Vec k) : 0 < total v ↔ ∃ i, 0 < v i := by
  simp [total,List.sum_pos_iff_exists_pos_nat]; grind

theorem positive_iff_enabled (p : Row k) (j : Fin k) : 0 < witness p j ↔ enabled p j := by
  unfold witness enabled
  by_cases hp : 0 < p.pos j
  · simp [hp,Nat.ne_of_gt hp,total_pos,show ∃ i, 0 < p.pos i from ⟨j,hp⟩]
  · have zp := Nat.eq_zero_of_not_pos hp
    by_cases hn : 0 < p.neg j
    · simp [zp,hn,Nat.ne_of_gt hn,total_pos,show ∃ i, 0 < p.neg i from ⟨j,hn⟩]
    · simp [zp,Nat.eq_zero_of_not_pos hn]

theorem maximal (p : Row k) (c : Vec k) (sol : p.Holds c) (j : Fin k) (cj : 0 < c j) :
    enabled p j := by
  have supported (v : Vec k) : 0 < dot v c ↔ ∃ i, 0 < v i ∧ 0 < c i := by
    rw [dot,total_pos]
    apply exists_congr
    intro i
    exact ⟨fun h => ⟨Nat.pos_of_mul_pos_right h,Nat.pos_of_mul_pos_left h⟩,
      fun ⟨hv,hc⟩ => Nat.mul_pos hv hc⟩
  by_cases h : p.pos j = 0 ∧ p.neg j = 0
  · exact .inr h
  · have dot_eq : dot p.pos c = dot p.neg c := sol
    have live : 0 < dot p.pos c := by
      by_cases hp : 0 < p.pos j
      · exact (supported _).mpr ⟨j,hp,cj⟩
      · rw [dot_eq]
        exact (supported _).mpr ⟨j,by omega,cj⟩
    obtain ⟨i,hi,_⟩ := (supported _).mp live
    obtain ⟨l,hl,_⟩ := (supported _).mp (dot_eq ▸ live)
    exact .inl ⟨⟨i,hi⟩,l,hl⟩

theorem feasible_iff (r : Row n) (rs : List (Row n)) (gs : List (Vec n))
    (basis : BasisCorrect rs gs) :
    (∃ x, SystemHolds (r :: rs) x ∧ ∀ i, 0 < x i) ↔
      ∀ i, ∃ j : Fin gs.length, 0 < gs.get j i ∧ enabled (r.pullback gs.get) j := by
  let p := r.pullback gs.get
  constructor
  · rintro ⟨x,sol,live⟩
    obtain ⟨c,rfl⟩ := (basis x).mp (fun s hs => sol s (List.mem_cons_of_mem r hs))
    have hc := (r.pullback_iff gs.get c).mpr (sol r List.mem_cons_self)
    intro i
    obtain ⟨t,ht,pos⟩ := List.sum_pos_iff_exists_pos_nat.mp (live i)
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨j,Nat.pos_of_mul_pos_right pos,maximal p c hc j (Nat.pos_of_mul_pos_left pos)⟩
  · intro all
    let c := witness p
    refine ⟨mix gs.get c,?_,?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | h
      · exact (s.pullback_iff _ _).mp (witness_holds p)
      · exact (basis _).mpr ⟨c,rfl⟩ s h
    · intro i
      obtain ⟨j,hg,hj⟩ := all i
      exact List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.mem_ofFn.mpr ⟨j,rfl⟩,Nat.mul_pos hg ((positive_iff_enabled p j).mpr hj)⟩

end Tamarin.ACBasis.PositiveWitness
