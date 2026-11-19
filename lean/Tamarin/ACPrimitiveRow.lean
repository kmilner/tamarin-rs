import TamarinRuntime.ACPlane

/-! A common divisor can be removed from a homogeneous row before searching
for its nonnegative integer solutions. The coordinates keep their positions. -/
namespace Tamarin.ACBasis

private theorem fold_gcd_dvd {xs : List Nat} {v : Nat} (mem : v ∈ xs) :
    xs.foldr Nat.gcd 0 ∣ v := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp mem with rfl | rest
    · exact Nat.gcd_dvd_left ..
    · exact Nat.dvd_trans (Nat.gcd_dvd_right ..) (ih rest)

theorem Row.divisor_pos {n} (r : Row n) : 0 < r.divisor := Nat.le_max_left 1 _

private theorem divisor_dvd {n} (r : Row n) {v : Nat} (mem : v ∈ List.ofFn r.pos ++ List.ofFn r.neg) :
    r.divisor ∣ v := by
  unfold Row.divisor
  generalize h : (List.ofFn r.pos ++ List.ofFn r.neg).foldr Nat.gcd 0 = d
  cases d with
  | zero => exact Nat.one_dvd _
  | succ k =>
    rw [Nat.max_eq_right (by omega),←h]
    exact fold_gcd_dvd mem

theorem Row.primitive_pos_scale {n} (r : Row n) (i : Fin n) :
    r.primitive.pos i * r.divisor = r.pos i :=
  Nat.div_mul_cancel (divisor_dvd r (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))

theorem Row.primitive_neg_scale {n} (r : Row n) (i : Fin n) :
    r.primitive.neg i * r.divisor = r.neg i :=
  Nat.div_mul_cancel (divisor_dvd r (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))

private theorem dot_scale {n} (a v x : Vec n) (d : Nat) (eq : ∀ i, a i * d = v i) :
    dot a x * d = dot v x := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    have tail := ih (fun i => a i.succ) (fun i => v i.succ) (fun i => x i.succ) (fun i => eq i.succ)
    simp only [dot,total,List.ofFn_succ,List.sum_cons,Nat.add_mul] at tail ⊢
    rw [tail,Nat.mul_right_comm,eq 0]

/-- The primitive row has exactly the same solutions, including when all its
coefficients vanish or its dimension is zero. -/
theorem Row.primitive_holds {n} (r : Row n) (x : Vec n) : r.primitive.Holds x ↔ r.Holds x := by
  unfold Row.Holds
  rw [← dot_scale _ _ x _ r.primitive_pos_scale,← dot_scale _ _ x _ r.primitive_neg_scale,
    Nat.mul_right_cancel_iff r.divisor_pos]

theorem Row.primitive_cap_le {n} (r : Row n) : r.primitive.cap ≤ r.cap := by
  apply (List.max_le_iff _).mpr
  intro v mem
  rcases List.mem_cons.mp mem with rfl | rows
  · exact List.le_max_of_mem (show 1 ∈ 1 :: (List.ofFn r.pos ++ List.ofFn r.neg) from List.mem_cons_self)
  rcases List.mem_append.mp rows with p | q
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp p
    exact Nat.le_trans (Nat.div_le_self ..) (List.le_max_of_mem (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp q
    exact Nat.le_trans (Nat.div_le_self ..) (List.le_max_of_mem (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))

end Tamarin.ACBasis
