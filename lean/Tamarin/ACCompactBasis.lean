import Tamarin.ACBasis

/-! Stable thinning of a coefficient search before projecting it into the
previous row basis. The result preserves the order of the reference answer. -/
namespace Tamarin.ACBasis

private def Below {n} (v w : Vec n) : Prop :=
  (∃ i, 0 < v i) ∧ (∀ i, v i ≤ w i) ∧ v ≠ w

private theorem below_trans {n} {a b c : Vec n} (ab : Below a b) (bc : Below b c) : Below a c :=
  ⟨ab.1, fun i => Nat.le_trans (ab.2.1 i) (bc.2.1 i), fun eq => ab.2.2
    (funext fun i => Nat.le_antisymm (ab.2.1 i) (eq ▸ bc.2.1 i))⟩

private theorem mix_positive {k n} (g : Fin k → Vec n) (live : ∀ j, ∃ i, 0 < g j i)
    (c : Vec k) (nz : ∃ j, 0 < c j) : ∃ i, 0 < mix g c i := by
  obtain ⟨j,hj⟩ := nz
  obtain ⟨i,hi⟩ := live j
  refine ⟨i,List.sum_pos_iff_exists_pos_nat.mpr ?_⟩
  exact ⟨g j i * c j, List.mem_ofFn.mpr ⟨j,rfl⟩, Nat.mul_pos hi hj⟩

private theorem mix_add' {k n} (g : Fin k → Vec n) (x y : Vec k) (i : Fin n) :
    mix g (fun j => x j + y j) i = mix g x i + mix g y i := by
  simp only [mix,dot,Nat.mul_add,total_add]

private theorem mix_below {k n} (g : Fin k → Vec n) (live : ∀ j, ∃ i, 0 < g j i)
    {c d : Vec k} (smaller : Below d c) : Below (mix g d) (mix g c) := by
  let diff := fun j => c j - d j
  have split : c = fun j => d j + diff j := by
    funext j
    exact (Nat.add_sub_of_le (smaller.2.1 j)).symm
  have pos : ∃ j, 0 < diff j := by
    apply Classical.byContradiction
    intro hn
    apply smaller.2.2
    funext j
    have h : ¬ 0 < diff j := fun hj => hn ⟨j,hj⟩
    have hj : c j = d j + diff j := congrFun split j
    omega
  obtain ⟨i,inc⟩ := mix_positive g live diff pos
  have val j : mix g c j = mix g d j + mix g diff j :=
    (congrArg (fun v => mix g v j) split).trans (mix_add' g d diff j)
  exact ⟨mix_positive g live d smaller.1, fun j => (val j) ▸ Nat.le_add_right ..,
    fun eq => by have := congrFun eq i; have := val i; omega⟩

/-- A removed coefficient has a retained, nonzero proper subvector. If every
previous generator is nonzero, its image is strictly dominated as well.
Even when several coefficients project to the same answer, every occurrence
of an answer that survives minimization is retained. -/
theorem minimize_lift_filter {k n} (g : Fin k → Vec n) (coeffs : List (Vec k))
    (keep : Vec k → Bool) (live : ∀ j, ∃ i, 0 < g j i)
    (covered : ∀ c ∈ coeffs, keep c = false →
      ∃ d ∈ coeffs, keep d = true ∧ (∃ j, 0 < d j) ∧ (∀ j, d j ≤ c j) ∧ d ≠ c) :
    minimize (lift g (coeffs.filter keep)) = minimize (lift g coeffs) := by
  have good c (hc : c ∈ coeffs) (drop : keep c = false) :
      ∃ d ∈ coeffs, keep d = true ∧ Below (mix g d) (mix g c) := by
    obtain ⟨d,hd,hk,small⟩ := covered c hc drop
    exact ⟨d,hd,hk,mix_below g live small⟩
  unfold minimize lift
  congr 1
  rw [List.filter_map,List.filter_map,List.filter_filter]
  apply congrArg (List.map (mix g))
  apply List.filter_congr
  intro c hc
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
    decide_eq_true_eq, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨pos,minimal⟩,_⟩
    refine ⟨pos,?_⟩
    rintro _ ⟨a,ha,rfl⟩ below
    cases hk : keep a with
    | true => exact minimal _ ⟨a,⟨ha,hk⟩,rfl⟩ below
    | false =>
      obtain ⟨d,hd,kd,bd⟩ := good a ha hk
      exact minimal _ ⟨d,⟨hd,kd⟩,rfl⟩ (below_trans bd below)
  · rintro ⟨pos,minimal⟩
    refine ⟨⟨pos,?_⟩,?_⟩
    · rintro _ ⟨a,⟨ha,_⟩,rfl⟩
      exact minimal _ ⟨a,ha,rfl⟩
    · cases hk : keep c with
      | true => rfl
      | false =>
        obtain ⟨d,hd,_,bd⟩ := good c hc hk
        exact False.elim (minimal _ ⟨d,hd,rfl⟩ bd)

end Tamarin.ACBasis
