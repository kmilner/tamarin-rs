import Tamarin.ACSeparation
import Tamarin.ACRationalCone
import TamarinRuntime.ACRationalProjection

/-! The integer Stiemke alternative for homogeneous AC feasibility. -/
namespace Tamarin.ACFeasibility.Alternative
open ACBasis
variable {n k : Nat}

private def coeff (p : Row n) (i : Fin n) : Int := (p.pos i : Int) - p.neg i
private abbrev weight (xs : List Int) (rs : List (Row n)) :=
  Separation.combination (xs.zip rs)

private theorem weight_cons (y : Int) (p : Row n) (ys) (rs) (i) :
    weight (y::ys) (p::rs) i = y * coeff p i + weight ys rs i := rfl

private theorem weight_scale (ys : List Int) (rs : List (Row n)) (a : Int) (i) :
    weight (ys.map (a*·)) rs i = a * weight ys rs i := by
  induction ys generalizing rs with
  | nil => simp [weight,Separation.combination]
  | cons y ys ih =>
    cases rs with
    | nil => simp [weight,Separation.combination]
    | cons r rs => rw [List.map_cons,weight_cons,weight_cons,ih]; grind

private theorem weight_zero (rs : List (Row n)) (i) :
    weight (List.replicate rs.length 0) rs i = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [List.replicate_succ,weight_cons,ih]

/-- The neutral singletons and opposite-sign pairs cover one mixed
equation. Each nonnegative combination of these rays satisfies it. -/
private def rays (p : Row n) : List (Vec n) :=
  ((RationalProjection.neutralIds p).map (spike · 1)) ++
    (RationalProjection.positiveIds p).flatMap fun i =>
      (RationalProjection.negativeIds p).map (Cone.pair p i)

private theorem ray_table (p : Row n) (v : Vec n) : v ∈ rays p ↔ Cone.Ray p v := by
  simp [rays,RationalProjection.neutralIds,RationalProjection.positiveIds,RationalProjection.negativeIds,Cone.Ray]
  grind

private theorem covered (p : Row n) (hp : ∃ i, 0 < p.pos i) (hn : ∃ i, 0 < p.neg i)
    (i : Fin n) : ∃ v ∈ rays p, 0 < v i := by
  obtain ⟨ip,hip⟩ := hp
  obtain ⟨im,him⟩ := hn
  by_cases pos : 0 < p.pos i
  · exact ⟨_,(ray_table ..).mpr (.inr ⟨i,im,pos,him,rfl⟩),by simp [Cone.pair,spike]; omega⟩
  by_cases neg : 0 < p.neg i
  · exact ⟨_,(ray_table ..).mpr (.inr ⟨ip,i,hip,neg,rfl⟩),by simp [Cone.pair,spike]; omega⟩
  exact ⟨_,(ray_table ..).mpr (.inl ⟨i,by omega,by omega,rfl⟩),by simp [spike]⟩

private theorem primal_lift (p : Row n) (rs : List (Row n))
    (hp : ∃ i, 0 < p.pos i) (hn : ∃ i, 0 < p.neg i)
    (sol : Feasible (rs.map (·.pullback (rays p).get))) : Feasible (p::rs) := by
  obtain ⟨x,sol,pos⟩ := sol
  refine ⟨mix (rays p).get x,?_,?_⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Cone.mix_holds r (rays r).get (fun j =>
        Cone.ray_holds r ((ray_table ..).mp (List.get_mem _ j))) x
    · exact (r.pullback_iff ..).mp (sol _ (List.mem_map_of_mem hr))
  · intro i
    obtain ⟨v,hv,hi⟩ := covered p hp hn i
    obtain ⟨j,eq⟩ := List.mem_iff_get.mp hv
    apply List.sum_pos_iff_exists_pos_nat.mpr
    have hi' : 0 < (rays p).get j i := by rw [eq]; exact hi
    exact ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,Nat.mul_pos hi' (pos j)⟩

private theorem coeff_pullback (r : Row n) (g : Fin k → Vec n) (t : Fin k) :
    coeff (r.pullback g) t = (dot r.pos (g t) : Int) - dot r.neg (g t) := by
  simp only [coeff,Row.pullback,Row.ofWeights]
  omega

private theorem dot_pair (v : Vec n) (p : Row n) (i j : Fin n) :
    dot v (Cone.pair p i j) = v i * p.neg j + v j * p.pos i := by
  unfold Cone.pair dot
  simp only [Nat.mul_add,total_add]
  change dot v (spike i _) + dot v (spike j _) = _
  rw [dot_spike,dot_spike]

private theorem weight_pullback (ys : List Int) (rs : List (Row n)) (g : Fin k → Vec n)
    (t : Fin k) (i j : Fin n) (u v : Int)
    (linear : ∀ r, coeff (r.pullback g) t = u * coeff r i + v * coeff r j) :
    weight ys (rs.map (·.pullback g)) t = u * weight ys rs i + v * weight ys rs j := by
  induction ys generalizing rs with
  | nil => simp [weight,Separation.combination]
  | cons y ys ih =>
    cases rs with
    | nil => simp [weight,Separation.combination]
    | cons r rs => rw [List.map_cons,weight_cons,weight_cons,weight_cons,ih,linear]; grind

private theorem weight_unit (ys : List Int) (rs : List (Row n)) (g : Fin k → Vec n)
    (t : Fin k) (i : Fin n) (eq : g t = spike i 1) :
    weight ys (rs.map (·.pullback g)) t = weight ys rs i := by
  have h := weight_pullback ys rs g t i i 1 0 (fun r => by
    rw [coeff_pullback,eq,dot_spike,dot_spike]; simp [coeff])
  simpa using h

private theorem weight_pair (ys : List Int) (rs : List (Row n)) (g : Fin k → Vec n)
    (t : Fin k) (p : Row n) (i j : Fin n) (eq : g t = Cone.pair p i j) :
    weight ys (rs.map (·.pullback g)) t =
      (p.neg j : Int)*weight ys rs i + (p.pos i : Int)*weight ys rs j := by
  apply weight_pullback
  intro r
  rw [coeff_pullback,eq,dot_pair,dot_pair]
  simp only [coeff,Int.natCast_add,Int.natCast_mul]
  grind

private theorem minimum_ratio {α : Type} (ks : List α) (value den : α → Int)
    (positive : ∀ i ∈ ks, 0 < den i) (live : ks ≠ []) :
    ∃ j ∈ ks, ∀ i ∈ ks, value j * den i ≤ value i * den j := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    by_cases empty : ks = []
    · subst ks; exact ⟨k,by simp,by simp⟩
    obtain ⟨j,hj,best⟩ := ih (fun i hi => positive i (List.mem_cons_of_mem _ hi)) empty
    by_cases before : value k * den j ≤ value j * den k
    · refine ⟨k,List.mem_cons_self,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact Int.le_refl _
      · apply Int.le_of_not_gt
        intro bad
        have h1 := Int.mul_le_mul_of_nonneg_right before (Int.le_of_lt (positive i (by simp [hi])))
        have h2 := Int.mul_le_mul_of_nonneg_right (best i hi) (Int.le_of_lt (positive k (by simp)))
        have h3 := Int.mul_lt_mul_of_pos_right bad (positive j (by simp [hj]))
        grind
    · refine ⟨j,List.mem_cons_of_mem _ hj,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · exact best i hi


/-- Lift a separator on the rays of a mixed row. Pick a positive
coordinate minimizing fᵢ/pᵢ. Subtracting this ratio times the equation
makes every coefficient nonnegative. Multiplication by the positive
pivot coefficient keeps both the denominator and the result integral. -/
private theorem lift_coefficients (p : Row n) (f : Fin n → Int)
    (hp : ∃ i, 0 < p.pos i)
    (neutral : ∀ i, p.pos i = 0 → p.neg i = 0 → 0 ≤ f i)
    (pairs : ∀ i j, 0 < p.pos i → 0 < p.neg j →
      0 ≤ (p.neg j : Int)*f i + (p.pos i : Int)*f j)
    (strict : (∃ i, p.pos i = 0 ∧ p.neg i = 0 ∧ 0 < f i) ∨
      ∃ i j, 0 < p.pos i ∧ 0 < p.neg j ∧
        0 < (p.neg j : Int)*f i + (p.pos i : Int)*f j) :
    ∃ z d : Int, (∀ i, 0 ≤ z * coeff p i + d*f i) ∧ ∃ i, 0 < z * coeff p i + d*f i := by
  let ids := RationalProjection.positiveIds p
  have mem (i : Fin n) : i ∈ ids ↔ 0 < p.pos i := by simp [ids,RationalProjection.positiveIds]
  obtain ⟨i,live⟩ := hp
  have used : ids ≠ [] := fun e => by simpa [e] using ((mem i).mpr live)
  obtain ⟨j,hj,best⟩ := minimum_ratio ids f (fun t => (p.pos t : Int))
    (fun t h => by exact_mod_cast (mem t).mp h) used
  have jp := (mem j).mp hj
  have den : 0 < (p.pos j : Int) := by exact_mod_cast jp
  let v (i : Fin n) := -f j * coeff p i + (p.pos j : Int)*f i
  have ok (i : Fin n) : 0 ≤ v i := by
    by_cases pos : 0 < p.pos i
    · have zn := (p.disjoint i).resolve_left (Nat.ne_of_gt pos)
      have lo := best i ((mem i).mpr pos)
      simp [v,coeff,zn]; grind
    by_cases neg : 0 < p.neg i
    · have zp := Nat.eq_zero_of_not_pos pos
      have lo := pairs j i jp neg
      simp [v,coeff,zp]; grind
    have zp := Nat.eq_zero_of_not_pos pos
    have zn := Nat.eq_zero_of_not_pos neg
    simpa [v,coeff,zp,zn] using (Int.mul_nonneg (Int.le_of_lt den) (neutral i zp zn))
  refine ⟨-f j,(p.pos j : Int),ok,?_⟩
  change ∃ i, 0 < v i
  by_cases yes : ∃ i, 0 < v i
  · exact yes
  have zero (i : Fin n) : v i = 0 := by
    have a := ok i
    have b : ¬ 0 < v i := fun h => yes ⟨i,h⟩
    omega
  rcases strict with ⟨i,zp,zn,h⟩ | ⟨i,k,pi,nk,h⟩
  · have eq := zero i
    have pos := Int.mul_pos den h
    simp [v,coeff,zp,zn] at eq
    omega
  · have zi := (p.disjoint i).resolve_left (Nat.ne_of_gt pi)
    have zk := (p.disjoint k).resolve_right (Nat.ne_of_gt nk)
    have eq : (p.neg k : Int) * v i + (p.pos i : Int) * v k = 0 := by rw [zero,zero]; simp
    have pos := Int.mul_pos den h
    simp only [v,coeff,zi,zk,Int.natCast_zero,Int.sub_zero,Int.zero_sub] at eq
    grind

private theorem dual_lift (p : Row n) (rs : List (Row n)) (ys : List Int)
    (hp : ∃ i, 0 < p.pos i)
    (cert : Separation.Certificate (rs.map (·.pullback (rays p).get)) ys) :
    ∃ zs, Separation.Certificate (p::rs) zs := by
  obtain ⟨len,nonneg,idx,positive⟩ := cert
  let f := weight ys rs
  have neutral (i : Fin n) (zp : p.pos i = 0) (zn : p.neg i = 0) : 0 ≤ f i := by
    have mem := (ray_table p _).mpr (.inl ⟨i,zp,zn,rfl⟩)
    obtain ⟨t,eq⟩ := List.mem_iff_get.mp mem
    change 0 ≤ weight ys rs i
    rw [← weight_unit ys rs _ t i eq]
    exact nonneg t
  have pairs (i j : Fin n) (pi : 0 < p.pos i) (nj : 0 < p.neg j) :
      0 ≤ (p.neg j : Int)*f i + (p.pos i : Int)*f j := by
    have mem := (ray_table p _).mpr (.inr ⟨i,j,pi,nj,rfl⟩)
    obtain ⟨t,eq⟩ := List.mem_iff_get.mp mem
    exact (weight_pair ys rs _ t p i j eq) ▸ nonneg t
  have strict : (∃ i, p.pos i = 0 ∧ p.neg i = 0 ∧ 0 < f i) ∨
      ∃ i j, 0 < p.pos i ∧ 0 < p.neg j ∧
        0 < (p.neg j : Int)*f i + (p.pos i : Int)*f j := by
    rcases (ray_table p _).mp (List.get_mem _ idx) with ⟨i,zp,zn,eq⟩ | ⟨i,j,pi,nj,eq⟩
    · refine .inl ⟨i,zp,zn,?_⟩
      change 0 < weight ys rs i
      rw [← weight_unit ys rs _ idx i eq]
      exact positive
    · exact .inr ⟨i,j,pi,nj,(weight_pair ys rs _ idx p i j eq) ▸ positive⟩
  obtain ⟨z,d,ok,i,gt⟩ := lift_coefficients p f hp neutral pairs strict
  refine ⟨z :: ys.map (d*·),by simpa using len,?_,i,?_⟩
  · intro t
    change 0 ≤ weight _ _ _
    rw [weight_cons,weight_scale]
    exact ok t
  · change 0 < weight _ _ _
    rw [weight_cons,weight_scale]
    exact gt

private theorem single_separator (p : Row n) (rs : List (Row n)) (z : Int)
    (ok : ∀ i, 0 ≤ z*coeff p i) (pos : ∃ i, 0 < z*coeff p i) :
    ∃ ys, Separation.Certificate (p::rs) ys := by
  obtain ⟨i,gt⟩ := pos
  refine ⟨z :: List.replicate rs.length 0,by simp,?_,i,?_⟩
  · intro t
    change 0 ≤ weight _ _ _
    simpa [weight_cons,weight_zero] using ok t
  · change 0 < weight _ _ _
    simpa [weight_cons,weight_zero] using gt

private theorem either_length (m : Nat) : ∀ {n} (rows : List (Row n)), rows.length = m →
    Feasible rows ∨ ∃ ys, Separation.Certificate rows ys := by
  induction m with
  | zero =>
    intro n rows len
    have eq : rows = [] := List.length_eq_zero_iff.mp len
    subst rows
    exact .inl ⟨fun _ => 1,by simp [SystemHolds],by simp⟩
  | succ m ih =>
    intro n rows len
    cases rows with
    | nil => contradiction
    | cons p rs =>
      have size : rs.length = m := by simpa using len
      by_cases hp : ∃ i, 0 < p.pos i
      · by_cases hn : ∃ i, 0 < p.neg i
        · rcases ih (rs.map (·.pullback (rays p).get)) (by simpa using size) with primal | ⟨ys,dual⟩
          · exact .inl (primal_lift p rs hp hn primal)
          · exact .inr (dual_lift p rs ys hp dual)
        · have zero (i : Fin n) : p.neg i = 0 := Nat.eq_zero_of_not_pos (fun pos => hn ⟨i,pos⟩)
          obtain ⟨i,gt⟩ := hp
          exact .inr (single_separator p rs 1 (by simp [coeff,zero]) ⟨i,by simpa [coeff,zero] using gt⟩)
      · have zp (i : Fin n) : p.pos i = 0 := Nat.eq_zero_of_not_pos (fun pos => hp ⟨i,pos⟩)
        by_cases hn : ∃ i, 0 < p.neg i
        · obtain ⟨i,gt⟩ := hn
          exact .inr (single_separator p rs (-1) (by simp [coeff,zp]) ⟨i,by simpa [coeff,zp] using gt⟩)
        · have zn (i : Fin n) : p.neg i = 0 := Nat.eq_zero_of_not_pos (fun pos => hn ⟨i,pos⟩)
          rcases ih rs size with ⟨x,sol,pos⟩ | ⟨ys,length,nonneg,i,gt⟩
          · refine .inl ⟨x,?_,pos⟩
            intro r hr
            rcases List.mem_cons.mp hr with rfl | mem
            · simp [Row.Holds,dot,zp,zn]
            · exact sol r mem
          · refine .inr ⟨0::ys,by simpa using length,?_,i,?_⟩
            · intro t
              change 0 ≤ weight _ _ _
              simpa [weight_cons] using nonneg t
            · change 0 < weight _ _ _
              simpa [weight_cons] using gt

/-- Every finite integer matrix has a positive natural primal solution or
an integer combination of its own rows that separates the positive orthant. -/
theorem primal_or_separator (rows : List (Row n)) :
    Feasible rows ∨ ∃ ys, Separation.Certificate rows ys := either_length rows.length rows rfl

/-- The two certificate types are exhaustive and mutually exclusive. -/
theorem separator_iff_infeasible (rows : List (Row n)) :
    (∃ ys, Separation.Certificate rows ys) ↔ ¬ Feasible rows := by
  constructor
  · rintro ⟨ys,cert⟩
    exact Separation.separates_refutes ((Separation.separates_iff ..).mpr cert)
  · intro no
    exact (primal_or_separator rows).resolve_left no

end Tamarin.ACFeasibility.Alternative
