import TamarinRuntime.ACRationalProjection
import Tamarin.ACRationalCone

namespace Tamarin.ACBasis.RationalProjection
open Homogeneous
variable {n k : Nat}

private theorem cached_eq (p : Row k) : cached p = p := by
  cases p; simp [cached]; exact ⟨funext fun i => by simp [coordinates],funext fun i => by simp [coordinates]⟩

private theorem lookup (gs : List (Vec n)) :
    (fun j : Fin gs.length => gs.toArray[j.val]'(by simp)) = gs.get := by
  funext j; simp [List.get_eq_getElem]

private theorem mix_unit (g : Fin k → Vec n) (i : Fin k) : mix g (spike i 1) = g i := by
  funext t; simp [mix,dot_spike]

private theorem mix_pair (g : Fin k → Vec n) (p : Row k) (i j : Fin k) :
    mix g (Cone.pair p i j) = combine g p i j := by
  funext t
  unfold mix Cone.pair dot combine
  simp only [Nat.mul_add,total_add]
  change dot _ (spike i _) + dot _ (spike j _) = _
  rw [dot_spike,dot_spike]
  ac_rfl

private def rays (p : Row k) :=
  (neutralIds p).map (spike · 1) ++ (positiveIds p).flatMap fun i =>
    (negativeIds p).map (Cone.pair p i)

private theorem ray_table (p : Row k) (x : Vec k) : x ∈ rays p ↔ Cone.Ray p x := by
  simp [rays,neutralIds,positiveIds,negativeIds,Cone.Ray]
  grind

private theorem images_lift (g : Fin k → Vec n) (p : Row k) :
    images g p (neutralIds p) (positiveIds p) (negativeIds p) = lift g (rays p) := by
  simp [images,lift,rays,List.map_flatMap,List.map_map,Function.comp_def,mix_unit,mix_pair]

private theorem gcd_dvd {xs : List Nat} {a : Nat} (h : a ∈ xs) : xs.foldr Nat.gcd 0 ∣ a := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|mem
    · exact Nat.gcd_dvd_left ..
    · exact Nat.dvd_trans (Nat.gcd_dvd_right ..) (ih mem)

private theorem primitive_scale (x : Vec n) : ∃ d, 0 < d ∧
    Cone.scale d (coordinates (primitive x)) = x := by
  let v := Vector.ofFn x
  let d := max 1 (v.toList.foldr Nat.gcd 0)
  refine ⟨d,Nat.le_max_left 1 _,?_⟩
  funext i
  by_cases h : d = 1
  · simp [Cone.scale,primitive,coordinates,v,d] at h ⊢
    simp [h]
  · have g : d = v.toList.foldr Nat.gcd 0 := by dsimp [d] at h ⊢; omega
    have m : x i ∈ v.toList := by simp [v]
    have dvd := g ▸ gcd_dvd m
    change d * coordinates (if d == 1 then v else v.map (· / d)) i = x i
    simp [h,coordinates,v]
    exact (Nat.mul_comm ..).trans (Nat.div_mul_cancel dvd)

private theorem compact_correct (rs : List (Row n)) (xs : List (Vec n)) (src : Cone.ScaleCorrect rs xs) :
    Cone.ScaleCorrect rs (compact xs) where
  sound := by
    rintro _ ⟨c,rfl⟩ r hr
    apply Cone.mix_holds r _ _ c
    intro i
    have mem := List.get_mem (compact xs) i
    simp only [compact,List.mem_map,List.mem_eraseDups] at mem
    obtain ⟨_,⟨x,hx,rfl⟩,eq⟩ := mem
    change coordinates (primitive x) = (compact xs).get i at eq
    rw [←eq]
    obtain ⟨d,hd,ex⟩ := primitive_scale x
    have holds := src.sound x (Cone.gen_member hx) r hr
    rw [←ex] at holds
    unfold Row.Holds at holds ⊢
    rw [Cone.dot_scale,Cone.dot_scale] at holds
    exact Nat.mul_left_cancel hd holds
  complete := by
    intro x hx
    obtain ⟨a,ha,c,hc⟩ := src.complete x hx
    refine ⟨a,ha,?_⟩
    rw [←hc]
    have same (i : Fin xs.length) : Generates (compact xs) (xs.get i) := by
      obtain ⟨d,_,eq⟩ := primitive_scale (xs.get i)
      rw [←eq]
      apply Cone.gen_scale
      apply Cone.gen_member
      simp only [compact,List.mem_map,List.mem_eraseDups]
      exact ⟨_,⟨_,List.get_mem xs i,rfl⟩,rfl⟩
    have sum := Cone.gen_sum (fun i => Cone.scale (c i) (xs.get i)) (fun i => Cone.gen_scale _ (same i))
    apply Eq.subst (motive := Generates (compact xs)) ?_ sum
    funext t; unfold mix dot Cone.scale; congr 1; funext i; ac_rfl

private theorem project_spec (r : Row n) (gs out : List (Vec n)) (run : project r gs = some out) :
    out = compact (lift gs.get (rays (r.pullback gs.get))) := by
  simp only [project,lookup,cached_eq,Option.bind_eq_bind,Option.bind_eq_some_iff] at run
  obtain ⟨_,_,_,_,_,_,eq⟩ := run
  exact (Option.some.inj eq).symm.trans (congrArg compact (images_lift ..))

theorem basis_correct (rs : List (Row n)) (gs : List (Vec n)) (run : basis rs = some gs) :
    Cone.ScaleCorrect rs gs := by
  induction rs generalizing gs with
  | nil =>
    simp only [basis] at run; split at run
    · cases run; exact Cone.units_correct n
    · contradiction
  | cons r rs ih =>
    obtain ⟨prev,hp,h⟩ := Option.bind_eq_some_iff.mp run
    rw [project_spec r prev gs h]
    exact compact_correct _ _ (Cone.lift_correct _ _ _ (ih prev hp) _
      (Cone.row_correct _ _ (ray_table _)))

/-- Input-only upper bounds. These depend on dimensions and row coefficients, not
on which ray family the executable selects or which subsets it examines. -/
def sizes {n} : List (Row n) → Nat × Nat
  | [] => (n,1)
  | r :: rs =>
    let (k,m) := sizes rs
    let weight := n * (r.cap * m)
    (k + k*k, max m (2 * (weight * m)))

def Within {n} : List (Row n) → Prop
  | [] => n ≤ 32
  | r :: rs => Within rs ∧ (sizes (r :: rs)).1 ≤ 256 ∧
    n * (r.cap * (sizes rs).2) < 2^128 ∧ (sizes (r :: rs)).2 < 2^128

private theorem len_erase {α} [BEq α] (xs : List α) : xs.eraseDups.length ≤ xs.length := by
  induction h : xs.length using Nat.strongRecOn generalizing xs with
  | ind k ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [←h,List.eraseDups_cons,List.length_cons,List.length_cons]
      apply Nat.succ_le_succ
      apply Nat.le_trans (ih _ _ _ rfl) (List.length_filter_le ..)
      have := List.length_filter_le (fun a => !(a == x)) xs
      simp at h; omega

private theorem short (v : Vector Nat n) (x : Vec n) (e : primitive x = v) (i : Fin n) :
    coordinates v i ≤ x i := by
  obtain ⟨d,hd,eq⟩ := primitive_scale x
  rw [←e]; have h := congrFun eq i
  change d * coordinates (primitive x) i = x i at h
  rw [←h]
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (coordinates (primitive x) i) hd

private theorem dot_bound (a b : Vec n) (A B : Nat) (ah : ∀ i, a i ≤ A) (bh : ∀ i, b i ≤ B) :
    dot a b ≤ n * (A*B) := by
  induction n with
  | zero => simp [dot,total]
  | succ n ih =>
    have tail := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => ah i.succ) (fun i => bh i.succ)
    simpa only [dot,total,List.ofFn_succ,List.sum_cons,Nat.succ_mul,Nat.add_comm] using
      Nat.add_le_add (Nat.mul_le_mul (ah 0) (bh 0)) tail

private theorem images_length (g : Fin k → Vec n) (p : Row k) (zs ps ns : List (Fin k)) :
    (images g p zs ps ns).length = zs.length + ps.length * ns.length := by
  simp only [images,List.length_append,List.length_map,Nat.add_right_inj]
  induction ps with
  | nil => simp
  | cons i ps ih => simp [ih,Nat.succ_mul,Nat.add_comm]

theorem basis_within (rs : List (Row n)) (domain : Within rs) :
    ∃ gs, basis rs = some gs ∧ gs.length ≤ (sizes rs).1 ∧ ∀ x ∈ gs, ∀ i, x i ≤ (sizes rs).2 := by
  induction rs with
  | nil =>
    refine ⟨units n,by simpa [basis,Within] using domain,by simp [units,sizes],?_⟩
    intro x hm t
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    simp [spike,sizes]; split <;> decide
  | cons r rs ih =>
    obtain ⟨within,count,weights,coeff⟩ := domain
    obtain ⟨gs,run,lg,mg⟩ := ih within
    let p := r.pullback gs.get
    let zs := neutralIds p
    let ps := positiveIds p
    let ns := negativeIds p
    let raw := images gs.get p zs ps ns
    let out := compact raw
    let m := (sizes rs).2
    let W := n * (r.cap * m)
    have bound_count (xs : List (Fin gs.length)) (h : xs.length ≤ gs.length) : xs.length ≤ (sizes rs).1 :=
      Nat.le_trans h lg
    have len_filter (test : Fin gs.length → Bool) :
        ((List.finRange _).filter test).length ≤ (sizes rs).1 :=
      bound_count _ (by simpa using List.length_filter_le test (List.finRange gs.length))
    have l : zs.length + ps.length*ns.length ≤ (sizes (r :: rs)).1 :=
      Nat.add_le_add (len_filter _) (Nat.mul_le_mul (len_filter _) (len_filter _))
    have orig (j : Fin gs.length) t := mg _ (List.get_mem _ j) t
    have limits (j : Fin gs.length) : p.pos j ≤ W ∧ p.neg j ≤ W := by
      have ap (i : Fin n) : r.pos i ≤ r.cap := List.le_max_of_mem (by simp [List.mem_ofFn])
      have an (i : Fin n) : r.neg i ≤ r.cap := List.le_max_of_mem (by simp [List.mem_ofFn])
      exact ⟨Nat.le_trans (Nat.sub_le ..) (dot_bound r.pos _ r.cap m ap (orig j)),
        Nat.le_trans (Nat.sub_le ..) (dot_bound r.neg _ r.cap m an (orig j))⟩
    have raw_bound (x) (hm : x ∈ raw) t : x t ≤ (sizes (r :: rs)).2 := by
      change x ∈ images _ _ _ _ _ at hm
      simp only [images,List.mem_append,List.mem_map,List.mem_flatMap] at hm
      rcases hm with ⟨j,_,rfl⟩|⟨i,_,j,_,rfl⟩
      · exact Nat.le_trans (orig j t) (Nat.le_max_left ..)
      · apply Nat.le_trans _ (Nat.le_max_right ..)
        change _ ≤ 2*(W*m)
        rw [Nat.two_mul]
        exact Nat.add_le_add (Nat.mul_le_mul (limits j).2 (orig i t)) (Nat.mul_le_mul (limits i).1 (orig j t))
    have coords (x) (mem : x ∈ out) t : x t ≤ (sizes (r :: rs)).2 := by
      change x ∈ compact raw at mem
      simp only [compact,List.mem_map,List.mem_eraseDups] at mem
      obtain ⟨v,⟨a,ha,eq⟩,rfl⟩ := mem
      exact Nat.le_trans (short v a eq t) (raw_bound a ha t)
    refine ⟨out,?_,?_,coords⟩
    · rw [basis,run]; change project r gs = some out
      have lc : zs.length + ps.length*ns.length ≤ maxRays := Nat.le_trans l count
      have wc i : p.pos i ≤ maxCoeff ∧ p.neg i ≤ maxCoeff := by
        have h := limits i; change W < 2^128 at weights; unfold maxCoeff; omega
      have mc : (out.all fun v => (List.finRange n).all fun t => v t ≤ maxCoeff) = true := by
        simp only [List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq]
        intro x hx t; have he := coords x hx t; unfold maxCoeff; omega
      simp only [project,lookup,cached_eq]
      change (do {guard (zs.length + ps.length * ns.length ≤ maxRays); guard (∀ i, p.pos i ≤ maxCoeff ∧ p.neg i ≤ maxCoeff); guard (out.all fun v => (List.finRange n).all fun t => v t ≤ maxCoeff); pure out}) = some out
      simp [lc,wc,mc,guard]
    · change (List.map coordinates (List.map primitive raw).eraseDups).length ≤ _
      rw [List.length_map]
      apply Nat.le_trans (len_erase _)
      simpa [raw,images_length] using l

end Tamarin.ACBasis.RationalProjection
