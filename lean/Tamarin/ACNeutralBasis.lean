import Tamarin.ACCompactBasis
import Tamarin.ACCompactPlane

/-! A row with no coefficients on one side can retain exactly the previous
generators whose coefficient columns are neutral. This computes their order
in the reference lexicographic coefficient box as well as their membership. -/
namespace Tamarin.ACBasis

private def zvec (n : Nat) : Vec n := fun _ => 0
private def unit {n} (i : Fin n) := spike i 1

private theorem total_cases {n} (h : Nat) (v : Vec n) : total (Fin.cases h v) = h + total v := by
  simp [total,List.ofFn_succ]

private theorem unit_succ {n} (j : Fin n) : Fin.cases 0 (unit j) = unit j.succ := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp [unit,spike,Ne.symm (Fin.succ_ne_zero _)]

private theorem unit_first {n} : Fin.cases 1 (zvec n) = unit (0 : Fin (n+1)) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp [unit,spike,zvec,Fin.succ_ne_zero]

private theorem zvec_cons {n} : Fin.cases 0 (zvec n) = zvec (n+1) := by
  funext i; refine Fin.cases rfl (fun _ => rfl) i

private theorem binary_layers (n : Nat) :
    ((box n fun _ => 1).filter fun v => total v == 0) = [zvec n] ∧
    ((box n fun _ => 1).filter fun v => total v == 1) = (List.finRange n).reverse.map unit := by
  induction n with
  | zero =>
    have zero : (Fin.elim0 : Vec 0) = zvec 0 := funext fun i => Fin.elim0 i
    simp [box,total,zero]
  | succ n ih =>
    let b := box n (fun _ => 1)
    let put (h : Nat) (t : Vec n) : Vec (n+1) := Fin.cases h t
    have split : box (n+1) (fun _ => 1) =
        b.map (put 0) ++ b.map (put 1) := by simp [box,b,put,List.range_succ]
    have left (m : Nat) : ((b.map (put 0)).filter fun v => total v == m) =
        (b.filter fun v => total v == m).map (put 0) := by
      simp [List.filter_map,Function.comp_def,put,total_cases]
    have right (m : Nat) : ((b.map (put 1)).filter fun v => total v == m+1) =
        (b.filter fun v => total v == m).map (put 1) := by
      simp [List.filter_map,Function.comp_def,put,total_cases]
      apply congrArg (List.map _); apply List.filter_congr; intro v _
      apply Bool.eq_iff_iff.mpr; simp; omega
    have none : ((b.map (put 1)).filter fun v => total v == 0) = [] := by
      simp [List.filter_map,Function.comp_def,put,total_cases]
    obtain ⟨hz,hu⟩ := ih
    change (b.filter _) = _ at hz hu
    constructor
    · rw [split,List.filter_append,left,none,hz]; simp [put,zvec_cons]
    · rw [split,List.filter_append,left,right 0,hu,hz,List.finRange_succ,List.reverse_cons,
          List.map_append,List.map_map,←List.map_reverse,List.map_map]
      simp [Function.comp_def,put,unit_succ,unit_first]

private theorem coord_le_total {n} (v : Vec n) (i : Fin n) : v i ≤ total v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    change v i ≤ (List.ofFn v).sum
    rw [List.ofFn_succ,List.sum_cons]
    exact Fin.cases (by omega) (fun j => Nat.le_trans (ih (fun k => v k.succ) j) (Nat.le_add_left ..)) i

private theorem limits_positive {n} (p : Row n) (i : Fin n) : 1 ≤ p.limits i := by
  have pos : 1 ≤ p.cap := List.le_max_of_mem (show 1 ∈ 1 :: (List.ofFn p.pos ++ List.ofFn p.neg) from List.mem_cons_self)
  unfold Row.limits; split <;> first | omega | split <;> omega

private theorem box_units {n} (p : Row n) :
    ((box n p.limits).filter fun v => total v == 1) = (List.finRange n).reverse.map unit := by
  rw [←(binary_layers n).2]
  have limits : (fun i => min (p.limits i) 1) = fun _ => 1 := funext fun i => Nat.min_eq_right (limits_positive p i)
  rw [←limits,box_cap,List.filter_filter]
  apply List.filter_congr
  intro v _
  by_cases eq : total v = 1
  · have small : ∀ i, v i ≤ 1 := fun i => eq ▸ coord_le_total v i
    simp [eq,small]
  · simp [eq]

private theorem unit_total {n} (i : Fin n) : total (unit i) = 1 := by
  have eq := dot_spike (fun _ : Fin n => 1) i 1
  simpa [dot,unit] using eq

private def neutralCol {n} (p : Row n) (i : Fin n) : Bool := p.pos i == 0 && p.neg i == 0

private theorem selected_units {n} (p : Row n) :
    (p.generators.filter fun v => total v == 1) =
      ((List.finRange n).reverse.filter (neutralCol p)).map unit := by
  let test := fun v => dot p.pos v == dot p.neg v && (List.ofFn v).any (0 < ·)
  change (((box n p.limits).filter test).filter _) = _
  have commute : (((box n p.limits).filter test).filter fun v => total v == 1) =
      (((box n p.limits).filter fun v => total v == 1).filter test) := by
    simp only [List.filter_filter]; simp only [Bool.and_comm]
  rw [commute,box_units,List.filter_map]
  apply congrArg (List.map _)
  apply List.filter_congr; intro i _
  have yes : (List.ofFn (unit i)).any (0 < ·) := List.any_eq_true.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [unit,spike]⟩
  change (dot p.pos (unit i) == dot p.neg (unit i) && _) = _
  rw [yes,Bool.and_true]
  simp only [unit,dot_spike,Nat.mul_one,neutralCol]
  rcases p.disjoint i with h|h <;> simp [h,BEq.comm]

private theorem zero_dot {n} (a c : Vec n) (h : ∀ i, a i = 0) : dot a c = 0 := by
  simp [dot,total,List.sum_eq_zero_iff_forall_eq_nat,h]

/-- Every coefficient used by a solution of a one-sided homogeneous row
belongs to a neutral column. -/
theorem Row.neutral_of_active {n} (p : Row n) (c : Vec n)
    (sided : (∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)) (holds : p.Holds c)
    {i} (pos : 0 < c i) : p.pos i = 0 ∧ p.neg i = 0 := by
  have factor (a : Vec n) (hz : dot a c = 0) : a i = 0 := by
    have eq := List.sum_eq_zero_iff_forall_eq_nat.mp hz _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact (Nat.mul_eq_zero.mp eq).resolve_right (by omega)
  rcases sided with h|h
  · exact ⟨h i,factor _ (holds.symm.trans (zero_dot _ _ h))⟩
  · exact ⟨factor _ (holds.trans (zero_dot _ _ h)),h i⟩

private theorem erase_nodup {α} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => exact .nil
  | cons x xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups],erase_nodup _⟩
termination_by xs.length
decreasing_by have := List.length_filter_le (fun y => !y == x) xs; simp; omega

private theorem erase_id {α} [DecidableEq α] (xs : List α) (nd : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.eraseDups_cons,List.filter_eq_self.mpr,ih nd.tail]
    intro y hy; by_cases eq : y = x
    · exact ((List.nodup_cons.mp nd).1 (eq ▸ hy)).elim
    · simp [eq]

private theorem generate_distinct {n} (rs : List (Row n)) : (generate rs).Nodup := by
  cases rs <;> apply erase_nodup

private theorem minimize_subset {n} (rs : List (Row n)) (xs : List (Vec n))
    (within : xs ⊆ generate rs) (nd : xs.Nodup) : minimize xs = xs := by
  unfold minimize
  rw [List.filter_eq_self.mpr,erase_id _ nd]
  intro x hx
  have minimal := (mem_generate rs x).mp (within hx)
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.any_eq_false]
  refine ⟨minimal.2.1,?_⟩
  intro y hy
  rintro ⟨live,le,ne⟩
  exact ne (minimal.2.2 y ((mem_generate rs y).mp (within hy)).1 live le)

private theorem map_finRange_get {α} (xs : List α) : (List.finRange xs.length).map xs.get = xs := by
  simp [List.finRange,List.map_ofFn,Function.comp_def,List.get_eq_getElem]

/-- The previous Hilbert basis is an ordered antichain. For a one-sided
row only the neutral previous generators survive. In the reference box
the first two unit vectors visited use the last and penultimate coordinates. -/
theorem neutral_basis_ordered {n} (rs : List (Row n)) (p : Row (generate rs).length)
    (sided : (∀ i, p.pos i = 0) ∨ (∀ i, p.neg i = 0)) :
    minimize (lift (generate rs).get p.generators) =
      ((List.finRange (generate rs).length).reverse.filter (fun i => p.pos i == 0 && p.neg i == 0)).map (generate rs).get := by
  let prev := generate rs
  let keep := fun c : Vec prev.length => total c == 1
  have live (j : Fin prev.length) := ((mem_generate rs _).mp (List.get_mem prev j)).2.1
  have thin := minimize_lift_filter prev.get p.generators keep live
  have covered (c : Vec prev.length) (mem : c ∈ p.generators) (drop : keep c = false) :
      ∃ d ∈ p.generators, keep d = true ∧ (∃ j, 0 < d j) ∧ (∀ j, d j ≤ c j) ∧ d ≠ c := by
    obtain ⟨_,hc,j,hj⟩ := (p.mem_generators c).mp mem
    obtain ⟨left,right⟩ := p.neutral_of_active c sided hc hj
    have nz : ∃ i, 0 < unit j i := ⟨j,by simp [unit,spike]⟩
    have le (i) : unit j i ≤ c i := by
      by_cases eq : i = j
      · subst i; simp [unit,spike]; omega
      · simp [unit,spike,eq]
    have small (i) : unit j i ≤ p.limits i := by
      have h := limits_positive p i
      by_cases e : i = j
      · subst i; simpa [unit,spike] using h
      · simp [unit,spike,e]
    have good : keep (unit j) = true := by simp [keep,unit_total]
    exact ⟨unit j,(p.mem_generators _).mpr ⟨small,by simp [Row.Holds,unit,dot_spike,left,right],nz⟩,
      good,nz,le,fun eq => by rw [eq,drop] at good; contradiction⟩
  change minimize (lift prev.get p.generators) = _
  rw [←thin covered]
  change minimize (lift prev.get (p.generators.filter fun v => total v == 1)) = _
  rw [selected_units,lift,List.map_map]
  have mix_unit (i : Fin prev.length) : mix prev.get (unit i) = prev.get i := by
    funext j; simp [mix,unit,dot_spike]
  simp only [Function.comp_def,mix_unit]
  let idx := (List.finRange prev.length).reverse.filter (neutralCol p)
  change minimize (idx.map prev.get) = idx.map prev.get
  have sub : (idx.map prev.get).Sublist prev.reverse := by
    have h := List.filter_sublist (p := neutralCol p) (l := (List.finRange prev.length).reverse)
    simpa only [idx,List.map_reverse,map_finRange_get] using h.map prev.get
  apply minimize_subset rs _ (fun _ h => List.mem_reverse.mp (sub.subset h))
  exact (List.pairwise_reverse.mpr ((generate_distinct rs).imp (fun h => Ne.symm h))).sublist sub

end Tamarin.ACBasis
