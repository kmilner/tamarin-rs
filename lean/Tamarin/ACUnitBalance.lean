import TamarinRuntime.ACUnitBalance
import Tamarin.ACSparsePlane

namespace Tamarin.ACBasis.UnitBalance
variable {n : Nat}

private theorem enumerate_cons (r : Row n) (i : Fin n) (is : List (Fin n)) :
    enumerate r (i::is) = enumerate r is ++ block r i is := by
  simp [enumerate,enumerateWith,blocksWith]

private theorem pair_comm (i j : Fin n) : pair i j = pair j i := by
  funext k; simp [pair,Nat.add_comm]

/-- The coefficients returned for any collection of columns, regardless of
their numeric identifiers, are exactly neutral units and opposite pairs. -/
private theorem mem_enumerate (r : Row n) (is : List (Fin n)) (v : Vec n) :
    v ∈ enumerate r is ↔
      (∃ i ∈ is, r.pos i = 0 ∧ r.neg i = 0 ∧ v = spike i 1) ∨
      ∃ i ∈ is, ∃ j ∈ is, 0 < r.pos i ∧ 0 < r.neg j ∧ v = pair i j := by
  induction is with
  | nil => simp [enumerate,enumerateWith,blocksWith]
  | cons k ks ih =>
    rw [enumerate_cons,List.mem_append,ih]
    simp only [List.mem_cons,exists_eq_or_imp]
    by_cases p : 0 < r.pos k
    · have z := (r.disjoint k).resolve_left (Nat.ne_of_gt p)
      simp [block,blockWith,p,z,Nat.ne_of_gt p,List.mem_map,List.mem_filter]
      grind
    · have z := Nat.eq_zero_of_not_pos p
      by_cases q : 0 < r.neg k
      · simp [block,blockWith,z,q,Nat.ne_of_gt q,List.mem_map,List.mem_filter]
        grind [pair_comm]
      · simp [block,blockWith,z,Nat.eq_zero_of_not_pos q]
        grind

private abbrev Before (v w : Vec n) := List.ofFn v < List.ofFn w

private theorem first_diff (v w : Vec n) (i : Fin n) (equal : ∀ k, k < i → v k = w k)
    (lt : v i < w i) : Before v w := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [Before,List.ofFn_succ]
      exact List.Lex.rel lt
    | succ i =>
      have head := equal 0 (Nat.zero_lt_succ _)
      simp only [Before,List.ofFn_succ,head,List.cons_lt_cons_self]
      exact ih _ _ i (fun j h => equal j.succ (Fin.succ_lt_succ_iff.mpr h)) lt

private theorem pairs_sorted (i : Fin n) (xs : List (Fin n)) (h : xs.Pairwise (· < ·))
    (later : ∀ j ∈ xs, i < j) : (xs.reverse.map (pair i)).Pairwise Before := by
  rw [List.pairwise_map,List.pairwise_reverse]
  apply List.pairwise_iff_forall_sublist.mpr
  intro a b sub
  have order := List.pairwise_iff_forall_sublist.mp h sub
  have low := later a (sub.subset (by simp))
  apply first_diff _ _ a
  · intro k hk
    have ka : k ≠ a := Fin.ne_of_lt hk
    have kb : k ≠ b := Fin.ne_of_lt (Fin.lt_trans hk order)
    simp [pair,spike,ka,kb]
  · simp [pair,spike,Fin.ne_of_lt order,Ne.symm (Fin.ne_of_lt low)]

private theorem block_cases (r : Row n) (i : Fin n) (xs : List (Fin n)) {v : Vec n}
    (h : v ∈ block r i xs) : v = spike i 1 ∨ ∃ j ∈ xs, v = pair i j := by
  unfold block blockWith at h
  split at h
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    exact .inr ⟨j,(List.mem_filter.mp (List.mem_reverse.mp hj)).1,rfl⟩
  · split at h
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
      exact .inr ⟨j,(List.mem_filter.mp (List.mem_reverse.mp hj)).1,rfl⟩
    · exact .inl (List.mem_singleton.mp h)

private theorem enum_sorted (r : Row n) (xs : List (Fin n)) (ordered : xs.Pairwise (· < ·)) :
    (enumerate r xs).Pairwise Before := by
  induction xs with
  | nil => simp [enumerate,enumerateWith,blocksWith]
  | cons i xs ih =>
    obtain ⟨later,tail⟩ := List.pairwise_cons.mp ordered
    rw [enumerate_cons,List.pairwise_append]
    have blocks_ordered (p : Fin n → Bool) :
        ((xs.filter p).reverse.map (pair i)).Pairwise Before :=
      pairs_sorted i _ (tail.sublist List.filter_sublist) (fun j hj => later j (List.mem_filter.mp hj).1)
    refine ⟨ih tail,?_,?_⟩
    · unfold block blockWith
      split
      · exact blocks_ordered _
      · split
        · exact blocks_ordered _
        · simp
    · intro a ha b hb
      have early (k : Fin n) (hk : k ≤ i) : a k = 0 := by
        have diff (j) (hj : j ∈ xs) : k ≠ j := Fin.ne_of_lt (Fin.lt_of_le_of_lt hk (later j hj))
        rcases (mem_enumerate r xs a).mp ha with ⟨j,hj,_,_,rfl⟩ | ⟨j,hj,l,hl,_,_,rfl⟩
        · simp [spike,diff j hj]
        · simp [pair,spike,diff j hj,diff l hl]
      rcases block_cases r i xs hb with rfl | ⟨j,hj,rfl⟩
      · apply first_diff _ _ i
        · intro k hk; simp [early k (Fin.le_of_lt hk),spike,Fin.ne_of_lt hk]
        · simp [early i (Fin.le_refl i),spike]
      · apply first_diff _ _ i
        · intro k hk
          simp [early k (Fin.le_of_lt hk),pair,spike,Fin.ne_of_lt hk,Fin.ne_of_lt (Fin.lt_trans hk (later j hj))]
        · simp [early i (Fin.le_refl i),pair,spike,Fin.ne_of_lt (later j hj)]

private theorem mem_units (r : Row n) (v : Vec n) :
    v ∈ r.unitGenerators ↔
      (∃ i, r.pos i = 0 ∧ r.neg i = 0 ∧ v = spike i 1) ∨
      ∃ i j, 0 < r.pos i ∧ 0 < r.neg j ∧ v = pair i j := by
  simp [Row.unitGenerators,mem_enumerate]

private theorem dot_pair (p : Vec n) (i j : Fin n) : dot p (pair i j) = p i + p j := by
  calc
    _ = dot p (spike i 1) + dot p (spike j 1) := by simp only [dot,pair,Nat.mul_add,total_add]
    _ = _ := by simp [dot_spike]

private theorem in_reference (r : Row n) (uniform : r.equalMagnitude = true)
    {v : Vec n} (hv : v ∈ r.unitGenerators) : v ∈ r.generators := by
  apply (r.mem_generators v).mpr
  have cap : 1 ≤ r.cap := List.le_max_of_mem (show 1 ∈ 1 :: (List.ofFn r.pos ++ List.ofFn r.neg) from List.mem_cons_self)
  have bounds (i : Fin n) : 1 ≤ r.limits i := by
    unfold Row.limits; split <;> first | omega | split <;> omega
  have mag : ∀ i, (r.pos i = 0 ∨ r.pos i = r.cap) ∧ (r.neg i = 0 ∨ r.neg i = r.cap) := by
    simpa [Row.equalMagnitude] using uniform
  rcases (mem_units r v).mp hv with ⟨i,p,q,rfl⟩ | ⟨i,j,p,q,rfl⟩
  · refine ⟨fun k => ?_,by simp [Row.Holds,dot_spike,p,q],i,by simp [spike]⟩
    by_cases same : k = i <;> simp [spike,same,bounds]
  · have pi := (mag i).1.resolve_left (Nat.ne_of_gt p)
    have nj := (mag j).2.resolve_left (Nat.ne_of_gt q)
    have ni := (r.disjoint i).resolve_left (Nat.ne_of_gt p)
    have pj := (r.disjoint j).resolve_right (Nat.ne_of_gt q)
    have diff : i ≠ j := by rintro rfl; omega
    refine ⟨fun k => ?_,by simp [Row.Holds,dot_pair,pi,nj,ni,pj],i,by simp [pair,spike,diff]⟩
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [pair,spike]

private theorem dominated (r : Row n) {c : Vec n} (hc : c ∈ r.generators) :
    ∃ d ∈ r.unitGenerators, (∃ i, 0 < d i) ∧ ∀ i, d i ≤ c i := by
  obtain ⟨_,balance,k,ck⟩ := (r.mem_generators c).mp hc
  by_cases u : ∃ i, r.pos i = 0 ∧ r.neg i = 0 ∧ 0 < c i
  · obtain ⟨i,p,q,pos⟩ := u
    refine ⟨spike i 1,(mem_units ..).mpr (.inl ⟨i,p,q,rfl⟩),⟨i,by simp [spike]⟩,fun j => ?_⟩
    by_cases e : j = i <;> simp [spike,e]; omega
  · have hits (v : Vec n) : 0 < dot v c ↔ ∃ i, 0 < v i ∧ 0 < c i := by
      simp only [dot,total,List.sum_pos_iff_exists_pos_nat,List.mem_ofFn]
      constructor
      · rintro ⟨_,⟨i,rfl⟩,h⟩
        exact ⟨i,Nat.pos_of_mul_pos_right h,Nat.pos_of_mul_pos_left h⟩
      · rintro ⟨i,p,q⟩; exact ⟨_,⟨i,rfl⟩,Nat.mul_pos p q⟩
    have eq : dot r.pos c = dot r.neg c := balance
    have live : 0 < dot r.pos c := by
      by_cases pk : 0 < r.pos k
      · exact (hits _).mpr ⟨k,pk,ck⟩
      · rw [eq]
        have q : 0 < r.neg k := by
          apply Nat.pos_of_ne_zero; exact fun z => u ⟨k,Nat.eq_zero_of_not_pos pk,z,ck⟩
        exact (hits _).mpr ⟨k,q,ck⟩
    obtain ⟨i,pi,ci⟩ := (hits _).mp live
    obtain ⟨j,nj,cj⟩ := (hits _).mp (eq ▸ live)
    have diff : i ≠ j := by rintro rfl; have := r.disjoint i; omega
    refine ⟨pair i j,(mem_units ..).mpr (.inr ⟨i,j,pi,nj,rfl⟩),⟨i,by simp [pair,spike,diff]⟩,fun k => ?_⟩
    by_cases a : k = i <;> by_cases b : k = j <;> simp_all [pair,spike] <;> omega

private noncomputable def selected (r : Row n) (v : Vec n) : Bool := by
  classical exact decide (v ∈ r.unitGenerators)

private theorem filtered (r : Row n) (uniform : r.equalMagnitude = true) :
    r.unitGenerators = r.generators.filter (selected r) := by
  classical
  have direct : r.unitGenerators.Pairwise Before := enum_sorted _ _ (List.pairwise_lt_finRange n)
  have ref : (r.generators.filter (selected r)).Pairwise Before :=
    ((SparsePlane.box_sorted _ _).sublist List.filter_sublist).sublist List.filter_sublist
  have nodup {xs : List (Vec n)} (h : xs.Pairwise Before) : xs.Nodup :=
    h.imp fun {a b} ab eq => by subst b; exact List.lt_irrefl _ ab
  apply List.Perm.eq_of_pairwise (le := fun a b => List.ofFn a ≤ List.ofFn b)
  · intro a b _ _ ab ba
    have eq := List.le_antisymm ab ba
    funext i
    simpa [List.getElem?_ofFn,i.isLt] using congrArg (fun l : List Nat => l[i.val]?) eq
  · exact direct.imp (fun h => List.le_of_lt h)
  · exact ref.imp (fun h => List.le_of_lt h)
  · apply (List.perm_ext_iff_of_nodup (nodup direct) (nodup ref)).mpr
    intro v
    simp only [List.mem_filter,selected,decide_eq_true_eq]
    exact ⟨fun h => ⟨in_reference r uniform h,h⟩,And.right⟩

/-- Every omitted coefficient has a proper nonzero retained subvector.
Strict domination survives any live previous basis, even when generators
coincide. The whole ordered list after minimization is identical. -/
theorem minimize_lift {k n} (r : Row k) (uniform : r.equalMagnitude = true)
    (g : Fin k → Vec n) (live : ∀ j, ∃ i, 0 < g j i) :
    minimize (lift g r.unitGenerators) = minimize (lift g r.generators) := by
  classical
  rw [filtered r uniform]
  apply minimize_lift_filter _ _ _ live
  intro c hc removed
  obtain ⟨d,hd,pos,le⟩ := dominated r hc
  have kept : selected r d = true := by simp [selected,hd]
  exact ⟨d,in_reference r uniform hd,kept,pos,le,fun eq => by simp [eq,removed] at kept⟩

private theorem counts (r : Row n) (xs : List (Fin n)) :
    let neutral := (xs.filter fun i => r.neutralAt i).length
    let pos := (xs.filter fun i => 0 < r.pos i).length
    let neg := (xs.filter fun i => 0 < r.neg i).length
    (enumerate r xs).length = neutral + pos*neg ∧ neutral + pos + neg = xs.length := by
  dsimp only
  induction xs with
  | nil => simp [enumerate,enumerateWith,blocksWith]
  | cons i xs ih =>
    rw [enumerate_cons,List.length_append,ih.1]
    simp only [Row.neutralAt] at ih
    by_cases p : 0 < r.pos i
    · have z := (r.disjoint i).resolve_left (Nat.ne_of_gt p)
      simp [Row.neutralAt,block,blockWith,p,z,Nat.ne_of_gt p,Nat.succ_mul]
      omega
    · have z := Nat.eq_zero_of_not_pos p
      by_cases q : 0 < r.neg i
      · simp [Row.neutralAt,block,blockWith,z,q,Nat.ne_of_gt q,Nat.mul_succ]
        omega
      · simp [Row.neutralAt,block,blockWith,z,Nat.eq_zero_of_not_pos q]
        omega

theorem length_eq (r : Row n) :
    r.unitGenerators.length =
      ((List.finRange n).filter r.neutralAt).length +
      ((List.finRange n).filter fun i => 0 < r.pos i).length *
      ((List.finRange n).filter fun i => 0 < r.neg i).length :=
  (counts r _).1

private theorem rectangle (a b : Nat) : 4*a*b ≤ (a+b)*(a+b) := by
  rcases Nat.le_total a b with le | le
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    grind
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    grind

theorem length_le_1024 (r : Row n) (width : n ≤ 64) : r.unitGenerators.length ≤ 1024 := by
  obtain ⟨count,partition⟩ := counts r (List.finRange n)
  simp only [List.length_finRange] at partition
  let a := ((List.finRange n).filter fun i => 0 < r.pos i).length
  let b := ((List.finRange n).filter fun i => 0 < r.neg i).length
  let z := ((List.finRange n).filter r.neutralAt).length
  change z + a + b = n at partition
  rw [length_eq]
  change z + a*b ≤ 1024
  by_cases nonzero : 0 < b
  · have room : z+a+b ≤ 64 := by omega
    have area := Nat.le_trans (rectangle (z+a) b) (Nat.mul_le_mul room room)
    have push : z ≤ z*b := by simpa using (Nat.mul_le_mul_left z nonzero)
    rw [Nat.mul_assoc,Nat.add_mul] at area
    omega
  · simp [Nat.eq_zero_of_not_pos nonzero]; omega

theorem count_eq (r : Row n) : count r = r.unitGenerators.length := by
  obtain ⟨num,part⟩ := counts r (List.finRange n)
  simp only [List.length_finRange] at part
  change _ = (enumerate _ _).length
  rw [num]
  simp only [count,List.countP_eq_length_filter]
  omega

private theorem mapped {β} (r : Row n) (f : Vec n → β) (one : Fin n → β) (two : Fin n → Fin n → β)
    (fstEq : ∀ i, f (spike i 1) = one i) (sndEq : ∀ i j, f (pair i j) = two i j)
    (xs : List (Fin n)) :
    enumerateWith r one two xs = (enumerate r xs).map f := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [enumerate_cons,List.map_append]
    have step : enumerateWith r one two (i::xs) = enumerateWith r one two xs ++ blockWith r one two i xs := by
      simp [enumerateWith,blocksWith]
    rw [step,ih]
    apply congrArg (_ ++ ·)
    simp only [block,blockWith]
    split
    · simp [List.map_map,Function.comp_def,sndEq]
    · split
      · simp [List.map_map,Function.comp_def,sndEq]
      · simp [fstEq]

/-- A singleton contributes the previous generator directly; an opposite
pair contributes their pointwise sum. No dense coefficient dot product is
required for either projection. -/
theorem unitLift_eq {k n} (r : Row k) (basis : Vector (Vec n) k) :
    r.unitLift basis = lift (fun i => basis[i]) r.unitGenerators := by
  apply mapped
  · intro i; funext c; simp [mix,dot_spike]
  · intro i j; funext c; simp [mix,dot_pair]

private theorem antichain (r : Row n) {x y : Vec n} (hx : x ∈ r.unitGenerators)
    (hy : y ∈ r.unitGenerators) (small : ∀ i, x i ≤ y i) : x = y := by
  rcases (mem_units ..).mp hx with ⟨i,pi,ni,rfl⟩ | ⟨i,j,pi,nj,rfl⟩ <;>
    rcases (mem_units ..).mp hy with ⟨k,pk,nk,rfl⟩ | ⟨k,l,pk,nl,rfl⟩
  · have h := small i
    by_cases e : i = k <;> simp_all [spike]
  · have h := small i
    have ik : i ≠ k := fun eq => Nat.ne_of_gt pk (eq ▸ pi)
    have il : i ≠ l := fun eq => Nat.ne_of_gt nl (eq ▸ ni)
    simp [pair,spike,ik,il] at h
  · have h := small i
    have ik : i ≠ k := fun eq => Nat.ne_of_gt pi (eq ▸ pk)
    simp [pair,spike,ik] at h
  · have hi := small i
    have hj := small j
    have il : i ≠ l := by rintro rfl; have := r.disjoint i; omega
    have jk : j ≠ k := by rintro rfl; have := r.disjoint j; omega
    have ik : i = k := by apply Classical.byContradiction; intro e; simp [pair,spike,e,il] at hi
    have jl : j = l := by apply Classical.byContradiction; intro e; simp [pair,spike,e,jk] at hj
    rw [ik,jl]

private theorem mix_at {n k} (basis : Vector (Vec n) k) {j : Fin k} {c : Fin n}
    (only : ∀ y : Fin k, j ≠ y → basis[y] c = 0) (v : Vec k) :
    mix (fun i => basis[i]) v c = basis[j] c * v j := by
  have coords : (fun i : Fin k => basis[i] c) = spike j (basis[j] c) := by
    funext i
    by_cases e : i = j
    · subst i; simp [spike]
    · simp [spike,e,only i (Ne.symm e)]
  unfold mix
  rw [coords]
  calc
    _ = dot v (spike j (basis[j] c)) := by simp only [dot,Nat.mul_comm]
    _ = _ := by simp [dot_spike,Nat.mul_comm]

/-- A private coordinate is a positive observation belonging to exactly one
old generator. It witnesses order reflection regardless of overlap elsewhere. -/
theorem reflects {k n} (basis : Vector (Vec n) k) (apart : separates basis = true) {a b : Vec k}
    (le : ∀ c, mix (fun j => basis[j]) a c ≤ mix (fun j => basis[j]) b c) : ∀ j, a j ≤ b j := by
  have unique := of_decide_eq_true (Bool.and_eq_true_iff.mp apart).2
  intro j
  obtain ⟨c,pos,only⟩ := unique j
  have witness := le c
  simp only [mix_at basis only] at witness
  exact Nat.le_of_mul_le_mul_left witness pos

private theorem erase_eq {α} [BEq α] [LawfulBEq α] (xs : List α) (nd : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.eraseDups_cons,List.filter_eq_self.mpr,ih nd.tail]
    intro y hy
    by_cases e : y = x
    · exact ((List.nodup_cons.mp nd).1 (e ▸ hy)).elim
    · simp [e]

theorem minimize_unitLift {k n} (r : Row k) (basis : Vector (Vec n) k) (apart : separates basis = true) :
    minimize (r.unitLift basis) = r.unitLift basis := by
  let combine := mix (fun i : Fin k => basis[i])
  have injective : Function.Injective combine := by
    intro a b eq
    funext j
    exact Nat.le_antisymm (reflects basis apart (fun c => Nat.le_of_eq (congrFun eq c)) j)
      (reflects basis apart (fun c => Nat.le_of_eq (congrFun eq c).symm) j)
  have distinct : r.unitGenerators.Nodup :=
    (enum_sorted r _ (List.pairwise_lt_finRange k)).imp fun {a b} ab eq => by subst b; exact List.lt_irrefl _ ab
  have nd : (r.unitLift basis).Nodup := by
    rw [unitLift_eq,lift]
    apply List.pairwise_map.mpr
    exact distinct.imp fun ne eq => ne (injective eq)
  unfold minimize
  rw [List.filter_eq_self.mpr,erase_eq _ nd]
  intro x hx
  rw [unitLift_eq,lift] at hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  have vn : ∃ i, 0 < v i := by
    rcases (mem_units ..).mp hv with ⟨i,_,_,rfl⟩ | ⟨i,j,_,_,rfl⟩
    · exact ⟨i,by simp [spike]⟩
    · exact ⟨i,by simp [pair,spike]; omega⟩
  obtain ⟨i,vi⟩ := vn
  obtain ⟨c,positive,only⟩ := (of_decide_eq_true (Bool.and_eq_true_iff.mp apart).2) i
  have pos : 0 < mix (fun j => basis[j]) v c := by rw [mix_at basis only v]; exact Nat.mul_pos positive vi
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.any_eq_false]
  refine ⟨⟨c,pos⟩,?_⟩
  intro y hy bad
  rw [unitLift_eq,lift] at hy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hy
  obtain ⟨_,le,neq⟩ := bad
  exact neq (congrArg combine (antichain r hu hv (reflects basis apart le)))

/-- Decide size before constructing any lifted candidate. This guard can
be used precisely when the next stage requires a bounded basis. -/
theorem minimized_length {k n} (r : Row k) (basis : Vector (Vec n) k) (apart : separates basis = true) :
    (minimize (r.unitLift basis)).length = count r := by
  rw [minimize_unitLift r basis apart,unitLift_eq,lift,List.length_map,count_eq]

end Tamarin.ACBasis.UnitBalance
