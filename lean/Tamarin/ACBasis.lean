import Tamarin.ACSystem
import TamarinRuntime.ACBasis

/-! Finite generation of nonnegative homogeneous integer kernels. All bounds
and coefficients are natural numbers. The enumeration is a reference, and its
completeness statement allows faster implementations to return other bases. -/
namespace Tamarin.ACBasis
theorem total_add {n} (v w : Vec n) :
    total (fun i => v i + w i) = total v + total w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun i => v i.succ) (fun i => w i.succ)
    simp only [total, List.ofFn_succ, List.sum_cons] at h ⊢
    omega

private theorem total_le {n} (v : Vec n) (M : Nat) (bound : ∀ i, v i ≤ M) : total v ≤ n * M := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    have tail := ih (fun i => v i.succ) (fun i => bound i.succ)
    simp only [total, List.ofFn_succ, List.sum_cons, Nat.succ_mul] at tail ⊢
    have := bound 0
    omega

private theorem le_total {n} (v : Vec n) (i : Fin n) : v i ≤ total v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [total, List.ofFn_succ, List.sum_cons]
    refine Fin.cases (by omega) (fun j => ?_) i
    have := ih (fun k => v k.succ) j
    unfold total at this
    omega

private theorem dot_add {n} (a x y : Vec n) :
    dot a (fun i => x i + y i) = dot a x + dot a y := by
  simp only [dot, Nat.mul_add, total_add]

theorem dot_spike {n} (v : Vec n) (i : Fin n) (m : Nat) :
    dot v (spike i m) = v i * m := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [dot,total,spike,List.ofFn_succ,Fin.succ_ne_zero, List.sum_eq_zero_iff_forall_eq_nat]
    · change total (fun k => v k * spike j.succ m k) = _
      rw [total, List.ofFn_succ, List.sum_cons]
      simpa [spike, dot, total, Ne.symm (Fin.succ_ne_zero j)] using ih (fun k => v k.succ) j

private theorem cap_pos {n} (r : Row n) : 0 < r.cap := by
  exact List.le_max_of_mem (show 1 ∈ 1 :: (List.ofFn r.pos ++ List.ofFn r.neg) from List.mem_cons_self ..)
private theorem pos_le_cap {n} (r : Row n) (i : Fin n) : r.pos i ≤ r.cap := by
  exact List.le_max_of_mem <| List.mem_cons_of_mem _ <| List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
private theorem neg_le_cap {n} (r : Row n) (i : Fin n) : r.neg i ≤ r.cap := by
  exact List.le_max_of_mem <| List.mem_cons_of_mem _ <| List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem row_small {n} (p q x : Vec n) (m : Nat)
    (hp : ∀ i, p i ≤ m) (small : ∀ i, 0 < p i → x i < m)
    (balance : dot p x = dot q x) (live : ∀ i, 0 < x i → 0 < p i ∨ 0 < q i) :
    ∀ i, x i ≤ m + n * (m * m) := by
  have upper : dot p x ≤ n * (m*m) := by
    apply total_le
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · exact Nat.mul_le_mul (hp i) (Nat.le_of_lt (small i (by omega)))
  intro i
  by_cases hx : 0 < x i
  · rcases live i hx with h | h
    · have := small i h; omega
    · have hle : x i ≤ q i * x i := by
        simpa using (Nat.mul_le_mul_right (x i) h : 1 * x i ≤ q i * x i)
      have hq := le_total (fun j => q j * x j) i
      change q i * x i ≤ dot q x at hq
      omega
  · omega

/-- A nonzero solution always dominates a nonzero bounded solution.
If large inventories occur on both signs, remove a two-coordinate solution.
Otherwise the entire inventory on the smaller sign has bounded weight. -/
theorem dominated {n} (r : Row n) (x : Vec n) (hx : r.Holds x) (nonzero : ∃ i, 0 < x i) :
    ∃ y : Vec n, r.Holds y ∧ (∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ (∀ i, y i ≤ r.bound) := by
  classical
  have cap := cap_pos r
  have bound : r.cap ≤ r.bound := by unfold Row.bound; omega
  by_cases neutral : ∃ i, 0 < x i ∧ r.pos i = 0 ∧ r.neg i = 0
  · obtain ⟨j, hj, hp, hn⟩ := neutral
    refine ⟨spike j 1, ?_, ⟨j, by simp [spike]⟩, ?_, ?_⟩
    · simp [Row.Holds, dot_spike, hp, hn]
    · intro i; by_cases he : i = j <;> simp_all [spike] <;> omega
    · intro i; by_cases he : i = j <;> simp_all [spike] <;> omega
  have live (i) (hi : 0 < x i) : 0 < r.pos i ∨ 0 < r.neg i := by
    by_cases p : r.pos i = 0
    · exact Or.inr (Nat.pos_of_ne_zero (fun q => neutral ⟨i,hi,p,q⟩))
    · exact Or.inl (Nat.pos_of_ne_zero p)
  by_cases largeP : ∃ i, 0 < r.pos i ∧ r.cap ≤ x i
  · by_cases largeN : ∃ j, 0 < r.neg j ∧ r.cap ≤ x j
    · obtain ⟨i, hpi, hxi⟩ := largeP
      obtain ⟨j, hnj, hxj⟩ := largeN
      have hni : r.neg i = 0 := (r.disjoint i).resolve_left (by omega)
      have hpj : r.pos j = 0 := (r.disjoint j).resolve_right (by omega)
      have ne : i ≠ j := by intro h; subst j; omega
      let y : Vec n := fun k => spike i (r.neg j) k + spike j (r.pos i) k
      refine ⟨y, ?_, ⟨i, by simpa [y, spike, ne] using hnj⟩, ?_, ?_⟩
      · simp [Row.Holds, y, dot_add, dot_spike, hni, hpj, Nat.mul_comm]
      · intro k
        have hi := neg_le_cap r j
        have hj := pos_le_cap r i
        by_cases eq : k = i
        · subst k; simp [y,spike,ne]; omega
        · by_cases ej : k = j
          · subst k; simp [y,spike,ne.symm]; omega
          · simp [y,spike,eq,ej]
      · intro k
        have hi := neg_le_cap r j
        have hj := pos_le_cap r i
        by_cases eq : k = i
        · subst k; simp [y,spike,ne]; omega
        · by_cases ej : k = j
          · subst k; simp [y,spike,ne.symm]; omega
          · simp [y,spike,eq,ej]
    · exact ⟨x,hx,nonzero,fun _ => Nat.le_refl _, row_small _ _ _ _ (neg_le_cap r)
        (fun i hi => Nat.lt_of_not_ge (fun h => largeN ⟨i,hi,h⟩)) hx.symm (fun i hi => (live i hi).symm)⟩
  · exact ⟨x,hx,nonzero,fun _ => Nat.le_refl _, row_small _ _ _ _ (pos_le_cap r)
      (fun i hi => Nat.lt_of_not_ge (fun h => largeP ⟨i,hi,h⟩)) hx live⟩

/-- Select exactly k unit occurrences from a sufficiently large inventory. -/
private theorem take_total {n} (stock : Vec n) (k : Nat) (enough : k ≤ total stock) :
    ∃ y : Vec n, total y = k ∧ ∀ i, y i ≤ stock i := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa [total] using enough
    exact ⟨stock, by simp [total,this],fun _ => Nat.le_refl _⟩
  | succ n ih =>
    let h := min (stock 0) k
    let tail := fun i : Fin n => stock i.succ
    have sum : total stock = stock 0 + total tail := by simp [total,tail,List.ofFn_succ]
    obtain ⟨y,hy,down⟩ := ih tail (k-h) (by dsimp [h]; omega)
    refine ⟨Fin.cases h y, ?_,fun i => Fin.cases (Nat.min_le_left ..) down i⟩
    simp only [total,List.ofFn_succ,List.sum_cons,Fin.cases_zero,Fin.cases_succ]
    change h + total y = k
    rw [hy]; dsimp [h]; omega

private theorem dominated_unit_side {n} (p q x : Vec n) (cap : Nat)
    (disjoint : ∀ i, p i = 0 ∨ q i = 0) (unit : ∀ i, q i ≤ 1)
    (bound : ∀ i, p i ≤ cap) (balance : dot p x = dot q x) (active : 0 < dot p x) :
    ∃ y : Vec n, dot p y = dot q y ∧ (∃ j, 0 < y j) ∧
      (∀ i, y i ≤ x i) ∧ (∀ i, y i ≤ cap) := by
  obtain ⟨_,mem,pos⟩ := List.sum_pos_iff_exists_pos_nat.mp active
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  have hp := Nat.pos_of_mul_pos_right pos
  have hx := Nat.pos_of_mul_pos_left pos
  have qi := (disjoint i).resolve_left (by omega)
  have enough : p i ≤ dot q x := by
    have := le_total (fun j => p j * x j) i
    have step := Nat.mul_le_mul_left (p i) hx
    change p i * x i ≤ dot p x at this
    simp only [Nat.mul_one] at step
    omega
  obtain ⟨z,totalz,down⟩ := take_total (fun j => q j * x j) (p i) enough
  have off (j) (h : q j = 0) : z j = 0 := by simpa [h] using down j
  have qz : dot q z = p i := by
    have same : (fun j => q j * z j) = z := by
      funext j
      by_cases h : q j = 0
      · simp [h,off j h]
      · have one : q j = 1 := by have := unit j; omega
        simp [one]
    simpa only [dot,same] using totalz
  have pz : dot p z = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro v hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    rcases disjoint j with h|h <;> simp_all
  let y := fun j => spike i 1 j + z j
  refine ⟨y, by simp [y,dot_add,dot_spike,pz,qz,qi], ⟨i,by simp [y,spike]; omega⟩, ?_, ?_⟩
  · intro j
    by_cases e : j = i
    · subst j; simp [y,spike,off i qi]; omega
    · have h := Nat.mul_le_mul_right (x j) (unit j)
      simpa [y,spike,e] using (Nat.le_trans (down j) (by simpa using h : q j * x j ≤ x j))
  · intro j
    by_cases e : j = i
    · subst j; have := bound i; simp [y,spike,off i qi]; omega
    · have := le_total z j
      simpa [y,spike,e] using (Nat.le_trans this (by rw [totalz]; exact bound i))

private theorem dominated_limits {n} (r : Row n) (x : Vec n) (hx : r.Holds x) (nz : ∃ i, 0 < x i) :
    ∃ y : Vec n, r.Holds y ∧ (∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ (∀ i, y i ≤ r.limits i) := by
  have one (i) : 1 ≤ r.limits i := by
    have := cap_pos r; simp only [Row.limits]; split <;> (try split) <;> omega
  by_cases neutral : ∃ j, 0 < x j ∧ r.pos j = 0 ∧ r.neg j = 0
  · obtain ⟨j,hj,hp,hn⟩ := neutral
    exact ⟨spike j 1, by simp [Row.Holds, dot_spike, hp, hn], ⟨j,by simp [spike]⟩,
      fun i => by by_cases h : i = j <;> simp_all [spike] <;> omega,
      fun i => by unfold spike; split <;> first | exact one i | omega⟩
  by_cases unit : r.unitSide
  · have active : 0 < dot r.pos x := by
      obtain ⟨j,hj⟩ := nz
      have l := le_total (fun i => r.pos i * x i) j
      have b := le_total (fun i => r.neg i * x i) j
      change r.pos j * x j ≤ dot r.pos x at l
      change r.neg j * x j ≤ dot r.neg x at b
      by_cases h : r.pos j = 0
      · have hn : r.neg j ≠ 0 := fun hn => neutral ⟨j,hj,h,hn⟩
        rw [hx]; exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero hn) hj) b
      · exact Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero h) hj) l
    have step : ∃ y : Vec n, r.Holds y ∧ (∃ i, 0 < y i) ∧
        (∀ i, y i ≤ x i) ∧ (∀ i, y i ≤ r.cap) := by
      rcases unit with u|u
      · obtain ⟨y,h,nz,lo,hi⟩ := dominated_unit_side r.neg r.pos x r.cap
          (fun i => (r.disjoint i).symm) u (neg_le_cap r) hx.symm (hx ▸ active)
        exact ⟨y,h.symm,nz,lo,hi⟩
      · exact dominated_unit_side r.pos r.neg x r.cap r.disjoint u (pos_le_cap r) hx active
    obtain ⟨y,hy,ynz,down,small⟩ := step
    refine ⟨y,hy,ynz,down,fun i => ?_⟩
    by_cases h : r.pos i = 0 ∧ r.neg i = 0
    · have hx0 : x i = 0 := by have hn : ¬0 < x i := fun hp => neutral ⟨i,hp,h⟩; omega
      have hi := down i; simp [Row.limits,h.1,h.2]; omega
    · simpa [Row.limits,h,unit] using small i
  · obtain ⟨y,hy,ynz,down,small⟩ := dominated r x hx nz
    refine ⟨y,hy,ynz,down,fun i => ?_⟩
    by_cases h : r.pos i = 0 ∧ r.neg i = 0
    · have hx0 : x i = 0 := by have hn : ¬0 < x i := fun hp => neutral ⟨i,hp,h⟩; omega
      have := down i; omega
    · simpa [Row.limits,unit,h,Row.bound] using small i

theorem mem_box {n} (b v : Vec n) : v ∈ box n b ↔ ∀ i, v i ≤ b i := by
  induction n with
  | zero => simp [box]; funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [box, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨h,hb,t,ht,rfl⟩ i
      exact Fin.cases (by simp; omega) (fun j => by simpa using (ih _ _).mp ht j) i
    · intro h
      refine ⟨v 0, by have := h 0; omega, fun i => v i.succ, (ih _ _).mpr (fun j => h j.succ), ?_⟩
      funext i; exact Fin.cases rfl (fun _ => rfl) i

theorem Row.mem_generators {n} (r : Row n) (v : Vec n) :
    v ∈ r.generators ↔ (∀ i, v i ≤ r.limits i) ∧ r.Holds v ∧ ∃ i, 0 < v i := by
  simp [generators, mem_box, Holds]; grind

def Generates {n} (gs : List (Vec n)) (x : Vec n) : Prop :=
  ∃ c, mix gs.get c = x

private theorem total_zero {n} : total (fun _ : Fin n => 0) = 0 := by
  simp [total, List.sum_eq_zero_iff_forall_eq_nat]

private theorem mix_zero {k n} (g : Fin k → Vec n) : mix g (fun _ => 0) = fun _ => 0 := by
  funext i; simp [mix,dot,total_zero]

private theorem mix_add {k n} (g : Fin k → Vec n) (x y : Vec k) :
    mix g (fun j => x j + y j) = fun i => mix g x i + mix g y i := by
  funext i; exact dot_add _ x y

def SystemHolds {n} (rows : List (Row n)) (x : Vec n) : Prop := ∀ r ∈ rows, r.Holds x

private theorem generate_of_dominated {n} (rs : List (Row n)) (gs : List (Vec n))
    (step : ∀ x, SystemHolds rs x → (∃ i, 0 < x i) →
      ∃ y ∈ gs, SystemHolds rs y ∧ (∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i))
    (x : Vec n) (hx : SystemHolds rs x) : Generates gs x := by
  induction h : total x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    by_cases nz : ∃ i, 0 < x i
    · obtain ⟨y,hm,hy,ynz,down⟩ := step x hx nz
      obtain ⟨i, hi⟩ := List.get_of_mem hm
      let z : Vec n := fun j => x j - y j
      have add : x = fun j => z j + y j := by funext j; exact (Nat.sub_add_cancel (down j)).symm
      have hz : SystemHolds rs z := by
        intro r hr
        have xh := hx r hr
        have yh := hy r hr
        unfold Row.Holds at xh yh ⊢
        rw [add, dot_add, dot_add] at xh
        omega
      have less : total z < m := by
        obtain ⟨j,hj⟩ := ynz
        have le := le_total y j
        rw [add,total_add] at h
        omega
      obtain ⟨c,hc⟩ := ih _ less z hz rfl
      refine ⟨fun j => c j + spike i 1 j, ?_⟩
      rw [mix_add, hc]
      funext j
      have hpart : mix gs.get (spike i 1) j = y j := by
        simp only [mix, dot_spike, Nat.mul_one, hi]
      simpa [hpart, z] using (Nat.sub_add_cancel (down j))
    · have zero : (fun _ => 0) = x := by
        funext i; exact Nat.eq_zero_of_not_pos (fun hi => nz ⟨i,hi⟩) |>.symm
      exact ⟨_, (mix_zero _).trans zero⟩

/-- One row admits a finite generating set. Every step subtracts a
componentwise dominated nonzero solution, strictly reducing total mass. -/
theorem Row.complete {n} (r : Row n) (x : Vec n) (hx : r.Holds x) : Generates r.generators x := by
  apply generate_of_dominated [r] _ _ x (by simpa [SystemHolds] using hx)
  intro v hv nz
  obtain ⟨y,hy,ynz,le,small⟩ := dominated_limits r v (hv _ (by simp)) nz
  exact ⟨y, (r.mem_generators y).mpr ⟨small,hy,ynz⟩, by simpa [SystemHolds] using hy, ynz, le⟩

private theorem total_mul {n} (a : Nat) (v : Vec n) :
    total (fun i => a * v i) = a * total v := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    have h := ih (fun i => v i.succ)
    simp only [total, List.ofFn_succ, List.sum_cons, Nat.mul_add] at h ⊢
    rw [h]

private theorem total_swap {k n} (a : Fin k → Vec n) :
    total (fun i => total (a i)) = total (fun j => total (fun i => a i j)) := by
  induction k with
  | zero => exact (@total_zero n).symm
  | succ k ih =>
    have split {s} (v : Vec (s+1)) : total v = v 0 + total (fun i => v i.succ) := by
      simp only [total, List.ofFn_succ, List.sum_cons]
    rw [split, show (fun j => total (fun i => a i j)) =
        (fun j => a 0 j + total (fun i => a i.succ j)) from funext (fun _ => split _), total_add]
    exact congrArg (total (a 0) + ·) (ih (fun i => a i.succ))

private theorem dot_mix {k n} (a : Vec n) (g : Fin k → Vec n) (c : Vec k) :
    dot a (mix g c) = dot (fun i => dot a (g i)) c := by
  unfold dot mix
  simp only [dot, ← total_mul]
  rw [total_swap]
  congr 1; funext j
  rw [Nat.mul_comm (total _) (c j), ← total_mul]
  congr 1; funext i; ac_rfl

theorem Row.ofWeights_holds {n} (p q x : Vec n) :
    (Row.ofWeights p q).Holds x ↔ dot p x = dot q x := by
  let shared : Vec n := fun i => min (p i) (q i)
  have splitP : p = fun i => shared i + (p i - q i) := by funext i; simp [shared]; omega
  have splitQ : q = fun i => shared i + (q i - p i) := by funext i; simp [shared]; omega
  have split {a b : Vec n} : dot (fun i => a i + b i) x = dot a x + dot b x := by
    simp [dot, Nat.add_mul, total_add]
  change dot (fun i => p i - q i) x = dot (fun i => q i - p i) x ↔ dot p x = dot q x
  conv => rhs; lhs; rw [splitP, split]
  conv => rhs; rhs; rw [splitQ, split]
  omega

theorem Row.pullback_iff {k n} (r : Row n) (g : Fin k → Vec n) (c : Vec k) :
    (r.pullback g).Holds c ↔ r.Holds (mix g c) := by
  rw [pullback, ofWeights_holds, Holds, dot_mix, dot_mix]

private theorem mix_assoc {l k n} (a : Fin k → Vec n) (b : Fin l → Vec k) (c : Vec l) :
    mix (fun i => mix a (b i)) c = mix a (mix b c) := by
  funext j; exact (dot_mix (fun i => a i j) b c).symm

/-- A candidate may choose any finite generators. Both directions of span
are required for every natural vector, with no bound on queried vectors. -/
def BasisCorrect {n} (rows : List (Row n)) (gs : List (Vec n)) : Prop :=
  ∀ x, SystemHolds rows x ↔ Generates gs x

private theorem system_mix {k n} (rows : List (Row n)) (g : Fin k → Vec n) (c : Vec k)
    (h : ∀ i, SystemHolds rows (g i)) : SystemHolds rows (mix g c) := by
  intro r hr
  unfold Row.Holds
  rw [dot_mix, dot_mix, show (fun i => dot r.pos (g i)) =
    (fun i => dot r.neg (g i)) from funext (fun i => h i r hr)]

theorem mem_sol {n} (rows : List (Row n)) (gs : List (Vec n)) (hc : BasisCorrect rows gs)
    (i : Fin gs.length) : SystemHolds rows (gs.get i) := by
  apply (hc _).mpr
  refine ⟨spike i 1, ?_⟩
  funext j; simp only [mix, dot_spike, Nat.mul_one]

theorem lift_generates {k n} (g : Fin k → Vec n) (coeffs : List (Vec k)) (x : Vec n) :
    Generates (lift g coeffs) x ↔ ∃ c, Generates coeffs c ∧ mix g c = x := by
  let cast (i : Fin (lift g coeffs).length) : Fin coeffs.length := ⟨i.val, by simpa [lift] using i.isLt⟩
  let back (i : Fin coeffs.length) : Fin (lift g coeffs).length := ⟨i.val, by simp [lift]⟩
  have castEq (c : Vec coeffs.length) :
      mix (lift g coeffs).get (fun i => c (cast i)) = mix g (mix coeffs.get c) := by
    rw [← mix_assoc]
    funext j
    unfold mix dot total
    congr 1
    apply List.ext_getElem
    · simp [lift]
    · intro i hi hj
      simp [lift, cast]; rfl
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨_, ⟨fun i => u (back i),rfl⟩, (castEq (fun i => u (back i))).symm.trans hu⟩
  · rintro ⟨_, ⟨u,rfl⟩, rfl⟩
    exact ⟨_, castEq u⟩

theorem intersect_correct {n} (r : Row n) (rs : List (Row n)) (gs : List (Vec n))
    (hg : BasisCorrect rs gs) : BasisCorrect (r :: rs) (intersect r gs) := by
  intro x
  rw [intersect, lift_generates]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (hg x).mp (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact ⟨c, (r.pullback gs.get).complete c <| (r.pullback_iff ..).mpr (hc ▸ h r (List.mem_cons_self ..)), hc⟩
  · rintro ⟨c, ⟨w,hw⟩,rfl⟩ q hq
    rcases List.mem_cons.mp hq with rfl | hr
    · apply (q.pullback_iff ..).mp
      rw [← hw]
      apply (system_mix [q.pullback gs.get] _ _ _) _ (List.mem_singleton_self _)
      intro i row hr
      obtain rfl := List.mem_singleton.mp hr
      exact (((q.pullback gs.get).mem_generators _).mp (List.get_mem _ _)).2.1
    · exact system_mix rs _ _ (mem_sol rs gs hg) q hr

private theorem units_correct (n : Nat) : BasisCorrect [] (units n) := by
  intro x
  refine ⟨fun _ => ?_, fun _ _ hm => nomatch hm⟩
  let c : Vec (units n).length := fun i => x ⟨i.val, by simpa [units] using i.isLt⟩
  refine ⟨c, ?_⟩
  funext j
  have h : mix (units n).get c j = dot x (spike j 1) := by
    unfold mix dot total
    congr 1
    apply List.ext_getElem
    · simp [units]
    · intro i hi hj
      simp only [List.getElem_ofFn, List.get_eq_getElem, units, c, spike]
      rw [Nat.mul_comm]
      congr 2
      exact propext eq_comm
  rw [h, dot_spike, Nat.mul_one]

theorem mem_minimize {n} (gs : List (Vec n)) (x : Vec n) :
    x ∈ minimize gs ↔ x ∈ gs ∧ (∃ i, 0 < x i) ∧
      ∀ y ∈ gs, (∃ i, 0 < y i) → (∀ i, y i ≤ x i) → y = x := by
  simp [minimize]

private theorem below {n} (gs : List (Vec n)) (x : Vec n) (rep : Generates gs x) (nz : ∃ i, 0 < x i) :
    ∃ y ∈ gs, (∃ i, 0 < y i) ∧ ∀ i, y i ≤ x i := by
  obtain ⟨c,rfl⟩ := rep
  obtain ⟨j, hj⟩ := nz
  change 0 < (List.ofFn (fun i => gs.get i j * c i)).sum at hj
  obtain ⟨t, ht, pos⟩ := List.sum_pos_iff_exists_pos_nat.mp hj
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  have hc := Nat.pos_of_mul_pos_left pos
  have hi := Nat.pos_of_mul_pos_right pos
  refine ⟨gs.get i,List.get_mem _ _,⟨j,hi⟩,fun k => ?_⟩
  exact Nat.le_trans (by simpa using (Nat.mul_le_mul_left (gs.get i k) hc))
    (le_total (fun a => gs.get a k * c a) i)

private theorem minimal_below {n} (gs : List (Vec n)) (x : Vec n) (mem : x ∈ gs) (nz : ∃ i, 0 < x i) :
    ∃ y ∈ minimize gs, ∀ i, y i ≤ x i := by
  classical
  induction h : total x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    by_cases hm : x ∈ minimize gs
    · exact ⟨x,hm,fun _ => Nat.le_refl _⟩
    · have bad : ∃ y ∈ gs, (∃ i, 0 < y i) ∧ (∀ i, y i ≤ x i) ∧ y ≠ x := by
        apply Classical.byContradiction; intro no
        exact hm ((mem_minimize ..).mpr ⟨mem,nz,fun y ym yn yd => Classical.byContradiction
          (fun ne => no ⟨y,ym,yn,yd,ne⟩)⟩)
      obtain ⟨y,hy,ynz,down,ne⟩ := bad
      have add : x = fun i => (x i - y i) + y i := by funext i; exact (Nat.sub_add_cancel (down i)).symm
      have diff : ∃ i, 0 < x i - y i := by
        apply Classical.byContradiction; intro same; apply ne; funext i
        have hn : ¬ 0 < x i - y i := fun pos => same ⟨i,pos⟩
        have := down i; omega
      obtain ⟨i,hi⟩ := diff
      have lt : total y < m := by
        have le := le_total (fun i => x i - y i) i
        rw [add,total_add] at h
        omega
      obtain ⟨z,hz,d⟩ := ih _ lt y hy ynz rfl
      exact ⟨z,hz,fun i => Nat.le_trans (d i) (down i)⟩

theorem minimize_correct {n} (rows : List (Row n)) (gs : List (Vec n)) (hg : BasisCorrect rows gs) :
    BasisCorrect rows (minimize gs) := by
  have sound (x) (hx : x ∈ gs) : SystemHolds rows x := by
    obtain ⟨i,rfl⟩ := List.get_of_mem hx
    exact mem_sol rows gs hg i
  intro x
  constructor
  · apply generate_of_dominated
    intro v hv nz
    obtain ⟨y,hy,ynz,down⟩ := below gs v ((hg v).mp hv) nz
    obtain ⟨z,hz,le⟩ := minimal_below gs y hy ynz
    obtain ⟨mem,live,_⟩ := (mem_minimize ..).mp hz
    exact ⟨z,hz,sound z mem,live,fun i => Nat.le_trans (le i) (down i)⟩
  · rintro ⟨c,rfl⟩
    exact system_mix rows _ c (fun i => sound _ ((mem_minimize ..).mp (List.get_mem _ i)).1)

/-- Complete unrestricted finite generation for arbitrary finite systems. -/
theorem generate_correct {n} (rows : List (Row n)) : BasisCorrect rows (generate rows) := by
  induction rows with
  | nil => exact minimize_correct _ _ (units_correct n)
  | cons r rs ih => exact minimize_correct _ _ (intersect_correct r rs _ ih)

/-- Basis correctness is invariant under changing the table order, including
the choice of concrete witness indices. -/
theorem BasisCorrect.of_mem {n} {rows : List (Row n)} {gs hs : List (Vec n)}
    (correct : BasisCorrect rows hs) (members : ∀ g, g ∈ gs ↔ g ∈ hs) : BasisCorrect rows gs := by
  have sound (g) (m : g ∈ hs) : SystemHolds rows g := by
    obtain ⟨j,rfl⟩ := List.get_of_mem m
    exact mem_sol rows hs correct j
  intro x
  constructor
  · apply generate_of_dominated
    intro y sol live
    obtain ⟨g,m,h,pos⟩ := below hs y ((correct y).mp sol) live
    exact ⟨g,(members g).mpr m,sound g m,h,pos⟩
  · rintro ⟨c,rfl⟩
    exact system_mix rows _ c (fun j => sound _ ((members _).mp (List.get_mem _ j)))

/-- A nonzero kernel vector belongs to the Hilbert basis precisely when it
dominates no smaller nonzero solution. -/
def Irreducible {n} (rows : List (Row n)) (x : Vec n) : Prop :=
  SystemHolds rows x ∧ (∃ i, 0 < x i) ∧
    ∀ y, SystemHolds rows y → (∃ i, 0 < y i) → (∀ i, y i ≤ x i) → y = x

theorem minimize_iff_irreducible {n} (rs : List (Row n)) (gs : List (Vec n))
    (hg : BasisCorrect rs gs) (x : Vec n) : x ∈ minimize gs ↔ Irreducible rs x := by
  have sound (u) (hu : u ∈ gs) : SystemHolds rs u := by
    obtain ⟨i,rfl⟩ := List.get_of_mem hu
    exact mem_sol rs gs hg i
  rw [mem_minimize]
  constructor
  · rintro ⟨mem,nz,minimal⟩
    refine ⟨sound x mem,nz,fun y hy ynz d => ?_⟩
    obtain ⟨z,hz,znz,le⟩ := below gs y ((hg y).mp hy) ynz
    obtain rfl := minimal z hz znz (fun i => Nat.le_trans (le i) (d i))
    funext i; exact Nat.le_antisymm (d i) (le i)
  · rintro ⟨hx,nz,m⟩
    obtain ⟨y,hy,ynz,d⟩ := below gs x ((hg x).mp hx) nz
    obtain rfl := m y (sound y hy) ynz d
    exact ⟨hy,nz,fun z hz => m z (sound z hz)⟩

theorem mem_generate {n} (rows : List (Row n)) (x : Vec n) :
    x ∈ generate rows ↔ Irreducible rows x := by
  cases rows with
  | nil => exact minimize_iff_irreducible _ _ (units_correct n) _
  | cons r rs => exact minimize_iff_irreducible _ _ (intersect_correct _ _ _ (generate_correct rs)) _

/-- The numeric projection of a side contains its variable multiplicities in
the caller's chosen coordinate order. -/
def coefficients {n} (names : Fin n → Variable) (xs : List Variable) : Vec n :=
  fun i => xs.count (names i)

def encode {n} (names : Fin n → Variable) (row : ACSystem.Row) : Row n :=
  Row.ofWeights (coefficients names row.lhs.vars) (coefficients names row.rhs.vars)

private theorem weight_eq {n} (names : Fin n → Variable)
    (unique : ∀ i j, names i = names j → i = j)
    (xs : List Variable) (live : ∀ v ∈ xs, ∃ i, names i = v) (c : ACSystem.Column) :
    dot (coefficients names xs) (fun i => c (names i)) = (xs.map c).sum := by
  induction xs with
  | nil => simp [coefficients, dot,total_zero]
  | cons v xs ih =>
    obtain ⟨j,hj⟩ := live v (List.mem_cons_self ..)
    have eq : coefficients names (v::xs) = fun i => spike j 1 i + coefficients names xs i := by
      funext i
      by_cases h : i = j
      · subst i; simp [coefficients,spike, hj, Nat.add_comm]
      · have ne : v ≠ names i := fun hv => h (unique i j (hv.symm.trans hj.symm))
        simp [coefficients,spike,h,ne]
    have swap (v w : Vec n) : dot v w = dot w v := by simp only [dot, Nat.mul_comm]
    have hs : dot (spike j 1) (fun i => c (names i)) = c v := by
      rw [swap, dot_spike,Nat.mul_one,hj]
    rw [eq]
    change total _ = _
    simp only [Nat.add_mul, total_add, List.map_cons, List.sum_cons]
    exact congr (congrArg Nat.add hs) (ih (fun v hv => live v (List.mem_cons_of_mem _ hv)))

/-- The column frame accounts for every occurrence exactly once. -/
theorem coefficients_total {n} (names : Fin n → Variable)
    (unique : ∀ i j, names i = names j → i = j) (xs : List Variable)
    (live : ∀ v ∈ xs, ∃ i, names i = v) : total (coefficients names xs) = xs.length := by
  have ones (l : List Variable) : (l.map (fun _ => (1 : Nat))).sum = l.length := by
    induction l with
    | nil => rfl
    | cons v tail ih => simp [ih,Nat.add_comm]
  simpa [dot,ones] using weight_eq names unique xs live (fun _ => 1)

theorem encode_iff {n} (names : Fin n → Variable) (unique : ∀ i j, names i = names j → i = j)
    (rows : List ACSystem.Row) (live : ∀ v ∈ ACSystem.variables rows, ∃ i, names i = v)
    (c : ACSystem.Column) :
    SystemHolds (rows.map (encode names)) (fun i => c (names i)) ↔ ACSystem.Balanced rows c := by
  have eq (r : ACSystem.Row) (hr : r ∈ rows) : (encode names r).Holds (fun i => c (names i)) ↔
      r.lhs.weight c = r.rhs.weight c := by
    rw [encode, Row.ofWeights_holds, weight_eq names unique, weight_eq names unique]
    · rfl
    · exact fun v hv => live v (List.mem_flatMap.mpr ⟨r,hr,List.mem_append_right _ hv⟩)
    · exact fun v hv => live v (List.mem_flatMap.mpr ⟨r,hr,List.mem_append_left _ hv⟩)
  constructor
  · intro h r hr; exact (eq r hr).mp (h _ (List.mem_map_of_mem hr))
  · intro h _ hm
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    exact (eq r hr).mpr (h r hr)

/-- Replacing the enumeration requires only an unrestricted span proof for
the numeric rows. Every factor of one substitution uses the same basis. -/
theorem solves_iff_generates {sig : Signature} {n} (f : sig.ACSym) (names : Fin n → Variable)
    (unique : ∀ i j, names i = names j → i = j) (rows : List ACSystem.Row)
    (live : ∀ v ∈ ACSystem.variables rows, ∃ i, names i = v) (gs : List (Vec n))
    (correct : BasisCorrect (rows.map (encode names)) gs) (σ : Substitution sig) :
    (ACSystem.problem f rows).Solves σ ↔ ∀ a ∈ ACSystem.factors f rows σ,
      Generates gs (fun i => ACSystem.factorColumn f σ a (names i)) := by
  rw [ACSystem.solves_iff_finite]
  exact forall_congr' (fun a => forall_congr' (fun _ =>
    (encode_iff names unique rows live (ACSystem.factorColumn f σ a)).symm.trans (correct _)))

/-- With no unit, each variable image must contain at least one factor.
Adding all generators witnesses simultaneous positivity precisely when
every coordinate occurs in at least one generator. -/
def coversCoordinates {n} (gs : List (Vec n)) : Bool :=
  decide (∀ i, ∃ g ∈ gs, 0 < g i)

theorem coversCoordinates_iff {n} (rs : List (Row n)) (gs : List (Vec n))
    (hg : BasisCorrect rs gs) :
    coversCoordinates gs = true ↔ ∃ x, SystemHolds rs x ∧ ∀ i, 0 < x i := by
  simp only [coversCoordinates, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨mix gs.get (fun _ => 1), (hg _).mpr ⟨_, rfl⟩, ?_⟩
    intro i
    obtain ⟨g,hm,hp⟩ := h i
    obtain ⟨j,rfl⟩ := List.get_of_mem hm
    apply List.sum_pos_iff_exists_pos_nat.mpr
    exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, by simpa using hp⟩
  · rintro ⟨x,sol,pos⟩ i
    obtain ⟨c,rfl⟩ := (hg x).mp sol
    obtain ⟨t,ht,hp⟩ := List.sum_pos_iff_exists_pos_nat.mp (pos i)
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨_, List.get_mem _ j, Nat.pos_of_mul_pos_right hp⟩

/-- Unifiability decision for an entire homogeneous AC system. All names
are live, and each admits terms of the operator's result sort. This decides
existence only; enumeration of complete substitutions is a separate step. -/
theorem satisfiable_iff_basis_support {sig : Signature} {n} (f : sig.ACSym)
    (names : Fin n → Variable) (unique : Function.Injective names) (rows : List ACSystem.Row)
    (live : ∀ v, v ∈ ACSystem.variables rows ↔ ∃ i, names i = v)
    (sorts : ∀ v ∈ ACSystem.variables rows, Subsort (sig.acSort f) v.sort)
    (gs : List (Vec n)) (hg : BasisCorrect (rows.map (encode names)) gs) :
    (ACSystem.problem f rows).Satisfiable ↔ coversCoordinates gs = true := by
  rw [ACSystem.satisfiable_iff_positive f rows sorts, coversCoordinates_iff _ gs hg]
  have balance := encode_iff names unique rows (fun v h => (live v).mp h)
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨_, (balance c).mpr hc, fun i => hp _ ((live _).mpr ⟨i,rfl⟩)⟩
  · rintro ⟨x, hx, hp⟩
    classical
    let c := fun v => if h : ∃ i, names i = v then x h.choose else 0
    have atName (i) : c (names i) = x i := by
      simp only [c, dite_eq_left (show ∃ j, names j = names i from ⟨i,rfl⟩)]
      congr 1
      apply unique
      exact (show ∃ j, names j = names i from ⟨i,rfl⟩).choose_spec
    refine ⟨c, (balance c).mp (by simpa only [atName] using hx), ?_⟩
    intro v hv
    obtain ⟨i,rfl⟩ := (live v).mp hv
    rw [atName]
    exact hp i

end Tamarin.ACBasis
