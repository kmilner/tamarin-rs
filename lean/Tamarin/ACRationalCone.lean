import Tamarin.ACPositiveWitness

/-! Natural generators for a rational solution cone. A positive integral
scale is sufficient for existence and for strict positivity of every
coordinate. The columns need not generate every integral point exactly. -/
namespace Tamarin.ACBasis.Cone

variable {n k : Nat}

def scale (a : Nat) (x : Vec n) : Vec n := fun i => a * x i

structure ScaleCorrect (rs : List (Row n)) (gs : List (Vec n)) : Prop where
  sound : ∀ x, Generates gs x → SystemHolds rs x
  complete : ∀ x, SystemHolds rs x → ∃ a, 0 < a ∧ Generates gs (scale a x)

def pair (p : Row n) (i j : Fin n) : Vec n :=
  fun t => spike i (p.neg j) t + spike j (p.pos i) t

private theorem sum_zero : total (fun _ : Fin n => 0) = 0 := by
  simp [total,List.sum_eq_zero_iff_forall_eq_nat]

private theorem sum_mul (a : Nat) (v : Vec n) : total (fun i => a * v i) = a * total v := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total,List.ofFn_succ,List.sum_cons,Nat.mul_add]
    exact congrArg (a * v 0 + ·) (ih (fun i => v i.succ))

private theorem sum_swap (a : Fin k → Vec n) :
    total (fun i => total (a i)) = total (fun j => total (fun i => a i j)) := by
  induction k with
  | zero => exact sum_zero.symm
  | succ k ih =>
    have split {l} (v : Vec (l+1)) : total v = v 0 + total (fun i => v i.succ) := by
      simp [total,List.ofFn_succ]
    rw [split, show (fun j => total (fun i => a i j)) =
        (fun j => a 0 j + total (fun i => a i.succ j)) from funext (fun _ => split _),total_add]
    exact congrArg (total (a 0) + ·) (ih (fun i => a i.succ))

private theorem sum_pick (i : Fin n) (v : Vec n) :
    total (fun j => if i = j then v j else 0) = v i := by
  have e : (fun j => if i = j then v j else 0) = fun j => v j * spike i 1 j := by
    funext j; by_cases h : i = j <;> simp_all [spike,eq_comm]
  rw [e]; exact (dot_spike v i 1).trans (Nat.mul_one _)

private theorem gen_zero (gs : List (Vec n)) : Generates gs (fun _ => 0) :=
  ⟨fun _ => 0, funext fun _ => by simp [mix,dot,sum_zero]⟩

theorem gen_member {gs : List (Vec n)} {x} (hx : x ∈ gs) : Generates gs x := by
  obtain ⟨i,hi⟩ := List.get_of_mem hx
  exact ⟨spike i 1, funext fun t => by simp only [mix,dot_spike,Nat.mul_one,hi]⟩

theorem dot_scale (v : Vec n) (a : Nat) (c : Vec n) :
    dot v (scale a c) = a * dot v c := by
  simp only [dot,scale,← sum_mul]
  congr 1; funext i; ac_rfl

private theorem mix_scale {g : Fin k → Vec n} (a : Nat) (c : Vec k) :
    mix g (scale a c) = scale a (mix g c) := funext fun _ => dot_scale _ a c

theorem gen_scale {gs : List (Vec n)} {x} (a : Nat) (hx : Generates gs x) :
    Generates gs (scale a x) := by
  obtain ⟨c,rfl⟩ := hx
  exact ⟨_,mix_scale a c⟩

private theorem gen_add {gs : List (Vec n)} {x y} (hx : Generates gs x) (hy : Generates gs y) :
    Generates gs (fun i => x i + y i) := by
  obtain ⟨c,rfl⟩ := hx; obtain ⟨d,rfl⟩ := hy
  exact ⟨fun i => c i + d i, funext fun _ => by simp [mix,dot,Nat.mul_add,total_add]⟩

theorem gen_sum {gs : List (Vec n)} (v : Fin k → Vec n) (h : ∀ i, Generates gs (v i)) :
    Generates gs (fun t => total (fun i => v i t)) := by
  induction k with
  | zero => exact gen_zero gs
  | succ k ih =>
    simpa [total,List.ofFn_succ] using gen_add (h 0) (ih (fun i => v i.succ) (fun i => h i.succ))

private def half (a b : Vec n) (i j : Fin n) : Vec n :=
  fun t => if 0 < a i then spike i (b j) t else 0

private theorem sum_half (a b c : Vec n) (t : Fin n) :
    total (fun i => total (fun j => c i * c j * half a b i j t)) =
      if 0 < a t then c t * dot b c else 0 := by
  apply Eq.trans (b := total (fun i => if t = i then (if 0 < a i then c i * dot b c else 0) else 0))
  · congr 1; funext i
    by_cases h : t = i
    · subst i; by_cases pos : 0 < a t
      · simp only [half,pos,spike,↓reduceIte,dot,←sum_mul]
        congr 1; funext j; ac_rfl
      · simp [half,pos,sum_zero]
    · simp [half,spike,h,sum_zero]
  · exact sum_pick t _

private def edge (p : Row n) (i j : Fin n) : Vec n :=
  fun t => half p.pos p.neg i j t + half p.neg p.pos j i t

private theorem edge_sum (p : Row n) (c : Vec n) (t : Fin n) :
    total (fun i => total (fun j => c i * c j * edge p i j t)) =
    (if 0 < p.pos t then c t * dot p.neg c else 0) +
    (if 0 < p.neg t then c t * dot p.pos c else 0) := by
  simp only [edge,Nat.mul_add,total_add,sum_half]
  congr 1
  rw [sum_swap]
  rw [←sum_half p.neg p.pos c t]
  congr 1; funext j; congr 1; funext i; ac_rfl

private theorem gen_edge {gs : List (Vec n)} (p : Row n)
    (pairs : ∀ i j, 0 < p.pos i → 0 < p.neg j → pair p i j ∈ gs) (i j : Fin n) :
    Generates gs (edge p i j) := by
  by_cases hi : 0 < p.pos i <;> by_cases hj : 0 < p.neg j
  · rw [show edge p i j = pair p i j from funext fun _ => by simp [edge,half,hi,hj,pair]]
    exact gen_member (pairs i j hi hj)
  all_goals
    apply (show edge p i j = (fun _ => 0) from ?_) ▸ gen_zero gs
    funext t
    simp_all [edge,half,spike,Nat.eq_zero_of_not_pos]

/-- If the common weighted sum is positive, the scale is that sum itself.
A positive/negative coordinate pair (i,j) carries cᵢcⱼ copies of its edge.
If the weighted sum is zero, only neutral coordinates can be occupied. -/
theorem row_complete (p : Row n) (gs : List (Vec n))
    (units : ∀ i, p.pos i = 0 → p.neg i = 0 → spike i 1 ∈ gs)
    (pairs : ∀ i j, 0 < p.pos i → 0 < p.neg j → pair p i j ∈ gs)
    (c : Vec n) (h : p.Holds c) :
    Generates gs (scale (max 1 (dot p.pos c)) c) := by
  let S := dot p.pos c
  let a := max 1 S
  have hn : dot p.neg c = S := h.symm
  let neutral (i : Fin n) : Vec n := if p.pos i = 0 ∧ p.neg i = 0 then
    scale (a * c i) (spike i 1) else fun _ => 0
  have neu i : Generates gs (neutral i) := by
    dsimp only [neutral]; split
    next h => exact gen_scale _ (gen_member (units i h.1 h.2))
    next => exact gen_zero gs
  have nn t : total (fun i => neutral i t) = if p.pos t = 0 ∧ p.neg t = 0 then a * c t else 0 := by
    rw [←sum_pick t (fun t => if p.pos t = 0 ∧ p.neg t = 0 then a * c t else 0)]
    congr 1; funext i; by_cases e : t = i <;> by_cases hp : p.pos i = 0 ∧ p.neg i = 0 <;>
      simp [neutral,scale,spike,hp,e]
  have edges := gen_sum (fun i t => total (fun j => c i * c j * edge p i j t))
    (fun i => gen_sum (fun j => scale (c i * c j) (edge p i j))
      (fun j => gen_scale _ (gen_edge p pairs i j)))
  have rep := gen_add (gen_sum neutral neu) edges
  refine Eq.subst (motive := Generates gs) (Eq.symm ?_) rep
  funext t
  change a * c t = _ + _
  rw [nn,edge_sum,hn]
  change _ = _ + ((if _ then c t * S else _) + (if _ then c t * S else _))
  by_cases hs : 0 < S
  · have ha : a = S := Nat.max_eq_right hs
    rcases p.disjoint t with hp|hn <;> by_cases hp' : p.pos t = 0 <;> by_cases hn' : p.neg t = 0 <;>
      simp_all [Nat.pos_iff_ne_zero,Nat.mul_comm]
  · have zero (b : Vec n) (hb : dot b c = 0) : b t = 0 ∨ c t = 0 := by
      apply Nat.mul_eq_zero.mp
      exact (List.sum_eq_zero_iff_forall_eq_nat.mp hb) _ (List.mem_ofFn.mpr ⟨t,rfl⟩)
    have hp := zero p.pos (show S = 0 by omega)
    have hq := zero p.neg (by omega)
    rcases hp with hp|hc <;> rcases hq with hq|hc <;> simp_all [Nat.eq_zero_of_not_pos]

/-- Membership condition for the finite generator family, independent of order,
repetition and storage. -/
def Ray (p : Row n) (v : Vec n) : Prop :=
  (∃ i, p.pos i = 0 ∧ p.neg i = 0 ∧ v = spike i 1) ∨
  ∃ i j, 0 < p.pos i ∧ 0 < p.neg j ∧ v = pair p i j

theorem ray_holds (p : Row n) {v} (h : Ray p v) : p.Holds v := by
  rcases h with ⟨i,hi,hn,rfl⟩|⟨i,j,hi,hj,rfl⟩
  · simp [Row.Holds,dot_spike,hi,hn]
  · have hn := (p.disjoint i).resolve_left (Nat.ne_of_gt hi)
    have hp := (p.disjoint j).resolve_right (Nat.ne_of_gt hj)
    have eval (w : Vec n) : dot w (pair p i j) = w i * p.neg j + w j * p.pos i := by
      unfold pair dot
      simp only [Nat.mul_add,total_add]
      change dot w (spike i _) + dot w (spike j _) = _
      rw [dot_spike,dot_spike]
    simp [Row.Holds,eval,hn,hp,Nat.mul_comm]

theorem mix_holds (r : Row n) (g : Fin k → Vec n) (good : ∀ i, r.Holds (g i)) (c : Vec k) :
    r.Holds (mix g c) := by
  apply (r.pullback_iff _ _).mp
  have eq : (fun i => dot r.pos (g i)) = fun i => dot r.neg (g i) := funext good
  simp [Row.pullback,Row.ofWeights_holds,eq]

theorem row_correct (p : Row n) (gs : List (Vec n)) (table : ∀ v, v ∈ gs ↔ Ray p v) :
    ScaleCorrect [p] gs where
  sound := by
    rintro _ ⟨c,rfl⟩
    simpa [SystemHolds] using mix_holds p gs.get (fun i =>
      ray_holds p ((table _).mp (List.get_mem _ i))) c
  complete c h := ⟨_,Nat.le_max_left 1 _,row_complete p gs
    (fun i hp hn => (table _).mpr (.inl ⟨i,hp,hn,rfl⟩))
    (fun i j hp hn => (table _).mpr (.inr ⟨i,j,hp,hn,rfl⟩)) c (h _ List.mem_cons_self)⟩

theorem units_correct (n : Nat) : ScaleCorrect [] (units n) where
  sound := by simp [SystemHolds]
  complete x _ := by
    refine ⟨1,by decide,?_⟩
    have units_mem (i : Fin n) : spike i 1 ∈ units n := List.mem_ofFn.mpr ⟨i,rfl⟩
    have sum := gen_sum (fun i => scale (x i) (spike i 1)) (fun i => gen_scale _ (gen_member (units_mem i)))
    refine Eq.subst (motive := Generates (units n)) ?_ sum
    funext t
    change total _ = 1 * x t
    rw [Nat.one_mul,←sum_pick t x]
    congr 1; funext i; by_cases h : t = i <;> simp [scale,spike,h]

theorem lift_correct (r : Row n) (rs : List (Row n)) (gs : List (Vec n))
    (previous : ScaleCorrect rs gs) (cs : List (Vec gs.length))
    (coeffs : ScaleCorrect [r.pullback gs.get] cs) :
    ScaleCorrect (r :: rs) (lift gs.get cs) where
  sound := by
    intro x rep s mem
    obtain ⟨c,hc,rfl⟩ := (lift_generates ..).mp rep
    rcases List.mem_cons.mp mem with rfl|hm
    · exact (s.pullback_iff _ _).mp (coeffs.sound c hc _ List.mem_cons_self)
    · exact previous.sound _ ⟨c,rfl⟩ s hm
  complete := by
    intro x sol
    obtain ⟨a,ha,c,hc⟩ := previous.complete x (fun s h => sol s (List.mem_cons_of_mem r h))
    have pulled : (r.pullback gs.get).Holds c := by
      apply (r.pullback_iff _ _).mpr
      rw [hc]; unfold Row.Holds; rw [dot_scale,dot_scale,sol r List.mem_cons_self]
    obtain ⟨b,hb,rep⟩ := coeffs.complete c (by simpa [SystemHolds] using pulled)
    refine ⟨b*a,Nat.mul_pos hb ha,(lift_generates ..).mpr ⟨scale b c,rep,?_⟩⟩
    rw [mix_scale,hc]
    funext i; exact (Nat.mul_assoc ..).symm

theorem of_exact (rs : List (Row n)) (gs : List (Vec n)) (basis : BasisCorrect rs gs) :
    ScaleCorrect rs gs where
  sound x := (basis x).mpr
  complete x h := by
    refine ⟨1,by decide,?_⟩
    rw [show scale 1 x = x from funext fun _ => Nat.one_mul _]
    exact (basis x).mp h

/-- The final row may use the maximal-support witness and avoid constructing
its projected ray table entirely. -/
theorem last_row_iff (r : Row n) (rs : List (Row n)) (gs : List (Vec n))
    (basis : ScaleCorrect rs gs) :
    (∃ x, SystemHolds (r :: rs) x ∧ ∀ i, 0 < x i) ↔
      ∀ i, ∃ j : Fin gs.length, 0 < gs.get j i ∧ PositiveWitness.enabled (r.pullback gs.get) j := by
  let p := r.pullback gs.get
  constructor
  · rintro ⟨x,sol,live⟩
    obtain ⟨a,ha,c,eq⟩ := basis.complete x (fun s h => sol s (List.mem_cons_of_mem r h))
    have pulled : p.Holds c := by
      apply (r.pullback_iff _ _).mpr
      rw [eq]; unfold Row.Holds; rw [dot_scale,dot_scale,sol r List.mem_cons_self]
    intro i
    have pos : 0 < mix gs.get c i := by rw [eq]; exact Nat.mul_pos ha (live i)
    obtain ⟨_,hm,hpos⟩ := List.sum_pos_iff_exists_pos_nat.mp pos
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
    exact ⟨j,Nat.pos_of_mul_pos_right hpos,
      PositiveWitness.maximal p c pulled j (Nat.pos_of_mul_pos_left hpos)⟩
  · intro all
    let c := PositiveWitness.witness p
    refine ⟨mix gs.get c,?_,?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl|hm
      · exact (s.pullback_iff _ _).mp (PositiveWitness.witness_holds p)
      · exact basis.sound _ ⟨_,rfl⟩ s hm
    · intro i
      obtain ⟨j,hg,hj⟩ := all i
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,
        Nat.mul_pos hg ((PositiveWitness.positive_iff_enabled p j).mpr hj)⟩

theorem covers_iff {rs : List (Row n)} {gs : List (Vec n)} (basis : ScaleCorrect rs gs) :
    coversCoordinates gs = true ↔ ∃ x, SystemHolds rs x ∧ ∀ i, 0 < x i := by
  simp only [coversCoordinates, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨mix gs.get (fun _ => 1),basis.sound _ ⟨_,rfl⟩,?_⟩
    intro i
    obtain ⟨v,mem,pos⟩ := h i
    obtain ⟨j,rfl⟩ := List.get_of_mem mem
    exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,by simpa using pos⟩
  · rintro ⟨x,sol,pos⟩ i
    obtain ⟨a,ha,c,hc⟩ := basis.complete x sol
    have live : 0 < mix gs.get c i := by rw [hc]; exact Nat.mul_pos ha (pos i)
    obtain ⟨t,mem,ht⟩ := List.sum_pos_iff_exists_pos_nat.mp live
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
    exact ⟨_,List.get_mem _ j,Nat.pos_of_mul_pos_right ht⟩

end Tamarin.ACBasis.Cone
