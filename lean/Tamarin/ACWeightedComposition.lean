import TamarinRuntime.ACWeightedComposition
import Tamarin.ACCompactBasis

namespace Tamarin.ACBasis.WeightedComposition
variable {n : Nat}

def Uniform (r : Row n) (a b : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ (∀ i, r.pos i = 0 ∨ r.pos i = a) ∧ ∀ i, r.neg i = 0 ∨ r.neg i = b

def mask (tag : Fin n → Side) (s : Side) (v : Vec n) : Vec n := fun i => if tag i = s then v i else 0

def mass (tag : Fin n → Side) (s : Side) (v : Vec n) := total (mask tag s v)

def Meets (tag : Fin n → Side) (q : Quota) (v : Vec n) := ∀ s, mass tag s v = q s

private theorem select (stock : Vec n) (k : Nat) (enough : k ≤ total stock) :
    ∃ y : Vec n, total y = k ∧ ∀ i, y i ≤ stock i := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa [total] using enough
    exact ⟨stock,by simp [total,this],fun _ => Nat.le_refl _⟩
  | succ n ih =>
    let h := min (stock 0) k
    let tail := fun i : Fin n => stock i.succ
    have sum : total stock = stock 0 + total tail := by simp [total,tail,List.ofFn_succ]
    obtain ⟨v,hv,bound⟩ := ih tail (k-h) (by dsimp [h]; omega)
    refine ⟨Fin.cases h v,?_,fun i => Fin.cases (Nat.min_le_left ..) bound i⟩
    simp only [total,List.ofFn_succ,List.sum_cons,Fin.cases_zero,Fin.cases_succ]
    change h + total v = k
    rw [hv]; dsimp [h]; omega

private theorem sum_mul (a : Nat) (v : Vec n) : total (fun i => a * v i) = a * total v := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total,List.ofFn_succ,List.sum_cons,Nat.mul_add]
    exact congrArg (a * v 0 + ·) (ih (fun i => v i.succ))

theorem holds_iff (r : Row n) {a b} (u : Uniform r a b) (x : Vec n) :
    r.Holds x ↔ a * mass (side r) .pos x = b * mass (side r) .neg x := by
  obtain ⟨ha,hb,pa,pb⟩ := u
  have eqp (i) : r.pos i = if side r i = .pos then a else 0 := by
    rcases pa i with h|h <;> rcases pb i with h'|h' <;> simp [side,h,h',ha,hb]
  have eqn (i) : r.neg i = if side r i = .neg then b else 0 := by
    have dj := r.disjoint i
    rcases pa i with h|h <;> rcases pb i with h'|h' <;> simp [side,h,h',ha,hb] <;> omega
  have factor (f : Vec n) (s : Side) (w : Nat) (eq : ∀ i, f i = if side r i = s then w else 0) :
      dot f x = w * mass (side r) s x := by
    unfold dot mass; rw [←sum_mul]; congr 1; funext i
    rw [eq]; by_cases h : side r i = s <;> simp [mask,h]
  rw [Row.Holds,factor _ _ _ eqp,factor _ _ _ eqn]

private theorem ratios {a b x y : Nat} (ha : 0 < a) (hb : 0 < b) :
    a*x = b*y ↔ ∃ t, x = (b/a.gcd b)*t ∧ y = (a/a.gcd b)*t := by
  let d := a.gcd b
  let A := a/d
  let B := b/d
  have da : d*A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have db : d*B = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  have hB : 0 < B := Nat.pos_of_mul_pos_left (db.symm ▸ hb)
  have balance : a*x = b*y ↔ A*x = B*y := by
    rw [←da,←db,Nat.mul_assoc,Nat.mul_assoc,Nat.mul_right_inj (Nat.ne_of_gt hd)]
  rw [balance]
  constructor
  · intro h
    have rel : B.gcd A = 1 := (Nat.gcd_comm ..).trans (Nat.gcd_div_gcd_div_gcd_of_pos_left ha)
    have div : B ∣ x := by
      have z : B ∣ A*x := h ▸ Nat.dvd_mul_right .. 
      simpa [rel] using (Nat.dvd_gcd_mul_iff_dvd_mul.mpr z)
    obtain ⟨t,rfl⟩ := div
    refine ⟨t,rfl, Nat.mul_left_cancel hB ?_⟩
    change B*y = B*(A*t); rw [←h]; ac_rfl
  · rintro ⟨t,rfl,rfl⟩; change A*(B*t) = B*(A*t); ac_rfl

private theorem choose_below (tag : Fin n → Side) (q : Quota) (v : Vec n)
    (enough : ∀ s, q s ≤ mass tag s v) : ∃ y, Meets tag q y ∧ ∀ i, y i ≤ v i := by
  have sel (s) := select (mask tag s v) (q s) (enough s)
  let picks s := (sel s).choose
  have eq s : total (picks s) = q s := (sel s).choose_spec.1
  have down s : ∀ i, picks s i ≤ mask tag s v i := (sel s).choose_spec.2
  let y i := picks (tag i) i
  refine ⟨y,?_,fun i => by simpa [y,mask] using down (tag i) i⟩
  intro s; rw [←eq s]; unfold mass; congr 1; funext i
  by_cases h : tag i = s
  · simp [mask,h,y]
  · have bd := down s i; simp [mask,h] at bd; simp [mask,h,bd]

private theorem sum_le {x y : Vec n} (h : ∀ i, x i ≤ y i) : total x ≤ total y := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simpa only [total,List.ofFn_succ,List.sum_cons] using
      Nat.add_le_add (h 0) (ih (fun i => h i.succ))

private theorem masses_le {x y : Vec n} (tag : Fin n → Side) (h : ∀ i, x i ≤ y i) (s) :
    mass tag s x ≤ mass tag s y := sum_le fun i => by by_cases e : tag i = s <;> simp [mask,e,h]

private theorem equal_of_below {x y : Vec n} (tag : Fin n → Side) (below : ∀ i, x i ≤ y i)
    (eq : ∀ s, mass tag s x = mass tag s y) : x = y := by
  funext i
  let s := tag i
  let delta := fun k => mask tag s y k - mask tag s x k
  have add : mask tag s y = fun k => mask tag s x k + delta k := by
    funext k; have le : mask tag s x k ≤ mask tag s y k := by by_cases h : tag k = s <;> simp [mask,h,below]
    exact (Nat.add_sub_of_le le).symm
  have he := eq s; unfold mass at he; rw [add,total_add] at he
  have z : total delta = 0 := by omega
  have hz := List.sum_eq_zero_iff_forall_eq_nat.mp z _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  simp [delta,mask,s] at hz
  exact Nat.le_antisymm (below i) (by omega)

private theorem mass_pos {x : Vec n} (tag : Fin n → Side) (s : Side) :
    0 < mass tag s x ↔ ∃ i, tag i = s ∧ 0 < x i := by
  rw [mass,total,List.sum_pos_iff_exists_pos_nat]
  simp only [List.mem_ofFn]; constructor
  · rintro ⟨_,⟨i,rfl⟩,hp⟩
    by_cases h : tag i = s <;> simp_all [mask]
    exact ⟨i,h,hp⟩
  · rintro ⟨i,hi,hp⟩; exact ⟨_,⟨i,rfl⟩,by simpa [mask,hi] using hp⟩

theorem meets_singleton_iff (tag : Fin n → Side) (v : Vec n) :
    Meets tag singleton v ↔ ∃ i, tag i = .neutral ∧ v = spike i 1 := by
  have spike_mass (i : Fin n) (t : Side) :
      mass tag t (spike i 1) = if tag i = t then 1 else 0 := by
    let weight : Vec n := fun j => if tag j = t then 1 else 0
    have em : mass tag t (spike i 1) = dot weight (spike i 1) := by
      unfold mass dot; congr 1; funext j
      by_cases h : tag j = t <;> simp [mask,weight,h]
    rw [em,dot_spike]; simp [weight]
  constructor
  · intro h
    obtain ⟨i,hi,pos⟩ := (mass_pos tag .neutral).mp (show 0 < mass tag .neutral v by rw [h]; decide)
    refine ⟨i,hi,Eq.symm (equal_of_below tag ?_ ?_)⟩
    · intro j; by_cases e : j = i <;> simp [spike,e] <;> exact pos
    · intro t; rw [h,spike_mass,hi]; cases t <;> rfl
  · rintro ⟨i,hi,rfl⟩ t
    rw [spike_mass,hi]; cases t <;> rfl

private theorem quotas_pos {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    0 < active a b .pos ∧ 0 < active a b .neg := by
  exact ⟨Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right ..)) (Nat.gcd_pos_of_pos_left _ ha),
    Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ ha)⟩

def Primitive (r : Row n) (a b : Nat) (v : Vec n) :=
  Meets (side r) (active a b) v ∨ Meets (side r) singleton v

private theorem primitive_sol (r : Row n) {a b} (u : Uniform r a b) {v} (prim : Primitive r a b v) :
    r.Holds v ∧ ∃ i, 0 < v i := by
  have ⟨qp,qn⟩ := quotas_pos u.1 u.2.1
  rw [holds_iff r u,ratios u.1 u.2.1]
  rcases prim with h|h
  · refine ⟨⟨1,by simp [h .pos,h .neg,active]⟩,?_⟩
    obtain ⟨i,_,hi⟩ := (mass_pos _ _).mp ((h .pos).symm ▸ qp)
    exact ⟨i,hi⟩
  · refine ⟨⟨0,by simp [h .pos,h .neg,singleton]⟩,?_⟩
    obtain ⟨i,_,hi⟩ := (mass_pos _ _).mp (show 0 < mass _ _ v by rw [h .neutral]; decide)
    exact ⟨i,hi⟩

theorem dominated (r : Row n) {a b} (u : Uniform r a b) {v} (sol : r.Holds v) (nz : ∃ i, 0 < v i) :
    ∃ y, Primitive r a b y ∧ ∀ i, y i ≤ v i := by
  let tag := side r
  by_cases neutral : 0 < mass tag .neutral v
  · obtain ⟨y,h,le⟩ := choose_below tag singleton v (fun s => by cases s <;> first | exact neutral | exact Nat.zero_le _)
    exact ⟨y,.inr h,le⟩
  obtain ⟨t,hp,hn⟩ := (ratios u.1 u.2.1).mp ((holds_iff r u v).mp sol)
  have ht : 0 < t := by
    obtain ⟨i,hi⟩ := nz
    have live := (mass_pos tag (tag i)).mpr ⟨i,rfl,hi⟩
    cases h : tag i <;> rw [h] at live
    · change 0 < mass (side r) .pos v at live; cases t <;> simp_all
    · change 0 < mass (side r) .neg v at live; cases t <;> simp_all
    · contradiction
  obtain ⟨y,h,le⟩ := choose_below tag (active a b) v (fun s => by
    cases s with
    | neutral => exact Nat.zero_le _
    | pos => exact hp ▸ (by simpa [active] using Nat.mul_le_mul_left (b / a.gcd b) ht)
    | neg => exact hn ▸ (by simpa [active] using Nat.mul_le_mul_left (a / a.gcd b) ht))
  exact ⟨y,.inl h,le⟩

theorem primitive_iff (r : Row n) {a b} (u : Uniform r a b) (v : Vec n) :
    Primitive r a b v ↔ Irreducible [r] v := by
  constructor
  · intro p
    obtain ⟨sol,nz⟩ := primitive_sol r u p
    refine ⟨by simpa [SystemHolds] using sol,nz,?_⟩
    intro y hy live below
    obtain ⟨z,prim,small⟩ := dominated r u (hy _ List.mem_cons_self) live
    have le (s) := masses_le (side r) (fun i => Nat.le_trans (small i) (below i)) s
    have ⟨pos,_⟩ := quotas_pos u.1 u.2.1
    have equal : z = v := by
      apply equal_of_below (side r) (fun i => Nat.le_trans (small i) (below i))
      rcases prim with h|h <;> rcases p with hv|hv
      · intro s; rw [h s,hv s]
      · have := le .pos; rw [h .pos,hv .pos] at this; change _ ≤ 0 at this; omega
      · have := le .neutral; rw [h .neutral,hv .neutral] at this; contradiction
      · intro s; rw [h s,hv s]
    exact funext fun i => Nat.le_antisymm (below i) (equal ▸ small i)
  · intro h
    obtain ⟨y,p,le⟩ := dominated r u (h.1 _ List.mem_cons_self) h.2.1
    obtain ⟨sol,nz⟩ := primitive_sol r u p
    exact h.2.2 y (by simpa [SystemHolds] using sol) nz le ▸ p

end Tamarin.ACBasis.WeightedComposition
