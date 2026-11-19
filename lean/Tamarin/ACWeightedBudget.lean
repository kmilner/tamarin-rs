import Tamarin.ACWeightedOrder

namespace Tamarin.ACBasis.WeightedComposition
variable {n : Nat}

/-- Number of weak compositions of q into k parts, by conditioning on the
sum allocated to all but one part. -/
def ways : Nat → Nat → Nat
  | 0, q => if q = 0 then 1 else 0
  | k+1, q => ((List.range (q+1)).map (ways k)).sum

private theorem ways_zero (k) : ways k 0 = 1 := by induction k <;> simp_all [ways]

private theorem ways_one (q) : ways 1 q = 1 := by
  induction q with
  | zero => exact ways_zero _
  | succ q ih =>
    change ((List.range (q+1+1)).map (ways 0)).sum = 1
    rw [List.range_succ,List.map_append,List.sum_append]
    change ways 1 q + _ = 1
    rw [ih]; simp [ways]

private theorem ways_succ (k q) : ways (k+1) (q+1) = ways (k+1) q + ways k (q+1) := by
  change ((List.range (q+1+1)).map (ways k)).sum = _
  rw [List.range_succ,List.map_append,List.sum_append]; simp [ways]

private theorem ways_pos (k q : Nat) : 0 < ways (k+1) q := by
  induction q with
  | zero => simp [ways_zero]
  | succ q ih => rw [ways_succ]; omega

private theorem ways_two (k q : Nat) : q+1 ≤ ways (k+2) q := by
  induction q with
  | zero => simp [ways_zero]
  | succ q ih => rw [ways_succ]; have := ways_pos k (q+1); change q+1 ≤ ways (k+1+1) q at ih; omega

private theorem cumulative_append (base : Nat) (xs ys : List Nat) :
    cumulative base (xs ++ ys) = cumulative base xs ++ cumulative (base+xs.sum) ys := by
  induction xs generalizing base with
  | nil => simp [cumulative]
  | cons x xs ih => simp [cumulative,ih,Nat.add_assoc]

private theorem counts_eq (q d : Nat) : counts q d = (List.range (q+1)).map (ways (d+1)) := by
  induction d with
  | zero => rw [show ways 1 = (fun _ => 1) from funext ways_one]; simp [counts,List.map_const']
  | succ d ih =>
    rw [counts,ih]
    clear ih
    induction q with
    | zero => simp [cumulative,ways_zero]
    | succ q h =>
      rw [List.range_succ,List.map_append,List.map_append,cumulative_append,h]
      simp only [List.append_cancel_left_eq,Nat.zero_add]
      exact congrArg (fun x => [x]) (ways_succ (d+1) q).symm

theorem waysWithin_some (k q budget : Nat) (bound : ways k q ≤ budget) :
    waysWithin k q budget = some (ways k q) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => simp [waysWithin,ways_one]
    | succ k =>
      have small : q < budget := by have le : q+1 ≤ ways (k+1+1) q := ways_two k q; omega
      simp [waysWithin,small,counts_eq,List.range_succ]

private theorem slots_succ (tag : Fin (n+1) → Side) (s) :
    slots tag s = slots (fun i : Fin n => tag i.succ) s + (if tag 0 = s then 1 else 0) := by
  simp [slots,List.ofFn_succ,List.count_cons]

private theorem slots_pos (tag : Fin n → Side) (s) : 0 < slots tag s ↔ ∃ i, tag i = s := by
  simp [slots,List.count_pos_iff]

private theorem ways_heads (tag : Fin n → Side) (s) (q : Nat) :
    ((heads tag s q).map (fun h => ways (slots tag s) (q-h))).sum = ways (slots tag s + 1) q := by
  unfold heads; split
  · have eq : (List.range (q+1)).map (fun h => q-h) = (List.range (q+1)).reverse := by
      apply List.ext_getElem
      · simp
      · intro i hi hj; simp
    have h := congrArg (fun xs => (xs.map (ways (slots tag s))).sum) eq
    simpa [List.map_map,Function.comp_def,List.map_reverse,ways] using h
  · rename_i none
    have z : slots tag s = 0 := by have : ¬0 < slots tag s := fun h => none ((slots_pos tag s).mp h); omega
    rw [z]; simp only [Nat.zero_add,ways_one,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.sub_self,Nat.add_zero]; rfl

def distributions (tag : Fin n → Side) (q : Quota) :=
  ways (slots tag .pos) (q .pos) * ways (slots tag .neg) (q .neg) * ways (slots tag .neutral) (q .neutral)

private theorem sum_scale (xs : List Nat) (f : Nat → Nat) (a) :
    (xs.map (fun x => a * f x)).sum = a*(xs.map f).sum := by
  induction xs <;> simp_all [Nat.mul_add]

theorem draw_length (tag : Fin n → Side) (q : Quota) : (draw n tag q).length = distributions tag q := by
  induction n generalizing q with
  | zero =>
    simp [draw_zero,slots,distributions,ways]
    split <;> rename_i h <;> by_cases hp : q .pos = 0 <;> by_cases hn : q .neg = 0 <;> by_cases hz : q .neutral = 0 <;> simp_all
  | succ n ih =>
    let tail i := tag (Fin.succ i)
    simp only [draw_succ,List.length_flatMap,List.length_map,ih]
    unfold distributions; simp only [slots_succ]
    cases tag 0 with
    | pos =>
      let f := fun t => ways (slots tail .pos) (q .pos - t)
      let m := ways (slots tail .neg) (q .neg) * ways (slots tail .neutral) (q .neutral)
      simp [spend]
      change ((heads tail .pos _).map (fun t => f t * _ * _)).sum = _
      rw [show (fun t => f t * ways (slots tail .neg) (q .neg) * ways (slots tail .neutral) (q .neutral)) =
        (fun t => m * f t) from funext fun t => by dsimp [m]; ac_rfl,sum_scale]
      dsimp [f,m]; rw [ways_heads]; ac_rfl
    | neg =>
      let f := fun t => ways (slots tail .neg) (q .neg - t)
      let m := ways (slots tail .pos) (q .pos) * ways (slots tail .neutral) (q .neutral)
      simp [spend]
      change ((heads tail .neg _).map (fun t => _ * f t * _)).sum = _
      rw [show (fun t => ways (slots tail .pos) (q .pos) * f t * ways (slots tail .neutral) (q .neutral)) =
        (fun t => m * f t) from funext fun t => by dsimp [m]; ac_rfl,sum_scale]
      dsimp [f,m]; rw [ways_heads]; ac_rfl
    | neutral =>
      let f := fun t => ways (slots tail .neutral) (q .neutral - t)
      let m := ways (slots tail .pos) (q .pos) * ways (slots tail .neg) (q .neg)
      simp [spend]
      change ((heads tail .neutral _).map (fun t => m * f t)).sum = _
      rw [sum_scale]; dsimp [f,m]; rw [ways_heads]

private theorem ways_unit (k : Nat) : ways k 1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [ways_zero,ih,Nat.add_comm] using ways_succ k 0

theorem enumerate_length (r : Row n) (a b : Nat) :
    (enumerate r a b).length =
      ways (slots (side r) .pos) (active a b .pos) * ways (slots (side r) .neg) (active a b .neg) +
        slots (side r) .neutral := by
  rw [enumerate_eq_merge]
  simp only [List.length_merge,draw_length,distributions]
  simp [active,singleton,ways_zero,ways_unit]

theorem waysWithin_exact (k q budget w : Nat) (h : waysWithin k q budget = some w) :
    w = ways k q := by
  cases k with
  | zero => exact (Option.some.inj h).symm
  | succ k =>
    cases k with
    | zero => simpa [waysWithin,ways_one,eq_comm] using h
    | succ k =>
      change (if q < budget then (counts q (k+1)).getLast? else none) = some w at h
      split at h
      · simpa [counts_eq,List.range_succ,eq_comm] using h
      · contradiction

/-- Independent admission floor in terms of the mathematical number of weak
compositions. Its weights, side counts and quotas are read from the original
row; no executable classifier, bound or generator is used. -/
def Within (r : Row n) : Prop :=
  let a := (List.ofFn r.pos).foldr max 0
  let b := (List.ofFn r.neg).foldr max 0
  let P := ways (List.ofFn (fun i => if 0 < r.pos i then 1 else 0)).sum (b / a.gcd b)
  let N := ways (List.ofFn (fun i => if 0 < r.neg i then 1 else 0)).sum (a / a.gcd b)
  let Z := (List.ofFn (fun i => if r.pos i = 0 ∧ r.neg i = 0 then 1 else 0)).sum
  n ≤ 64 ∧ Uniform r a b ∧ b / a.gcd b < 2^128 ∧ a / a.gcd b < 2^128 ∧
    P ≤ 2048 ∧ N ≤ 2048 ∧ P*N + Z ≤ 2048

private theorem slots_sum (tag : Fin n → Side) (s) :
    slots tag s = (List.ofFn fun i => if tag i = s then 1 else 0).sum := by
  induction n with
  | zero => simp [slots]
  | succ n ih => rw [slots_succ,ih,List.ofFn_succ,List.sum_cons,Nat.add_comm]

private theorem observed (r : Row n) :
    slots (side r) .pos = (List.ofFn fun i => if 0 < r.pos i then 1 else 0).sum ∧
    slots (side r) .neg = (List.ofFn fun i => if 0 < r.neg i then 1 else 0).sum ∧
    slots (side r) .neutral = (List.ofFn fun i => if r.pos i = 0 ∧ r.neg i = 0 then 1 else 0).sum := by
  simp only [slots_sum]
  constructor
  · congr 2; funext i; by_cases p : 0 < r.pos i <;> by_cases q : 0 < r.neg i <;> simp [side,p,q]
  constructor <;> congr 2 <;> funext i <;> have dj := r.disjoint i <;>
    by_cases p : 0 < r.pos i <;> by_cases q : 0 < r.neg i <;> simp [side,p,q] <;> omega

theorem candidate_complete (r : Row n) (h : Within r) : (candidate r).isSome := by
  obtain ⟨width,uniform,left,right,p,q,budget⟩ := h
  obtain ⟨pc,nc,zc⟩ := observed r
  rw [←pc] at p budget; rw [←nc] at q budget; rw [←zc] at budget
  let a := magnitude r.pos; let b := magnitude r.neg
  change Uniform r a b at uniform
  change active a b .pos < _ at left; change active a b .neg < _ at right
  change ways _ (active a b .pos) ≤ _ at p; change ways _ (active a b .neg) ≤ _ at q
  change ways _ (active a b .pos) * ways _ (active a b .neg) + _ ≤ _ at budget
  dsimp only [a,b] at *
  have pfit := waysWithin_some _ _ _ p
  have nfit := waysWithin_some _ _ _ q
  change 0 < _ ∧ 0 < _ ∧ (∀ i, r.pos i = 0 ∨ r.pos i = _) ∧ ∀ i, r.neg i = 0 ∨ r.neg i = _ at uniform
  simp [candidate,width,uniform,left,right,pfit,nfit,budget,guard]

theorem candidate_spec (r : Row n) {xs : List (Vec n)} (h : candidate r = some xs) :
    Uniform r (magnitude r.pos) (magnitude r.neg) ∧ xs = enumerate r (magnitude r.pos) (magnitude r.neg) ∧
    xs.length ≤ 2048 := by
  simp only [candidate,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨_,_,u,un,_,_,v,hv,w,hw,_,bd,last⟩ := h
  have ok : Uniform r (magnitude r.pos) (magnitude r.neg) := by
    apply Classical.byContradiction; intro hu
    unfold Uniform at hu; simp [hu,guard] at un
  obtain rfl := Option.some.inj last
  refine ⟨ok,rfl,?_⟩
  rw [enumerate_length,←waysWithin_exact _ _ _ _ hv,←waysWithin_exact _ _ _ _ hw]
  apply Classical.byContradiction; intro ng; simp [ng,guard] at bd

theorem candidate_lift {k} (r : Row k) {xs : List (Vec k)} (run : candidate r = some xs)
    (g : Fin k → Vec n) (live : ∀ i, ∃ j, 0 < g i j) :
    minimize (lift g xs) = minimize (lift g r.generators) := by
  obtain ⟨u,rfl,_⟩ := candidate_spec r run
  exact minimize_lift r u g live

end Tamarin.ACBasis.WeightedComposition
