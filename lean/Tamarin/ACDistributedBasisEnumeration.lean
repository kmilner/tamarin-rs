import Tamarin.ACDistributedBasis
import Tamarin.ACWeightedBudget
import Tamarin.ACNeutralBasis
import TamarinRuntime.ACDistributedBasis

namespace Tamarin.ACBasis.Distributed
open ACFeasibility.ColumnQuotient
variable {n k : Nat}

private def heads (tail : Fin n → Fin k) (s : Fin k) (q : Nat) :=
  if ∃ i, tail i = s then List.range (q+1) else [q]

private theorem draw_cons (tag : Fin (n+1) → Fin k) (q : Vec k) :
    (plan (n+1) tag).draw q =
    (heads (fun i => tag i.succ) (tag 0) (q (tag 0))).flatMap fun h =>
      ((plan n (fun i => tag i.succ)).draw (spend q (tag 0) h)).map (prepend h) := by
  simp [plan,Plan.draw,heads]

private theorem absent (tag : Fin n → Fin k) {j : Fin k} (unused : ¬ ∃ i, tag i = j) (x : Vec n) :
    aggregate tag x j = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : j ≠ tag 0 := fun eq => unused ⟨0,eq.symm⟩
    simp [aggregate,h,ih (fun i => tag i.succ) (fun ⟨i,e⟩ => unused ⟨i.succ,e⟩)]

theorem mem_draw (tag : Fin n → Fin k) (q : Vec k) (x : Vec n) :
    x ∈ (plan n tag).draw q ↔ aggregate tag x = q := by
  induction n generalizing q with
  | zero =>
    have empty : x = Fin.elim0 := funext fun i => i.elim0
    simp only [plan,Plan.draw,aggregate]
    split <;> rename_i h
    · simp [empty,funext_iff,h]
    · simp only [List.not_mem_nil,false_iff,funext_iff]
      exact fun eq => h (fun i => (eq i).symm)
  | succ n ih =>
    let s := tag 0
    let tail := fun i : Fin n => tag i.succ
    let w := fun i : Fin n => x i.succ
    have split (t) : aggregate tag x t = (if t = s then x 0 else 0) + aggregate tail w t := rfl
    rw [draw_cons]
    simp only [List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨h,hm,u,hu,hx⟩
      have head : h = x 0 := congrFun hx 0
      have cut : u = w := funext fun i => congrFun hx i.succ
      have bound : h ≤ q s := by
        change h ∈ heads tail s (q s) at hm
        unfold heads at hm; split at hm <;> simp_all <;> omega
      have eq : aggregate tail u = spend q s h := (ih ..).mp hu
      funext t
      rw [split,←cut,eq,←head]
      by_cases e : t = s <;> simp [spend,e] <;> omega
    · intro eq
      have atS := congrFun eq s; rw [split] at atS; simp only [ite_true] at atS
      refine ⟨x 0,?_,w,(ih ..).mpr ?_,funext fun i => Fin.cases rfl (fun _ => rfl) i⟩
      · change x 0 ∈ heads tail s (q s)
        unfold heads; split
        · simp; omega
        · rename_i no; rw [absent _ no] at atS; simp_all
      · funext t
        change aggregate tail w t = spend q s (x 0) t
        have atT := congrFun eq t; rw [split] at atT
        by_cases e : t = s <;> simp [spend,e] at atT ⊢ <;> omega

theorem ordered_draw (tag : Fin n → Fin k) (q : Vec k) :
    ((plan n tag).draw q).Pairwise (fun x y => List.ofFn x < List.ofFn y) := by
  induction n generalizing q with
  | zero => simp only [plan,Plan.draw]; split <;> simp
  | succ n ih =>
    rw [draw_cons,List.pairwise_flatMap]
    constructor
    · intro h _; apply List.pairwise_map.mpr
      exact (ih _ _).imp (fun lt => by simpa [List.ofFn_succ] using lt)
    · have sorted (tail : Fin n → Fin k) (s) (w) : (heads tail s w).Pairwise (· < ·) := by
        unfold heads; split; exact List.pairwise_lt_range; simp
      apply (sorted ..).imp
      rintro a b lt u hu v hv
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hu; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv
      simp only [List.ofFn_succ,Fin.cases_zero,Fin.cases_succ]
      exact List.Lex.rel lt

theorem classify_correct (rs : List (Row n)) (reps : List (Fin n))
    (cover : ∀ i : Fin n, ∃ j : Fin reps.length, profile rs (reps.get j) = profile rs i) :
    ∃ v, classify rs reps = some v ∧ ∀ i : Fin n, profile rs (reps.get v[i]) = profile rs i := by
  let query (i : Fin n) := (List.finRange reps.length).find? (fun j => profile rs (reps.get j) == profile rs i)
  have found (i : Fin n) : (query i).isSome := by
    obtain ⟨j,h⟩ := cover i
    dsimp only [query]
    rw [List.isSome_find?]
    apply List.any_eq_true.mpr
    exact ⟨j,List.mem_finRange j,beq_iff_eq.mpr h⟩
  let ids := Vector.ofFn (fun i => (query i).get (found i))
  refine ⟨ids,?_,?_⟩
  · unfold classify
    simp only [List.getElem_toArray,List.getElem_map]
    split
    · simp [ids,query,List.get_eq_getElem]
    · rename_i bad
      apply False.elim; apply bad
      simpa [query,List.get_eq_getElem] using found
  · intro i
    have got := Option.some_get (found i)
    have h := List.find?_some (p := fun j : Fin reps.length => profile rs (reps.get j) == profile rs i) got.symm
    simpa [ids] using h

private def size (slots : Vector Nat k) (q : Vec k) :=
  ((List.finRange k).map fun j => WeightedComposition.ways slots[j] (q j)).prod

open WeightedComposition (ways)

private def slots (tag : Fin n → Fin k) (j : Fin k) := (List.ofFn tag).count j

private theorem sum_heads (tag : Fin n → Fin k) (s : Fin k) (q) :
    ((heads tag s q).map fun h => ways (slots tag s) (q-h)).sum = ways (slots tag s+1) q := by
  unfold heads; split
  · have rev : (List.range (q+1)).map (fun h => q-h) = (List.range (q+1)).reverse := by
      apply List.ext_getElem
      · simp
      · intro i hi hj; simp
    have h := congrArg (fun xs => (xs.map (ways (slots tag s))).sum) rev
    simpa [List.map_map,Function.comp_def,List.map_reverse,ways] using h
  · rename_i none
    have zero : slots tag s = 0 := by simp [slots,List.count_eq_zero,none]
    have one := WeightedComposition.waysWithin_exact 1 q 0 1 rfl
    rw [zero]
    change ways 0 (q-q) + 0 = ways 1 q
    rw [←one,Nat.sub_self]; rfl

private theorem prod_split (s : Fin k) (fn : Fin k → Nat) :
    ((List.finRange k).map fn).prod = fn s * (((List.finRange k).erase s).map fn).prod := by
  exact ((List.perm_cons_erase (List.mem_finRange s)).map fn).prod_nat

private theorem sum_mul (xs : List Nat) (f : Nat → Nat) (c) :
    (xs.map (fun x => f x*c)).sum = (xs.map f).sum*c := by
  induction xs <;> simp_all [Nat.add_mul]

/-- Exact fiber cardinality for arbitrary interleavings of the classes. -/
theorem draw_length (tag : Fin n → Fin k) (q : Vec k) :
    ((plan n tag).draw q).length = size (slotCounts tag) q := by
  simp [size,slotCounts]
  change _ = ((List.finRange k).map (fun j => ways (slots tag j) (q j))).prod
  induction n generalizing q with
  | zero =>
    simp only [plan,Plan.draw]
    by_cases h : ∀ i, q i = 0
    · simp [h,slots,ways,List.map_const',List.prod_replicate_nat]
    · have bad : ∃ i, q i ≠ 0 := Classical.not_forall.mp h
      obtain ⟨j,p⟩ := bad
      rw [prod_split j]
      simp [h,slots,ways,p]
  | succ n ih =>
    let s := tag 0
    let tail := fun i : Fin n => tag i.succ
    let rest := (List.finRange k).erase s
    let fixed := (rest.map fun t => ways (slots tail t) (q t)).prod
    have ne t (m : t ∈ rest) : t ≠ s := ((List.Nodup.mem_erase_iff (List.nodup_finRange k)).mp m).1
    have next (t : Fin k) : slots tag t = slots tail t + (if s = t then 1 else 0) := by
      simp [slots,tail,s,List.ofFn_succ,List.count_cons]
    have full : ((List.finRange k).map fun j => ways (slots tag j) (q j)).prod =
        ways (slots tail s+1) (q s)*fixed := by
      rw [prod_split s,next]
      simp only [ite_true]; apply congrArg (Nat.mul _)
      apply congrArg List.prod; apply List.map_inj_left.mpr; intro t ht
      rw [next,ite_eq_right (Ne.symm (ne t ht)),Nat.add_zero]
    have tails (h) : ((List.finRange k).map fun j => ways (slots tail j) (spend q s h j)).prod =
        ways (slots tail s) (q s-h)*fixed := by
      rw [prod_split s]
      simp only [spend,ite_true]; apply congrArg (Nat.mul _)
      apply congrArg List.prod; apply List.map_inj_left.mpr; intro t ht
      simp [ne t ht]
    rw [draw_cons,full]
    simp only [List.length_flatMap,List.length_map,ih]
    change ((heads tail s (q s)).map fun h => ((List.finRange k).map (fun j => ways (slots tail j) (spend q s h j))).prod).sum = _
    simp only [tails,sum_mul,sum_heads]

private theorem charge_exact (slots : Vector Nat k) (q : Vec k) (room left)
    (got : charge slots q room = some left) : left + size slots q = room := by
  unfold charge at got
  rw [Option.bind_eq_bind,Option.bind_eq_some_iff] at got
  obtain ⟨cs,run,finish⟩ := got
  have eq (js : List (Fin k)) (ws : List Nat)
      (h : js.mapM (fun j => WeightedComposition.waysWithin slots[j] (q j) room) = some ws) :
      ws = js.map fun j => WeightedComposition.ways slots[j] (q j) := by
    induction js generalizing ws with
    | nil => simpa using h.symm
    | cons j js ih =>
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨w,hw,vs,hs,rfl⟩ := h
      simp [WeightedComposition.waysWithin_exact _ _ _ _ hw,ih _ hs]
  rw [eq _ _ run] at finish
  change (do guard (size slots q ≤ room); pure (room-size slots q)) = some left at finish
  by_cases fits : size slots q ≤ room
  · simp [guard,fits] at finish
    omega
  · simp [guard,fits,failure] at finish

private theorem charge_fits (slots : Vector Nat k) (q : Vec k) (room)
    (each : ∀ j : Fin k, WeightedComposition.ways slots[j] (q j) ≤ room)
    (fits : size slots q ≤ room) : charge slots q room = some (room-size slots q) := by
  have eq (js : List (Fin k)) :
      js.mapM (fun j => WeightedComposition.waysWithin slots[j] (q j) room) =
        some (js.map (fun j => WeightedComposition.ways slots[j] (q j))) := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      rw [List.mapM_cons,WeightedComposition.waysWithin_some _ _ _ (each j),ih]
      rfl
  unfold charge
  rw [eq]
  change (do guard (size slots q ≤ room); pure (room-size slots q)) = some (room-size slots q)
  simp [fits,guard]

private def familySize (tag : Fin n → Fin k) (qs : List (Vec k)) :=
  (qs.map (size (slotCounts tag))).sum

/-- Input-only cardinality. The slot counts are taken directly from the
original coordinate-to-class map. -/
def allocations (tag : Fin n → Fin k) (qs : List (Vec k)) :=
  (qs.map fun q => ((List.finRange k).map (fun j => ways ((List.ofFn tag).count j) (q j))).prod).sum

private theorem familySize_eq (tag : Fin n → Fin k) (qs : List (Vec k)) :
    familySize tag qs = allocations tag qs := by
  unfold familySize allocations; apply congrArg List.sum; apply List.map_inj_left.mpr; intro q _
  simp [size,slotCounts]

private theorem each_le (tag : Fin n → Fin k) (covered : ∀ j, ∃ i, tag i = j)
    (q : Vec k) (j : Fin k) : ways (slotCounts tag)[j] (q j) ≤ size (slotCounts tag) q := by
  rw [size,prod_split j]
  have pos (t : Fin k) : 0 < ways (slotCounts tag)[t] (q t) := by
    have nonempty : 0 < (List.ofFn tag).count t := List.count_pos_iff.mpr
      (List.mem_ofFn.mpr (covered t))
    have positive k b : 0 < ways (k+1) b := by
      induction k generalizing b with
      | zero => rw [←WeightedComposition.waysWithin_exact 1 b 0 1 rfl]; decide
      | succ k ih =>
        unfold ways
        apply List.sum_pos_iff_exists_pos_nat.mpr
        exact ⟨_,List.mem_map.mpr ⟨0,by simp,rfl⟩,ih 0⟩
    simp only [slotCounts] ; simp
    obtain ⟨c,hc⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt nonempty)
    rw [hc]; exact positive c _
  have good := (List.prod_pos_iff_forall_pos_nat (l := (((List.finRange k).erase j).map
    (fun t => ways (slotCounts tag)[t] (q t))))).mpr (fun _ m => by
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp m; exact pos t)
  exact Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ good)

/-- Mathematical work floor. Allocation counts are products of weak
composition counts and sum over the supplied quotient basis. -/
def Within (tag : Fin n → Fin k) (qs : List (Vec k)) (limit : Nat) : Prop :=
  (n ≤ 64 ∧ k ≤ 64 ∧ limit ≤ 2048 ∧ qs.length ≤ 2048) ∧
  (∀ j, ∃ i, tag i = j) ∧ allocations tag qs ≤ limit

private theorem live_iff (tag : Fin n → Fin k) :
    (slotCounts tag).all (0 < ·) = true ↔ ∀ j, ∃ i, tag i = j := by
  simp [slotCounts,Vector.all_eq_true,List.count_pos_iff]
  exact ⟨fun h j => h j.val j.isLt,fun h j hj => h ⟨j,hj⟩⟩

theorem expand_complete (tag : Fin n → Fin k) (qs : List (Vec k)) {limit}
    (h : Within tag qs limit) : expand tag qs limit = some (qs.flatMap (plan n tag).draw) := by
  obtain ⟨ok,covered,enough⟩ := h
  rw [←familySize_eq] at enough
  have go (gs : List (Vec k)) (room) (fits : familySize tag gs ≤ room) :
      gs.foldlM (fun r q => charge (slotCounts tag) q r) room = some (room - familySize tag gs) := by
    induction gs generalizing room with
    | nil => simp [familySize]
    | cons g gs ih =>
      have sz : familySize tag (g::gs) = size (slotCounts tag) g + familySize tag gs := rfl
      rw [sz] at fits ⊢
      have cap : size (slotCounts tag) g ≤ room := by omega
      rw [List.foldlM_cons,charge_fits _ _ _ (fun j => Nat.le_trans (each_le tag covered g j) cap) cap]
      simp only [Option.bind_eq_bind,Option.bind_some]
      rw [ih _ (by omega),Nat.sub_sub]
  simp only [expand,guard,ok,(live_iff tag).mpr covered,and_self,ite_true,Option.pure_def,Option.bind_eq_bind,
    Option.bind_some,go _ _ enough]

theorem expand_spec (tag : Fin n → Fin k) (qs : List (Vec k)) {limit out}
    (got : expand tag qs limit = some out) :
    out = qs.flatMap (plan n tag).draw ∧ out.length ≤ limit ∧
      ∀ x, x ∈ out ↔ aggregate tag x ∈ qs := by
  have go (gs : List (Vec k)) (room left) (done : gs.foldlM (fun r q => charge (slotCounts tag) q r) room = some left) :
      left + familySize tag gs = room := by
    induction gs generalizing room with
    | nil => simp [familySize] at done ⊢; exact done.symm
    | cons g gs ih =>
      simp only [List.foldlM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff] at done
      obtain ⟨r,step,rest⟩ := done
      have h := charge_exact _ _ _ _ step
      have t := ih _ rest
      change left + (size (slotCounts tag) g + familySize tag gs) = room
      omega
  simp [expand,guard,Option.bind_eq_some_iff] at got
  obtain ⟨_,_,⟨left,done⟩,rfl⟩ := got
  refine ⟨rfl,?_,?_⟩
  · have bound := go qs limit left done
    simpa only [List.length_flatMap,draw_length,familySize] using (show familySize tag qs ≤ limit by omega)
  · intro x; simp only [List.mem_flatMap,mem_draw]
    exact ⟨fun ⟨_,m,e⟩ => e ▸ m,fun m => ⟨_,m,rfl⟩⟩

theorem expand_generators (rs : List (Row n)) (rep : Fin k → Fin n) (tag : Fin n → Fin k)
    (profiles : ∀ i, profile rs (rep (tag i)) = profile rs i) (qs : List (Vec k))
    (basis : ∀ q, q ∈ qs ↔ q ∈ generate (rs.map (restrict rep))) {limit out}
    (got : expand tag qs limit = some out) (x : Vec n) : x ∈ out ↔ x ∈ generate rs :=
  ((expand_spec tag qs got).2.2 x).trans ((basis _).trans (generate_iff rs rep tag profiles x).symm)

private theorem representatives_unique (rs : List (Row n)) :
    ((representatives rs).map (profile rs)).Nodup := by
  let key := profile rs
  have loop (xs : List (Fin n)) (seen : Std.HashSet Profile) (stored : List (Fin n))
      (inv : ∀ s ∈ stored, key s ∈ seen) (nd : (stored.map key).Nodup) :
      ((collect key xs seen stored).map key).Nodup := by
    induction xs generalizing seen stored with
    | nil => simp only [collect,List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr nd
    | cons x xs ih =>
      by_cases h : seen.contains (key x) = true <;> simp only [collect,h,ite_true]
      · exact ih _ _ inv nd
      · apply ih
        · intro s m
          rcases List.mem_cons.mp m with rfl | m
          · exact Std.HashSet.mem_insert_self
          · exact Std.HashSet.mem_insert.mpr (.inr (inv _ m))
        · rw [List.map_cons,List.nodup_cons]; refine ⟨?_,nd⟩
          rintro hm
          obtain ⟨s,m,eq⟩ := List.mem_map.mp hm
          exact h (Std.HashSet.contains_iff_mem.mpr (eq ▸ inv s m))
  exact loop _ ∅ [] (by simp) (by simp)

theorem layout (rs : List (Row n)) :
    ∃ cls, classify rs (representatives rs) = some cls ∧
      (∀ i : Fin n, profile rs ((representatives rs).get cls[i]) = profile rs i) ∧
        ∀ j : Fin (representatives rs).length, ∃ i : Fin n, cls[i] = j := by
  obtain ⟨cls,run,ok⟩ := classify_correct rs _ (covers rs)
  refine ⟨cls,run,ok,fun j => ⟨(representatives rs).get j,?_⟩⟩
  let i := (representatives rs).get j
  apply Fin.ext
  have h := representatives_unique rs
  have eq := ok i
  exact h.eq_of_getElem_eq (by simp) (by simp) (by simpa [List.get_eq_getElem,i] using eq)

private theorem flat_distinct (tag : Fin n → Fin k) (qs : List (Vec k)) (distinct : qs.Nodup) :
    (qs.flatMap (plan n tag).draw).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun q _ => (ordered_draw tag q).imp (fun {a b} lt eq => by
    subst b; exact List.lt_irrefl _ lt),?_⟩
  apply distinct.imp
  intro q p ne x mx y my eq
  subst y
  exact ne (((mem_draw ..).mp mx).symm.trans ((mem_draw ..).mp my))

theorem run_permutation (solve : {k : Nat} → List (Row k) → Option (List (Vec k)))
    (valid : ∀ {k : Nat} (rows : List (Row k)) gs, solve rows = some gs → gs.Perm (generate rows))
    (rs : List (Row n)) {limit out} (got : run solve rs limit = some out) :
    out.Perm (generate rs) ∧ out.length ≤ limit := by
  obtain ⟨cls,classified,profiles,_⟩ := layout rs
  simp [run,guard,Option.bind_eq_some_iff,classified] at got
  obtain ⟨_,_,gs,sol,hit⟩ := got
  let tag := fun i : Fin n => cls[i]
  have outSpec := expand_spec tag gs hit
  have quotPerm := valid _ _ sol
  have sourceDistinct := generate_distinct rs
  have quotDistinct := quotPerm.nodup_iff.mpr (generate_distinct _)
  refine ⟨(List.perm_ext_iff_of_nodup (outSpec.1 ▸ flat_distinct tag gs quotDistinct) sourceDistinct).mpr ?_,outSpec.2.1⟩
  intro x
  apply expand_generators rs (representatives rs).get tag profiles gs _ hit
  intro q
  simpa [projected,show (representatives rs).get =
    (fun j : Fin (representatives rs).length => (representatives rs)[j.val]) from rfl] using
    (quotPerm.mem_iff (a := q))

/-- Mandatory coverage uses the fixed deduplicated columns, unrestricted
reference generators and weak-composition counts. -/
def RunWithin (domain : {k : Nat} → List (Row k) → Prop) (rs : List (Row n)) (limit : Nat) : Prop :=
  let reps := reference rs
  (n ≤ 64 ∧ rs.length ≤ 64) ∧ reps.length < n ∧ domain (projected rs reps) ∧
    ∃ tag : Fin n → Fin reps.length, (∀ i, profile rs (reps.get (tag i)) = profile rs i) ∧
      Within tag (generate (projected rs reps)) limit

theorem run_complete (solve : {k : Nat} → List (Row k) → Option (List (Vec k)))
    (domain : {k : Nat} → List (Row k) → Prop)
    (complete : ∀ {k : Nat} (rows : List (Row k)), domain rows →
      ∃ gs, solve rows = some gs ∧ gs.Perm (generate rows))
    (rs : List (Row n)) (limit) (within : RunWithin domain rs limit) :
    (run solve rs limit).isSome := by
  unfold RunWithin at within
  rw [←representatives_eq] at within
  obtain ⟨bounds,reduces,allowed,tag,profiles,ok⟩ := within
  obtain ⟨cls,layoutEq,correct,_⟩ := layout rs
  have idx (i : Fin n) : cls[i] = tag i := by
    apply Fin.ext
    apply (representatives_unique rs).eq_of_getElem_eq (by simp) (by simp)
    simpa [List.get_eq_getElem] using (correct i).trans (profiles i).symm
  obtain ⟨gs,done,perm⟩ := complete _ allowed
  have sameSize := (perm.map (fun q => ((List.finRange _).map (fun j => ways ((List.ofFn tag).count j) (q j))).prod)).sum_nat
  obtain ⟨small,all,room⟩ := ok
  have fits : Within (fun i : Fin n => cls[i]) gs limit := by
    rw [funext idx]
    refine ⟨⟨small.1,small.2.1,small.2.2.1,perm.length_eq ▸ small.2.2.2⟩,all,?_⟩
    exact Nat.le_trans (Nat.le_of_eq sameSize) room
  have drawn := expand_complete _ _ fits
  unfold run
  simp only [guard,bounds,reduces,and_self,ite_true,Option.pure_def,Option.bind_eq_bind,Option.bind_some,
    layoutEq,done,drawn,Option.isSome_some]

section

private def interleaved : Fin 6 → Fin 3 := fun i => [0,1,0,2,1,2][i.val]'(by simp)
private def active : Vec 3 := fun j => [2,1,0][j.val]'(by simp)
private def neutral : Vec 3 := spike 2 1

/-- A two-copy repeated class with quota 2 and a two-copy repeated class
with quota 1 give six active distributions. The neutral class contributes
its two singleton vectors. Lowering the shared budget by one defers all. -/
theorem interleaved_active_neutral :
    ((expand interleaved [active,neutral] 8).map (List.map List.ofFn)) =
      some [[0,0,2,0,1,0],[0,1,2,0,0,0],[1,0,1,0,1,0],[1,1,1,0,0,0],
        [2,0,0,0,1,0],[2,1,0,0,0,0],[0,0,0,0,0,1],[0,0,0,1,0,0]] ∧
    (expand interleaved [active,neutral] 7).isNone := by
  have admit : Within interleaved [active,neutral] 8 := ⟨by decide,by decide,by decide⟩
  have rows := expand_complete _ _ admit
  constructor
  · rw [rows]; decide
  · cases short : expand interleaved [active,neutral] 7 with
    | none => rfl
    | some out =>
      obtain ⟨eq,cap,_⟩ := expand_spec _ _ short
      rw [eq] at cap
      have wide : ([active,neutral].flatMap (plan 6 interleaved).draw).length = 8 := by decide
      omega

end
end Tamarin.ACBasis.Distributed
