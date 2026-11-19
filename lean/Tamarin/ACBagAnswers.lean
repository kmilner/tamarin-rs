import TamarinRuntime.ACBagAnswers
import Tamarin.ACBagSearch

namespace Tamarin.Matching.ACBagAnswers
open ACBags ACBagSearch

def keys (rows : Rows) := (rows.flatMap Prod.fst).eraseDups
abbrev atoms (rows : Rows) := (rows.flatMap Prod.snd).eraseDups

private theorem usedKeys (rows : Rows) : Keys rows (keys rows) := by
  intro k; simp [keys,List.mem_eraseDups,List.mem_flatMap]

private theorem usedAtoms (rows : Rows) (a) : a ∈ atoms rows ↔ ∃ r ∈ rows, a ∈ r.2 := by
  simp [atoms,List.mem_eraseDups,List.mem_flatMap]

private theorem mem_choices {rows : Rows} {a col} :
    col ∈ choices rows (keys rows) a ↔ ∃ v, Balanced rows a v ∧ (keys rows).map v = col := by
  constructor
  · intro h
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp h)
    exact ⟨v,balancedColumns_sound hv,rfl⟩
  · rintro ⟨v,h,rfl⟩
    obtain ⟨u,hu,eq⟩ := balancedColumns_cover (usedKeys rows) a v h
    exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨u,hu,List.map_congr_left eq⟩)

theorem atKey_map {α : Type} (ks : List UInt64) (f : UInt64 → α) (fallback : α)
    {k : UInt64} (hk : k ∈ ks) : atKey ks (ks.map f) fallback k = f k := by
  have h := List.idxOf_lt_length_of_mem hk
  simp [atKey,List.getElem?_map,List.getElem?_eq_getElem h,List.getElem_idxOf h]

def batch (rs : Rows) (as : List UInt64) : Batch :=
  as.map fun a => (a,choices rs (keys rs) a)

private def selected (ks as : List UInt64) (w : UInt64 → Column) : Pick :=
  as.map fun a => (a,ks.map (w a))

private theorem product_covers {rows : Rows} (as : List UInt64) (w : UInt64 → Column)
    (good : ∀ a ∈ as, Balanced rows a (w a)) :
    selected (keys rows) as w ∈ product (batch rows as) := by
  induction as with
  | nil => exact List.mem_cons_self
  | cons a as ih =>
    exact List.mem_flatMap.mpr ⟨_,mem_choices.mpr ⟨w a,good a List.mem_cons_self,rfl⟩,
      List.mem_map.mpr ⟨_,ih (fun b hb => good b (List.mem_cons_of_mem _ hb)),rfl⟩⟩

private theorem product_sound {rows : Rows} (as : List UInt64) (nd : as.Nodup)
    (p : Pick) (hp : p ∈ product (batch rows as)) :
    ∃ w : UInt64 → Column, (∀ a ∈ as, Balanced rows a (w a)) ∧ p = selected (keys rows) as w := by
  induction as generalizing p with
  | nil =>
    obtain rfl : p = [] := by simpa [product,batch] using hp
    exact ⟨fun _ _ => 0,by simp,rfl⟩
  | cons a as ih =>
    obtain ⟨col,mem,z⟩ := List.mem_flatMap.mp hp
    obtain ⟨v,good,rfl⟩ := mem_choices.mp mem
    obtain ⟨past,hm,rfl⟩ := List.mem_map.mp z
    obtain ⟨u,ok,rfl⟩ := ih nd.tail past hm
    let w (b) := if b = a then v else u b
    have other b (hb : b ∈ as) : w b = u b := by
      have ne : b ≠ a := fun h => (List.nodup_cons.mp nd).1 (h ▸ hb)
      simp [w,ne]
    refine ⟨w,?_,?_⟩
    · rw [List.forall_mem_cons]
      exact ⟨by simpa [w] using good,fun b hb => other b hb ▸ ok b hb⟩
    · simp only [selected,List.map_cons]
      have left : w a = v := by simp [w]
      rw [left]
      congr 1
      apply List.map_congr_left; intro b hb; rw [other b hb]

private def bag (as : List UInt64) (w : UInt64 → Column) (k : UInt64) :=
  as.flatMap fun a => List.replicate (w a k) a

private theorem flatCongr {α β} {l : List α} {f g : α → List β} (h : ∀ k ∈ l, f k = g k) :
    l.flatMap f = l.flatMap g := congrArg List.flatten (List.map_congr_left h)

private theorem emit (ks as : List UInt64) (w : UInt64 → Column) :
    materialize ks (selected ks as w) = ks.map (bag as w) := by
  apply List.map_congr_left
  intro k hk
  simp only [selected,List.flatMap_map,bag]
  apply flatCongr
  intro a _
  rw [atKey_map _ _ _ hk]

private theorem replay {rows : Rows} (w : UInt64 → Column)
    (ok : ∀ a ∈ atoms rows, Balanced rows a (w a)) (r) (hr : r ∈ rows) :
    (r.1.flatMap (bag (atoms rows) w)).Perm r.2 := by
  apply List.perm_iff_count.mpr; intro a
  rw [countExpanded]
  have co (k a) : (bag (atoms rows) w k).count a = if a ∈ atoms rows then w a k else 0 :=
    countBag (fun b => w b k) a (atoms rows) (dedup_distinct _)
  by_cases ha : a ∈ atoms rows
  · simp only [co,ite_eq_left ha]; exact ok a ha r hr
  · have absent : a ∉ r.2 := fun h => ha ((usedAtoms rows a).2 ⟨r,hr,h⟩)
    simp only [co,ite_eq_right ha,List.count_eq_zero.mpr absent]
    generalize r.1 = ks
    induction ks with
    | nil => rfl
    | cons _ _ ih => simpa only [List.map_cons,List.sum_cons,Nat.zero_add] using ih

private theorem realize {rows : Rows} (image : UInt64 → List UInt64) (sol : Solution rows image)
    {k : UInt64} (hk : k ∈ keys rows) :
    (image k).Perm (bag (atoms rows) (fun a k => (image k).count a) k) := by
  obtain ⟨r,hr,used⟩ := (usedKeys rows k).1 hk
  apply List.perm_iff_count.mpr; intro a
  rw [bag,countBag (fun b => (image k).count b) a (atoms rows) (dedup_distinct _)]
  by_cases ha : a ∈ atoms rows
  · simp [ha]
  · have absent : a ∉ image k := fun h => ha ((usedAtoms rows a).2 ⟨r,hr,
      (sol.2 r hr).subset (List.mem_flatMap.mpr ⟨k,used,h⟩)⟩)
    simp [ha,List.count_eq_zero.mpr absent]

theorem exact_family (rows : Rows) :
    Complete rows ((family (keys rows) (batch rows (atoms rows))).map (decode (keys rows))) := by
  constructor
  · intro arm ha
    obtain ⟨raw,h,rfl⟩ := List.mem_map.mp ha
    obtain ⟨gen,nonempty⟩ := List.mem_filter.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp gen
    obtain ⟨w,good,rfl⟩ := product_sound (atoms rows) (dedup_distinct _) p hp
    rw [emit] at nonempty ⊢
    have read {k} (hk : k ∈ keys rows) : decode (keys rows) ((keys rows).map (bag (atoms rows) w)) k =
        bag (atoms rows) w k := atKey_map _ _ _ hk
    refine ⟨?_,?_⟩
    · intro r hr k hk
      have used := (usedKeys rows k).2 ⟨r,hr,hk⟩
      rw [read used]
      simpa using List.all_eq_true.mp nonempty _ (List.mem_map_of_mem (f := bag (atoms rows) w) used)
    · intro r hr
      have eq := flatCongr (l := r.1) (fun k hk => read ((usedKeys rows k).2 ⟨r,hr,hk⟩))
      exact eq ▸ replay w good r hr
  · intro image sol
    let w (a k : UInt64) := (image k).count a
    have ok (a) (_ : a ∈ atoms rows) : Balanced rows a (w a) := by
      intro r hr; exact (countExpanded r.1 image a).symm.trans ((sol.2 r hr).count_eq a)
    let arm := (keys rows).map (bag (atoms rows) w)
    have mem : arm ∈ family (keys rows) (batch rows (atoms rows)) := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨_,product_covers _ w ok,emit ..⟩,?_⟩
      apply List.all_eq_true.mpr
      intro b hb
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
      obtain ⟨r,hr,used⟩ := (usedKeys rows k).1 hk
      have perm := realize image sol hk
      have nz := sol.1 r hr k used
      simpa using (show bag (atoms rows) w k ≠ [] from fun h => nz (List.perm_nil.mp (h ▸ perm)))
    refine ⟨_,List.mem_map_of_mem (f := decode (keys rows)) mem,?_⟩
    intro r hr k hk
    have used := (usedKeys rows k).2 ⟨r,hr,hk⟩
    change (image k).Perm (atKey (keys rows) ((keys rows).map (bag (atoms rows) w)) [] k)
    rw [atKey_map _ _ _ used]
    exact realize image sol used

theorem product_size (layers : Batch) :
    (product layers).length = (layers.map (fun entry => entry.2.length)).prod := by
  induction layers with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨a,cols⟩ := entry
    simp only [product,List.length_flatMap,List.length_map,List.map_const',
      List.sum_replicate_nat,ih,List.map_cons,List.prod_cons]

private theorem family_of_run {rows : Rows} {out : List Arm} (done : run rows = some out) :
    out = family (keys rows) (batch rows (atoms rows)) := by
  cases hi : inventories rows with
  | none => simp [run,hi] at done
  | some ctx =>
    rw [inventories_eq hi] at hi
    have returned : collect rows (keys rows) (atoms rows) = some out := by simpa [run,hi,keys] using done
    dsimp only [collect] at returned
    split at returned
    · rename_i zero
      have nil := List.length_eq_zero_iff.mp ((product_size (batch rows (atoms rows))).trans zero)
      cases returned
      simp [family,nil]
    · split at returned
      · exact (Option.some.inj returned).symm
      · contradiction

private theorem subset_mass {ks raw : List UInt64} (distinct : ks.Nodup) (sub : ks ⊆ raw)
    (im : UInt64 → List UInt64) : (ks.flatMap im).length ≤ (raw.flatMap im).length := by
  induction ks generalizing raw with
  | nil => exact Nat.zero_le _
  | cons k ks ih =>
    have perm := List.perm_cons_erase (sub List.mem_cons_self)
    have rest : ks ⊆ raw.erase k := by
      intro j hj
      have hit := List.mem_cons.mp (perm.mem_iff.mp (sub (List.mem_cons_of_mem k hj)))
      exact hit.resolve_left (fun h => (List.nodup_cons.mp distinct).1 (h ▸ hj))
    rw [(perm.flatMap_right im).length_eq]
    simpa only [List.flatMap_cons,List.length_append,Nat.add_le_add_iff_left] using ih distinct.tail rest

/-- Each generated capture is used in at least one equation. Consequently
even a raw pick discarded for leaving another capture empty expands to no
more factor occurrences than are present in the submitted target rows. -/
theorem pick_mass {rows : Rows} {pick : Pick} (mem : pick ∈ product (batch rows (atoms rows))) :
    ((materialize (keys rows) pick).map List.length).sum ≤ (rows.map fun r => r.2.length).sum := by
  obtain ⟨w,balanced,rfl⟩ := product_sound (atoms rows) (dedup_distinct _) pick mem
  let im := bag (atoms rows) w
  have domain : keys rows ⊆ rows.flatMap Prod.fst := fun _ hk => List.mem_eraseDups.mp hk
  have upper := subset_mass (dedup_distinct _) domain im
  have targets : ((rows.flatMap Prod.fst).flatMap im).length = (rows.map fun r => r.2.length).sum := by
    rw [List.flatMap_assoc,List.length_flatMap]
    exact congrArg List.sum (List.map_congr_left fun r hr => (replay w balanced r hr).length_eq)
  rw [emit,List.map_map]
  simpa only [targets,List.length_flatMap,Function.comp_def,keys,im] using upper

theorem arm_mass {rows : Rows} {out : List Arm} (h : run rows = some out) {arm} (mem : arm ∈ out) :
    (arm.map List.length).sum ≤ (rows.map fun r => r.2.length).sum := by
  rw [family_of_run h] at mem
  obtain ⟨appears,_⟩ := List.mem_filter.mp mem
  obtain ⟨pick,inProduct,rfl⟩ := List.mem_map.mp appears
  exact pick_mass inProduct

/-- The lists of count vectors here are upper bounds on mathematical solutions
of each individual factor column. They may include extra vectors. In particular,
a unique column per factor permits one arm no matter how many factors occur. -/
def Within (rows : Rows) : Prop :=
  ACBagSearch.Within rows ∧ ∃ upper : UInt64 → List (List Nat),
  (∀ a ∈ (rows.flatMap Prod.snd).eraseDups, ∀ v, Balanced rows a v → (keys rows).map v ∈ upper a) ∧
  (let n := ((rows.flatMap Prod.snd).eraseDups.map fun a => (upper a).length).prod
   n ≤ 4096 ∧ n * (1 + (keys rows).length * (1 + (rows.flatMap Prod.snd).eraseDups.length) +
      (rows.map fun r => r.2.length).sum) ≤ 65536)

theorem Within.of_determined {rows : Rows} (valid : ACBagSearch.Within rows)
    (profile : UInt64 → List Nat)
    (unique : ∀ a ∈ (rows.flatMap Prod.snd).eraseDups, ∀ v, Balanced rows a v → (keys rows).map v = profile a)
    (room : 1 + (keys rows).length * (1 + (rows.flatMap Prod.snd).eraseDups.length) +
      (rows.map fun r => r.2.length).sum ≤ 65536) : Within rows := by
  refine ⟨valid,fun a => [profile a],?_,?_⟩
  · intro a ha v ok; simp [unique a ha v ok]
  · simpa [List.map_const',List.prod_replicate_nat] using room

theorem Within.of_unique {rows : Rows} (valid : ACBagSearch.Within rows)
    (determined : ∀ a ∈ (rows.flatMap Prod.snd).eraseDups, ∀ u v, Balanced rows a u → Balanced rows a v →
      ∀ k ∈ keys rows, u k = v k)
    (room : 1 + (keys rows).length * (1 + (rows.flatMap Prod.snd).eraseDups.length) +
      (rows.map fun r => r.2.length).sum ≤ 65536) : Within rows := by
  classical
  let profile (a : UInt64) := if h : ∃ v, Balanced rows a v then (keys rows).map h.choose else []
  apply Within.of_determined valid profile _ room
  intro a ha v hv
  have live : ∃ u, Balanced rows a u := ⟨v,hv⟩
  rw [show profile a = (keys rows).map live.choose by simp [profile,live]]
  exact List.map_congr_left (determined a ha v _ hv live.choose_spec)

structure Correct (candidate : Rows → Option (List Arm)) : Prop where
  sound_complete : ∀ rs answers, candidate rs = some answers → Complete rs (answers.map (decode (keys rs)))
  shape : ∀ rs answers, candidate rs = some answers → ∀ arm ∈ answers,
    arm.length = (keys rs).length ∧ ∀ bag ∈ arm, bag ≠ []
  completes : ∀ rs, Within rs → (candidate rs).isSome

private theorem prod_mono (as : List UInt64) (f g : UInt64 → Nat) (le : ∀ a ∈ as, f a ≤ g a) :
    (as.map f).prod ≤ (as.map g).prod := by
  induction as with
  | nil => exact Nat.le_refl _
  | cons a as ih => exact Nat.mul_le_mul (le a List.mem_cons_self) (ih fun b hb => le b (List.mem_cons_of_mem _ hb))

/-- A semantic column cover bounds the raw number of joint choices. The
cover may contain duplicate or unrealizable count vectors. -/
theorem product_bound (rs : Rows) (upper : UInt64 → List (List Nat))
    (ub : ∀ a ∈ atoms rs, ∀ v, Balanced rs a v → (keys rs).map v ∈ upper a) :
    ((atoms rs).map fun a => (choices rs (keys rs) a).length).prod ≤
      ((atoms rs).map fun a => (upper a).length).prod := by
  exact prod_mono (atoms rs) (fun a => (choices rs (keys rs) a).length) (fun a => (upper a).length) (by
    intro a ha
    have nodup : (choices rs (keys rs) a).Nodup := by exact dedup_distinct ((balancedColumns rs (keys rs) a).map fun v => (keys rs).map v)
    apply nodup.length_le_of_subset
    intro c hc
    obtain ⟨v,bal,rfl⟩ := mem_choices.mp hc
    exact ub a ha v bal)

theorem run_correct : Correct run := by
  constructor
  · intro rs answers h; rw [family_of_run h]; exact exact_family rs
  · intro rs answers h arm mem
    rw [family_of_run h] at mem
    obtain ⟨p,hn⟩ := List.mem_filter.mp mem
    obtain ⟨pick,_,rfl⟩ := List.mem_map.mp p
    exact ⟨by simp [materialize],fun bag hb => by simpa using List.all_eq_true.mp hn bag hb⟩
  · intro rs ⟨admit,upper,ub,count,words⟩
    obtain ⟨ctx,hi⟩ := Option.isSome_iff_exists.mp (inventories_complete admit)
    rw [inventories_eq hi] at hi
    have le := product_bound rs upper ub
    have cap := Nat.le_trans le count
    have fits := Nat.le_trans (Nat.mul_le_mul_right _ le) words
    rw [run,hi]
    change (collect rs (keys rs) (atoms rs)).isSome
    by_cases empty : ((atoms rs).map fun a => (choices rs (keys rs) a).length).prod = 0
    · simp [collect,List.map_map,Function.comp_def,empty]
    · simp [collect,List.map_map,Function.comp_def,empty,cap,fits]


end Tamarin.Matching.ACBagAnswers
