import TamarinRuntime.ACBagSearch
import Tamarin.ACMatchColumns

namespace Tamarin.Matching.ACBagSearch
open ACBags

private def Keys (rows : Rows) (ks : List UInt64) :=
  ∀ k, k ∈ ks ↔ ∃ r ∈ rows, k ∈ r.1

private theorem eqs_ok (rows : Rows) (a : UInt64) (v : Column) :
    ((equations rows a).all fun (ks,n) => (ks.map v).sum == n) = true ↔ Balanced rows a v := by
  simp [equations,Balanced,List.all_eq_true]

private theorem vectors_cover (v : Column) (b : Nat) (ks : List UInt64) (bound : ∀ k ∈ ks, v k ≤ b) :
    ∃ u ∈ vectors b ks, ∀ k ∈ ks, u k = v k := by
  induction ks with
  | nil => exact ⟨_,List.mem_cons_self,by simp⟩
  | cons k ks ih =>
    obtain ⟨u,hu,h⟩ := ih fun i hi => bound i (List.mem_cons_of_mem _ hi)
    let w : Column := fun i => if i = k then v k else u i
    refine ⟨w,List.mem_flatMap.mpr ⟨v k,List.mem_range.mpr (Nat.lt_succ_of_le (bound _ List.mem_cons_self)),
      List.mem_map.mpr ⟨u,hu,rfl⟩⟩,?_⟩
    intro i hi
    by_cases same : i = k
    · simp [w,same]
    · exact (ite_eq_right same).trans (h i ((List.mem_cons.mp hi).resolve_left same))

private theorem le_sum {k : UInt64} (v : Column) {ks : List UInt64} (mem : k ∈ ks) :
    v k ≤ (ks.map v).sum := by
  induction ks with
  | nil => simp at mem
  | cons j js ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp mem with rfl|h
    · omega
    · exact Nat.le_trans (ih h) (Nat.le_add_left ..)

private theorem le_largest (eqs : List (List UInt64 × Nat)) (r) (hr : r ∈ eqs) : r.2 ≤ largest eqs := by
  induction eqs with
  | nil => simp at hr
  | cons e es ih =>
    change _ ≤ max e.2 (largest es)
    rcases List.mem_cons.mp hr with rfl|h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

private theorem mem_options {rows : Rows} {ks : List UInt64} {a : UInt64} {s : List UInt64}
    (h : s ∈ options rows ks a) :
    ∃ u : Column, Balanced rows a u ∧ ∀ k ∈ ks, k ∈ s ↔ 0 < u k := by
  simp only [options,List.mem_eraseDups,List.mem_map,List.mem_filter] at h
  obtain ⟨u,⟨_,ok⟩,rfl⟩ := h
  exact ⟨u,(eqs_ok ..).1 ok,by intro k hk; simp [hk]⟩

private theorem options_cover {rows : Rows} {ks : List UInt64} (keys : Keys rows ks)
    (a : UInt64) (v : Column) (ok : Balanced rows a v) :
    ∃ s ∈ options rows ks a, ∀ k ∈ ks, k ∈ s ↔ 0 < v k := by
  have bound k (hk : k ∈ ks) : v k ≤ largest (equations rows a) := by
    obtain ⟨r,hr,hm⟩ := (keys k).1 hk
    apply Nat.le_trans (le_sum v hm)
    rw [ok r hr]
    exact le_largest _ (r.1, r.2.count a) (List.mem_map.mpr ⟨r,hr,rfl⟩)
  obtain ⟨u,hu,agree⟩ := vectors_cover v _ ks bound
  have good : Balanced rows a u := by
    intro r hr
    have eq := List.map_congr_left (f := u) (g := v) (l := r.1)
      (fun k hk => agree k ((keys k).2 ⟨r,hr,hk⟩))
    rw [eq,ok r hr]
  refine ⟨_,List.mem_eraseDups.mpr (List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨hu,(eqs_ok ..).2 good⟩,rfl⟩),?_⟩
  intro k hk
  simp [hk,agree k hk]

private theorem step_support {rows : Rows} {ks as : List UInt64} {a s} :
    s ∈ supports rows ks (a :: as) ↔
      ∃ c ∈ options rows ks a, ∃ p ∈ supports rows ks as, (ks.filter fun k => c.contains k || p.contains k) = s := by
  rw [supports]
  split
  · rename_i h
    simp [List.isEmpty_iff.mp h]
  · simp only [List.mem_eraseDups,List.mem_flatMap,List.mem_map]

private def Hits (w : UInt64 → Column) (atoms : List UInt64) (k : UInt64) :=
  ∃ a ∈ atoms, 0 < w a k

private theorem hits_cons (w : UInt64 → Column) (a : UInt64) (as : List UInt64) (k : UInt64) :
    Hits w (a :: as) k ↔ 0 < w a k ∨ Hits w as k := by
  simp [Hits]

private theorem covers_all {rows : Rows} {ks : List UInt64} (keys : Keys rows ks) (as : List UInt64)
    (w : UInt64 → Column) (good : ∀ a ∈ as, Balanced rows a (w a)) :
    ∃ s ∈ supports rows ks as, ∀ k ∈ ks, k ∈ s ↔ Hits w as k := by
  induction as with
  | nil => exact ⟨[],List.mem_cons_self,by simp [Hits]⟩
  | cons a as ih =>
    obtain ⟨c,hc,cap⟩ := options_cover keys a (w a) (good a List.mem_cons_self)
    obtain ⟨p,hp,prior⟩ := ih (fun b hb => good b (List.mem_cons_of_mem _ hb))
    exact ⟨_,step_support.mpr ⟨c,hc,p,hp,rfl⟩,by
      intro k hk; simp [hk,cap k hk,prior k hk,hits_cons]⟩

private theorem supports_sound {rows : Rows} (ks as : List UInt64) (nd : as.Nodup)
    (s : List UInt64) (mem : s ∈ supports rows ks as) :
    ∃ w : UInt64 → Column, (∀ a ∈ as, Balanced rows a (w a)) ∧ ∀ k ∈ ks, k ∈ s ↔ Hits w as k := by
  induction as generalizing s with
  | nil =>
    obtain rfl : s = [] := by simpa [supports] using mem
    exact ⟨fun _ _ => 0,by simp,by simp [Hits]⟩
  | cons a as ih =>
    obtain ⟨c,hc,p,hp,rfl⟩ := step_support.mp mem
    obtain ⟨u,ok,cap⟩ := mem_options hc
    obtain ⟨v,tail,prior⟩ := ih nd.tail p hp
    let w (b) := if b = a then u else v b
    have other b (hb : b ∈ as) : w b = v b := by
      have ne : b ≠ a := fun h => (List.nodup_cons.mp nd).1 (h ▸ hb)
      simp [w,ne]
    refine ⟨w,?_,?_⟩
    · rw [List.forall_mem_cons]
      exact ⟨by simpa [w] using ok,fun b hb => other b hb ▸ tail b hb⟩
    · intro k hk
      have prev : Hits w as k ↔ Hits v as k :=
        ⟨fun ⟨b,hb,h⟩ => ⟨b,hb,other b hb ▸ h⟩,fun ⟨b,hb,h⟩ => ⟨b,hb,other b hb ▸ h⟩⟩
      simp [hk,cap k hk,prior k hk,hits_cons,prev,w]

private theorem dedup_distinct {α} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups],dedup_distinct _⟩
termination_by xs.length
decreasing_by have := List.length_filter_le (fun (v : α) => !v == x) xs; simp; omega

private theorem decision (rows : Rows) :
    let ks := (rows.flatMap Prod.fst).eraseDups
    let as := (rows.flatMap Prod.snd).eraseDups
    ((supports rows ks as).any fun s => ks.all s.contains) = true ↔ Feasible rows := by
  extract_lets ks as
  have keys : Keys rows ks := by intro k; simp [ks,List.mem_eraseDups,List.mem_flatMap]
  have atoms (a) : a ∈ as ↔ ∃ r ∈ rows, a ∈ r.2 := by simp [as,List.mem_eraseDups,List.mem_flatMap]
  rw [feasible_columns rows as (dedup_distinct _) atoms,List.any_eq_true]
  constructor
  · rintro ⟨s,mem,hit⟩
    obtain ⟨w,bal,prior⟩ := supports_sound ks as (dedup_distinct _) s mem
    refine ⟨w,bal,?_⟩
    intro r hr k hk
    have used := (keys k).2 ⟨r,hr,hk⟩
    exact (prior k used).1 (List.contains_iff_mem.mp (List.all_eq_true.mp hit k used))
  · rintro ⟨w,ok,hit⟩
    obtain ⟨s,mem,prior⟩ := covers_all keys as w ok
    refine ⟨s,mem,List.all_eq_true.mpr ?_⟩
    intro k hk
    obtain ⟨r,hr,used⟩ := (keys k).1 hk
    exact List.contains_iff_mem.mpr ((prior k hk).2 (hit r hr k used))

/-- Independent of the candidate: count caller keys and rigid factor kinds
in the input itself. Each factor has a per-row multiplicity bound; the small
integer search box is charged per factor, never across their product. -/
def Within (rows : List (List UInt64 × List UInt64)) : Prop :=
  rows.length ≤ 64 ∧ (rows.map (fun r => r.1.length + r.2.length)).sum ≤ 4096 ∧
  (rows.flatMap Prod.fst).eraseDups.length ≤ 5 ∧ (rows.flatMap Prod.snd).eraseDups.length ≤ 128 ∧
  ∀ a ∈ rows.flatMap Prod.snd, ∃ b : Nat, (∀ r ∈ rows, r.2.count a ≤ b) ∧
    (b+1)^(rows.flatMap Prod.fst).eraseDups.length ≤ 256

structure Correct (candidate : List (List UInt64 × List UInt64) → Option Bool) : Prop where
  exact : ∀ rows b, candidate rows = some b → (b = true ↔ Feasible rows)
  completes : ∀ rows, Within rows → (candidate rows).isSome

private theorem largest_le (xs : List (List UInt64 × Nat)) (b : Nat) (ok : ∀ x ∈ xs, x.2 ≤ b) :
    largest xs ≤ b := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact Nat.max_le.mpr ⟨ok x List.mem_cons_self,ih fun y hy => ok y (List.mem_cons_of_mem _ hy)⟩

theorem run_correct : Correct run := by
  constructor
  · intro rows b out
    unfold run at out
    split at out <;> try contradiction
    dsimp only at out
    split at out <;> try contradiction
    split at out <;> try contradiction
    cases out
    exact decision rows
  · intro rows ⟨nr,size,nk,na,bounds⟩
    have box : ((rows.flatMap Prod.snd).eraseDups.all fun a =>
        (largest (equations rows a)+1)^(rows.flatMap Prod.fst).eraseDups.length ≤ 256) = true := by
      apply List.all_eq_true.mpr
      intro a ha
      obtain ⟨b,upper,limit⟩ := bounds a (List.mem_eraseDups.mp ha)
      have cap := largest_le (equations rows a) b (by
        intro x hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
        exact upper r hr)
      exact decide_eq_true (Nat.le_trans (Nat.pow_le_pow_left (Nat.succ_le_succ cap) _) limit)
    simp [run,nr,size,nk,na,box]

end Tamarin.Matching.ACBagSearch
