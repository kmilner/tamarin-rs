import TamarinRuntime.ACSortedBagSearch
import Tamarin.ACBagAnswers

namespace Tamarin.Matching.ACSortedBagSearch
open ACBags ACBagSearch ACBagAnswers

/-- A simultaneous mathematical matching image with the required singleton
sort tests. Whitelists are checked only for keys used in the problem. -/
def Feasible (rows : Rows) (limits : Limits) : Prop :=
  ∃ image, Solution rows image ∧ ∀ r ∈ rows, ∀ k ∈ r.1,
    ∀ rule ∈ limits, rule.1 = k → ∃ a ∈ rule.2, image k = [a]

private def partialFit (limits : Limits) (k : UInt64) (bag : List UInt64) : Prop :=
  ∀ rule ∈ limits, rule.1 = k → bag.length ≤ 1 ∧ ∀ a ∈ bag, a ∈ rule.2

private theorem fit_perm {lim : Limits} {k : UInt64} {x y : List UInt64} (eq : x.Perm y) :
    partialFit lim k x ↔ partialFit lim k y := by
  constructor <;> intro fit rule hr same
  · obtain ⟨le,all⟩ := fit rule hr same
    exact ⟨eq.length_eq ▸ le,fun a ha => all a (eq.mem_iff.mpr ha)⟩
  · obtain ⟨le,all⟩ := fit rule hr same
    exact ⟨eq.length_eq ▸ le,fun a ha => all a (eq.mem_iff.mp ha)⟩

private theorem fit_concat {lim : Limits} {k : UInt64} {xs ys : List UInt64} :
    partialFit lim k (xs ++ ys) ↔ partialFit lim k xs ∧ partialFit lim k ys ∧
      (narrow lim k = true → xs = [] ∨ ys = []) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro r hr same
      obtain ⟨le,all⟩ := h r hr same
      exact ⟨by simp at le; omega,fun a ha => all a (List.mem_append_left _ ha)⟩
    · intro r hr same
      obtain ⟨le,all⟩ := h r hr same
      exact ⟨by simp at le; omega,fun a ha => all a (List.mem_append_right _ ha)⟩
    · intro hit
      obtain ⟨r,hr,same⟩ := List.any_eq_true.mp hit
      have le := (h r hr (eq_of_beq same)).1
      cases xs <;> cases ys <;> simp_all
  · rintro ⟨left,right,disjoint⟩ r hr same
    have either := disjoint (List.any_eq_true.mpr ⟨r,hr,by simp [same]⟩)
    rcases either with nil|nil
    · simpa [nil] using right r hr same
    · simpa [nil] using left r hr same

private theorem fit_replicate (lim : Limits) (k a : UInt64) (n : Nat) :
    partialFit lim k (List.replicate n a) ↔
      (narrow lim k = true → n = 0 ∨ (n = 1 ∧ allows lim k a = true)) := by
  constructor
  · intro fit hit
    by_cases nz : n = 0
    · exact Or.inl nz
    · obtain ⟨r,hr,same⟩ := List.any_eq_true.mp hit
      have le := (fit r hr (eq_of_beq same)).1
      simp only [List.length_replicate] at le
      refine Or.inr ⟨by omega,List.all_eq_true.mpr ?_⟩
      intro s hs
      by_cases same : s.1 = k
      · have mem := (fit s hs same).2 a (by simp [nz])
        simp [same,mem]
      · simp [same]
  · intro h r hr same
    have hit : narrow lim k = true := List.any_eq_true.mpr ⟨r,hr,by simp [same]⟩
    rcases h hit with zero | ⟨one,allowed⟩
    · simp [zero]
    · have := List.all_eq_true.mp allowed r hr
      simpa [one,same] using this

private def capture (ks : List UInt64) (pick : Pick) (k : UInt64) :=
  pick.flatMap fun (a,col) => List.replicate (atKey ks col 0 k) a

private def relation (lim : Limits) (ks : List UInt64) (p : Pick) (s : List UInt64) :=
  ∀ k ∈ ks, partialFit lim k (capture ks p k) ∧ (k ∈ s ↔ capture ks p k ≠ [])

private def support (ks : List UInt64) (col : List Nat) :=
  ks.filter fun k => 0 < atKey ks col 0 k

private theorem option_iff (lim : Limits) (ks : List UInt64) (a : UInt64) (cs : List (List Nat))
    (s : List UInt64) :
    s ∈ options ks (ks.filter (narrow lim)) ((ks.filter (narrow lim)).filter (fun k => allows lim k a)) cs ↔
    ∃ col ∈ cs, (∀ k ∈ ks, partialFit lim k (List.replicate (atKey ks col 0 k) a)) ∧ support ks col = s := by
  simp only [options,List.mem_eraseDups,List.mem_map,List.mem_filter,List.all_eq_true,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem]
  constructor
  · rintro ⟨col,⟨hc,check⟩,rfl⟩
    refine ⟨col,hc,?_,rfl⟩
    intro k hk
    rw [fit_replicate]
    intro hit
    rcases check k ⟨hk,hit⟩ with zero | ⟨one,_,ok⟩
    · exact Or.inl zero
    · exact Or.inr ⟨one,ok⟩
  · rintro ⟨col,hc,fit,rfl⟩
    refine ⟨col,⟨hc,?_⟩,rfl⟩
    rintro k ⟨hk,hit⟩
    rcases (fit_replicate ..).mp (fit k hk) hit with zero | ⟨one,ok⟩
    · exact Or.inl zero
    · exact Or.inr ⟨one,⟨hk,hit⟩,ok⟩

private def disjoint (lim : Limits) (ks now prior : List UInt64) :=
  ∀ k ∈ ks, narrow lim k = true → k ∉ now ∨ k ∉ prior

private def merge (ks now prior : List UInt64) := ks.filter fun k => now.contains k || prior.contains k

private theorem step_iff (lim : Limits) (ks : List UInt64) (a : UInt64) (cols : List (List Nat))
    (rest : Batch) (s : List UInt64) :
    s ∈ supports lim ks (ks.filter (narrow lim)) ((a,cols)::rest) ↔
    ∃ col ∈ cols, (∀ k ∈ ks, partialFit lim k (List.replicate (atKey ks col 0 k) a)) ∧
      ∃ prior ∈ supports lim ks (ks.filter (narrow lim)) rest,
        disjoint lim ks (support ks col) prior ∧ merge ks (support ks col) prior = s := by
  rw [supports]
  split
  · rename_i h
    simp [List.isEmpty_iff.mp h]
  · simp only [List.mem_eraseDups,List.mem_flatMap,List.mem_map,List.mem_filter,List.all_eq_true,
        Bool.not_eq_true',Bool.and_eq_false_iff,List.contains_eq_mem,decide_eq_false_iff_not,option_iff]
    constructor
    · rintro ⟨_,⟨col,hc,fit,rfl⟩,p,⟨hp,apart⟩,rfl⟩
      exact ⟨col,hc,fit,p,hp,fun k hk hit => apart k ⟨hk,hit⟩,rfl⟩
    · rintro ⟨col,hc,fit,p,hp,apart,rfl⟩
      exact ⟨_,⟨col,hc,fit,rfl⟩,p,⟨hp,fun k ⟨hk,hit⟩ => apart k hk hit⟩,rfl⟩

private theorem local_mem (ks : List UInt64) (col : List Nat) (a : UInt64) {k : UInt64} (used : k ∈ ks) :
    k ∈ support ks col ↔ List.replicate (atKey ks col 0 k) a ≠ [] := by
  simp [support,used,Nat.pos_iff_ne_zero]

private theorem union_mem (ks now prior : List UInt64) {k : UInt64} (used : k ∈ ks) :
    k ∈ merge ks now prior ↔ k ∈ now ∨ k ∈ prior := by simp [merge,used]

private theorem joined {lim : Limits} {ks : List UInt64} {a col prior p}
    (part : ∀ k ∈ ks, partialFit lim k (List.replicate (atKey ks col 0 k) a))
    (tail : relation lim ks p prior) (apart : disjoint lim ks (support ks col) prior) :
    relation lim ks ((a,col)::p) (merge ks (support ks col) prior) := by
  intro k hk
  obtain ⟨fit,active⟩ := tail k hk
  have lhs := local_mem ks col a hk
  change partialFit lim k (List.replicate _ a ++ capture ks p k) ∧ _
  refine ⟨fit_concat.mpr ⟨part k hk,fit,?_⟩,?_⟩
  · intro hit
    simpa [lhs,active] using apart k hk hit
  · rw [union_mem _ _ _ hk,lhs,active]
    change _ ↔ List.replicate _ a ++ capture ks p k ≠ []
    grind [List.append_eq_nil_iff]

private theorem supports_sound (lim : Limits) (ks : List UInt64) (ls : Batch) {s}
    (generated : s ∈ supports lim ks (ks.filter (narrow lim)) ls) :
    ∃ p ∈ product ls, relation lim ks p s := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = [] := by simpa [supports] using generated
    exact ⟨[],List.mem_cons_self,by simp [relation,capture,partialFit]⟩
  | cons entry ls ih =>
    obtain ⟨a,cols⟩ := entry
    obtain ⟨col,hc,part,prior,hp,apart,rfl⟩ := (step_iff ..).mp generated
    obtain ⟨p,mem,tail⟩ := ih hp
    exact ⟨_,List.mem_flatMap.mpr ⟨col,hc,List.mem_map.mpr ⟨p,mem,rfl⟩⟩,joined part tail apart⟩

private theorem supports_cover (lim : Limits) (ks : List UInt64) (ls : Batch) {p}
    (generated : p ∈ product ls) (fit : ∀ k ∈ ks, partialFit lim k (capture ks p k)) :
    ∃ s ∈ supports lim ks (ks.filter (narrow lim)) ls, relation lim ks p s := by
  induction ls generalizing p with
  | nil =>
    obtain rfl : p = [] := by simpa [product] using generated
    exact ⟨[],List.mem_cons_self,by simp [relation,capture,partialFit]⟩
  | cons entry ls ih =>
    obtain ⟨a,cols⟩ := entry
    obtain ⟨col,hc,choose⟩ := List.mem_flatMap.mp generated
    obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp choose
    have splitFit k (hk : k ∈ ks) := fit_concat.mp (fit k hk)
    obtain ⟨prior,hp,rel⟩ := ih ht (fun k hk => (splitFit k hk).2.1)
    have apart : disjoint lim ks (support ks col) prior := by
      intro k hk hit
      have either := (splitFit k hk).2.2 hit
      change List.replicate (atKey ks col 0 k) a = [] ∨ capture ks tail k = [] at either
      rw [local_mem ks col a hk,(rel k hk).2]
      exact either.imp (fun h nz => nz h) (fun h nz => nz h)
    exact ⟨_,(step_iff ..).mpr ⟨col,hc,(fun k hk => (splitFit k hk).1),prior,hp,apart,rfl⟩,
      joined (fun k hk => (splitFit k hk).1) rel apart⟩

private theorem partial_full {lim : Limits} {k : UInt64} {bag : List UInt64} (nonempty : bag ≠ []) :
    partialFit lim k bag ↔ ∀ r ∈ lim, r.1 = k → ∃ a ∈ r.2, bag = [a] := by
  constructor
  · intro fit r hr same
    obtain ⟨len,ok⟩ := fit r hr same
    cases bag with
    | nil => contradiction
    | cons a tail =>
      have nil : tail = [] := by cases tail <;> simp_all
      exact ⟨a,ok a List.mem_cons_self,by rw [nil]⟩
  · intro all r hr same
    obtain ⟨a,ha,rfl⟩ := all r hr same
    simp [ha]

private theorem decision (rs : Rows) (lim : Limits) :
    let ks := keys rs
    let ls := batch rs (atoms rs)
    ((supports lim ks (ks.filter (narrow lim)) ls).any fun s => ks.all s.contains) = true ↔
      Feasible rs lim := by
  extract_lets ks ls
  have used k : k ∈ ks ↔ ∃ r ∈ rs, k ∈ r.1 := by simp [ks,keys,List.mem_eraseDups,List.mem_flatMap]
  have image (p : Pick) k (hk : k ∈ ks) :
      decode ks (materialize ks p) k = capture ks p k := atKey_map ks (capture ks p) [] hk
  have complete := exact_family rs
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s,mem,all⟩
    obtain ⟨p,hp,rel⟩ := supports_sound lim ks ls mem
    have nz k (hk : k ∈ ks) := (rel k hk).2.mp (List.contains_iff_mem.mp (List.all_eq_true.mp all k hk))
    have member : materialize ks p ∈ family ks ls := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_map_of_mem hp,List.all_eq_true.mpr ?_⟩
      intro bag hb
      change bag ∈ ks.map (capture ks p) at hb
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
      simpa using nz k hk
    refine ⟨_,complete.sound _ (List.mem_map_of_mem (f := decode ks) member),?_⟩
    intro r hr k hk
    have visible := (used k).mpr ⟨r,hr,hk⟩
    rw [image p k visible]
    exact (partial_full (nz k visible)).mp (rel k visible).1
  · rintro ⟨w,sol,typed⟩
    obtain ⟨im,mem,same⟩ := complete.covers w sol
    obtain ⟨arm,fromFamily,rfl⟩ := List.mem_map.mp mem
    obtain ⟨generated,_⟩ := List.mem_filter.mp fromFamily
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp generated
    have fits k (hk : k ∈ ks) : partialFit lim k (capture ks p k) ∧ capture ks p k ≠ [] := by
      obtain ⟨r,hr,usedKey⟩ := (used k).mp hk
      have eq := same r hr k usedKey
      rw [image p k hk] at eq
      have nz := sol.1 r hr k usedKey
      exact ⟨(fit_perm eq).mp ((partial_full nz).mpr (typed r hr k usedKey)),fun empty => nz (List.perm_nil.mp (empty ▸ eq))⟩
    obtain ⟨s,mem,rel⟩ := supports_cover lim ks ls hp (fun k hk => (fits k hk).1)
    exact ⟨s,mem,List.all_eq_true.mpr (fun k hk => List.contains_iff_mem.mpr ((rel k hk).2.mpr (fits k hk).2))⟩

structure Correct (candidate : Rows → Limits → Option Bool) : Prop where
  exact : ∀ rows limits b, candidate rows limits = some b → (b = true ↔ Feasible rows limits)
  completes : ∀ rows limits, ACBagSearch.Within rows → (candidate rows limits).isSome

theorem run_correct : Correct run := by
  constructor
  · intro rs lim b out
    cases h : inventories rs with
    | none => simp [run,h] at out
    | some pair =>
      rw [inventories_eq h] at h
      simp [run,h] at out
      exact out ▸ decision rs lim
  · intro rs lim valid
    obtain ⟨⟨ks,as⟩,h⟩ := Option.isSome_iff_exists.mp (inventories_complete valid)
    simp [run,h]

end Tamarin.Matching.ACSortedBagSearch
