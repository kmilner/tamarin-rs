import TamarinRuntime.OpenMatchSelect

namespace Tamarin.OpenMatchSelect

def decoded (out : Packet) := out.toList.map fun row => row.toList.map UInt64.toNat

def Admitted (k n : UInt64) : Prop :=
  n < k ∨ n ≤ 64 ∧ ways n.toNat k.toNat ≤ 4096

/-- A completed row uses every subject occurrence exactly once. Its first
`k` positions are aligned with the pattern in order. Every legal ordered
prefix must occur; arm order, duplicates within the packet limit, and the
ordering of unselected occurrences are all free. -/
structure Correct (solve : Kernel) : Prop where
  completes : ∀ k n, (solve k n).isSome ↔ Admitted k n
  bounded : ∀ k n out, solve k n = some out → out.size ≤ 4096
  sound : ∀ {k n out xs}, solve k n = some out → xs ∈ decoded out →
    k.toNat ≤ xs.length ∧ xs.Perm (List.range n.toNat)
  prefixes : ∀ {k n out} (pick : List Nat), solve k n = some out →
    pick.length = k.toNat → pick.Nodup → pick ⊆ List.range n.toNat →
    ∃ rest, pick ++ rest ∈ decoded out

private theorem mem_picks {pool : List Nat} (unique : pool.Nodup) (k : Nat) (xs : List Nat) :
    xs ∈ picks pool k ↔ xs.length = k ∧ xs.Nodup ∧ xs ⊆ pool := by
  induction k generalizing pool xs with
  | zero => cases xs <;> simp [picks]
  | succ k ih =>
    constructor
    · intro h
      obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
      obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp h
      obtain ⟨len, nd, sub⟩ := (ih (unique.erase i) tail).mp ht
      refine ⟨by simp [len], List.nodup_cons.mpr ⟨fun hm => unique.not_mem_erase (sub hm),nd⟩,?_⟩
      exact List.cons_subset.mpr ⟨hi, fun _ hm => List.mem_of_mem_erase (sub hm)⟩
    · rintro ⟨len, nd, sub⟩
      cases xs with
      | nil => simp at len
      | cons i tail =>
        have hi := sub List.mem_cons_self
        apply List.mem_flatMap.mpr
        refine ⟨i,hi,List.mem_map.mpr ⟨tail,?_,rfl⟩⟩
        apply (ih (unique.erase i) tail).mpr
        refine ⟨by simpa using len, nd.tail, ?_⟩
        intro j hj
        exact unique.mem_erase_iff.mpr ⟨fun eq => (List.nodup_cons.mp nd).1 (eq ▸ hj),
          sub (List.mem_cons_of_mem _ hj)⟩

private theorem length_picks (pool : List Nat) (k : Nat) :
    (picks pool k).length = ways pool.length k := by
  induction k generalizing pool with
  | zero => simp [picks,ways]
  | succ k ih =>
    rw [picks,List.length_flatMap]
    calc
      _ = (pool.map (fun _ => ways (pool.length - 1) k)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro i hi
        simp [ih,List.length_erase_of_mem hi]
      _ = _ := by simp [List.map_const', List.sum_replicate_nat, ways]

private theorem decode_one (n : UInt64) (pick : List Nat) (lt : ∀ i ∈ pick, i < n.toNat) :
    let xs := pick ++ (List.range n.toNat).filter (fun i => !pick.contains i)
    (xs.toArray.map Nat.toUInt64).toList.map UInt64.toNat = xs := by
  dsimp only
  simp only [Array.toList_map, List.map_map]
  refine Eq.trans (List.map_congr_left (g := id) ?_) (List.map_id _)
  intro i hi
  apply UInt64.toNat_ofNat_of_lt'
  apply Nat.lt_trans _ n.toNat_lt
  rcases List.mem_append.mp hi with hp | hr
  · exact lt i hp
  · exact List.mem_range.mp (List.mem_filter.mp hr).1

private theorem run_rows {k n out} (h : run k n = some out) (xs : List Nat) :
    xs ∈ decoded out ↔ ∃ pick : List Nat, pick.length = k.toNat ∧ pick.Nodup ∧
      (∀ i ∈ pick, i < n.toNat) ∧ xs = pick ++ (List.range n.toNat).filter (fun i => !pick.contains i) := by
  unfold run at h
  split at h
  · next small =>
    cases h
    simp only [decoded, List.map_nil, List.not_mem_nil, false_iff]
    rintro ⟨pick,len,nd,live,_⟩
    have := nd.length_le_of_subset (l₂ := List.range n.toNat) (by
      intro i hi; exact List.mem_range.mpr (live i hi))
    simp [len] at this
    exact (Nat.not_le_of_lt (UInt64.lt_iff_toNat_lt.mp small)) this
  · split at h
    · cases h
      simp only [decoded, Array.toList_map, List.mem_map]
      constructor
      · rintro ⟨_, ⟨p,hp,rfl⟩, rfl⟩
        obtain ⟨len, nd, sub⟩ := (mem_picks List.nodup_range _ _).mp hp
        have lt (i) (hi : i ∈ p) := List.mem_range.mp (sub hi)
        exact ⟨p,len,nd,lt,decode_one n p lt⟩
      · rintro ⟨p,len,nd,lt,rfl⟩
        refine ⟨_,⟨p,(mem_picks List.nodup_range _ _).mpr ⟨len,nd,fun _ hi => List.mem_range.mpr (lt _ hi)⟩,rfl⟩,?_⟩
        exact decode_one n p lt
    · contradiction

private theorem perm_rest (n : Nat) (p : List Nat) (nd : p.Nodup) (lt : ∀ i ∈ p, i < n) :
    (p ++ (List.range n).filter (fun i => !p.contains i)).Perm (List.range n) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_append]
  by_cases h : i ∈ p
  · have absent : i ∉ (List.range n).filter (fun j => !p.contains j) := by simp [h]
    rw [List.count_eq_zero.mpr absent, Nat.add_zero, nd.count_of_mem h,
      List.nodup_range.count_of_mem (List.mem_range.mpr (lt i h))]
  · rw [List.count_eq_zero.mpr h, Nat.zero_add, List.count_filter (by simpa using h)]

theorem run_correct : Correct run := by
  constructor
  · intro k n
    by_cases h : n < k <;> simp [run,Admitted,h]
  · intro k n out h
    unfold run at h
    split at h
    · cases h; decide
    · split at h
      · next bound =>
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
        simpa [length_picks] using bound.2
      · contradiction
  · intro k n out xs ran mem
    obtain ⟨p,len,nd,lt,rfl⟩ := (run_rows ran _).mp mem
    exact ⟨by simp [← len], perm_rest _ p nd lt⟩
  · intro k n out pick ran len nd sub
    exact ⟨_,(run_rows ran _).mpr ⟨pick,len,nd,fun i hi => List.mem_range.mp (sub hi),rfl⟩⟩

theorem Correct.perm {solve : Kernel} (c : Correct solve) {k n out xs}
    (ran : solve k n = some out) (member : xs ∈ decoded out) : xs.Perm (List.range n.toNat) :=
  (c.sound ran member).2

theorem Correct.covers {solve : Kernel} (c : Correct solve) {k n out} {picked rest : List Nat}
    (ran : solve k n = some out) (len : picked.length = k.toNat)
    (h : (picked ++ rest).Perm (List.range n.toNat)) :
    ∃ rest', picked ++ rest' ∈ decoded out ∧ rest'.Perm rest := by
  have nd := (List.nodup_append.mp (h.symm.nodup List.nodup_range)).1
  obtain ⟨rest',mem⟩ := c.prefixes picked ran len nd fun i hi => h.mem_iff.mp (List.mem_append_left _ hi)
  exact ⟨rest',mem,(List.perm_append_left_iff _).mp ((c.perm ran mem).trans h.symm)⟩

end Tamarin.OpenMatchSelect
