import Tamarin.Algebra

/-! Ascending witness indices used by the Rust AC answer reader. The end of the word
range is exclusive in this model, so advancing past the largest word never wraps. -/
namespace Tamarin.OrdinalAllocation

/-- Search at most `remaining` indices, starting at `lo`; stop at the first unreserved one. -/
def scan (reserved : UInt64 → Bool) (lo : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => if reserved lo.toUInt64 then scan reserved (lo + 1) k else some lo

theorem scan_some_iff (reserved : UInt64 → Bool) (lo remaining i : Nat) :
    scan reserved lo remaining = some i ↔
    lo ≤ i ∧ i < lo + remaining ∧ reserved i.toUInt64 = false ∧
      ∀ j, lo ≤ j → j < i → reserved j.toUInt64 = true := by
  induction remaining generalizing lo with
  | zero => simp [scan]; omega
  | succ k ih =>
    cases h : reserved lo.toUInt64 with
    | false =>
      simp only [scan, h, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨by omega, by omega, h, fun _ _ hj => by omega⟩
      · rintro ⟨_,_,_,minimal⟩
        by_cases eq : lo = i
        · exact eq
        · have := minimal lo (by omega) (by omega)
          simp_all
    | true =>
      simp only [scan,h,↓reduceIte,ih]
      constructor
      · rintro ⟨_,_,free,more⟩
        refine ⟨by omega, by omega, free, fun j hj lt => ?_⟩
        by_cases eq : j = lo
        · exact eq ▸ h
        · exact more j (by omega) lt
      · rintro ⟨_,_,free,more⟩
        have ne : i ≠ lo := by rintro rfl; simp_all
        exact ⟨by omega, by omega, free, fun j hj => more j (by omega)⟩

theorem scan_none_iff (reserved : UInt64 → Bool) (lo remaining : Nat) :
    scan reserved lo remaining = none ↔
      ∀ j, lo ≤ j → j < lo + remaining → reserved j.toUInt64 = true := by
  induction remaining generalizing lo with
  | zero => simp [scan]; omega
  | succ k ih =>
    cases h : reserved lo.toUInt64 with
    | false =>
      simp only [scan,h,Bool.false_eq_true,↓reduceIte,Option.some_ne_none,false_iff]
      intro impossible
      have := impossible lo (by omega) (by omega)
      simp_all
    | true =>
      simp only [scan,h,↓reduceIte,ih]
      constructor
      · intro tail j hj limit
        by_cases eq : j = lo
        · exact eq ▸ h
        · exact tail j (by omega) (by omega)
      · intro all j hj bound
        exact all j (by omega) (by omega)

/-- Each first occurrence of a new ordinal takes the next free index. -/
def takeFree (reserved : UInt64 → Bool) (endIdx lo : Nat) : Nat → Option (List Nat)
  | 0 => some []
  | n + 1 => do
    let first ← scan reserved lo (endIdx - lo)
    return first :: (← takeFree reserved endIdx (first + 1) n)

def Available (reserved : UInt64 → Bool) (endIdx lo : Nat) (xs : List Nat) : Prop :=
  xs.Pairwise (· < ·) ∧ ∀ i ∈ xs, lo ≤ i ∧ i < endIdx ∧ reserved i.toUInt64 = false

private theorem take_valid {reserved endIdx n lo xs} (h : takeFree reserved endIdx lo n = some xs) :
    xs.length = n ∧ Available reserved endIdx lo xs := by
  induction n generalizing lo xs with
  | zero => cases Option.some.inj h; simp [Available]
  | succ n ih =>
    cases hf : scan reserved lo (endIdx - lo) with
    | none => simp [takeFree,hf] at h
    | some i =>
      cases ht : takeFree reserved endIdx (i+1) n with
      | none => simp [takeFree,hf,ht] at h
      | some tail =>
        have eq : i :: tail = xs := by simpa [takeFree,hf,ht] using h
        subst xs
        obtain ⟨lower,upper,free,_⟩ := (scan_some_iff ..).mp hf
        obtain ⟨len,ordered,valid⟩ := ih ht
        refine ⟨by simp [len], List.pairwise_cons.mpr ⟨fun j hj => (valid j hj).1,ordered⟩, ?_⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hm
        · exact ⟨lower, by omega, free⟩
        · obtain ⟨_,b,c⟩ := valid j hm
          exact ⟨by omega,b,c⟩

private theorem take_exists {reserved endIdx lo xs} (h : Available reserved endIdx lo xs) :
    ∃ ys, takeFree reserved endIdx lo xs.length = some ys := by
  induction xs generalizing lo with
  | nil => exact ⟨[],rfl⟩
  | cons j tail ih =>
    obtain ⟨order,valid⟩ := h
    obtain ⟨loJ,hiJ,freeJ⟩ := valid j List.mem_cons_self
    cases hf : scan reserved lo (endIdx-lo) with
    | none =>
      have res := (scan_none_iff ..).mp hf j loJ (by omega)
      simp_all
    | some i =>
      obtain ⟨_,_,_,minimal⟩ := (scan_some_iff ..).mp hf
      have le : i ≤ j := by
        by_cases le : i ≤ j
        · exact le
        · have := minimal j loJ (by omega)
          simp_all
      obtain ⟨larger,tailOrd⟩ := List.pairwise_cons.mp order
      have avail : Available reserved endIdx (i+1) tail := by
        refine ⟨tailOrd, fun k hk => ?_⟩
        have gt := larger k hk
        exact ⟨by omega, (valid k (List.mem_cons_of_mem _ hk)).2⟩
      obtain ⟨ys,hy⟩ := ih avail
      exact ⟨i::ys, by simp [takeFree,hf,hy]⟩

/-- Take a prefix of Rust's inclusive UInt64 iterator; stop scanning once all requested
indices have been found. -/
def allocate (reserved : UInt64 → Bool) (count : Nat) : Option (List UInt64) :=
  (takeFree reserved UInt64.size 0 count).map (List.map Nat.toUInt64)

theorem allocate_valid {reserved count ws} (allocated : allocate reserved count = some ws) :
    ws.length = count ∧ (ws.map UInt64.toNat).Pairwise (· < ·) ∧ ∀ w ∈ ws, reserved w = false := by
  obtain ⟨xs, hx, rfl⟩ := Option.map_eq_some_iff.mp allocated
  obtain ⟨len,order,valid⟩ := take_valid hx
  have nums : (xs.map Nat.toUInt64).map UInt64.toNat = xs := by
    rw [List.map_map]
    calc
      _ = xs.map id := List.map_congr_left (fun i hi => UInt64.toNat_ofNat_of_lt' (valid i hi).2.1)
      _ = xs := List.map_id xs
  refine ⟨by simpa using len, by rw [nums]; exact order, ?_⟩
  intro w hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
  exact (valid i hi).2.2

/-- Exhaustion is equivalent to the absence of a long enough increasing list of free words. -/
theorem allocate_isSome_iff (reserved : UInt64 → Bool) (count : Nat) :
    (allocate reserved count).isSome ↔ ∃ ws : List UInt64,
      ws.length = count ∧ (ws.map UInt64.toNat).Pairwise (· < ·) ∧ ∀ w ∈ ws, reserved w = false := by
  constructor
  · intro ok
    obtain ⟨ws,h⟩ := Option.isSome_iff_exists.mp ok
    exact ⟨ws,allocate_valid h⟩
  · rintro ⟨ws,len,ordered,free⟩
    have avail : Available reserved UInt64.size 0 (ws.map UInt64.toNat) := by
      refine ⟨ordered,fun i hi => ?_⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
      exact ⟨by omega,w.toNat_lt_size,by simpa using free w hw⟩
    obtain ⟨ys,hy⟩ := take_exists avail
    simp only [List.length_map, len] at hy
    simp [allocate,hy]

/-- Interpret an ordinal in the caller's allocated vector. Only in-bounds ordinals
are observable; the default makes the interpretation a total function. -/
def nameAt (make : UInt64 → Variable) (ws : List UInt64) (ordinal : UInt64) : Variable :=
  make (ws[ordinal.toNat]?.getD 0)

/-- The Rust name constructor may use any faithful embedding of full variable identities.
Only the indices in the prefix need preserve identity and sort. Reserving an index for
several caller variables or for a different sort is harmless. -/
theorem names_correct {reserved count ws} (allocated : allocate reserved count = some ws)
    (make : UInt64 → Variable) (sort : SortId) (scope : List Variable)
    (injective : ∀ i ∈ ws, ∀ j ∈ ws, make i = make j → i = j)
    (typed : ∀ i ∈ ws, (make i).sort = sort)
    (occupied : ∀ i, make i ∈ scope → reserved i = true)
    (live : List UInt64) (bound : ∀ j ∈ live, j.toNat < count) :
    (∀ i ∈ live, ∀ j ∈ live, nameAt make ws i = nameAt make ws j → i = j) ∧
    (∀ j ∈ live, (nameAt make ws j).sort = sort) ∧
    (∀ j ∈ live, nameAt make ws j ∉ scope) := by
  obtain ⟨len,order,free⟩ := allocate_valid allocated
  have valid (j) (hj : j ∈ live) : j.toNat < ws.length := len ▸ bound j hj
  have atIndex (j) (hj : j ∈ live) : nameAt make ws j = make (ws[j.toNat]'(valid j hj)) := by
    simp [nameAt, List.getElem?_eq_getElem (valid j hj)]
  have nodup : ws.Nodup := by
    rw [List.pairwise_map] at order
    exact order.imp (fun lt same => by simp [same] at lt)
  refine ⟨?_, fun j hj => by rw [atIndex j hj]; exact typed _ (List.getElem_mem _), ?_⟩
  · intro i hi j hj eq
    rw [atIndex i hi,atIndex j hj] at eq
    have same := injective _ (List.getElem_mem _) _ (List.getElem_mem _) eq
    exact UInt64.toNat_inj.mp (nodup.getElem_inj.mp same)
  · intro j hj captured
    rw [atIndex j hj] at captured
    have used := occupied _ captured
    rw [free _ (List.getElem_mem _)] at used
    contradiction

end Tamarin.OrdinalAllocation
