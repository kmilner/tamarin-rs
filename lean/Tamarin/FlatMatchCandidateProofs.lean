import TamarinRuntime
import Tamarin.FlatMatchContract

namespace Tamarin.FlatMatchCandidateProofs

private theorem mem_singletons (rhs : List UInt64) (n : Nat) (rows : List (List UInt64)) :
    rows ∈ RuntimeCandidate.singletons rhs n ↔
    rows.length = n ∧ ∀ row ∈ rows, ∃ a ∈ rhs, row = [a] := by
  induction n generalizing rows with
  | zero => cases rows <;> simp [RuntimeCandidate.singletons]
  | succ n ih =>
    cases rows with
    | nil => simp [RuntimeCandidate.singletons]
    | cons r rs =>
      simp only [RuntimeCandidate.singletons, List.mem_flatMap,
        List.mem_map, List.cons.injEq, List.length_cons, Nat.succ.injEq, List.forall_mem_cons]
      constructor
      · rintro ⟨a, ha, _, hr, rfl, rfl⟩
        obtain ⟨hl, hh⟩ := (ih _).mp hr
        exact ⟨hl, ⟨a, ha, rfl⟩, hh⟩
      · rintro ⟨hl, ⟨a, ha, rfl⟩, hr⟩
        exact ⟨a, ha, rs, (ih _).mpr ⟨hl, hr⟩, rfl, rfl⟩

private theorem expanded_length (rows : List (List UInt64)) (occ : List Nat)
    (pos : ∀ i ∈ occ, 0 < (rows[i]?.getD []).length) :
    occ.length ≤ (FlatMatchSearch.expand rows occ).length ∧
    ((FlatMatchSearch.expand rows occ).length = occ.length →
      ∀ i ∈ occ, (rows[i]?.getD []).length = 1) := by
  induction occ with
  | nil => simp [FlatMatchSearch.expand]
  | cons i is ih =>
    obtain ⟨hle, heq⟩ := ih (fun j hj => pos j (by simp [hj]))
    have hp := pos i (by simp)
    change is.length + 1 ≤ ((rows[i]?.getD []) ++ FlatMatchSearch.expand rows is).length ∧ _
    simp only [List.length_append]
    constructor
    · omega
    · intro h
      change ((rows[i]?.getD []) ++ FlatMatchSearch.expand rows is).length = is.length + 1 at h
      rw [List.length_append] at h
      exact List.forall_mem_cons.mpr ⟨by omega, heq (by omega)⟩

private theorem expand_cons (row : List UInt64) (rows : List (List UInt64)) (occ : List Nat) :
    (FlatMatchSearch.expand (row :: rows) occ).length =
      occ.count 0 * row.length +
        (FlatMatchSearch.expand rows (occ.filterMap RuntimeCandidate.previousSlot)).length := by
  induction occ with
  | nil => simp [FlatMatchSearch.expand]
  | cons i is ih =>
    cases i <;> simp_all [FlatMatchSearch.expand, List.filterMap_cons, RuntimeCandidate.previousSlot,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem mem_fitting (images : List (List UInt64)) (n : Nat) (occ : List Nat)
    (room : Nat) (rows : List (List UInt64)) :
    rows ∈ RuntimeCandidate.fitting (images.map fun r => (r.length, r))
        (RuntimeCandidate.weights n occ) room ↔
      rows.length = n ∧ (∀ r ∈ rows, r ∈ images) ∧ (FlatMatchSearch.expand rows occ).length = room := by
  induction n generalizing occ room rows with
  | zero =>
    have zeros : (occ.map (fun _ => (0 : Nat))).sum = 0 := by induction occ <;> simp_all
    cases rows <;> by_cases h : room = 0 <;>
      simp [RuntimeCandidate.weights, RuntimeCandidate.fitting, FlatMatchSearch.expand, h, zeros, eq_comm]
  | succ n ih =>
    cases rows with
    | nil =>
      simp only [RuntimeCandidate.weights, RuntimeCandidate.fitting, List.flatMap_map, List.mem_flatMap,
        List.length_nil, Nat.zero_ne_add_one, false_and, iff_false]
      rintro ⟨r, _, h⟩
      split at h <;> simp at h
    | cons r rs =>
      simp only [RuntimeCandidate.weights, RuntimeCandidate.fitting, List.flatMap_map, List.mem_flatMap,
        List.length_cons, Nat.succ.injEq, List.forall_mem_cons, expand_cons]
      constructor
      · rintro ⟨s, hs, branch⟩
        split at branch
        next fits =>
          obtain ⟨ss, hss, rfl, rfl⟩ := by simpa only [List.mem_map, List.cons.injEq] using branch
          obtain ⟨len, rest, width⟩ := (ih _ _ _).mp hss
          exact ⟨len, ⟨hs, rest⟩, by omega⟩
        next => simp at branch
      · rintro ⟨len, ⟨hr, rest⟩, width⟩
        refine ⟨r, hr, ?_⟩
        rw [ite_eq_left (by omega)]
        exact List.mem_map.mpr ⟨rs, (ih _ _ _).mpr ⟨len, rest, by omega⟩, rfl⟩

private theorem mem_images (rhs row : List UInt64) :
    row ∈ RuntimeCandidate.images rhs ↔ row.Sublist rhs := by
  induction rhs generalizing row with
  | nil => simp [RuntimeCandidate.images]
  | cons a as ih =>
    simp only [RuntimeCandidate.images, List.mem_append, List.mem_filter, bne_iff_ne, ih, List.mem_map]
    constructor
    · rintro (⟨sub, _⟩ | ⟨r, sub, rfl⟩)
      · exact sub.cons a
      · exact sub.cons_cons a
    · intro sub
      cases sub with
      | cons _ sub =>
        by_cases h : row.head? = some a
        · cases row with
          | nil => simp at h
          | cons b bs =>
            have eq : b = a := by simpa using h
            exact Or.inr ⟨bs, (List.tail_sublist _).trans sub, by rw [eq]⟩
        · exact Or.inl ⟨sub, h⟩
      | cons_cons _ sub => exact Or.inr ⟨_, sub, rfl⟩

def imageHeads (a : UInt64) (rows : List (List UInt64)) : Nat :=
  rows.countP fun r => r.head? == some a

private theorem prefix_counts (a b : UInt64) (rows : List (List UInt64)) :
    let kept := rows.filter fun r => r.head? != some a
    kept.length + imageHeads a rows = rows.length ∧
    imageHeads b (kept ++ rows.map (a :: ·)) = if a = b then rows.length else imageHeads b rows := by
  induction rows with
  | nil => simp [imageHeads]
  | cons r rs ih =>
    by_cases h : a = b <;> by_cases ha : r.head? = some a <;> by_cases hb : r.head? = some b <;>
      simp_all [imageHeads, List.countP_append] <;> omega

/-- The Rust work estimate can count the exact image domain during a right-to-left scan.
Every step visits the previous domain and keeps one bucket per leading factor. -/
theorem image_counts_cons (a b : UInt64) (rhs : List UInt64) :
    let old := RuntimeCandidate.images rhs
    let newRows := RuntimeCandidate.images (a :: rhs)
    newRows.length = old.length + (old.length - imageHeads a old) ∧
    imageHeads b newRows = if a = b then old.length else imageHeads b old := by
  obtain ⟨length, heads⟩ := prefix_counts a b (RuntimeCandidate.images rhs)
  refine ⟨?_, heads⟩
  simp only [RuntimeCandidate.images, List.length_append, List.length_map]
  omega

private theorem mem_partition (n : Nat) (occ : List Nat) (tail rhs : List UInt64)
    (rows : List (List UInt64)) :
    rows ∈ RuntimeCandidate.partitionMatch n occ tail rhs ↔
      rows.length = n ∧ (∀ row ∈ rows, row ≠ [] ∧ row.Sublist rhs) ∧
      (FlatMatchSearch.expand rows occ ++ tail).Perm rhs := by
  simp only [RuntimeCandidate.partitionMatch, List.mem_filter, decide_eq_true_eq, mem_fitting,
    mem_images, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨len, valid, _⟩, perm⟩
    exact ⟨len, fun r hr => (valid r hr).symm, perm⟩
  · rintro ⟨len, valid, perm⟩
    have eq := perm.length_eq
    rw [List.length_append] at eq
    exact ⟨⟨len, fun r hr => (valid r hr).symm, by omega⟩, perm⟩

theorem correct : RuntimeCandidate.flatMatcher.Correct := by
  intro n occ tail rhs rows
  change rows ∈ RuntimeCandidate.flatMatch n occ tail rhs ↔ _
  unfold RuntimeCandidate.flatMatch
  split
  next valid =>
    have bounds (hl : rows.length = n) (hn : ∀ row ∈ rows, row ≠ [] ∧ row.Sublist rhs) :=
      expanded_length rows occ (fun i hi => by
        have hib : i < rows.length := hl ▸ valid i hi
        have hne := (hn rows[i] (List.getElem_mem hib)).1
        simpa [List.getElem?_eq_getElem hib] using List.length_pos_iff.mpr hne)
    split
    next short =>
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨hl, hn, hp⟩
      have hb := (bounds hl hn).1
      have he := hp.length_eq
      rw [List.length_append] at he
      omega
    next =>
      split
      next full =>
        simp only [List.mem_filter, decide_eq_true_eq, mem_singletons, List.mem_eraseDups]
        constructor
        · rintro ⟨⟨hl, hs⟩, hp⟩
          refine ⟨hl, ?_, hp⟩
          intro r hr
          obtain ⟨a, ha, rfl⟩ := hs r hr
          exact ⟨by simp, List.singleton_sublist.mpr ha⟩
        · rintro ⟨hl, hn, hp⟩
          refine ⟨⟨hl, ?_⟩, hp⟩
          have he := hp.length_eq
          rw [List.length_append, ← full.1] at he
          have ones := (bounds hl hn).2 (by omega)
          intro row hr
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
          have h1 := ones i (full.2 i (List.mem_range.mpr (hl ▸ hi)))
          simp only [List.getElem?_eq_getElem hi, Option.getD_some] at h1
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
          exact ⟨a, List.singleton_sublist.mp (ha ▸ (hn _ (List.getElem_mem hi)).2), ha⟩
      next => exact mem_partition _ _ _ _ _
  next => exact mem_partition _ _ _ _ _

theorem exported (n : UInt64) (occ tail rhs : Array UInt64) (rows : List (List UInt64)) :
    rows ∈ (Executable.flatACMatch n occ tail rhs).toList.map (fun answer => answer.toList.map Array.toList) ↔
    rows.length = n.toNat ∧ (∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs.toList) ∧
      (FlatMatchSearch.expand rows (occ.toList.map UInt64.toNat) ++ tail.toList).Perm rhs.toList := by
  simpa [Executable.flatACMatch, List.map_map, Function.comp_def] using
    correct n.toNat (occ.toList.map UInt64.toNat) tail.toList rhs.toList rows

/-- End-to-end semantic refinement of the actual exported rows, under the
request-local atom codec and full variable-identity table. Rust/C memory
layout and faithful construction of those tables remain separate obligations. -/
theorem semantic {sig : Signature} [DecidableEq sig.Atom]
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64) (f : sig.ACSym)
    (n : UInt64) (vars : Fin n.toNat → Variable) (occ : List (Fin n.toNat))
    (tail rhs : Array UInt64) (live : ∀ id ∈ tail.toList ++ rhs.toList, encode (decode id) = some id)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs.toList.map decode, Subsort (sig.atomSort a) (sig.acSort f))
    (hi : Function.Injective vars) (ho : ∀ i, i ∈ occ)
    (hq : FlatMatching.queryLeaves vars occ (tail.toList.map decode) ≠ [])
    (hr : rhs.toList ≠ []) :
    let out := (Executable.flatACMatch n (occ.map (fun i => UInt64.ofNat i.val)).toArray tail rhs).toList.map
      (fun answer => answer.toList.map (fun row => row.toList.map decode))
    ∃ hout : ∀ rows ∈ out, FlatMatching.admissibleRows (n := n.toNat) (rhs.toList.map decode) rows,
      Matching.Complete
        [⟨FlatMatching.pattern f (FlatMatching.queryLeaves vars occ (tail.toList.map decode)),
          FlatAC.term f (rhs.toList.map decode)⟩] (fun _ => True)
        (FlatMatching.answersFrom f vars (rhs.toList.map decode) hv hs out hout) := by
  dsimp only
  have hocc : (occ.map (fun i => UInt64.ofNat i.val)).map UInt64.toNat = occ.map Fin.val := by
    simp only [List.map_map]
    congr 1
    funext i
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt n.toNat_lt_size)
  have hm : ∀ rows,
      rows ∈ (Executable.flatACMatch n (occ.map (fun i => UInt64.ofNat i.val)).toArray tail rhs).toList.map
        (fun answer => answer.toList.map (fun row => row.toList.map decode)) ↔
      rows ∈ FlatMatchSearch.solve n.toNat (occ.map Fin.val) (tail.toList.map decode) (rhs.toList.map decode) := by
    intro rows
    simpa [Executable.flatACMatch, List.map_map, Function.comp_def, hocc] using
      correct.decoded_rows decode encode n.toNat (occ.map Fin.val) tail.toList rhs.toList live rows
  have hout : ∀ rows ∈ (Executable.flatACMatch n (occ.map (fun i => UInt64.ofNat i.val)).toArray tail rhs).toList.map
      (fun answer => answer.toList.map (fun row => row.toList.map decode)),
      FlatMatching.admissibleRows (n := n.toNat) (rhs.toList.map decode) rows := by
    intro rows h
    have hh := (FlatMatchSearch.mem_solve _ _ _ _ _).mp ((hm rows).mp h)
    exact ⟨hh.1, hh.2.1⟩
  exact ⟨hout, FlatMatching.complete_of_rows f vars occ _ _ hv hs hi ho hq
    (by simpa using hr) _ hout hm⟩

end Tamarin.FlatMatchCandidateProofs
