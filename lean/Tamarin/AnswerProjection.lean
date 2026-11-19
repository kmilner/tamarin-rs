import TamarinRuntime.AnswerProjection
import Std.Data.HashMap.Lemmas

/-! The caller assigns names to dense ordinals. The ordinal of a witness is its
first-appearance index in the list of distinct slots, shared across all columns
and arms. Column tags index the original query's variable inventory. -/
namespace Tamarin.AnswerProjection
open Homogeneous

def slots (raw : Answers) : List UInt64 := raw.toList.flatMap fun arm => arm.toList.flatMap Array.toList

def keys (raw : Answers) := (slots raw).eraseDups

def rank (raw : Answers) (j : UInt64) := ((keys raw).idxOf j).toUInt64

def tagArm (ordinal : UInt64 → UInt64) (arm : Arm) : Arm :=
  Array.ofFn fun i : Fin arm.size => #[i.val.toUInt64] ++ arm[i].map ordinal

def Shape (width : UInt64) (raw : Answers) : Prop :=
  0 < width ∧ width ≤ 65 ∧ ∀ a ∈ raw.toList,
    a.size = width.toNat ∧ ∀ row ∈ a.toList, row ≠ #[]

def Admitted (width : UInt64) (raw : Answers) := Shape width raw ∧ (keys raw).length ≤ UInt64.size

def Correct (p : Kernel) : Prop :=
  ∀ width raw out, p width raw = some out ↔ Admitted width raw ∧ out = raw.map (tagArm (rank raw))

private theorem nodup_distinct (xs : List UInt64) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨by simp [List.mem_eraseDups], nodup_distinct _⟩
termination_by xs.length
decreasing_by have := List.length_filter_le (fun (v : UInt64) => !v == x) xs; simp; omega

theorem keys_nodup (raw : Answers) : (keys raw).Nodup := nodup_distinct _

theorem keys_fit (raw : Answers) : (keys raw).length ≤ UInt64.size := by
  let ks := keys raw
  have distinct : (ks.map UInt64.toNat).Nodup := by
    apply List.Pairwise.map (R := (· ≠ ·))
    · intro a b different same
      exact different (UInt64.toNat_inj.mp same)
    · exact keys_nodup raw
  have subset : ks.map UInt64.toNat ⊆ List.range UInt64.size := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact List.mem_range.mpr j.toNat_lt_size
  simpa [ks] using distinct.length_le_of_subset subset

private theorem rank_nat (raw : Answers) {j : UInt64} (hj : j ∈ slots raw) :
    (rank raw j).toNat = (keys raw).idxOf j := by
  exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le
    (List.idxOf_lt_length_of_mem (List.mem_eraseDups.mpr hj)) (keys_fit raw))

theorem rank_lt {width raw} (_ : Admitted width raw) {i} (hi : i ∈ slots raw) :
    (rank raw i).toNat < (keys raw).length := by
  rw [rank_nat raw hi]
  exact List.idxOf_lt_length_of_mem (List.mem_eraseDups.mpr hi)

theorem rank_injective {width raw} (h : Admitted width raw) {i j} (hi : i ∈ slots raw) (hj : j ∈ slots raw)
    (eq : rank raw i = rank raw j) : i = j := by
  have same := congrArg UInt64.toNat eq
  rw [rank_nat raw hi, rank_nat raw hj] at same
  have atI := List.getElem_idxOf (rank_nat raw hi ▸ rank_lt h hi)
  have atJ := List.getElem_idxOf (rank_nat raw hj ▸ rank_lt h hj)
  simpa [same, atJ] using atI.symm

theorem rank_onto (raw : Answers) (i : Fin (keys raw).length) :
    ∃ j ∈ slots raw, (rank raw j).toNat = i.val := by
  have inKeys : (keys raw)[i.val] ∈ keys raw := List.getElem_mem i.isLt
  have used := List.mem_eraseDups.mp inKeys
  exact ⟨_, used, (rank_nat _ used).trans ((keys_nodup raw).idxOf_getElem _ i.isLt)⟩

private def Tracks (seen : Std.HashMap UInt64 Nat) (ks : List UInt64) : Prop :=
  seen.size = ks.length ∧ ∀ j, seen[j]? = if j ∈ ks then some (ks.idxOf j) else none

private theorem distinct_push (xs : List UInt64) (j : UInt64) :
    (xs ++ [j]).eraseDups = if j ∈ xs.eraseDups then xs.eraseDups else xs.eraseDups ++ [j] := by
  rw [List.eraseDups_append]
  by_cases hit : j ∈ xs <;> simp [hit, List.removeAll, List.mem_eraseDups, List.eraseDups_cons]

private theorem tracks_push {seen xs} (h : Tracks seen xs.eraseDups) (k : UInt64) :
    Tracks (insertSlot seen k) (xs ++ [k]).eraseDups := by
  obtain ⟨size, get⟩ := h
  have mem : k ∈ seen ↔ k ∈ xs.eraseDups := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, get]
    by_cases hit : k ∈ xs.eraseDups <;> simp [hit]
  rw [distinct_push]
  by_cases hit : k ∈ xs.eraseDups
  · simp [hit, Tracks, insertSlot, Std.HashMap.size_insertIfNew, Std.HashMap.getElem?_insertIfNew,
      mem.mpr hit, size, get]
  · have miss := mt mem.mp hit
    refine ⟨by simp [insertSlot, Std.HashMap.size_insertIfNew, miss, hit, size], ?_⟩
    intro j
    by_cases same : k = j
    · subst j
      simp only [insertSlot, Std.HashMap.getElem?_insertIfNew]
      simp [miss, hit, size, List.idxOf_append]
    · by_cases known : j ∈ xs.eraseDups <;>
        simp [insertSlot, Std.HashMap.getElem?_insertIfNew, hit, same, Ne.symm same, known, get,
          List.idxOf_append]

private theorem tracks_fold (words : List UInt64) (before : List UInt64) (seen : Std.HashMap UInt64 Nat)
    (h : Tracks seen before.eraseDups) : Tracks (words.foldl insertSlot seen) (before ++ words).eraseDups := by
  induction words generalizing before seen with
  | nil => simpa using h
  | cons j rest ih => simpa using ih (before ++ [j]) _ (tracks_push h j)

private theorem index_tracks (raw : Answers) : Tracks (indexSlots raw) (keys raw) := by
  have empty : Tracks ∅ ([] : List UInt64).eraseDups := by simp [Tracks]
  simpa [indexSlots, keys, slots, List.foldl_flatMap, Array.foldl_toList] using
    tracks_fold (slots raw) [] _ empty

private theorem computed_rank (raw : Answers) (j : UInt64) :
    ((indexSlots raw)[j]?.getD (indexSlots raw).size).toUInt64 = rank raw j := by
  obtain ⟨size, get⟩ := index_tracks raw
  by_cases hit : j ∈ keys raw <;> simp [rank, get, size, hit, List.idxOf_eq_length]

private theorem projected_row (raw : Answers) (row : Array UInt64) (col : UInt64) :
    row.foldl (fun acc slot => acc.push (((indexSlots raw)[slot]?.getD (indexSlots raw).size).toUInt64))
      ((Array.emptyWithCapacity (row.size + 1)).push col) = #[col] ++ row.map (rank raw) := by
  apply Array.toList_inj.mp
  simp only [computed_rank, ← Array.foldl_toList, Array.foldl_toList_eq_map]
  simp

theorem project_correct : Correct project := by
  intro width raw out
  have shape : (raw.all fun arm => arm.size == width.toNat && arm.all (fun row => !row.isEmpty)) = true ↔
      ∀ a ∈ raw.toList, a.size = width.toNat ∧ ∀ row ∈ a.toList, row ≠ #[] := by
    simp only [← Array.all_toList, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      Array.isEmpty_eq_false_iff]
  have fits : (indexSlots raw).size ≤ UInt64.size := (index_tracks raw).1 ▸ keys_fit raw
  by_cases w : 0 < width ∧ width ≤ 65
  · by_cases ok : ∀ a ∈ raw.toList, a.size = width.toNat ∧ ∀ row ∈ a.toList, row ≠ #[]
    · have admit : Admitted width raw := ⟨⟨w.1, w.2, ok⟩, keys_fit _⟩
      rw [show project width raw = some (raw.map (tagArm (rank raw))) from ?_]
      · simp only [Option.some.injEq, admit, true_and, eq_comm]
      · unfold project
        simp only [w, shape.mpr ok, fits, guard, ↓reduceIte, pure_bind, bind_pure_comp]
        exact congrArg some (congrArg (fun fn : Arm → Arm => raw.map fn) (funext (fun arm =>
          congrArg Array.ofFn (funext (fun i => projected_row raw arm[i.val] i.val.toUInt64)))))
    · have reject : ¬Admitted width raw := fun h => ok h.1.2.2
      simp [project, w, show _ = false from Bool.eq_false_iff.mpr (mt shape.mp ok), reject, guard, failure]
  · have reject : ¬Admitted width raw := fun h => w ⟨h.1.1,h.1.2.1⟩
    simp [project, w, reject, guard, failure]
end Tamarin.AnswerProjection
