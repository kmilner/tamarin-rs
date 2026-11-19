import Tamarin.FlatMatching
import TamarinRuntime.Interface

namespace Tamarin

/-- A fixed, declarative denotation: enumerate every solution using nonempty
subsequence representatives. Answer order and duplicate answers are irrelevant.
Subsequences may contain several orderings of the same AC image;
`FlatMatching.complete` proves that it loses no semantic matching solutions. -/
def FlatMatchBackend.Correct (backend : FlatMatchBackend) : Prop :=
  ∀ n occ tail rhs rows, rows ∈ backend.run n occ tail rhs ↔
    rows.length = n ∧ (∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs) ∧
      (FlatMatchSearch.expand rows occ ++ tail).Perm rhs

/-- Any algorithm satisfying the fixed contract enumerates the same decoded
row set as the proved reference, without requiring algorithm equality. -/
theorem FlatMatchBackend.Correct.mem_iff {backend : FlatMatchBackend}
    (h : backend.Correct) (n : Nat) (occ : List Nat) (tail rhs : List UInt64)
    (rows : List (List UInt64)) : rows ∈ backend.run n occ tail rhs ↔
      rows ∈ FlatMatchSearch.solve n occ tail rhs :=
  (h n occ tail rhs rows).trans (FlatMatchSearch.mem_solve n occ tail rhs rows).symm

theorem FlatMatchBackend.Correct.decoded_rows {backend : FlatMatchBackend}
    (h : backend.Correct) {α : Type} [DecidableEq α] (decode : UInt64 → α)
    (encode : α → Option UInt64) (n : Nat) (occ : List Nat) (tail rhs : List UInt64)
    (live : ∀ id ∈ tail ++ rhs, encode (decode id) = some id) (mapped : List (List α)) :
    mapped ∈ (backend.run n occ tail rhs).map (List.map (List.map decode)) ↔
      mapped ∈ FlatMatchSearch.solve n occ (tail.map decode) (rhs.map decode) := by
  rw [FlatMatchSearch.mem_solve_map decode encode n occ tail rhs live]
  constructor
  · intro hm
    obtain ⟨rows, hr, rfl⟩ := List.mem_map.mp hm
    exact ⟨rows, (h.mem_iff n occ tail rhs rows).mp hr, rfl⟩
  · rintro ⟨rows, hr, rfl⟩
    exact List.mem_map.mpr ⟨rows, (h.mem_iff n occ tail rhs rows).mpr hr, rfl⟩

end Tamarin
