import TamarinCI

namespace Tamarin.OpenMatchSelectTests
open OpenMatchSelect

private def solve := Executable.openMatchSelect

#guard (solve 0 0).any (·.contains #[])
#guard solve 1 0 == some #[]
#guard (solve 0 3).any (fun out => out.any (fun row => row.toList.mergeSort == [0,1,2]))
#guard (solve 2 3).any (·.contains #[2,0,1])
#guard (solve 2 64).any (fun out => 4032 ≤ out.size && out.size ≤ 4096)
#guard solve 3 64 == none
#guard solve 1 65 == none
#guard solve 66 65 == some #[]
#guard solve 18446744073709551615 18446744073709551615 == none

private def words (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k+1 => (words n k).flatMap (fun tail => (List.range n).map (· :: tail))

-- Check every row is a full permutation and every ordered prefix is present.
private def stress (kernel : Kernel) : Bool := Id.run do
  for n in List.range 6 do
    let perms := (words n n).filter (fun row => decide row.Nodup)
    for k in List.range (n+2) do
      let some out := kernel k.toUInt64 n.toUInt64 | return false
      let rows := decoded out
      if !(rows.all fun row => k ≤ n && perms.contains row) then return false
      if k ≤ n then
        let prefixes := rows.map (·.take k)
        if !(perms.all fun row => prefixes.contains (row.take k)) then return false
  return true
#guard stress solve

private def reverseSuffix {α} (k : Nat) (xs : List α) := xs.take k ++ (xs.drop k).reverse

-- Deliberately change the representation of *every* completed packet.
private def alternative (k n : UInt64) : Option Packet :=
  (solve k n).map (fun out => out.map (fun r => (reverseSuffix k.toNat r.toList).toArray))

private theorem decode_reverse (k : Nat) (out : Packet) :
    decoded (out.map (fun r => (reverseSuffix k r.toList).toArray)) =
      (decoded out).map (reverseSuffix k) := by
  simp [decoded,reverseSuffix,List.map_map, Function.comp_def,List.map_take,List.map_drop]

private theorem alternative_correct : Correct alternative := by
  have c : Correct solve := exportedOpenMatchSelect_correct
  constructor
  · intro k n
    simpa [alternative] using c.completes k n
  · intro k n out h
    obtain ⟨a,ran,rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using c.bounded k n a ran
  · intro k n out row h member
    obtain ⟨a,ran,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [decode_reverse] at member
    obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp member
    obtain ⟨size,perm⟩ := c.sound ran hx
    have rearrange : (reverseSuffix k.toNat xs).Perm xs := by
      simpa [reverseSuffix] using ((xs.drop k.toNat).reverse_perm.append_left (xs.take k.toNat))
    exact ⟨rearrange.length_eq.symm ▸ size,rearrange.trans perm⟩
  · intro k n out pick h len nd live
    obtain ⟨a,ran,rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rest,member⟩ := c.prefixes pick ran len nd live
    refine ⟨rest.reverse,?_⟩
    rw [decode_reverse]
    exact List.mem_map.mpr ⟨_,member,by simp [reverseSuffix,← len]⟩

#guard stress alternative

-- A two-element remainder witnesses that this transformation can actually
-- change a row, even though it preserves the contract on all inputs.
#guard reverseSuffix 1 [1,0,2] == [1,2,0]

end Tamarin.OpenMatchSelectTests
