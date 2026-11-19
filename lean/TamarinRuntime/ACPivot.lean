namespace Tamarin.ACPivotCandidate

/-- One row encodes two equations: left slot, first image length, first image,
second left slot, second image. Slots 0–3 denote X, the pivot factor, Y, and
a fresh common remainder. Slots starting at 4 denote opposing occurrences. -/
def run (size : UInt64) : Option (Array (Array UInt64)) := do
  let n := size.toNat
  guard (0 < n && n ≤ 32)
  let others := (List.range n).map (fun i => (4 + i).toUInt64)
  let aligned := (List.finRange n).map fun i => ([1, 1, (4 + i.val).toUInt64, 0, 2] ++ others.eraseIdx i.val).toArray
  let separate := ([2, 1, 1, 0] ++ others).toArray
  let shared := ([2, 2, 1, 3, 0, 3] ++ others).toArray
  return (separate :: shared :: aligned).toArray

end Tamarin.ACPivotCandidate
