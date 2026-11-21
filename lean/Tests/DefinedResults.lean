import Tamarin.DefinedPatterns
import Tamarin.SubtermVariants
import Tamarin.TableWire

namespace Tamarin.DefinedResultsTests
open Rewriting

-- Every captured source frontier bounds all its normalized instances, including
-- the instances that enable a further equation inside the open right side.
example {s : Signature} {rs : Problem s} {r : Equation s} {rows}
    (hit : CheckedVariants.Reply (ruleRoot rs) [r.lhs] rows) : SubtermVariants.RowPaths rs r :=
  ShortVariantPaths.bounded_paths_of_complete_variants hit.complete

-- decode(box(x)) -> wrap(check(x)), check(a) -> b. The second rule fires
-- only for x=a, and the first result can escape with an open check(x).
private def ds : Array UInt64 := #[
  2,0,1,2,2, 2,1,1,2,2, 2,2,1,2,2, 2,3,0,2, 2,4,0,2, 2,5,1,2,2]
private def ns : Array (Array UInt64) := #[
  #[0,17,2], #[2,1,0], #[2,0,1], #[2,2,0], #[2,3], #[2,4], #[2,2,4], #[2,5,3]]
private def source (roots : Array UInt64) : Bool := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input ds ns roots #[] | return false
  let some r := rs.find? (fun r => match r.lhs with | .free f _ => f.val == 0 | _ => false) | return false
  return (DefinedPatterns.frontier rs 4 r).isSome

#guard source #[2,7, 6,5]
#guard source #[6,5, 2,7]
-- At x=a the extra check(a) -> a would make wrap(a) and wrap(b) both normal.
#guard !source #[2,7, 6,5, 6,4]

end Tamarin.DefinedResultsTests
