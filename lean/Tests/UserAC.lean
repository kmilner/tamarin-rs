import Tamarin.CertifiedTableWire

namespace Tamarin.UserACTests

-- Two unrelated declared AC heads, op and plus, and two message constants.
-- The IDs and declaration order have no relation to Tamarin's builtin groups.
private def ds : Array UInt64 := #[2,19,0,2, 4,71,2,2,2,2, 4,11,2,2,2,2, 2,41,0,2]
private def ns : Array (Array UInt64) := #[
  #[0,17,2], #[2,41], #[4,71,0,1], #[4,71,1,0], #[2,19], #[4,11,4,0],
  #[1,21,3], #[4,71,6,1], #[4,71,7,0], #[4,71,6,0], #[4,71,0,0], #[4,11,1,0],
  #[4,11,2,4], #[4,71,7,1], #[4,71,1,1], #[0,71,2]]
private def check (rules : Array UInt64) := CertifiedTableWire.run ds ns rules 0
private def reduce (rules : Array UInt64) (start finish : UInt64) : Bool := Id.run do
  let some ⟨_,rs,[t,want]⟩ := TableWire.input ds ns rules #[start,finish] | return false
  return (CheckedReduction.run rs 4 t).any fun u => ReferenceMatching.equal u want

-- op(x,e)=x and op(e,x)=x express the same oriented rule modulo AC.
#guard check #[2,0]
#guard check #[3,0]
-- Two unit theories can have distinct units, or can share one unit.
#guard check #[5,0, 2,0]
#guard check #[11,0, 2,0]
-- Material participation of the unit and the captured variable is essential.
#guard !check #[2,15]
#guard !check #[0,2]
-- op(x,e)=a adds a competing contraction; e -> a makes the unit reducible.
#guard !check #[2,0, 2,4]
#guard !check #[2,0, 1,4]

-- Within a kind-level product, only a subproduct of messages may eliminate a
-- unit. A Node next to a lone unit is stuck; a second unit can reduce with it.
#guard reduce #[2,0] 7 7
#guard reduce #[2,0] 8 9
#guard reduce #[2,0] 13 7
#guard reduce #[2,0] 14 1
-- A single reduction may use both user-declared AC inventories.
#guard reduce #[2,0, 5,0] 12 0

end Tamarin.UserACTests
