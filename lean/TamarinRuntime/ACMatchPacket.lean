/-! Alternating rows of request-local pattern-variable and rigid-factor
identifiers for a directional matching decision. -/
namespace Tamarin.Matching.ACMatchPacket

abbrev Row := List UInt64 × List UInt64
abbrev Packet := Array (Array UInt64)

def decode : List (Array UInt64) → Option (List Row)
  | [] => some []
  | pat :: subj :: tail => ((pat.toList,subj.toList) :: ·) <$> decode tail
  | [_] => none

def runWith (solve : List Row → Option Bool) (packet : Packet) : UInt8 :=
  match (decode packet.toList).bind solve with
  | none => 0
  | some false => 1
  | some true => 2

end Tamarin.Matching.ACMatchPacket
