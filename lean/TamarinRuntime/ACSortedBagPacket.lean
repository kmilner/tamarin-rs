import TamarinRuntime.ACMatchPacket
import TamarinRuntime.ACSortedBagSearch

namespace Tamarin.Matching.ACSortedBagPacket
open ACMatchPacket ACSortedBagSearch

def decodeLimits : List (Array UInt64) → Option Limits
  | [] => some []
  | w :: rest => do
    let key :: allowed := w.toList | none
    return (key,allowed) :: (← decodeLimits rest)

def runWith (solve : List Row → Limits → Option Bool) (rows limits : Packet) : UInt8 :=
  match (do
    let rs ← decode rows.toList
    let rules ← decodeLimits limits.toList
    solve rs rules) with
  | none => 0
  | some false => 1
  | some true => 2

end Tamarin.Matching.ACSortedBagPacket
