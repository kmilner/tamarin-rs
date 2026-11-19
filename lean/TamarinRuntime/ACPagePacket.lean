import TamarinRuntime.ACMatchPacket
import TamarinRuntime.ACBagPages

namespace Tamarin.Matching.ACPagePacket
open ACMatchPacket

/-- Little-endian base-2^64 digits, with the empty list for zero. -/
def cursor : List UInt64 → Nat
  | [] => 0
  | w :: tail => w.toNat + UInt64.size * cursor tail

def limbs (n : Nat) : List UInt64 :=
  if n = 0 then [] else n.toUInt64 :: limbs (n / UInt64.size)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def pack (stop total : Nat) (done : Bool) (answers : List (List (List UInt64))) : Answers :=
  (#[ (limbs stop).toArray, #[if done then 1 else 0], (limbs total).toArray ] ::
    answers.map (fun a => (a.map List.toArray).toArray)).toArray

def runWith (solve : List Row → Nat → Nat → Option ACBagPages.Page)
    (packet : Packet) (start : Array UInt64) (requested : UInt64) : Option Answers := do
  let rows ← decode packet.toList
  let page ← solve rows (cursor start.toList) requested.toNat
  return pack page.stop page.total page.done page.answers

end Tamarin.Matching.ACPagePacket
