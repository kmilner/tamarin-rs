import TamarinRuntime.OperandUnification

namespace Tamarin.MaskedOperands
open ACBasis Homogeneous

abbrev Mask (n : Nat) := Fin n → Bool
def wordMask (n : Nat) (bits : UInt64) : Mask n := fun i => bits.toNat.testBit i.val

def usable {n} (mask : Mask n) (v : Vec n) : Bool := decide (∀ i, mask i = true → v i ≤ 1)

def maskBits {n} (mask : Mask n) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn mask)).cast (by simp)

def spend (credit cost : Nat) : Option Nat :=
  if cost ≤ credit then some (credit-cost) else none

/-- Charge each visited prefix and each emitted word before assembling the
packet. On exhaustion a caller can still attempt its other complete splits. -/
def collect {n α} (allow : α → Bool) (weight : α → Nat) (mask full : BitVec n) :
    Coverage.Plan α n → BitVec n → Nat → Nat → Option (Nat × List (List α))
  | .done, seen, words, credit => do
    let credit ← spend credit 1
    if seen ≠ full then return (credit, [])
    return (← spend credit words, [[]])
  | .step x support remaining tail, seen, words, credit => do
    let credit ← spend credit 1
    if seen ||| remaining ≠ full then return (credit, [])
    let (credit, skip) ← collect allow weight mask full tail seen words credit
    if !allow x || seen &&& support &&& mask != 0 then return (credit, skip)
    let (credit, take) ← collect allow weight mask full tail (seen ||| support) (words+weight x) credit
    return (credit, skip ++ take.map (x :: ·))

def takeSelections {n} (gs : List (Vec n)) (mask : Mask n) (credit : Nat) :=
  let allow := Vector.ofFn (fun j => usable mask (gs.get j))
  let weight := Vector.ofFn (fun j => total (gs.get j))
  let plan := Coverage.prepare (fun j => Coverage.support (gs.get j)) (List.finRange gs.length)
  collect (fun j => allow[j]) (fun j => weight[j]) (maskBits mask) (BitVec.allOnes n) plan 0 (1+2*n) credit

def run (width bits : UInt64) (sides : Array (Array UInt64)) : Option Answers := do
  let m ← OperandCounts.run width sides
  guard (bits.toNat < 2^width.toNat && GraphUnification.hasConstraint m.toList)
  let rows ← readRows width.toNat m.toList
  let gs ← boundedBasis rows
  guard (gs.length ≤ 64)
  let mask := wordMask width.toNat bits
  if let some (_, js) := takeSelections gs mask 131072 then
    return (js.map (arm gs)).toArray
  guard (fitsOutput gs)
  return (emit gs).filter fun a => (List.finRange width.toNat).all fun i =>
    !mask i || (a[i.val]?.map Array.size == some 1)

end Tamarin.MaskedOperands
