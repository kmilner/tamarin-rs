import TamarinRuntime
import Tamarin.DHExponentPacket

/-! Replay the emitted programs in the free abelian group on three atoms.
Expected old and new exponents come from integer addition. Each observation
of the old exponent uses the same assignment of the two residual slots. -/
open Tamarin Tamarin.Rewriting.DHPeer Tamarin.Rewriting.DHExponent

-- Reordering and repeating a correct image both pass the same fixed gate.
example : Packet.Correct ((Executable.dhExponentImages ()).reverse.push #[9]) :=
  Packet.of_accepts (by decide +kernel)

private abbrev Bag := Int × Int × Int

private def add (a b : Bag) : Bag := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)
private def negate (a : Bag) : Bag := (-a.1, -a.2.1, -a.2.2)
private def positive (a : Bag) : Bag := (max 0 a.1, max 0 a.2.1, max 0 a.2.2)
private def zero : Bag := (0,0,0)

private def eval (old factor pos neg : Bag) : Expr Slot → Option Bag
  | .var .peer => some old
  | .var .fresh => some factor
  | .var .pos => some pos
  | .var .neg => some neg
  | .one => some zero
  | .inv t => (eval old factor pos neg t).map negate
  | .mul a b => return add (← eval old factor pos neg a) (← eval old factor pos neg b)
  | _ => none

private def check (programs : List (Expr Slot)) (old factor : Bag) : Bool := Id.run do
  let result := add old factor
  let pos := positive old
  let neg := positive (negate result)
  let branch : Rewriting.DHExponent.Branch := if old == zero then .unit
    else if positive (negate old) == neg then .unchanged
    else if pos == zero then (if neg == zero then .cancelAll else .cancelNegative)
    else if neg == zero then .cancelPositive else .cancelMixed
  return programs.any (fun image => image == branch.image && eval old factor pos neg image == some old)
    && eval old factor pos neg branch.result == some result

def main : IO Unit := do
  let rows := Executable.dhExponentImages ()
  let some programs := rows.toList.mapM Packet.decode | throw <| IO.userError "malformed exponent image"
  let mut checks := 0
  for a in [:9] do
    for b in [:9] do
      for c in [:9] do
        let old : Bag := (Int.ofNat a-4, Int.ofNat b-4, Int.ofNat c-4)
        for factor in [(1,0,0), (0,1,0), (0,0,1)] do
          unless check programs old factor do throw <| IO.userError s!"old {old}, factor {factor}"
          checks := checks + 1
  IO.println s!"{checks} joint old/product DH exponent observations replayed"
