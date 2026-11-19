import TamarinRuntime

open Tamarin.Executable

private def equivalent (w : UInt64) (sides : Array (Array UInt64)) (i j : Nat) : Option Bool := do
  let out ← forcedOperandClasses w sides
  return (← out[i]?) == (← out[j]?)

-- P + S = Q + T and P + 2S = Q + 2T force P = Q and S = T.
-- Extra unused columns, including ones beyond slot 32, remain independent.
private def coupled : Array (Array UInt64) := #[#[0,35],#[1,34],#[0,35,35],#[1,34,34]]
#guard equivalent 36 coupled 0 1 == some true
#guard equivalent 36 coupled 35 34 == some true
#guard equivalent 36 coupled 0 35 == some false
#guard equivalent 36 coupled 2 3 == some false
#guard equivalent 36 (coupled.extract 0 2) 0 1 == some false

#guard forcedOperandClasses 0 #[] == some #[]
#guard forcedOperandClasses 2 #[#[0],#[]] == none
#guard forcedOperandClasses 2 #[#[0]] == none
#guard forcedOperandClasses 2 #[#[0],#[2]] == none
