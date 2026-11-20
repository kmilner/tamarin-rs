import Tamarin.CheckedReductionWire

/-! A stage checks the original term against all active equations. Status 3
requests more rewrite depth. Status 2 records an unsupported table or a witnessed
conflict between normal forms. Status 1 carries the unique normal form. -/
namespace Tamarin.GeneralReductionWire

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (pairs : Array UInt64) (root fuel : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns pairs #[root] with
  | some ⟨_,rs,[t]⟩ =>
    if !CheckedReduction.rangeBound rs then #[#[2]] else
    match CheckedReduction.run rs fuel.toNat t with
    | some u => CheckedReductionWire.emit u
    | none => if CheckedReduction.ambiguous rs fuel.toNat t then #[#[2]] else #[#[3]]
  | _ => #[#[0]]

end Tamarin.GeneralReductionWire
