import Tamarin.CertifiedTable
import Tamarin.DHWire
import Tamarin.DHConstructorWire

namespace Tamarin.CertifiedTableTests
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

-- Reconstruct the operator assignment from both real Rust tables.
example : CertifiedTable.admits DHWire.rules 0 := by decide +kernel
example : CertifiedTable.admits DHConstructorWire.rules 0 := by decide +kernel

-- The five declarations are deliberately reordered, with new numeric IDs.
-- Rule variable IDs change too, and equation order has no semantic meaning.
private def relocated : Array UInt64 := #[4,14,2,2,2,2, 2,13,0,2, 2,12,0,2, 2,11,1,2,2, 2,10,2,2,2,2]
private def nodes := DHWire.nodes.map fun row =>
  if row[0]! == 0 then row.set! 1 (row[1]! + 51) else row.set! 1 (row[1]! + 10)

private def check (roots : Array UInt64) := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input relocated nodes roots #[] | return false
  return CertifiedTable.admits rs.reverse 0

#guard check DHWire.ruleRoots
-- Shape detection still sees all four hints after adding a competing DH rule.
-- Dropping one of the thirteen rules also rejects the module.
#guard !check (DHWire.ruleRoots ++ #[8,5])
#guard (List.range DHWire.rules.length).all fun i =>
  !CertifiedTable.admits (DHWire.rules.eraseIdx i) 1

-- Preserving operator vocabulary and row count alone cannot certify a
-- presentation. Reverse each oriented equation in turn.
#guard (List.range DHWire.rules.length).all fun i =>
  !CertifiedTable.admits (DHWire.rules.modify i (fun r => ⟨r.rhs,r.lhs⟩)) 1

end Tamarin.CertifiedTableTests
