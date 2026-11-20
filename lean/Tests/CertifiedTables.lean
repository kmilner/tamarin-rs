import Tamarin.CertifiedTable
import Tamarin.DHWire
import Tamarin.DHConstructorWire
import Tamarin.XorConstructorWire
import Tamarin.JointGroupWire

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

-- The encoder puts the three XOR equations last in the mixed six-rule packet.
-- A missing or reversed equation must never select the full XOR presentation.
private def xorPacket := (TableWire.input XorConstructorWire.declarations XorConstructorWire.nodes
    XorConstructorWire.ruleRoots #[]).get (by decide +kernel)
private abbrev xorRules := xorPacket.2.1

#guard xorRules.length == 6
#guard CertifiedTable.admits xorRules.reverse 0
#guard (List.range 3).all fun offset => !CertifiedTable.admits (xorRules.eraseIdx (offset + 3)) 4
#guard (List.range 3).all fun offset =>
  !CertifiedTable.admits (xorRules.modify (offset + 3) fun r => ⟨r.rhs,r.lhs⟩) 4

-- This extra row keeps every original equation, but makes m ⊕ m return m too.
#guard !CertifiedTableWire.run XorConstructorWire.declarations XorConstructorWire.nodes
  (XorConstructorWire.ruleRoots ++ #[9,0]) 4

private def jointPacket := (TableWire.input JointGroupWire.declarations JointGroupWire.nodes
    JointGroupWire.ruleRoots #[]).get (by decide +kernel)
private abbrev jointRules := jointPacket.2.1

-- On this production packet only fst and snd (positions 3 and 7) are optional.
-- Every one of the 16 group rows must have its original orientation.
#guard jointRules.length == 18
#guard CertifiedTable.admits ((jointRules.eraseIdx 7).eraseIdx 3).reverse 0
#guard (List.range 18).all fun i => i == 3 || i == 7 ||
  (!CertifiedTable.admits (jointRules.eraseIdx i) 0 &&
   !CertifiedTable.admits (jointRules.modify i fun r => ⟨r.rhs,r.lhs⟩) 0)

-- Relabeling every XOR application with the DH product's ID makes the two
-- rule sets compete for the same redex, even though all rows are still present.
#guard !CertifiedTableWire.run JointGroupWire.declarations
  (JointGroupWire.nodes.map fun row => if row[0]! == 4 && row[1]! == 8 then row.set! 1 4 else row)
  JointGroupWire.ruleRoots 4

end Tamarin.CertifiedTableTests
