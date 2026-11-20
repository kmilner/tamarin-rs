import Tamarin.ConstantDefinitions
import Tamarin.CheckedVariants
import Tamarin.FrontierWork
import Tamarin.TableWire
import Tamarin.TableAmbient

/-! Numeric interface to locally checked variant search on the active rule
table. The depth bounds frontier discovery and replay. Only a certified
complete family can produce a successful packet. -/
namespace Tamarin.CheckedVariantsWire
open TotalUnifyWire Rewriting MaudeOperations

def search {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (fuel : UInt64) :=
  if TableDecrease.sorted rs && FrontierWork.admits rs q fuel.toNat then
    CheckedVariants.solve (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat fuel.toNat
  else none

/-- Check the table once on its finite dictionary. A certificate in the
packet proof transfers admission to arbitrary additional caller names. -/
def definitions {d : Dictionary} (rs : Problem d.sig) : Bool :=
  ConstantDefinitions.accepts rs && TableDecrease.sorted rs

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64) (fuel : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns rules roots with
  | none => #[#[0]]
  | some ⟨_,rs,q⟩ =>
    if definitions rs then (pack (TableAmbient.observations q) [.identity]).getD #[#[2]]
    else match search rs q fuel with
    | none => #[#[2]]
    | some rows => (TableAmbient.emit q rows.val).getD #[#[2]]

end Tamarin.CheckedVariantsWire
