import Tamarin.DestructorVariants
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

def certifiedSearch {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) :=
  let table := TableAmbient.liftRules rs
  let query := q.map TableAmbient.liftTerm
  if h : DestructorTable.accepts table && TableDecrease.sorted table then
    have ok := Bool.and_eq_true_iff.mp h
    have cls := (DestructorTable.accepts_iff table).mp ok.1
    some (DestructorTable.variants cls cls.decreasing ok.2 query)
  else none

def encode {d : Dictionary} {rs : Problem d.sig} (q : List (Term d.sig))
    (family : Option {rows // CheckedVariants.Reply (ruleRoot (TableAmbient.liftRules rs)) (q.map TableAmbient.liftTerm) rows}) :=
  family.bind fun rows => TableAmbient.emit q rows.val

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
    else ((encode q (search rs q fuel)).orElse fun _ => encode q (certifiedSearch rs q)).getD #[#[2]]

end Tamarin.CheckedVariantsWire
