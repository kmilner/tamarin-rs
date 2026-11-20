import Tamarin.CheckedVariants
import Tamarin.FrontierWork
import Tamarin.TableWire
import Tamarin.TableAmbient

/-! Numeric interface to locally checked variant search on the active rule
table. The depth bounds frontier discovery and replay. Only a certified
complete family can produce a successful packet. -/
namespace Tamarin.CheckedVariantsWire
open TotalUnifyWire Rewriting MaudeOperations

private def search {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (fuel : UInt64) :=
  if TableDecrease.sorted rs && FrontierWork.admits rs q fuel.toNat then
    CheckedVariants.solve (TableAmbient.liftRules rs) (q.map TableAmbient.liftTerm) fuel.toNat fuel.toNat
  else none

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (rules roots : Array UInt64) (fuel : UInt64) :
    Array (Array UInt64) :=
  match TableWire.input ds ns rules roots with
  | none => #[#[0]]
  | some ⟨_,rs,q⟩ =>
    match search rs q fuel with
    | none => #[#[2]]
    | some rows => (TableAmbient.emit q rows.val).getD #[#[2]]

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array UInt64 → UInt64 → Array (Array UInt64)

def Required {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (fuel : UInt64) : Prop :=
  ∃ rows, search rs q fuel = some rows ∧ ∃ wire, TableAmbient.emit q rows.val = some wire

def Decodes {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (wire : Array (Array UInt64)) :=
  ∃ rows, TableAmbient.Decodes q wire rows ∧
    CheckedVariants.Reply (ruleRoot (TableAmbient.liftRules rs)) (q.map TableAmbient.liftTerm) rows

structure Correct (kernel : Kernel) : Prop where
  malformed : ∀ ds ns rs qs n, TableWire.input ds ns rs qs = none → kernel ds ns rs qs n = #[#[0]]
  valid : ∀ ds ns pairs roots n d rs q, TableWire.input ds ns pairs roots = some ⟨d,rs,q⟩ →
    Decodes rs q (kernel ds ns pairs roots n) ∨
      (kernel ds ns pairs roots n = #[#[2]] ∧ ¬ Required rs q n)

theorem correct : Correct run where
  malformed := by intros; simp_all [run]
  valid := by
    intro ds ns pairs roots n d rs q decoded
    simp only [run,decoded]
    cases h : search rs q n with
    | none => exact .inr ⟨rfl,by simp [Required,h]⟩
    | some rows =>
      cases g : TableAmbient.emit q rows.val with
      | some packet =>
        exact .inl ⟨rows.val,by simpa [g] using TableAmbient.emit_correct g,rows.property⟩
      | none => exact .inr ⟨by simp [g],by simp [Required,h,g]⟩

end Tamarin.CheckedVariantsWire
