import Tamarin.CertifiedTable
import Tamarin.TableWire

/-! One certificate can justify both staged operations on the same complete
rule table. Its result is independent of which observations are selected. -/
namespace Tamarin.CertifiedTableWire

def run (ds : Array UInt64) (ns : Array (Array UInt64)) (rules : Array UInt64) (fuel : UInt64) : Bool :=
  match TableWire.input ds ns rules #[] with
  | none => false
  | some ⟨_,rs,_⟩ => CertifiedTable.admits rs fuel.toNat

def Certified {d : TotalUnifyWire.Dictionary} (rs : Problem d.sig) : Prop :=
  ReferenceReduction.Bound (TableAmbient.liftRules rs) ∧
  MaudeOperations.CanonicalPresentation (Rewriting.ruleRoot (TableAmbient.liftRules rs)) ∧
  MaudeOperations.FiniteVariantProperty (Rewriting.ruleRoot (TableAmbient.liftRules rs))

/-- A replacement can certify additional theories by proving their semantic
properties. Recognizing the existing class is a minimum coverage obligation. -/
def Correct (check : Array UInt64 → Array (Array UInt64) → Array UInt64 → UInt64 → Bool) : Prop :=
  ∀ ds ns es fuel, match TableWire.input ds ns es #[] with
    | none => check ds ns es fuel = false
    | some ⟨_,rs,_⟩ =>
      (CertifiedTable.admits rs fuel.toNat → check ds ns es fuel = true) ∧
      (check ds ns es fuel = true → Certified rs)

theorem correct : Correct run := by
  intro ds ns es fuel
  cases h : TableWire.input ds ns es #[] with
  | none => simp [run,h]
  | some packet =>
    obtain ⟨d,rs,q⟩ := packet
    simpa only [run,h] using
      (show (_ → _) ∧ (_ → Certified rs) from ⟨id,CertifiedTable.admits_sound (fuel := fuel.toNat)⟩)

/-- A kernel proof on a concrete baseline packet applies to every executable
checker satisfying the replacement contract. -/
theorem Correct.admits {check} (spec : Correct check) {ds ns es fuel}
    (baseline : run ds ns es fuel = true) : check ds ns es fuel = true := by
  have h := spec ds ns es fuel
  unfold run at baseline
  split at h <;> simp_all

theorem sound {check} (spec : Correct check) {ds ns es roots d rs q fuel}
    (decoded : TableWire.input ds ns es roots = some ⟨d,rs,q⟩) (hit : check ds ns es fuel = true) :
    Certified rs := by
  have contract := spec ds ns es fuel
  rw [TableWire.withoutObservations decoded] at contract
  exact contract.2 hit

end Tamarin.CertifiedTableWire
