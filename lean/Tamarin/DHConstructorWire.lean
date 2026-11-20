import Tamarin.DHConstructorExtension
import Tamarin.DHConstructorWireData
import Tamarin.DHWire

/-! The production encoder's DH, pairing, encryption, signing, reveal-signing
and locations table. All checks run on the table lifted to arbitrary caller atoms. -/
namespace Tamarin.DHConstructorWire
open Rewriting DHPeer MaudeOperations
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private def packet := TableWire.input declarations nodes ruleRoots observationRoots
private def parsed := packet.get (by decide +kernel)
abbrev dict := parsed.1
abbrev rules := parsed.2.1
abbrev observations := parsed.2.2

theorem decoded : TableWire.input declarations nodes ruleRoots observationRoots =
    some ⟨dict,rules,observations⟩ := Option.some_get _ |>.symm

private def declared := DHWire.readSymbols (d := dict) ⟨0,by decide +kernel⟩ ⟨1,by decide +kernel⟩
  ⟨2,by decide +kernel⟩ ⟨3,by decide +kernel⟩ ⟨4,by decide +kernel⟩
private def ambient := DHWire.liftSymbols (declared.get (by decide +kernel))
private def keys (i : Fin 3) : Variable := ⟨i.val,.msg⟩

private theorem admitted : ConstructorExtension.accepts ambient keys ExactTable.weight 1 (TableAmbient.liftRules rules) := by
  simp only [ConstructorExtension.accepts,Bool.and_eq_true]
  exact ⟨⟨⟨by decide +kernel, by decide +kernel⟩,by decide +kernel⟩,by decide +kernel⟩

theorem complete : ReferenceReduction.Bound (TableAmbient.liftRules rules) ∧
    CanonicalPresentation (ruleRoot (TableAmbient.liftRules rules)) ∧
    FiniteVariantProperty (ruleRoot (TableAmbient.liftRules rules)) :=
  ConstructorExtension.accepts_sound ambient keys (fun _ => rfl) (fun _ _ e => Fin.ext (congrArg Variable.id e))
    admitted

end Tamarin.DHConstructorWire
