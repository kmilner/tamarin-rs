import Std

/-! Admission to two-branch specialization of a ground-result rule. Flexible
arguments and all variables of captured terms share the caller's ID space.
Anchor IDs, in contrast, are drawn from the table rule's variable space. -/
namespace Tamarin.Rewriting.GroundVariantDecision

def Admitted (holes anchors deps : Array UInt64) (rigid : Bool) : Prop :=
  holes.toList.Nodup ∧ anchors.toList.Nodup ∧
  (∀ w ∈ holes.toList, w ∉ deps.toList) ∧ rigid = true

def Correct (run : Array UInt64 → Array UInt64 → Array UInt64 → Bool → UInt8) : Prop :=
  ∀ holes anchors deps rigid,
    (run holes anchors deps rigid = 3 ↔ Admitted holes anchors deps rigid) ∧
    (run holes anchors deps rigid = 0 ↔ ¬ Admitted holes anchors deps rigid)

end Tamarin.Rewriting.GroundVariantDecision
