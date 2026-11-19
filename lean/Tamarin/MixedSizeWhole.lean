import Tamarin.MixedSizeGraph

namespace Tamarin.MixedSizeWhole
open Whole WholeProblem

private theorem refutes : Refutes MixedSizeGraph.refutesDecoded := by
  intro sig c p ds ns es rows decoded layout faithful negative
  exact MixedSizeGraph.refutesDecoded_unsatisfiable c p ⟨layout,faithful⟩ negative

theorem correct : Correct (runRefining MixedSizeGraph.refutesDecoded) :=
  runRefining_correct refutes

/-- Every admitted inconsistent affine system must give a complete empty
family at the existing unification export, for the original encoded terms. -/
def Required (run : Kernel) : Prop :=
  ∀ {s : Signature} (c : Codec s) (p : Problem s) ds ns es rows,
    Wire.decodeProblem ds ns es = some rows → RowLayout (encodeRows c p) rows →
    Faithful c p → MixedSizeGraph.Required c p ns es → run ds ns es = #[#[1]]

theorem required : Required (runRefining MixedSizeGraph.refutesDecoded) := by
  intro s c p ds ns es rows decoded layout faithful admitted
  exact runRefining_empty refutes c p decoded layout faithful (MixedSizeGraph.refutesDecoded_required c p layout admitted)

end Tamarin.MixedSizeWhole
