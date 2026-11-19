import TamarinRuntime.ACForcedCoordinates
import TamarinRuntime.GraphMatrix

namespace Tamarin.ForcedOperandClasses
open ACBasis

abbrev Kernel := UInt64 → Array (Array UInt64) → Option (Array UInt64)

/-- Check the elimination dimensions before allocating the occurrence
histograms. Each side lists the IDs of its factors in occurrence order. -/
def run : Kernel := fun width sides => do
  guard (SpanCertificate.dimensions width.toNat (sides.size / 2) && sides.size % 2 == 0 &&
    sides.all (fun side => 0 < side.size && side.size < UInt64.size && side.all (· < width)))
  let rows ← Homogeneous.readRows width.toNat (sides.map (GraphMatrix.histogram width)).toList
  let labels ← ForcedCoordinates.run rows
  return labels.toArray.map Nat.toUInt64

end Tamarin.ForcedOperandClasses
