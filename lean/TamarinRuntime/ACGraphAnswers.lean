import TamarinRuntime.ACRayPacket
import TamarinRuntime.ACPrincipalRay

namespace Tamarin.GraphAnswers
open Homogeneous

/-- Keep the original ordered answers and try the cheap one-ray certificate
before constructing a larger Hilbert basis. The general fallback has the
same intermediate-generator and output budgets as the original solver. -/
def solve (width : UInt64) (m : Matrix) : Option Answers :=
  RayPacket.solve @ACBasis.PrincipalRay.run width m <|>
    if 32 < width then Homogeneous.solveUpTo 64 width m else none

end Tamarin.GraphAnswers
