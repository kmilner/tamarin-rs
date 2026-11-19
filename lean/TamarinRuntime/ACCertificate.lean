import TamarinRuntime.ACSimplex
import TamarinRuntime.ACSeparation
import TamarinRuntime.ACReducedFeasibility

namespace Tamarin.ACFeasibility
open ACBasis

/-- Check an arbitrary candidate on the original equations. Both branches
return unknown on a malformed or inconclusive certificate. -/
def checkCertificate {n} (rows : List (Row n)) : Simplex.Certificate → Option Bool
  | .primal x =>
    if h : x.size = n then
      if positiveCertificate rows ⟨x,h⟩ then some true else none
    else none
  | .dual y => if Separation.separates rows y.toList then some false else none

def certifiedSearch {n} (rows : List (Row n)) : Option Bool :=
  (Simplex.search rows).bind (checkCertificate rows)

end Tamarin.ACFeasibility
