import Tamarin.DHCanonical
import Tamarin.NormalAlgebra

namespace Tamarin.Rewriting.DHPeer.ChurchRosser
export NormalAlgebra (representative representative_class Value value value_rep)
variable {sig : Signature}

/-- The normal-class product interpreted by the DH multiplication symbol. -/
abbrev Product (s : Symbols sig) (R : Root sig) := NormalAlgebra.Product s.mul R

end Tamarin.Rewriting.DHPeer.ChurchRosser
