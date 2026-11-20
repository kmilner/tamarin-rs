import Tamarin.CertifiedTableWire
import Tamarin.BilinearWireData

/-! Admission of the production packet carrying point actions, the commutative
map, both active AC group products, and ordinary pairing projections. -/
namespace Tamarin.BilinearWire

theorem admitted : CertifiedTableWire.run declarations nodes ruleRoots 0 = true := by decide +kernel

end Tamarin.BilinearWire
