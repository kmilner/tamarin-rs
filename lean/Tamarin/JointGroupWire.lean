import Tamarin.CertifiedTableWire
import Tamarin.JointGroupWireData

/-! Whole-table admission for the physical DH, XOR and pairing packet. -/
namespace Tamarin.JointGroupWire

theorem admitted : CertifiedTableWire.run declarations nodes ruleRoots 0 = true := by decide +kernel

end Tamarin.JointGroupWire
