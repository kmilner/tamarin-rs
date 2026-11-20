import Tamarin.CertifiedTableWire
import Tamarin.XorConstructorWireData

/-! Kernel check of the exact numeric table Rust encodes for XOR with pairing
and symmetric encryption, before selecting any observations. -/
namespace Tamarin.XorConstructorWire

theorem admitted : CertifiedTableWire.run declarations nodes ruleRoots 0 = true := by decide +kernel

end Tamarin.XorConstructorWire
