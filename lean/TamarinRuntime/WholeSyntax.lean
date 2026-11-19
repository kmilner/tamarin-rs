import TamarinWire

namespace Tamarin.Whole

/-- The default executable decoder uses the wire specification directly.
An optimized decoder must still satisfy the export contract on the same packets. -/
def decodeProblem := Wire.decodeProblem

end Tamarin.Whole
