namespace Tamarin.DHExponentCandidate

/-- Postfix programs for the input exponent. The adapter supplies the
observed exponent, positive factor, and two arm-local remainder slots. -/
def images (_ : Unit) : Array (Array UInt64) :=
  #[#[0], #[9], #[3,1,6,7], #[1,6], #[3,4,1,7,6,7], #[4,1,7,6]]

end Tamarin.DHExponentCandidate
