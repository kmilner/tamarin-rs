namespace Tamarin.DHPeerCandidate

/-- Postfix expressions for the received base in each answer. Slots 0..4
refer to the peer, caller's admitted exponent term, base and two exponent witnesses.
The four constructors are neutral (5), inversion (6), product (7), power (8). -/
def images (observesPower : Bool) : Option (Array (Array UInt64)) :=
  if observesPower then some #[
    #[0], #[5], #[2,3,8], #[2,3,1,6,7,8], #[2,1,6,8],
    #[2,3,4,1,7,6,7,8], #[2,4,1,7,6,8]]
  else none

end Tamarin.DHPeerCandidate
