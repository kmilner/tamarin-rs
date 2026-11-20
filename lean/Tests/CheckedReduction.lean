import TamarinRuntime
import Tamarin.CheckedReductionPacket

namespace Tamarin.CheckedReduction.Tests
private abbrev reduce := Executable.checkedReduce
-- One AC head, and three distinct nullary constructors a,b,c of sort Msg.
private def ds : Array UInt64 := #[4,0,2,2,2,2, 2,1,0,2, 2,2,0,2, 2,3,0,2]
private def ns : Array (Array UInt64) := #[
  #[2,1], #[2,2], #[2,3], #[0,0,3], #[4,0,0,1], #[4,0,3,1,0]]
-- a+b -> c inside a kind-level product with a Node outside the selected
-- subproduct. Even zero fallback fuel suffices by strict node decrease.
#guard reduce ds ns #[4,2] 5 0 == #[#[1],#[2,3,0,0,0,3,4,0,2]] ||
  reduce ds ns #[4,2] 5 0 == #[#[1],#[0,0,3,2,3,0,4,0,2]]
#guard reduce ds ns #[4,2,4,0] 5 10 == #[#[2]] -- distinct normal endpoints
#guard reduce ds ns #[0,1,1,0] 0 3 == #[#[2]] -- cycle
#guard reduce ds ns #[0,1,1,2] 0 1 == #[#[2]] -- uncertified chain exhausts fallback fuel
#guard reduce ds ns #[0,1] 0 0 == #[#[1],#[2,2,0]] -- total constructor definition
#guard reduce ds ns #[0,1] 0 2 == #[#[1],#[2,2,0]]
#guard reduce ds ns #[0,3] 0 20 == #[#[2]] -- unbound rule variable
#guard reduce ds ns #[0] 0 2 == #[#[0]]
#guard reduce ds ns #[] 8 2 == #[#[0]]
-- A defined constant can expand to a product well above the general search
-- budget. Its 64 factors and 63 AC nodes must survive the wire round trip.
private def wide := ns.push (#[4,0] ++ Array.replicate 64 1)
private def wideAnswer : Array (Array UInt64) := #[#[1],
  (Array.replicate 64 #[2,2,0]).flatten ++ (Array.replicate 63 #[4,0,2]).flatten]
#guard reduce ds wide #[0,6] 0 0 == wideAnswer
#guard reduce ds wide #[] 6 0 == wideAnswer
-- For an uncertified AC table the preflight still prevents an eager powerset.
#guard reduce ds wide #[4,2] 6 10 == #[#[2]]
end Tamarin.CheckedReduction.Tests
