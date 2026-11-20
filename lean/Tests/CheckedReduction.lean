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
#guard reduce ds ns #[0,1] 0 1 == #[#[2]] -- bounded search exhausted
#guard reduce ds ns #[0,1] 0 2 == #[#[1],#[2,2,0]]
#guard reduce ds ns #[0,3] 0 20 == #[#[2]] -- unbound rule variable
#guard reduce ds ns #[0] 0 2 == #[#[0]]
#guard reduce ds ns #[] 8 2 == #[#[0]]
-- The successor graph can grow a wide product even from a single constant.
-- Preflight must stop before allocating the powerset of its 64 occurrences.
private def wide := ns.push (#[4,0] ++ Array.replicate 64 1)
#guard reduce ds wide #[0,6] 0 10 == #[#[2]]
#guard reduce ds wide #[] 6 10 == #[#[2]]
end Tamarin.CheckedReduction.Tests
