import TamarinRuntime

namespace Tamarin.CheckedCommandPacketTests

private abbrev variants := Executable.checkedVariants
-- The two nullary constructors can be distinct terminal values for f(x).
private def ds : Array UInt64 := #[2,0,1,2,2, 2,1,0,2, 2,2,0,2]
private def ns : Array (Array UInt64) := #[#[0,0,2],#[2,0,0],#[2,1],#[2,2]]
#guard match (variants ds ns #[1,2] #[1,0] 4).toList with
  | [status,sep,binding] => status == #[1] && sep.isEmpty &&
    (match binding.toList with | [0,2,0,_,2] => true | _ => false)
  | _ => false
#guard variants ds ns #[1,2,1,3] #[1] 4 == #[#[2]]
#guard variants ds ns #[1] #[1] 4 == #[#[0]]
#guard variants ds ns #[] #[9] 4 == #[#[0]]
#guard variants ds ns #[] #[] 4 == #[#[1],#[]]

-- b := c is admitted over all caller names. With zero search budget the
-- original variable still has its full word-sized ID in the single answer.
private def lastId := UInt64.ofNat (UInt64.size - 1)
private def ids := ns.push #[0,lastId,3]
#guard variants ds ids #[2,3] #[2,4,4] 0 == #[#[1],#[],#[lastId,3,0,lastId,3]]
#guard variants ds ids #[2,3] #[] 0 == #[#[1],#[]]
#guard variants ds ids #[2,3,3,2] #[2] 0 == #[#[2]]

end Tamarin.CheckedCommandPacketTests
