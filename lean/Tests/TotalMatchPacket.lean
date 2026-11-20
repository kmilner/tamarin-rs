import TamarinRuntime

namespace Tamarin.TotalMatchWireTests

private abbrev kernel := Executable.totalMatch
private def decls : Array UInt64 := #[3,4,2,2,2,2, 4,5,2,2,2,2, 2,6,1,2,2]
-- x, y, a, c(x,y), c(a,y), ac(a,y), f(Node), Node
private def terms : Array (Array UInt64) :=
  #[#[0,0,2],#[0,1,2],#[1,3,0],#[3,4,0,1],#[3,4,2,1],#[4,5,2,1],
    #[1,8,3],#[2,6,6]]
private def yId : Array UInt64 := #[1,2,0,1,2]
private def xToA : Array UInt64 := #[0,2,1,3,0]

-- Freezing y selects precisely the orientation x=a, y=y. In a second
-- equation the same x must retain that image. The subject y never binds.
#guard kernel decls terms #[3,4,0,2] #[0] == #[#[1],#[],xToA,yId]
#guard kernel decls terms #[3,4,0,1] #[0] == #[#[1]]
#guard kernel decls terms #[0,1] #[] == #[#[1]]
#guard kernel decls terms #[0,1] #[0] == #[#[1],#[],#[0,2,0,1,2],yId]
-- A captured product retains the actual rigid y.
#guard kernel decls terms #[0,5] #[0] == #[#[1],#[],#[0,2,1,3,0,0,1,2,4,5,2],yId]
-- Kind equality is admissible even when the value cannot inhabit a Msg range.
#guard kernel decls terms #[7,7] #[] == #[#[1],#[]]
#guard kernel decls terms #[0,7] #[0] == #[#[1]]
#guard kernel decls terms #[0] #[] == #[#[0]]

end Tamarin.TotalMatchWireTests
