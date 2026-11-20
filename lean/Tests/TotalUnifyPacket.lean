import TamarinRuntime
import Tamarin.TotalUnifyPacket

namespace Tamarin.TotalUnifyWireTests

private abbrev kernel := Executable.totalUnify
private def decls : Array UInt64 := #[4,7,2,2,2,2,2,8,1,2,2]
private def nested : Array (Array UInt64) :=
  #[#[0,0,2],#[1,0,0],#[1,1,0],#[4,7,1,2],#[2,8,3]]

-- X = h(a*b) retains both atom identities and the outer free symbol.
#guard kernel decls nested #[0,4] == #[#[1],#[],#[0,2,1,0,0,1,1,0,4,7,2,2,8,1]]
#guard kernel #[] #[] #[] == #[#[1],#[]]
#guard kernel #[] #[#[1,0,0],#[1,1,0]] #[0,1] == #[#[1]]
#guard kernel decls #[#[2,8,1]] #[0,0] == #[#[0]]
#guard kernel decls nested #[0] == #[#[0]]

-- A Msg variable cannot bind to an ill-sorted h(Node). The same kind-level
-- subtree on both sides is nevertheless a legal ordinary unification query.
private def kindTerms : Array (Array UInt64) := #[#[0,0,2],#[1,0,3],#[2,8,1]]
#guard kernel decls kindTerms #[0,2] == #[#[1]]
#guard kernel decls kindTerms #[2,2] == #[#[1],#[]]

end Tamarin.TotalUnifyWireTests
