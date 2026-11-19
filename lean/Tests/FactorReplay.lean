import TamarinRuntime.FactorCheck

/-! Free-factor admission on the NAXOS shared-peer packet. The caller
proposes final simultaneous bindings, after aliases, free decomposition and
canonical rebuilding of nested exponent products. -/
namespace Tamarin.FactorReplayTests
open Whole FactorCheck

private def ds : List Decl :=
  [⟨2,0,2,[2,2]⟩, ⟨2,1,2,[2]⟩, ⟨2,2,2,[2,2]⟩, ⟨2,3,2,[2]⟩, ⟨4,0,2,[2,2]⟩]
private def msg (id : UInt64) := Tree.leaf 0 id 2
private def fresh (id : UInt64) := Tree.leaf 0 id 1
private def g := Tree.leaf 1 0 0
private def pow (u v : Tree) := Tree.app 2 0 [u,v]
private def hash (u : Tree) := Tree.app 2 1 [u]
private def pair (u v : Tree) := Tree.app 2 2 [u,v]
private def inv (u : Tree) := Tree.app 2 3 [u]
private def mul (xs : List Tree) := Tree.app 4 0 xs

private def esk := fresh 0
private def lkI := fresh 1
private def localEsk := fresh 2
private def localLkI := fresh 3
private def lkA := fresh 4
private def hR := hash (pair (fresh 5) (fresh 6))
private def hI := hash (pair esk lkI)
private def Y := msg 0
private def base := msg 175
private def exponent := msg 176
private def lhs := mul [msg 7,msg 8]

private def source : Equations :=
  [(esk,localEsk), (lkI,localLkI),
   (Y,pow base (mul [exponent,inv localLkI])),
   (pow g (mul [lkA,hR]),pow base exponent),
   (pow g lhs,pow base (mul [exponent,hash (pair localEsk localLkI),inv localLkI]))]

private def factor : Equations :=
  [(localEsk,esk), (localLkI,lkI),
   (Y,pow g (mul [lkA,hR,inv lkI])), (base,g), (exponent,mul [lkA,hR])]

private def rest : Equations := [(lhs,mul [lkA,hI,hR,inv lkI])]

#guard !direct ds source factor rest
#guard checkReplay ds source factor rest
#guard check ds source factor rest
#guard checkReplay ds source.reverse factor.reverse rest
-- Removing a hash factor or changing one alias loses a constraint. Both
-- mutants must defer even though they are well sorted.
#guard !checkReplay ds source factor [(lhs,mul [lkA,hI,inv lkI])]
#guard !checkReplay ds source ((localEsk,lkI) :: factor.tail) rest
#guard !checkReplay ds source ((msg 31,msg 32) :: factor) rest

-- A substitution can expose a pair of free applications that did not share
-- a head until the first variable was eliminated.
private def cascade := [(msg 0,pair (msg 1) (msg 2)),(msg 0,pair g (hash g))]
private def cascadeFactor := [(msg 0,pair g (hash g)),(msg 1,g),(msg 2,hash g)]
#guard checkReplay ds cascade cascadeFactor []
#guard !checkReplay ds cascade [(msg 0,pair g (hash g))] []
#guard !replay 1 cascade cascadeFactor

-- The same cascade through the public packet decoder. Nodes 4 and 6 are
-- the two pair terms. Node 5 is hash(g). Their shared left root is node 0.
private def declWords : Array UInt64 := #[2,2,2,2,2,2, 2,1,1,2,2]
private def nodes : Array (Array UInt64) := #[
  #[0,0,2], #[0,1,2], #[0,2,2], #[1,0,0],
  #[2,2,1,2], #[2,1,3], #[2,2,3,5]]
private def origRoots : Array UInt64 := #[0,4,0,6]
private def boundRoots : Array UInt64 := #[0,6,1,3,2,5]
#guard !runWith direct declWords nodes origRoots boundRoots #[]
#guard run declWords nodes origRoots boundRoots #[]
#guard !run declWords nodes origRoots #[0,6,1,5,2,3] #[]

-- Factor images must be stable and sort respecting, regardless of replay.
#guard !checkReplay ds [(msg 0,hash (msg 0))] [(msg 0,hash (msg 0))] []
#guard !checkReplay ds [(fresh 0,hash g)] [(fresh 0,hash g)] []
-- A C head can swap arguments, but never flatten like an AC head.
private def comm (a b : Tree) := Tree.app 3 1 [a,b]
#guard checkReplay (⟨3,1,2,[2,2]⟩ :: ds) [(msg 0,comm g (msg 1))]
  [(msg 0,comm (msg 1) g)] []
#guard !checkReplay ds [(pair g (msg 1),msg 2)] [(msg 2,pair (msg 1) g)] []
#guard !replayFits (List.replicate 4097 (msg 0,msg 0))

end Tamarin.FactorReplayTests
