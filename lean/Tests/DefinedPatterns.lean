import Tamarin.DefinedPatterns
import Tamarin.TableWire

namespace Tamarin.DefinedPatternsTests
set_option maxRecDepth 8192

-- inspect(check(x)) -> x; check(a) -> b; inspect(b) -> a.
-- The inner rule can match precisely when x is a. At that specialization
-- either path reduces to a. For all other x the outer row remains necessary.
private def decls : Array UInt64 := #[2,0,1,2,2, 2,1,1,2,2, 2,2,0,2, 2,3,0,2, 2,4,0,2]
private def nodes : Array (Array UInt64) := #[
  #[0,17,2], #[2,1,0], #[2,0,1], #[2,2], #[2,3], #[2,1,3], #[2,0,4], #[2,4]]
private def uniqueOuter (roots : Array UInt64) (fuel : Nat)
    (decls := decls) (nodes := nodes) : Bool := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input decls nodes roots #[] | return false
  let r :: _ := rs | return false
  return (DefinedPatterns.frontier rs fuel r).isSome

#guard uniqueOuter #[2,0, 5,4, 6,3] 4
-- Without the joining rule, inspect(check(a)) can reach a or inspect(b).
-- With a conflicting joining rule those endpoints reduce to a and c.
#guard !uniqueOuter #[2,0, 5,4] 4
#guard !uniqueOuter #[2,0, 5,4, 6,7] 4

-- Repeat the capture under a commutative check/2. A specialized inner
-- rewrite can now match either orientation, and the same join is required.
private def commDecls := decls.extract 0 5 ++ #[3,1,2,2,2,2] ++ decls.extract 10 decls.size
private def commNodes := (nodes.set! 1 #[3,1,0,0]).set! 5 #[3,1,3,3]
#guard uniqueOuter #[2,0, 5,4, 6,3] 4 commDecls commNodes
#guard !uniqueOuter #[2,0, 5,4, 6,7] 4 commDecls commNodes

end Tamarin.DefinedPatternsTests
