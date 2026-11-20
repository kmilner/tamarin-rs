import TamarinRuntime
import Tamarin.ConstructorRowOverlaps
import Tamarin.ConstructorPresentation
import Tamarin.SubtermDecrease
import Tamarin.SubtermVariants

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

-- The general reducer can distinguish an unfinished search, a witnessed fork
-- with inequivalent normal forms, and branches that join one step later.
private abbrev reduce := Executable.generalReduce
#guard reduce ds ns #[1,2,1,3] 1 1 == #[#[3]]
#guard reduce ds ns #[1,2,1,3] 1 2 == #[#[2]]
#guard reduce ds ns #[1,2,1,3,3,2] 1 2 == #[#[3]]
#guard reduce ds ns #[1,2,1,3,3,2] 1 3 == #[#[1],#[2,1,0]]
#guard reduce ds ns #[1,2,1,3] 3 1 == #[#[1],#[2,2,0]]
#guard reduce ds ns #[2,0] 2 4 == #[#[2]]
#guard reduce ds ns #[2] 2 4 == #[#[0]]
#guard reduce ds ns #[2,3,3,2] 2 10 == #[#[3]]

-- b := c is admitted over all caller names. With zero search budget the
-- original variable still has its full word-sized ID in the single answer.
private def lastId := UInt64.ofNat (UInt64.size - 1)
private def ids := ns.push #[0,lastId,3]
#guard variants ds ids #[2,3] #[2,4,4] 0 == #[#[1],#[],#[lastId,3,0,lastId,3]]
#guard variants ds ids #[2,3] #[] 0 == #[#[1],#[]]
#guard variants ds ids #[2,3,3,2] #[2] 0 == #[#[2]]

end Tamarin.CheckedCommandPacketTests

namespace Tamarin.DestructorPacketTests
-- pair/2, fst/1 and snd/1, all Msg-sorted. x and y are distinct rule variables.
private def ds : Array UInt64 := #[2,0,2,2,2,2, 2,1,1,2,2, 2,2,1,2,2]
private def ns : Array (Array UInt64) := #[#[0,0,2],#[0,1,2],#[2,0,0,1],#[2,1,2],#[2,2,2],#[0,2,2],#[2,1,5]]
private def rules : Array UInt64 := #[3,0,4,1]
-- Zero frontier budget forces the total path. The rows for fst(z),z must
-- include an unrestricted z and a pair of independent Msg witnesses.
#guard Id.run do
  let reply := Executable.checkedVariants ds ns rules #[6,5] 0
  return reply[0]? == some #[1] &&
    reply.any (fun row => match row.toList with | [2,2,0,_,2] => true | _ => false) &&
    reply.any (fun row => match row.toList with | [2,2,0,x,2,0,y,2,2,0,2] => x != y | _ => false)
-- Same root with conflicting result positions cannot certify the table.
#guard Executable.checkedVariants ds ns #[3,0,3,1] #[6,5] 0 == #[#[2]]
#guard Executable.checkedReduce ds ns #[3,0,3,1] 3 0 == #[#[2]]
end Tamarin.DestructorPacketTests

namespace Tamarin.GeneralVariantPacketTests
-- Six unary stages, pair/fst/snd and two nullary constructors a,b.
private def ds : Array UInt64 := (Array.range 6).flatMap (fun i => #[2,i.toUInt64,1,2,2]) ++
  #[2,6,2,2,2,2, 2,7,1,2,2, 2,8,1,2,2, 2,9,0,2, 2,10,0,2]
private def ns : Array (Array UInt64) := #[#[0,0,2],#[0,1,2]] ++
  (Array.range 6).map (fun i => #[2,i.toUInt64,0]) ++
  #[#[2,9],#[2,10],#[2,5,8],#[2,6,9,8],#[2,7,11],#[2,6,0,1],#[2,7,13],#[2,8,13]]
private def rules : Array UInt64 := #[2,3,3,4,4,5,5,6,6,7,10,12,14,0,15,1]
-- The open instance stays at stage5(x); x=a additionally returns b via fst.
-- The previous bounded raw search cannot replay even the seed at depth four.
#guard Id.run do
  let some ⟨_,rs,q⟩ := TableWire.input ds ns rules #[2,0] | return false
  let table := TableAmbient.liftRules rs
  let query := q.map TableAmbient.liftTerm
  return !DestructorTable.accepts rs && !ConstantDefinitions.accepts rs &&
    (CheckedVariants.solve table query 4 4).isNone && (GeneralVariants.run table query 32).isSome
#guard Id.run do
  let wire := Executable.checkedVariants ds ns rules #[2,0] 4
  return wire[0]? == some #[1] && wire.any (fun row => match row.toList with
    | [0,2,0,_,2] => true | _ => false) && wire.contains #[0,2,2,9,0]
-- The generic ABI distinguishes an unfinished stage from a completed family.
#guard Executable.generalVariants ds ns rules #[2,0] 4 == #[#[3]]
#guard (Executable.generalVariants ds ns rules #[2,0] 32)[0]? == some #[1]
-- A competing normal endpoint for the same specialized input invalidates the family.
#guard Executable.checkedVariants ds ns (rules ++ #[10,8]) #[2,0] 4 == #[#[2]]
end Tamarin.GeneralVariantPacketTests

-- [leaf 0, []] and [leaf 1, []] lower to one ordinary coordinate.
-- Moving the inner empty wrapper changes the shape, even at the same outer width.
private def spineNodes : Array (Array UInt64) :=
  #[#[],#[0],#[1],#[0,0],#[1,3],#[2,3],#[0,5]]
#guard Tamarin.Executable.unpackConjunction spineNodes 2 4 5 == #[#[1],#[0,1]]
#guard Tamarin.Executable.unpackConjunction spineNodes 2 4 3 == #[#[2]]
#guard Tamarin.Executable.unpackConjunction spineNodes 2 4 6 == #[#[2]]
#guard Tamarin.Executable.unpackConjunction spineNodes 2 0 0 == #[#[1]]
#guard Tamarin.Executable.unpackConjunction (spineNodes.push #[2,1]) 2 4 5 == #[#[0]]
#guard Tamarin.Executable.unpackConjunction spineNodes 1 4 5 == #[#[0]]

namespace Tamarin.SubtermPacketTests

-- bag is AC, and peel, check, pair, fst and snd are free. The ground RHS of
-- check(x,x) performs a projection from a different rule bucket.
private def ds : Array UInt64 := #[4,0,2,2,2,2, 2,1,1,2,2, 2,2,2,2,2,2, 2,3,2,2,2,2,
  2,4,1,2,2, 2,5,1,2,2, 2,6,0,2, 2,7,0,2, 3,8,2,2,2,2]
private def ns : Array (Array UInt64) := #[#[0,0,2],#[0,1,2],#[2,6],#[2,7],#[4,0,0,2],
  #[2,1,4],#[2,2,0,0],#[2,3,3,2],#[2,4,7],#[2,3,0,1],#[2,4,9],#[2,5,9],#[2,2,1,0],#[2,1,0],#[3,8,0,2]]
private def rules : Array UInt64 := #[5,0,6,8,10,0,11,1]
private def eligible (rows : Array UInt64) : Bool := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input ds ns rows #[13] | return false
  return SubtermVariants.accepts rs && SubtermVariants.accepts (TableAmbient.liftRules rs)

#guard eligible rules
#guard eligible (rules ++ #[14,0]) -- commutative head returning a child
#guard !eligible (rules ++ #[13,12]) -- open RHS rebuilt under a different head
#guard !eligible (rules ++ #[4,0]) -- AC-rooted rules require their own operator proof
#guard (Executable.generalVariants ds ns rules #[13,0] 16)[0]? == some #[1]

private def checkedGround (rows : Array UInt64) (fuel : Nat) (nodes := ns) : Bool := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input ds nodes rows #[13] | return false
  let some row := rs.head? | return false
  return ConstructorRows.groundRow rs fuel row

-- check(x,x) and check(y,x) return different syntax, fst(pair(ok,marker))
-- and ok. Both alternatives reduce to ok on the whole table.
private def jointGround : Array UInt64 := #[6,8,12,3,10,0]
#guard checkedGround jointGround 2
#guard !checkedGround jointGround 1
#guard !checkedGround (jointGround ++ #[12,2]) 3
-- An additional root that makes the fixed RHS itself ambiguous invalidates
-- the certificate even if the other check row is removed.
#guard !checkedGround #[6,8,10,0,10,1] 3
-- Same check for a commutative root with a rigid ground argument.
#guard checkedGround #[14,8,14,3,10,0] 2
#guard !checkedGround #[14,8,14,2,10,0] 2

-- Use the ordinary unifier to compare every root overlap, including
-- independent instantiations of the same rule modulo C and AC.
private def classified (rows : Array UInt64) : Option (Bool × Bool) := do
  let ⟨_,rs,_⟩ ← TableWire.input ds ns rows #[]
  let r ← rs.head?
  return (ConstructorRows.projectionRow rs r, ConstructorRows.overlapRow rs r)

-- fst(pair(x,y)) returns an ordered coordinate. peel(bag(x,marker)) also
-- returns a unique x, although AC reassociation gives it no fixed position.
#guard classified #[10,0,11,1] == some (true,true)
#guard classified #[5,0] == some (false,true)
#guard classified #[14,0] == some (false,true) -- a commutative rewrite head
-- Competing fst projections, an active bag pattern, and the empty projection
-- from peel(x) back to peel(x) each violate an admission condition.
#guard classified #[10,0,10,1] == some (false,false)
#guard classified #[5,0,4,0] == some (false,false)
#guard classified #[13,13] == some (false,false)
-- Repeating the same variable forces the two children to agree. With
-- distinct variables both commutative orientations must agree on the returned image.
private def commRows (same : Bool) : Bool := Id.run do
  let extra := ns ++ #[#[3,8,0,if same then 0 else 1],#[2,1,15]]
  let some ⟨_,[r],_⟩ := TableWire.input ds extra #[16,0] #[] | return false
  return ConstructorRows.overlapRow [r] r
#guard commRows true
#guard !commRows false

-- Renaming an AC pattern apart from itself doubles the independent captures.
-- The automatic checker can defer this open overlap before enumerating it.
#guard Id.run do
  let extra := ns ++ #[#[4,0,0,1],#[2,1,15]]
  let some ⟨_,[r],_⟩ := TableWire.input ds extra #[16,0] #[] | return false
  return !FrontierWork.admitsRootPair r.lhs r.lhs && !ConstructorRows.overlapRow [r] r

-- Projecting the other free argument agrees even when the first contains
-- four independent AC captures. No self-unifier is needed.
#guard Id.run do
  let extra := ns ++ #[#[0,2,2],#[0,3,2],#[4,0,0,1],#[4,0,15,16],#[4,0,17,18],#[2,2,19,0]]
  let some ⟨_,[r],_⟩ := TableWire.input ds extra #[20,0] #[] | return false
  return !FrontierWork.admitsRootPair r.lhs r.lhs && ConstructorRows.overlapRow [r] r

-- Two disjoint pair patterns under fst return different coordinates.
-- The two fixed constants prevent a cross-rule overlap.
#guard Id.run do
  let extra := ns ++ #[#[2,3,2,0],#[2,4,15],#[2,3,3,1],#[2,4,17]]
  let some ⟨_,rs,_⟩ := TableWire.input ds extra #[16,0,18,3] #[] | return false
  return rs.all fun r => !ConstructorRows.projectionRow rs r && ConstructorRows.overlapRow rs r

-- check(ok,ok) and check(marker,marker) may return different constants.
-- In check(ok,x) = x the only overlap with check(x,x) specializes x to ok.
private def extras := ns ++ #[#[2,2,3,3],#[2,2,2,2],#[2,2,3,0]]
#guard checkedGround #[15,3,16,2] 1 extras
#guard checkedGround #[6,3,17,0] 1 extras
#guard !checkedGround #[6,2,17,0] 1 extras

-- Even with zero search fuel, a common inert constant certifies the whole
-- ground-output bucket. The standalone presentation needs no DH rules.
#guard checkedGround #[6,3,12,3] 0
private def standalone (rows : Array UInt64) := Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input ds ns rows #[] | return false
  return ConstructorRows.accepts (SubtermDecrease.defaultWeight (fun _ => 1) rs) 3 rs
#guard standalone rules
#guard !standalone (rules ++ #[10,1])

-- A dozen independent captures under one AC constructor would generate a
-- wide unification problem. Identical ground outputs certify it at zero fuel.
-- An ambiguous competing ground output must defer before enumerating overlaps.
private def wideNodes := Id.run do
  let n := ns.size
  let vars := (Array.range 12).map fun i => #[0,UInt64.ofNat (i+30),2]
  let bag := #[4,0] ++ (Array.range 12).map (fun i => UInt64.ofNat (n+i))
  return ns ++ vars ++ #[bag,#[2,1,UInt64.ofNat (n+12)]]
#guard checkedGround #[28,3,5,3] 0 wideNodes
#guard !checkedGround #[28,3,5,2] 2 wideNodes

end Tamarin.SubtermPacketTests
