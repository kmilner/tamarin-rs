import Tamarin.MixedUnification

namespace Tamarin.MixedUnificationTests
open MixedUnification

private abbrev sig : Signature where
  FreeSym := Nat
  arity := fun f => f
  CSym := Nat
  ACSym := Nat
  Atom := Nat
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := fun _ => .msg
  acSort := fun _ => .msg
  atomSort := fun _ => .pub

private abbrev T := Term sig
private def v (i : Nat) : Variable := ⟨i,.msg⟩
private def x (i : Nat) : T := .var (v i)
private def a : T := .atom 1
private def b : T := .atom 2
private def h (t : T) : T := .free 1 fun _ => t
private def c (u w : T) : T := .comm 7 u w
private def plus (u w : T) : T := .ac 3 u w
private def times (u w : T) : T := .ac 4 u w

-- Multiple definitions of one output agree only after C swaps, AC
-- reassociation, and propagation of an alias under a free constructor.
private def nested : Problem sig := [
  ⟨x 0,h (x 1)⟩, ⟨x 1,plus a (plus (c (x 3) b) (x 2))⟩,
  ⟨x 0,h (plus (x 2) (plus (c b (x 4)) a))⟩, ⟨x 4,x 3⟩]

#guard match solve? nested with
  | some [θ] =>
    ReferenceMatching.equal (θ (v 0)) (h (plus (θ (v 2)) (plus (c b (θ (v 3))) a))) &&
      θ (v 3) == θ (v 4) && θ (v 2) != θ (v 3) &&
      (match θ (v 2), θ (v 3) with | .var _, .var _ => true | _, _ => false)
  | _ => false

-- A constructor cycle from the Maude AC implementation, then the same
-- dependency crossing C and free constructors, with the equations reversed.
#guard (solve? ([⟨x 0,plus (x 1) a⟩,⟨x 1,times (x 0) b⟩] : Problem sig)).any List.isEmpty
#guard (solve? ([⟨h (x 0),x 1⟩,⟨c (x 1) a,x 0⟩] : Problem sig)).any List.isEmpty
-- Pure aliases can be cyclic and admit every assignment of the shared parameter.
#guard match solve? ([⟨x 0,x 1⟩,⟨x 1,x 2⟩,⟨x 2,x 0⟩] : Problem sig) with
  | some [θ] => θ (v 0) == θ (v 1) && θ (v 1) == θ (v 2)
  | _ => false

-- The argument sort is checked when projecting raw rows. Fresh and Pub
-- are incomparable. An empty conjunction still has an identity solution.
#guard (unify? ([⟨.var ⟨0,.fresh⟩,a⟩] : Problem sig) []).any List.isEmpty
#guard ((unify? ([] : Problem sig) []).map List.length) == some 1

private def openAC : Problem sig := [⟨plus (x 0) a,plus (x 1) b⟩]
-- Swapping a and b gives a solution, and a further shared AC remainder
-- is possible. A failed reconstruction must leave these branches open.
#guard (solve? openAC).isNone
private def q := purify openAC
#guard (q.rows 3).length == 2 && (q.remaining 3).length == 2 && (q.rows 4).isEmpty
-- Both homogeneous rows share one output coordinate, even though these
-- two source products have different syntax.
#guard match q.rows 3 with
  | [l,r] => l.lhs.first == r.lhs.first && l.rhs.first != r.rhs.first
  | _ => false
-- A component really runs the homogeneous solver on shared slot IDs.
private def repeated := purify ([⟨x 1,plus (x 0) (x 0)⟩] : Problem sig)
#guard match repeated.solveComponent 3 [] with
  | [σ] =>
    let child := σ.image ⟨repeated.slot (x 0),.msg⟩
    σ.image ⟨repeated.slot (x 1),.msg⟩ == plus child child
  | _ => false

end Tamarin.MixedUnificationTests
