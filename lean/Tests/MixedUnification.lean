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

-- Require both mathematical families and check all returned rows on the source
-- equations. This permits redundant instances, differing orders and witness names.
private def exactSwap (θ : UnifierSorts.Template sig) :=
  ReferenceMatching.equal (θ (v 0)) b && ReferenceMatching.equal (θ (v 1)) a

private def sharesRemainder (θ : UnifierSorts.Template sig) :=
  (θ (v 0)).variables.any fun w =>
    ReferenceMatching.equal (θ (v 0)) (plus b (.var w)) &&
    ReferenceMatching.equal (θ (v 1)) (plus a (.var w))

private def bothFamilies (p : Problem sig) :=
  (solve? p).any fun rows => rows.any exactSwap && rows.any sharesRemainder &&
    rows.all (fun θ => p.all fun e => ReferenceMatching.equal (e.lhs.subst θ) (e.rhs.subst θ))

#guard bothFamilies openAC
#guard bothFamilies [⟨h (plus (x 0) a),h (plus (x 1) b)⟩]
#guard bothFamilies [⟨c (plus (x 0) a) b,c b (plus (x 1) b)⟩]

-- The second operator forces U = V only after its own branch has run.
-- Reopening the two original sums must recover both families, with the
-- reconstructed values of U and V sharing the very same parameter.
private def lateEquality : Problem sig :=
  [⟨x 2,plus (x 0) a⟩,⟨x 3,plus (x 1) b⟩,⟨times (x 2) (.atom 4),times (x 3) (.atom 4)⟩]
#guard bothFamilies lateEquality
#guard bothFamilies lateEquality.reverse
#guard (solve? lateEquality).any fun rows => rows.all fun θ =>
  ReferenceMatching.equal (θ (v 2)) (plus (θ (v 0)) a) &&
    ReferenceMatching.equal (θ (v 3)) (θ (v 2))

-- A third AC operator makes the equality propagate through two component
-- boundaries. All three operators have ordinary semigroup semantics.
private def chain : Problem sig := [
  ⟨x 2,plus (x 0) a⟩,⟨x 3,plus (x 1) b⟩,
  ⟨x 4,times (x 2) (.atom 4)⟩,⟨x 5,times (x 3) (.atom 4)⟩,
  ⟨.ac 8 (x 4) (.atom 5),.ac 8 (x 5) (.atom 5)⟩]
#guard bothFamilies chain

-- Both operators impose their equations on the same X and Y. Only the
-- exact swap survives the first conjunction. The second has no solution.
private def joint : Problem sig := openAC ++ [⟨times (x 0) a,times (x 1) b⟩]
#guard (solve? joint).any fun rows => !rows.isEmpty && rows.all exactSwap
#guard (solve? [⟨plus (x 0) a,plus a a⟩,⟨times (x 0) b,times b b⟩]).any List.isEmpty

-- C has two viable orientations. They must both survive rigid refinement.
private def orient : Problem sig := [⟨c (plus (x 0) a) (x 1),c (plus a b) (plus a a)⟩]
#guard (solve? orient).any fun rows =>
  rows.any (fun θ => θ (v 0) == b && ReferenceMatching.equal (θ (v 1)) (plus a a)) &&
  rows.any (fun θ => θ (v 0) == a && ReferenceMatching.equal (θ (v 1)) (plus a b))

-- A kind-level AC query can contain a Node as a rigid shared factor.
-- Its message variables still admit every common message value, and caller
-- reservations survive the projection out of the internal one-sort search.
private def nodeVar : T := .var ⟨99,.node⟩
private def kindLevel : Problem sig := [⟨plus nodeVar (x 0),plus (x 1) nodeVar⟩]
#guard (unify? kindLevel [v 100]).any fun answers => answers.any fun σ =>
  match σ.image (v 0), σ.image (v 1) with
  | .var u,.var w => u == w && u.sort == .msg && u != v 100 &&
    (match σ.image ⟨99,.node⟩ with | .var n => n.sort == .node | _ => false)
  | _,_ => false

-- Y = X+a and Y+b = X+Z force Z = a+b for every value of X.
private def sameHead : Problem sig :=
  [⟨plus (x 0) a,x 1⟩,⟨plus (x 1) b,plus (x 0) (x 2)⟩]
#guard (solve? sameHead).any fun rows =>
  rows.any (fun θ => match θ (v 0) with | .var _ => true | _ => false) &&
  rows.all (fun θ => ReferenceMatching.equal (θ (v 2)) (plus a b) &&
    ReferenceMatching.equal (θ (v 1)) (plus (θ (v 0)) a))

-- Compare direct evaluation of each ground assignment with membership in
-- the returned sorted family. Joint matching shares each answer parameter.
private def checkGround (p : Problem sig) :=
  let bank := [a,b,.atom 4,plus a a,plus a b,plus b b,h a,times a b,
    plus a (h a),plus b (h a),plus a (times a b),plus b (times a b)]
  (unify? p []).any fun rows => bank.all fun u => bank.all fun w =>
    let θ := fun i => if i = v 0 then u else if i = v 1 then w else Term.var i
    let solves := p.all fun e => ReferenceMatching.equal (e.lhs.subst θ) (e.rhs.subst θ)
    let covered := rows.any fun σ =>
      let test : Problem sig := [⟨σ.image (v 0),u⟩,⟨σ.image (v 1),w⟩]
      !(ReferenceMatching.solve test test.variables).isEmpty
    solves == covered

#guard checkGround openAC
#guard checkGround joint

end Tamarin.MixedUnificationTests
