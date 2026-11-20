import Tamarin.CheckedVariants
import Tamarin.PairingRewriting

namespace Tamarin.CheckedVariants.Tests
open Rewriting
private abbrev S := Pairing.signature
private def x : Variable := ⟨7,.msg⟩
private abbrev v := Term.var (sig := S) x
private def a : Term S := .atom (0,.msg)
private def b : Term S := .atom (1,.msg)
private def c : Term S := .atom (2,.msg)
private def n : Term S := .atom (0,.node)
private abbrev plus := Term.ac (sig := S) 0
private def f (t : Term S) : Term S := .free (.other 4 1) (fun _ => t)
private def eqB := ReferenceMatching.equal (s := S)

-- Both of Tamarin's pairing rules decrease through arbitrary B contexts.
#guard TableDecrease.decreasing Pairing.rules && TableDecrease.sorted Pairing.rules
#guard TableDecrease.decreasing ([⟨plus v v,v⟩] : List (Equation S))
-- The raw LHS is larger, but duplication on the RHS permits larger instances.
#guard !(TableDecrease.decreasing ([⟨f (f (f v)),plus v v⟩] : List (Equation S)))
#guard !(TableDecrease.sorted ([⟨f a,n⟩] : List (Equation S)))

private def answers (rs : List (Equation S)) (ts : List (Term S)) (depth := 2) :=
  (solve rs ts depth 6).map Subtype.val

-- The value of the second coordinate and the image of its input must
-- agree in both the identity branch and the branch exposed by x = a.
private def rewriteF : List (Equation S) := [⟨f a,b⟩]
#guard
  match answers rewriteF [f v,v] with
  | none => false
  | some rows =>
    let generic := rows.any fun r => eqB (r.subst.image x) v &&
      match r.values with | [p,q] => eqB p (f v) && eqB q v | _ => false
    let redex := rows.any fun r => eqB (r.subst.image x) a &&
      match r.values with | [p,q] => eqB p b && eqB q a | _ => false
    generic && redex
#guard (answers rewriteF [f v,v] 0).isNone

-- A proper AC redex can cross its concrete bracket boundary. A Node factor
-- remains in the untyped context; ordinary reduction must reconstruct it.
#guard
  match answers [⟨plus a b,c⟩] [plus (plus n a) b] with
  | some rows => !rows.isEmpty && rows.all fun r => match r.values with
    | [value] => eqB value (plus n c)
    | _ => false
  | none => false

-- Two reachable normal outputs for identical bindings prevent reconstruction.
private def divergent : List (Equation S) := [⟨f a,b⟩,⟨f a,c⟩]
#guard (answers divergent [f a]).isNone
-- The same nonconfluent table can still certify an independent tuple.
#guard (answers divergent [v,b]).isSome
-- Each open arm by itself replays to one normal value. At the joint
-- instance x=a, y=b the two distinct values violate specialization safety.
private def y : Variable := ⟨8,.msg⟩
private def pick (l r : Term S) := Pairing.pair l r
private def row (input value : Term S) : RootNarrowing.State S Unit :=
  ⟨fun _ => input, fun _ => value⟩
-- Recover an unknown below a free input and reuse it under an AC output.
#guard (determined [()] (row (pick a v) (plus v c))
  (row (pick a (.var y)) (plus (.var y) c)) 4).val
-- Knowing an unordered pair does not determine its left factor.
#guard !(determined [()] (row (plus a b) a) (row (plus b a) b) 4).val
-- Identically named invisible output variables have independent scopes.
#guard !(determined [()] (row a v) (row a v) 4).val
private def overlap : List (Equation S) :=
  [⟨pick a (.var y),b⟩, ⟨pick v b,c⟩]
#guard (answers overlap [pick v (.var y),v,.var y]).isNone
#guard (answers [] []).isSome
#guard (answers [⟨a,v⟩] [a]).isNone

end Tamarin.CheckedVariants.Tests
