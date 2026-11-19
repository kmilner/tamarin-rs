import Tamarin.ReferenceReduction
import Tamarin.ReferenceVariantFrontier
import Tamarin.MaudeOperationRefinements
import Tamarin.Pairing
import Tamarin.UnifierSorts

namespace Tamarin.ReferenceCommands.Tests
open Rewriting
private abbrev S := Pairing.signature
private def a : Term S := .atom (0,.msg)
private def b : Term S := .atom (1,.msg)
private def c : Term S := .atom (2,.msg)
private def x : Variable := ⟨0,.msg⟩
private def y : Variable := ⟨1,.msg⟩
private abbrev plus := Term.ac (sig := S) 0
private abbrev times := Term.ac (sig := S) 1
private def f (t : Term S) : Term S := .free (.other 8 1) (fun _ => t)
private def h (t : Term S) : Term S := .free (.other 9 1) (fun _ => t)

private def matchRows (p : Problem S) (keys : List Variable) :=
  (ReferenceMatching.matcher S).run p trivial keys
private def eqB := ReferenceMatching.equal (s := S)

-- Six ways to divide three distinct factors into two ordered nonempty groups.
#guard (matchRows [⟨plus (.var x) (.var y),plus a (plus b c)⟩] [x,y]).length == 6

-- A second equation selects a single joint assignment in a different theory.
private def mixed := matchRows [⟨plus (.var x) (.var y),plus b (plus a c)⟩,
  ⟨times (.var x) a,times a (plus c a)⟩] [x,y]
#guard mixed.length == 1 && mixed.all (fun σ => eqB (σ.image x) (plus a c) && eqB (σ.image y) b)
#guard (matchRows [⟨plus (.var x) (.var x),plus a b⟩] [x]).isEmpty
#guard (matchRows [⟨.var x,f (.var x)⟩] [x]).any (fun σ => eqB (σ.image x) (f (.var x)))
#guard (matchRows [⟨.var x,f (.var x)⟩] []).isEmpty

private abbrev N := { S with acSort := fun _ => SortId.nat : Signature }
private def ill : Term N := .ac 0 (.atom (0,.pub)) (.atom (1,.nat))
#guard !((ReferenceMatching.matcher N).run [⟨ill,ill⟩] trivial []).isEmpty
#guard ((ReferenceMatching.matcher N).run [⟨.var x,ill⟩] trivial [x]).isEmpty

-- The proper AC redex spans the original left/right boundary. Other
-- equations can also fire under a free head in that same subject.
private def subject := plus (f c) (plus b a)
private def rules : List (Equation S) := [⟨plus (f (.var x)) a,h (.var x)⟩,⟨f c,c⟩]
private def edges := ReferenceReduction.successors rules subject
#guard edges.any (eqB (plus (h c) b))
#guard edges.any (eqB (plus c (plus b a)))
#guard edges.all (fun u => eqB u (plus (h c) b) || eqB u (plus c (plus b a)))
#guard (ReferenceReduction.successors rules (h c)).isEmpty

private abbrev VRow := VariantJoin.Row S Unit Unit
private def row (input value : Term S) : VRow := ⟨fun _ => input,fun _ => value⟩
private def gen := row (plus (.var x) a) (f (.var x))
private def spec := row (plus a b) (f b)
private def different := row (plus a b) (f c)
#guard ReferenceVariantFolding.subsumes [()] [()] gen spec
#guard !ReferenceVariantFolding.subsumes [()] [()] gen different
#guard (ReferenceVariantFolding.foldRows [()] [()] [spec,different,gen,spec]).length == 2

-- The only sorted specialization of this raw component template makes
-- its shared parameter Nat. The input variable is still declared Msg.
private def nsum (u v : Term N) : Term N := Term.ac 0 u v
private def one : Term N := .atom (0,.nat)
private def kindProblem : Problem N := [⟨.var x, nsum (.var y) one⟩]
private def raw : UnifierSorts.Template N :=
  fun v => if v = x then nsum (.var y) one else .var v
private def sortedRows := UnifierSorts.solve kindProblem [raw] [⟨10,.nat⟩]
#guard sortedRows.length == 1
#guard sortedRows.all (fun σ =>
  match σ.image y with
  | .var w => w.sort == .nat && w.id > 10 && ReferenceMatching.equal (σ.image x) (nsum (.var w) one)
  | _ => false)

-- An overapproximating one-step oracle is complete for the empty table.
-- The checker must still reject incorrect results and missing live successors.
private def certifyEmpty {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] {n : Nat} (query : Fin n → Term s) (avoid : List Variable)
    (proposed : List (ReferenceVariantFrontier.Point s n)) (next : ReferenceVariantFrontier.Point s n →
      List (ReferenceVariantFrontier.Point s n)) :=
  ReferenceVariantFrontier.certify (rules := []) (by simp [ReferenceReduction.Bound]) (MaudeOperations.emptyReducer s)
    (ConstructorVariants.constructor_normal (sig := s) [] (by simp)).1 query avoid proposed next (by
      intro p _ δ _ j u step
      exact False.elim (((MaudeOperations.emptyReducer s).correct (δ.apply (p.value j))).normalForm.2.1 u step))

private def pairQuery : Fin 2 → Term S := fun i => if i = 0 then .var x else f (.var x)
private def wrong : ReferenceVariantFrontier.Point S 2 := ⟨.identity,fun _ => a⟩
#guard (certifyEmpty pairQuery [] [] (fun _ => [])).isSome
#guard (certifyEmpty pairQuery [] [wrong] (fun _ => [])).isNone
#guard (certifyEmpty pairQuery [] [] (fun _ => [wrong])).isNone
private def alias : Substitution S := Substitution.binding x (.var y) (HasSort.var y)
private def aliasRow : ReferenceVariantFrontier.Point S 2 := ⟨alias,fun i => alias.apply (pairQuery i)⟩
#guard (certifyEmpty pairQuery [] [] (fun _ => [aliasRow])).isSome
#guard (certifyEmpty pairQuery [y] [aliasRow] (fun _ => [])).isNone
#guard (certifyEmpty (fun _ : Fin 2 => ill) [] [] (fun _ => [])).isSome
#guard (certifyEmpty (s := S) (fun i : Fin 0 => i.elim0) [] [] (fun _ => [])).isSome

end Tamarin.ReferenceCommands.Tests
