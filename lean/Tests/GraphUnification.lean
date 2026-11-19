import Tamarin.GraphUnification
import Tamarin.ACRationalProjection
import Tamarin.ACReducedFeasibility
import Tamarin.ACColumnSupport
import TamarinRuntime

namespace Tamarin.GraphUnificationTests
open Executable

private def ds : Array UInt64 := #[4,7,2,2,2,2]
private def vars : Array (Array UInt64) := #[#[0,0,2],#[0,1,2]]
private def nodes := vars ++ #[#[4,7,0,0],#[4,7,1,1,1],#[4,7,1,0],#[4,7,0,1]]
private def feasible := graphACFeasible 2 7 2 ds nodes
private def run := graphHomogeneousUnify 2 7 2 ds nodes

-- One solution for 2x = 3y. Adding x = y eliminates it in a semigroup with no unit.
#guard run #[2,3] == some #[#[#[0,0,0],#[0,0]]]
#guard run #[2,3,0,1] == some #[]
#guard feasible #[2,3] == 2
#guard feasible #[2,3,0,1] == 1
#guard feasible #[4,5] == 2
#guard feasible #[2,9] == 0
#guard feasible #[2] == 0
#guard graphACFeasible 2 7 2 ds #[#[0,0,0],#[0,1,2],#[4,7,0,0]] #[2,1] == 0
-- All 64 equations constrain the same positive ray. The least common
-- multiple of the alternating coefficients gives sizes 2,3,2,3,... .
private def chainVars (n : Nat) : Array (Array UInt64) :=
  (List.range n).toArray.map fun i => #[0,i.toUInt64,2]
private def chainSides (n : Nat) : Array (Array UInt64) :=
  (List.range n).toArray.map fun i =>
    #[4,7] ++ Array.replicate (if i%2=0 then 3 else 2) i.toUInt64
private def chainRoots (n : Nat) : Array UInt64 :=
  ((List.range (n-1)).flatMap fun i => [(n+i).toUInt64,(n+i+1).toUInt64]).toArray
private def principalChain (n : Nat) :=
  graphHomogeneousUnify n.toUInt64 7 2 ds (chainVars n ++ chainSides n) (chainRoots n)
private def expectedRay (n : Nat) : Homogeneous.Arm :=
  (List.range n).toArray.map fun i => Array.replicate (if i%2=0 then 2 else 3) (0 : UInt64)
#guard principalChain 65 == some #[expectedRay 65]
#guard (principalChain 65 >>= projectAnswers 65) ==
  some #[Array.ofFn (fun i : Fin 65 => #[i.val.toUInt64] ++ (expectedRay 65)[i.val]!)]
#guard principalChain 66 == none

-- An existence query needs one positive valuation for the whole packet.
private def wideVars := (List.range 96).toArray.map fun i => #[0,i.toUInt64,2]
private def wideLeft := #[4,7] ++ (List.range 31).toArray.map Nat.toUInt64
private def wideRight := #[4,7] ++ ((List.range 65).toArray.map fun i => (31+i).toUInt64)
private def wideNodes := wideVars ++ #[wideLeft,wideRight,wideLeft.push 0]
#guard graphACFeasible 96 7 2 ds wideNodes #[96,97] == 2
#guard graphACFeasible 96 7 2 ds wideNodes #[96,97,96,98] == 1
#guard graphACFeasible 97 7 2 ds wideNodes #[96,97] == 0
#guard graphACFeasible 4097 7 2 ds wideNodes #[96,97] == 0
private def groupRow (k : Fin 37 → Nat) (l : Fin 37 → Nat) : ACBasis.Row 37 := .ofWeights k l
private def base37 := groupRow (fun i => if i.val < 19 then 1 else 0) (fun i => if 19 ≤ i.val then 1 else 0)
private def ratio37 (a b : Nat) := groupRow (fun i => if 1 ≤ i.val ∧ i.val < 19 then a else 0)
  (fun i => if 19 ≤ i.val then b else 0)
private def pair37 (a b : Nat) := [base37, ratio37 a b]

#guard (ACFeasibility.direct (pair37 2 1)).isNone
#guard (ACFeasibility.reducedFeasible (pair37 2 1)).isNone
#guard (ACFeasibility.reducedFeasible (pair37 1 2)).isNone
#guard ACFeasibility.ColumnSupport.run (pair37 2 1) 4096 == some true
#guard ACFeasibility.ColumnSupport.run (pair37 1 2) 4096 == some false
#guard (ACFeasibility.ColumnSupport.run (pair37 1 2) 32).isNone

-- Two variables with signed coefficients from -2 through 2. Every
-- nonzero mixed row fixes a ratio represented in the 2×2 positive grid.
private def smallRows : List (ACBasis.Row 2) :=
  (List.range 5).flatMap fun a => (List.range 5).map fun b =>
    ACBasis.Row.ofWeights (fun i => if i.val = 0 then a else b) (fun _ => 2)
private def reducedStress := smallRows.all fun a => smallRows.all fun b =>
  let witnesses := [#[1,1],#[1,2],#[2,1],#[2,2]]
  let positive := witnesses.any fun x =>
    [a,b].all fun r => ACBasis.dot r.pos (fun i => x[i.val]!) == ACBasis.dot r.neg (fun i => x[i.val]!)
  ACFeasibility.reducedFeasible [a,b] == some positive
#guard reducedStress

-- Swapped children are identical modulo AC. The whole-graph path supplies its identity answer.
#guard run #[4,5] == none
#guard run #[2] == none
#guard run #[2,9] == none
#guard graphHomogeneousUnify 1 7 2 ds nodes #[2,3] == none
#guard graphHomogeneousUnify 3 7 2 ds nodes #[2,3] == none
#guard graphHomogeneousUnify 2 8 2 ds nodes #[2,3] == none
#guard graphHomogeneousUnify 2 7 0 ds nodes #[2,3] == none
-- Public leaves are legal subsorts of Msg but cannot serve as its homogeneous variable columns.
#guard graphHomogeneousUnify 2 7 2 ds #[#[0,0,0],#[0,1,2],#[4,7,0,0]] #[2,1] == none
#guard graphHomogeneousUnify 2 7 2 ds (nodes.push #[1,0,2]) #[2,6] == none
#guard graphHomogeneousUnify 2 7 2 ds (nodes.push #[4,7,6,0]) #[2,6] == none

-- Test both flat AC rows and nested nodes sharing their children. The expected counts
-- come from the two variable sequences used to generate the graph.
private def sequences : List (List UInt64) :=
  let singles : List (List UInt64) := [[0],[1]]
  let prepend := fun (xs : List (List UInt64)) => [0,1].flatMap fun i => xs.map (fun tail => i :: tail)
  singles ++ prepend singles ++ prepend (prepend singles)

private def addSide (flat : Bool) (ns : Array (Array UInt64)) (xs : List UInt64) :=
  match xs with
  | [] => (ns, 0)
  | [i] => (ns, i)
  | i :: is =>
    if flat then (ns.push (#[4,7] ++ xs.toArray), ns.size.toUInt64)
    else is.foldl (fun (state : Array (Array UInt64) × UInt64) j =>
      (state.1.push #[4,7,state.2,j], state.1.size.toUInt64)) (ns, i)

private def counts (xs : List UInt64) : Array UInt64 :=
  #[(xs.count 0).toUInt64, (xs.count 1).toUInt64]

private def countsAgree : Bool :=
  sequences.all fun lhs => sequences.all fun rhs => [true,false].all fun flat =>
    let (ns,l) := addSide flat vars lhs
    let (ns,r) := addSide (!flat) ns rhs
    -- Repeat whole roots and reverse the second equation.
    let actual := GraphMatrix.build 2 7 2 ds ns #[l,r,r,l]
    let both := [0,1].all fun i => lhs.contains i || rhs.contains i
    let a := counts lhs
    let b := counts rhs
    actual == (if both then some #[a,b,b,a] else none)

#guard countsAgree

-- A small DAG can have many expanded occurrences. Exactly 4096 leaves on one side
-- fit the declared bound, and one more doubling is rejected.
private def powers (k : Nat) : Array (Array UInt64) :=
  (List.range k).foldl (fun ns _ =>
    let prev := (ns.size - 1).toUInt64
    ns.push #[4,7,prev,prev]) #[#[0,0,2]]
#guard GraphMatrix.build 1 7 2 ds (powers 12) #[12,0] == some #[#[4096],#[1]]
#guard GraphMatrix.build 1 7 2 ds (powers 13) #[13,0] == none

-- 131X+Y=137Z has no affordable integer basis on the old sparse search.
-- X=Y permits a positive solution. Requiring 131X+2Y=137Z forces Y=0.
private def coneNodes : Array (Array UInt64) :=
  let vars := #[#[0,0,2],#[0,1,2],#[0,2,2]]
  let a := #[4,7] ++ Array.replicate 131 0
  vars ++ #[a ++ #[1],#[4,7] ++ Array.replicate 137 2,a ++ #[1,1]]
#guard graphACFeasible 3 7 2 ds coneNodes #[0,1,3,4] == 2
#guard graphACFeasible 3 7 2 ds coneNodes #[5,4,3,4] == 1
#guard graphACFeasible 3 7 2 ds coneNodes #[0,1,5,4,3,4] == 1
#guard graphACFeasible 3 7 2 ds coneNodes #[3,4,0,1,3,4] == 2

private def expensive : ACBasis.Row 3 := .ofWeights (fun i => #[131,1,0][i.val]!) (fun i => #[0,0,137][i.val]!)
-- The new mandatory domain is certified independently of the execution.
example : ACBasis.RationalProjection.Within [expensive, expensive] := by
  simp only [ACBasis.RationalProjection.Within,ACBasis.RationalProjection.sizes]
  decide
#guard (Homogeneous.boundedBasis [expensive]).isNone
#guard (ACBasis.RationalProjection.basis [expensive]).isSome
-- 16 positive and 16 negative columns produce all 256 mixed pairs. A
-- second cross product exceeds the limit and defers before allocation.
private def partition (q : Fin 32 → Bool) : ACBasis.Row 32 :=
  .ofWeights (fun i => if q i then 1 else 0) (fun i => if q i then 0 else 1)
private def halves := partition (fun i => i.val < 16)
private def parity := partition (fun i => i.val % 2 == 0)
#guard ((ACBasis.RationalProjection.basis [halves]).map List.length) == some 256
#guard (ACBasis.RationalProjection.basis [parity,halves]).isNone
-- A coordinate beyond the bit budget cannot enter another stage.
#guard (ACBasis.RationalProjection.basis [ACBasis.Row.ofWeights
  (fun i : Fin 2 => if i.val = 0 then 2^128 else 0) (fun i => i.val)]).isNone

end Tamarin.GraphUnificationTests
