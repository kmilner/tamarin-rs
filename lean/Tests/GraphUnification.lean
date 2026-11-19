import Tamarin.GraphUnification
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

end Tamarin.GraphUnificationTests
