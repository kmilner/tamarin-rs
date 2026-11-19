import Tamarin.MixedSizeSystem
import TamarinRuntime

namespace Tamarin.MixedSizeTests
open MixedSizeSystem ACFeasibility

private def sig : Signature where
  FreeSym := Unit
  CSym := Empty
  ACSym := Unit
  Atom := Empty
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort := Empty.elim
  acSort _ := .msg
  atomSort := Empty.elim

private def name (i : Fin 8) : Variable := ⟨i.val,.msg⟩
private def x (i : Fin 8) : Term sig := .var (name i)
private def h (t : Term sig) : Term sig := .free () (fun _ => t)
private def sum (a b c d : Term sig) : Term sig := .ac () a (.ac () b (.ac () c d))
private def target := sum (x 4) (x 5) (x 6) (x 7)
private def first : Equation sig := ⟨sum (h (x 0)) (x 1) (x 2) (x 3),target⟩
private def second : Equation sig := ⟨sum (x 0) (h (h (x 1))) (x 2) (x 3),target⟩

-- A strictly positive size assignment exists for each individual equation.
example : checkCertificate [row name first] (.primal #[1,1,1,1,1,2,1,1,1]) = some true := by decide +kernel
example : checkCertificate [row name second] (.primal #[1,1,1,1,1,3,1,1,1]) = some true := by decide +kernel

-- Subtracting the first equation from the second gives a positive constant.
-- This refutation is about the original sorted terms at all substitutions.
example : ¬ Problem.Satisfiable [first,second] := by
  apply refutes _ name _ _ (c := .dual #[-1,1])
  · decide
  · intro i j eq
    exact Fin.ext (congrArg Variable.id eq)
  · intro e he v hv
    have mem : v ∈ List.ofFn name := by
      rcases List.mem_cons.mp he with rfl | he
      · exact (show first.lhs.variables ++ first.rhs.variables = List.ofFn name by decide +kernel) ▸ hv
      · obtain rfl := List.mem_singleton.mp he
        exact (show second.lhs.variables ++ second.rhs.variables = List.ofFn name by decide +kernel) ▸ hv
    exact List.mem_ofFn.mp mem

end Tamarin.MixedSizeTests

/-- Stress the physical export with shared graph nodes, permuted and regrouped
AC children, repeated variables, and both equation orientations. The variable
on the right of each equation is fresh and can be assigned either left side. -/
def main : IO Unit := do
  let ds : Array UInt64 := #[2,0,1,2,2, 3,1,2,2,2,2, 4,2,2,2,2,2]
  let mut cases := 0
  for k in [0:48] do
    let x := (3*k+11).toUInt64
    let y := x + 1
    let u := x + 2
    let mut ns : Array (Array UInt64) := #[#[0,x,2],#[0,y,2],#[0,u,2],#[2,0,0],#[3,1,1,3]]
    let factors : Array UInt64 := (Array.range (3+k%6)).map fun i => #[0,1,3,4][(i+k)%4]!
    -- The same sum once flat and once with a binary AC child.
    ns := ns.push (#[4,2] ++ factors)
    ns := ns.push (#[4,2] ++ factors.extract 0 2)
    ns := ns.push (#[4,2,6] ++ (factors.extract 2 factors.size).reverse)
    ns := ns.push #[2,0,7]
    for orientations in [0:4] do
      let first : Array UInt64 := if orientations % 2 = 0 then #[2,5] else #[5,2]
      let second := fun (t : UInt64) => if orientations / 2 = 0 then #[2,t] else #[t,2]
      for swap in [false,true] do
        let roots := fun t => if swap then second t ++ first else first ++ second t
        let yes := Tamarin.Executable.wholeUnify ds ns (roots 7)
        -- Setting u to the original sum solves this neighbor.
        unless yes == #[#[0]] || yes == #[#[2]] do
          throw <| IO.userError s!"refuted a satisfiable regrouping at {k}"
        -- Hash adds one node to the regrouped sum under every substitution.
        unless Tamarin.Executable.wholeUnify ds ns (roots 8) == #[#[1]] do
          throw <| IO.userError s!"missed a mixed-size contradiction at {k}"
        cases := cases + 2
  IO.println s!"Checked {cases} mixed graph requests against the original term-size argument."
