import Tamarin.MixedSizeSystem

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
