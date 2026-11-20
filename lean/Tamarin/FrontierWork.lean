import Tamarin.ACRepresentation
import Tamarin.VariablePermutation

/-! Charge prospective root/rule comparisons before entering a narrowing
layer. An AC position may select any nonempty subproduct. The estimate is
used only for deferral; passing it never certifies an answer. -/
namespace Tamarin.FrontierWork
variable {s : Signature} [DecidableEq s.ACSym]

/-- Under an AC head, shared variable classes can branch even when that head
is nested inside a free or commutative rule pattern. -/
private def acVariables : Term s → List Variable
  | .var _ | .atom _ => []
  | .free _ xs => (List.ofFn fun i => acVariables (xs i)).flatten
  | .comm _ a b => acVariables a ++ acVariables b
  | .ac _ a b => a.variables ++ b.variables

private def positions : Term s → Nat
  | .var _ | .atom _ => 1
  | .free _ xs => 1 + (List.ofFn fun i => positions (xs i)).sum
  | .comm _ a b => 2 + positions a + positions b
  | .ac f a b => 2 ^ min 20 ((ACRepresentation.flatten f a).length + (ACRepresentation.flatten f b).length) +
      positions a + positions b

def admits (rules : Problem s) (q : List (Term s)) (depth : Nat) : Bool :=
  let table := (rules.map fun r =>
    (positions r.lhs + positions r.rhs) * 2 ^ min 20 (acVariables r.lhs).eraseDups.length).sum
  (1 + table) * (q.map positions).sum ≤ 64 * depth

/-- Automatic table admission can compare two rule patterns by unification.
They are standardized apart, so even identical source variable IDs on the two
sides count separately. Use the same per-stage allowance as frontier discovery. -/
def admitsRootPair (p q : Term s) (depth : Nat := 4) : Bool :=
  let captures := (acVariables p).eraseDups.length + (acVariables q).eraseDups.length
  (positions p + 1) * (positions q + 1) * 2 ^ min 20 captures ≤ 64 * depth

end Tamarin.FrontierWork
