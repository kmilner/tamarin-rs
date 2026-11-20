import Tamarin.DHFiniteVariants
import Tamarin.CheckedReduction

namespace Tamarin.Rewriting.DHPeer.CanonicalTests
open Builtin

example : WellFounded (fun b a => StepModulo (ruleRoot rules) a b) := exactTable.terminating

example : MaudeOperations.CanonicalPresentation (ruleRoot rules) := exactTable.canonical

example : MaudeOperations.FiniteVariantProperty (ruleRoot rules) := exactTable.finiteVariantProperty

private abbrev mul := s.product.mul
private abbrev inv := s.product.inv
private abbrev pow := s.power
private abbrev one := s.product.one
private abbrev x : Term sig := .var ⟨0,.msg⟩
private abbrev y : Term sig := .var ⟨1,.msg⟩
private abbrev z : Term sig := .var ⟨2,.msg⟩
private abbrev node : Term sig := .var ⟨3,.node⟩

private def normalizes (t expected : Term sig) := match
    CheckedReduction.run rules (SymbolWeight.rank ExactTable.weight t + 1) t with
  | some u => ReferenceMatching.equal u expected
  | none => false

-- At the whole power root, removing exponent one and flattening the tower
-- join. The inverse root below can pull either inverse or let its child join.
#guard normalizes (pow (pow x y) one) (pow x y)
#guard normalizes (inv (mul (inv x) (inv y))) (mul x y)
#guard normalizes (mul (inv (mul x y)) (mul y z)) (mul (inv x) z)

-- A Node cannot instantiate a Msg rule variable. It can surround an active
-- AC subproduct, and a final unit may persist next to it.
#guard normalizes (mul node (mul (inv (mul x y)) (mul y z))) (mul node (mul (inv x) z))
#guard normalizes (mul node (mul x (inv x))) (mul node one)
#guard normalizes (pow node one) (pow node one)

end Tamarin.Rewriting.DHPeer.CanonicalTests
