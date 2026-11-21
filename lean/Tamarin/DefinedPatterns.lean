import Tamarin.CheckedVariants
import Tamarin.NormalAlgebra

/-! A closed singleton variant frontier checks an entire open left side in
the supplied table. Its uniqueness proof covers steps inside the pattern and
at its root under the same normalized substitution. Constructing this frontier
requires neither global confluence nor a finite variant property assumption. -/
namespace Tamarin.DefinedPatterns
open Rewriting
variable {s : Signature} {rs : Problem s} {r : Equation s}

theorem unique_of_reply {rows} (h : CheckedVariants.Reply (ruleRoot rs) [r.lhs] rows) :
    NormalAlgebra.UniqueRow rs r := by
  intro σ norm a b left right
  exact (h.unique σ norm [a] [b] ⟨left,trivial⟩ ⟨right,trivial⟩).1

def frontier [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
    (rs : Problem s) (fuel : Nat) (r : Equation s) :
    Option {rows // CheckedVariants.Reply (ruleRoot rs) [r.lhs] rows} :=
  CheckedVariants.solve rs [r.lhs] fuel fuel

end Tamarin.DefinedPatterns
