import Tamarin.Algebra
namespace Tamarin.Term
variable {s : Signature} [DecidableEq s.Atom] [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym]

/-- Structural identity for interning source operands, including every argument
of a free symbol. Equality modulo the theory is specified separately by EquivB. -/
def syntaxEq : (x y : Term s) → Decidable (x = y)
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .atom x, .atom y => decidable_of_iff (x = y) (by simp)
  | .free f xs, .free g ys => by
    by_cases h : f = g
    · subst g
      letI checks (i : Fin (s.arity f)) := syntaxEq (xs i) (ys i)
      exact decidable_of_iff (∀ i, xs i = ys i) ⟨fun eq => congrArg _ (funext eq), fun eq => by cases eq; simp⟩
    · exact isFalse (fun eq => by cases eq; exact h rfl)
  | .comm f a b, .comm g c d | .ac f a b, .ac g c d => by
    letI := syntaxEq a c
    letI := syntaxEq b d
    exact decidable_of_iff (f = g ∧ a = c ∧ b = d) (by simp)
  | .var _, .atom _ | .var _, .free .. | .var _, .comm .. | .var _, .ac ..
  | .atom _, .var _ | .atom _, .free .. | .atom _, .comm .. | .atom _, .ac ..
  | .free .., .var _ | .free .., .atom _ | .free .., .comm .. | .free .., .ac ..
  | .comm .., .var _ | .comm .., .atom _ | .comm .., .free .. | .comm .., .ac ..
  | .ac .., .var _ | .ac .., .atom _ | .ac .., .free .. | .ac .., .comm .. =>
    isFalse (by intro eq; cases eq)
termination_by structural x => x
instance : DecidableEq (Term s) := syntaxEq

end Tamarin.Term
