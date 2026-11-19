import Tamarin.MatchingFree

/-! A checked contradiction in one equation suffices to refute a conjunction.
Decomposing a pair of equal free heads preserves every solution at each
corresponding argument, independently of any other equations or bindings. -/
namespace Tamarin.ConjunctRefutation
variable {sig : Signature}

inductive Part (p : Problem sig) : Equation sig → Prop where
  | member {e} : e ∈ p → Part p e
  | child {f : sig.FreeSym} {xs ys : Fin (sig.arity f) → Term sig} (i : Fin (sig.arity f)) :
    Part p ⟨.free f xs,.free f ys⟩ → Part p ⟨xs i,ys i⟩

theorem Part.solves {p : Problem sig} {e : Equation sig} (h : Part p e) {σ : Substitution sig}
    (solution : p.Solves σ) : EquivB (σ.apply e.lhs) (σ.apply e.rhs) := by
  induction h with
  | member m => exact solution _ m
  | child i _ ih => exact (Matching.free_equiv_iff ..).mp ih i

theorem refutes {p : Problem sig} {e : Equation sig} (part : Part p e)
    (empty : CompleteSet [e] []) : CompleteSet p [] := by
  apply (complete_empty_iff p).mpr
  rintro ⟨σ,solution⟩
  apply (complete_empty_iff [e]).mp empty
  refine ⟨σ,?_⟩
  intro x hx
  obtain rfl := List.mem_singleton.mp hx
  exact part.solves solution

end Tamarin.ConjunctRefutation
