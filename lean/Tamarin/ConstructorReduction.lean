import Tamarin.ConstructorVariants
import Tamarin.SortCheck

namespace Tamarin.Rewriting.ConstructorVariants
variable {sig : Signature}

/-- An inert free symbol preserves normal forms independently in each argument.
The child reducers can use different strategies under the same active equations. -/
theorem free_normalForm (rules : List (Equation sig))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : sig.FreeSym)
    (absent : Head.free f ∉ ruleHeads rules) (xs ys : Fin (sig.arity f) → Term sig)
    (children : ∀ i, NormalForm (ruleRoot rules) (xs i) (ys i)) :
    NormalForm (ruleRoot rules) (.free f xs) (.free f ys) := by
  refine ⟨.free f xs ys (fun i => (children i).1),
    constructor_node_normal rules apps _ absent (fun i => (children i).2.1), ?_⟩
  intro s hs
  have input := Term.checkSort_complete hs
  simp only [Term.checkSort, Bool.and_eq_true, List.all_eq_true] at input
  exact .widen (.free f ys (fun i => (children i).2.2 _
    (Term.checkSort_sound _ _ (input.2 i (List.mem_finRange i))))) (Term.rootSort_le hs)

end Tamarin.Rewriting.ConstructorVariants
