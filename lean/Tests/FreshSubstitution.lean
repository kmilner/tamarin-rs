import Tamarin.FreshSubstitution

namespace Tamarin.FreshSubstitutionChecks

private def msg : Variable := ⟨1, .msg⟩
private def pub : Variable := ⟨1, .pub⟩
private def context : Variable := ⟨2, .msg⟩

/-- Equal numeric IDs of different sorts are different identities. -/
private def permutation : VariablePermutation :=
  VariablePermutation.ofBlock [msg, pub, msg] 3 (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> decide)

example : permutation.forward msg = ⟨4, .msg⟩ := rfl
example : permutation.forward pub = ⟨4, .pub⟩ := rfl
example : permutation.forward context = context := rfl
example : permutation.backward ⟨4, .msg⟩ = msg := rfl
example : permutation.backward ⟨4, .pub⟩ = pub := rfl
example : permutation.forward ⟨99, .msg⟩ = ⟨99, .msg⟩ := rfl

/-- The reference supply is unbounded. A future u64 adapter must report
overflow explicitly rather than wrapping/clamping distinct witnesses. -/
example : VariablePermutation.freshBound [⟨18446744073709551615, .msg⟩] =
    18446744073709551616 := rfl

example (sig : Signature) (σ : Substitution sig) (avoid : List Variable) (v : Variable) :
    (FreshAnswer.freshen [] avoid σ).image v = .var v := rfl

example {sig : Signature} (t : Term sig) :
    (permutation.inverse.subst sig).apply ((permutation.subst sig).apply t) = t :=
  permutation.inverse_apply t

/-- The whole-set theorem permits a different fresh witness scope per arm. -/
example {sig : Signature} (request : Request sig) (answers : List (Substitution sig)) :
    OutputRefinement request answers
      (answers.map (FreshAnswer.freshen request.problem request.avoid)) :=
  FreshAnswer.output_refinement request answers

/-- A packet cannot exploit first/last map insertion to assign two different
images to the same variable. Equal repeated entries remain permitted. -/
example {sig : Signature} (v : Variable) (a b : Term sig) (h : a ≠ b) :
    ¬ ∃ answer : FreshAnswer sig, answer.bindings = [(v, a), (v, b)] := by
  rintro ⟨answer, hb⟩
  apply h
  exact answer.consistent v a b (by simp [hb]) (by simp [hb])

example {sig : Signature} (p : Problem sig) (avoid : List Variable)
    (σ : Substitution sig) (t : Term sig) :
    (FreshAnswer.freshen p avoid σ).apply ((FreshAnswer.freshen p avoid σ).apply t) =
      (FreshAnswer.freshen p avoid σ).apply t :=
  FreshAnswer.freshen_idempotent p avoid σ t

end Tamarin.FreshSubstitutionChecks
