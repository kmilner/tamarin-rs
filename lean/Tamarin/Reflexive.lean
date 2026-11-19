import Tamarin.Unification
import TamarinRuntime.Interface

/-! Reflexive equations impose no constraints, even for nonground inputs.
This specifies mathematical answer coverage, not Maude's redundant enumeration.
The hybrid adapter uses this recipe for reflexive AC equations whose operands
are constants or variables strictly below the AC result sort and cannot split. Native-only can also use flat AC cancellation. -/
namespace Tamarin.Reflexive

def Recognized {sig : Signature} (p : Problem sig) : Prop :=
  ∀ e ∈ p, e.lhs = e.rhs

theorem identity_complete {sig : Signature} (p : Problem sig) (hp : Recognized p) :
    CompleteSet p [Substitution.identity] := by
  constructor
  · intro σ hσ e he
    rw [hp e he]; exact .refl _
  · intro ρ _
    refine ⟨Substitution.identity, by simp, ρ, ?_⟩
    intro v _; exact .refl _

theorem identity_correctIn {sig : Signature} (p : Problem sig) (hp : Recognized p)
    (avoid : List Variable) : Outcome.CorrectIn p avoid (.complete [Substitution.identity]) := by
  constructor
  · exact identity_complete p hp
  · intro σ hσ
    have := List.mem_singleton.mp hσ; subst σ
    intro v _; rfl
  · intro σ hσ
    have := List.mem_singleton.mp hσ; subst σ
    intro v hv w hw hn
    exact False.elim (hn (hw ▸ hv))

def decode {sig : Signature} (code : UInt8) : Outcome sig :=
  if code = 2 then .complete [Substitution.identity]
  else if code = 1 then .complete [] else .stopped .unsupported []

end Reflexive

structure ReflexiveBackend.Correct (backend : ReflexiveBackend) : Prop where
  correct : ∀ {sig : Signature} (p : Problem sig), Reflexive.Recognized p →
    ∀ avoid, Outcome.CorrectIn p avoid (Reflexive.decode (backend.solve true))
  completes : ∀ (sig : Signature),
    ∃ answers, Reflexive.decode (sig := sig) (backend.solve true) = .complete answers
  unsupported : backend.solve false = 0

end Tamarin
