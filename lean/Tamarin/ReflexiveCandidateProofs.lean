import Tamarin.Reflexive
import TamarinRuntime

namespace Tamarin.ReflexiveCandidateProofs

theorem correct : ReflexiveBackend.Correct RuntimeCandidate.reflexive where
  correct := fun p hp avoid => Reflexive.identity_correctIn p hp avoid
  completes := fun _ => ⟨[Substitution.identity], rfl⟩
  unsupported := rfl

end Tamarin.ReflexiveCandidateProofs
