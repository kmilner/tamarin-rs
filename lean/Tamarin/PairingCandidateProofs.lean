import Tamarin.PairingContract
import TamarinRuntime

namespace Tamarin.PairingCandidateProofs
open Pairing

theorem correct : PairingBackend.Correct RuntimeCandidate.pairing := by
  constructor
  · intro q hq avoid
    refine ⟨[Substitution.identity], rfl, constructor_variants_complete q hq, ?_⟩
    intro σ hσ; have := List.mem_singleton.mp hσ; subst σ
    exact identity_safe q avoid
  · intro first x a b hx ha hb hab hax hbx q hq hqx avoid haa hba
    refine ⟨[Substitution.identity, splitSubst x a b hx ha hb], rfl,
      projection_variants_complete first x a b hx ha hb hab q hq, ?_⟩
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact identity_safe q avoid
    · exact split_safe first x a b hx ha hb hax hbx q hq hqx avoid haa hba
  · intro first a b ha hb
    cases first
    · exact ⟨b, rfl, .snd _ _, hb⟩
    · exact ⟨a, rfl, .fst _ _, ha⟩

end Tamarin.PairingCandidateProofs
