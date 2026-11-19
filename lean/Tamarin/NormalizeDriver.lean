import Tamarin.Rewriting

/-! A reusable bounded normalization driver. A reducer may choose any rewrite
strategy or specialized kernel. Its `done` case must establish irreducibility
modulo the whole theory, not merely failure to find a syntactic root match.
This matters for AC: reassociation can expose a redex across child boundaries.
-/
namespace Tamarin.Rewriting
variable {sig : Signature}

inductive Progress (sig : Signature) where
  | done (term : Term sig)
  | next (term : Term sig)
  | stopped (reason : StopReason) (term : Term sig)

def Progress.Correct (root : Root sig) (input : Term sig) : Progress sig → Prop
  | .done result => NormalForm root input result
  | .next result => Reduces root input result ∧ ∀ s, HasSort input s → HasSort result s
  | .stopped _ result => Reduces root input result

def normalizeFuel (reduce : Term sig → Progress sig) : Nat → Term sig → NormalizeResult sig
  | 0, t => .stopped .resourceLimit t
  | fuel + 1, t => match reduce t with
    | .done u => .complete u
    | .next u => normalizeFuel reduce fuel u
    | .stopped reason u => .stopped reason u

theorem normalizeFuel_correct (root : Root sig) (reduce : Term sig → Progress sig)
    (hc : ∀ t, (reduce t).Correct root t) (fuel : Nat) (t : Term sig) :
    (normalizeFuel reduce fuel t).Correct root t := by
  induction fuel generalizing t with
  | zero => exact .basis (.refl _)
  | succ fuel ih =>
    have h := hc t
    cases hr : reduce t with
    | done u => simpa only [normalizeFuel, hr, Progress.Correct, NormalizeResult.Correct] using h
    | stopped reason u => simpa only [normalizeFuel, hr, Progress.Correct, NormalizeResult.Correct] using h
    | next u =>
      simp only [hr, Progress.Correct] at h
      have hi := ih u
      simp only [normalizeFuel, hr]
      cases hn : normalizeFuel reduce fuel u with
      | complete result =>
        simp only [hn, NormalizeResult.Correct] at hi
        exact ⟨.trans h.1 hi.1, hi.2.1, fun s hs => hi.2.2 s (h.2 s hs)⟩
      | stopped reason result =>
        simp only [hn, NormalizeResult.Correct] at hi
        exact .trans h.1 hi

/-- A rank proof supplies completion; correctness alone permits an endless
sequence of `next` results. The driver never treats a bound as such a proof. -/
def Decreases (reduce : Term sig → Progress sig) (rank : Term sig → Nat) : Prop :=
  ∀ t, match reduce t with
  | .done _ => True
  | .next u => rank u < rank t
  | .stopped _ _ => False

theorem normalizeFuel_completes (reduce : Term sig → Progress sig) (rank : Term sig → Nat)
    (hd : Decreases reduce rank) (fuel : Nat) (t : Term sig) (hf : rank t < fuel) :
    ∃ u, normalizeFuel reduce fuel t = .complete u := by
  induction fuel generalizing t with
  | zero => exact False.elim (Nat.not_lt_zero _ hf)
  | succ fuel ih =>
    have h := hd t
    cases hr : reduce t with
    | done u => exact ⟨u, by simp only [normalizeFuel, hr]⟩
    | stopped reason u => simp only [hr] at h
    | next u =>
      simp only [hr] at h
      obtain ⟨v, hv⟩ := ih u (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ hf))
      exact ⟨v, by simp only [normalizeFuel, hr, hv]⟩

def rankedNormalizer (root : Root sig) (reduce : Term sig → Progress sig)
    (rank : Term sig → Nat) (hc : ∀ t, (reduce t).Correct root t)
    (hd : Decreases reduce rank) : Normalizer root (fun _ => True) where
  run := fun t => normalizeFuel reduce (rank t + 1) t
  correct := fun t _ => normalizeFuel_correct root reduce hc _ t
  completes := fun t _ => normalizeFuel_completes reduce rank hd _ t (Nat.lt_succ_self _)

end Tamarin.Rewriting
