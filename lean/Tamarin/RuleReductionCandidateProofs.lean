import Tamarin.RuleReduction
import TamarinRuntime.Candidate

namespace Tamarin.RuleReductionCandidateProofs
open Rewriting.RuleReduction

private theorem lookup_mem {rows : Rows} {k w : UInt64}
    (h : rows.lookup k = some w) : (k, w) ∈ rows := by
  obtain ⟨xs, ys, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

private theorem checked_iff (rows : Rows) :
    (∀ r ∈ rows, rows.lookup r.1 = some r.2) ↔ Consistent rows := by
  constructor
  · intro h k a b ha hb
    exact Option.some.inj ((h (k,a) ha).symm.trans (h (k,b) hb))
  · intro h r hr
    cases r with
    | mk k w =>
      cases he : rows.lookup k with
      | none =>
        have hn := List.lookup_eq_none_iff.mp he (k,w) hr
        simp at hn
      | some v =>
        exact congrArg some (h k v w (lookup_mem he) hr)

theorem correct : Correct RuntimeCandidate.reduceRuleSlot := by
  intro slot keys subjects
  unfold RuntimeCandidate.reduceRuleSlot
  dsimp only
  generalize keys.toList.zip subjects.toList = rows
  by_cases hc : keys.size = subjects.size ∧ ∀ r ∈ rows, rows.lookup r.1 = some r.2
  · rw [ite_eq_left hc]
    have hd := (checked_iff rows).mp hc.2
    cases hl : rows.lookup slot with
    | none =>
      refine ⟨Or.inl rfl, fun w => ⟨(by intro h; cases h), ?_⟩⟩
      intro ⟨_, _, hm⟩
      exact absurd (hc.2 (slot,w) hm) (by simp [hl])
    | some v =>
      refine ⟨Or.inr ⟨v, rfl⟩, fun w => ⟨?_, ?_⟩⟩
      · intro hw
        have he : v = w := by simpa using hw
        subst w; exact ⟨hc.1, hd, lookup_mem hl⟩
      · intro ⟨_, _, hm⟩
        rw [hd slot v w (lookup_mem hl) hm]
  · rw [ite_eq_right hc]
    refine ⟨Or.inl rfl, fun w => ⟨(by intro h; cases h), ?_⟩⟩
    intro ⟨he, hd, _⟩
    exact False.elim (hc ⟨he, (checked_iff rows).mpr hd⟩)

end Tamarin.RuleReductionCandidateProofs
