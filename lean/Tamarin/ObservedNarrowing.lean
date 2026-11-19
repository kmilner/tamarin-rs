import Tamarin.OpenNarrowing

/-! Narrow a single open application and return its normal value together with
the instantiated arguments. A match need not determine the selected variable
uniquely. Each possible normal result chooses its own match and that same
match accounts for every argument. -/
namespace Tamarin.Rewriting.OpenNarrowing.Schema
variable {sig : Signature} {P : Term sig → Prop} (s : Schema sig P)

/-- Every normal value after a successful match is the result of an actual
root match, even when the left side contains C or AC operators. -/
theorem result_match {R : Root sig} (atHead : s.AtHead R) {ρ : Substitution sig}
    (hn : Normalized R ρ) (hit : ∃ μ, s.Matches ρ μ) {u : Term sig}
    (nf : NormalForm R (ρ.apply (s.input none)) u) :
    ∃ μ, s.Matches ρ μ ∧ EquivB u (μ.image s.z) := by
  let results := fun v => ∃ μ, s.Matches ρ μ ∧ v = μ.image s.z
  have normal (v) (h : results v) : Normal R v := by
    obtain ⟨μ, hm, rfl⟩ := h
    obtain ⟨j, hz⟩ := s.outputOccurs
    exact RulePattern.image_normal ((normal_equiv _ (hm j)).mp (hn _)) hz
  have all ys (hy : ∀ i, EquivB (ρ.image (s.x i)) (ys i)) b
      (hr : R (.free s.d ys) b) : ∃ v, results v ∧ EquivB b v := by
    obtain ⟨μ, hμ, rfl⟩ := (atHead _ _).mp hr
    exact ⟨_, ⟨μ, fun i => hμ i ▸ hy i, rfl⟩, .refl _⟩
  rcases reduces_free_root_results (fun i => hn (s.x i)) results normal all nf.1 with eq | ⟨_, ⟨μ, hm, rfl⟩, eq⟩
  · obtain ⟨μ, hm⟩ := hit
    exact False.elim (((normal_equiv _ eq).mpr nf.2.1) (μ.image s.z)
      ⟨_, _, .free _ _ _ hm, .root ((atHead _ _).mpr ⟨μ, fun _ => rfl, rfl⟩), .refl _⟩)
  · exact ⟨μ, hm, eq⟩

def observations (indices : List s.Index) : List (Option s.Index) := none :: indices.map some

theorem observed_complete {R : Root sig} (atHead : s.AtHead R)
    (vars : Normalized R Substitution.identity) (patterns : ∀ i, Normal R (s.p i))
    (indices : List s.Index) :
    let q := s.observations indices
    CompleteVariants R (q.map s.input) [s.identityArm q, s.ruleArm q] := by
  classical
  let q := s.observations indices
  have hq : none ∈ q := by simp [q, observations]
  refine ⟨s.arms_sound atHead vars patterns q, ?_⟩
  intro ρ hn values hvs
  cases values with
  | nil => exact False.elim hvs
  | cons u tail =>
    have obs : NormalForm R (ρ.apply (s.input none)) u := hvs.1
    by_cases hit : ∃ μ, s.Matches ρ μ
    · obtain ⟨μ, hm, hu⟩ := s.result_match atHead hn hit obs
      let δ := s.restrict μ
      have hδ : Normalized R δ := by
        intro v
        by_cases hl : s.Local v
        · obtain ⟨i, hv⟩ := hl
          simpa [δ, restrict, show s.Local v from ⟨i, hv⟩] using
            RulePattern.image_normal ((normal_equiv _ (hm i)).mp (hn _)) hv
        · change Normal R (if s.Local v then μ.image v else .var v)
          rw [ite_eq_right hl]; exact vars v
      refine ⟨s.ruleArm q, by simp [q], δ, hδ, ?_, ?_⟩
      · intro v hv
        obtain ⟨i, rfl⟩ := (s.observed_iff q hq v).mp hv
        change EquivB _ (δ.apply (s.split.image _))
        rw [s.split_owned, s.restrict_pattern]
        exact hm i
      · refine ⟨?_, ?_⟩
        · simpa [q, observations, ruleArm, value, δ, Substitution.apply, Term.subst,
            restrict, show s.Local s.z from s.outputOccurs] using hu
        · apply aligned_values (indices.map some) s.input s.value tail hvs.2
          rintro _ h w nf
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
          change EquivB w (δ.apply (s.p i))
          rw [s.restrict_pattern]
          exact (normal_reduces_equiv nf.1 (hn (s.x i))).symm.trans (hm i)
    · refine ⟨s.identityArm q, by simp [q], ρ, hn, fun _ _ => .refl _,
        aligned_values q s.input s.input _ hvs ?_⟩
      intro a _ w nf
      apply (normal_reduces_equiv nf.1 _).symm
      cases a with
      | some i => exact hn (s.x i)
      | none => exact s.noMatch atHead hn hit

theorem observed_table (rules : List (Equation sig)) (original : s.Index → Term sig)
    (rhs : Variable) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free s.d original, .var rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, .var rhs⟩)
    (patterns : ∀ i, s.p i = (π.subst sig).apply (original i)) (result : s.z = π.forward rhs)
    (constructors : ∀ i, ∀ f ∈ ConstructorVariants.operators (s.p i), f ∉ ConstructorVariants.ruleHeads rules)
    (indices : List s.Index) (avoid : List Variable)
    (fresh : ∀ v, s.Local v → v ∉ avoid ∧ ¬ ∃ i, s.x i = v) :
    let q := s.observations indices
    s.Admissible (ruleRoot rules) q avoid [s.identityArm q, s.ruleArm q] := by
  have atHead : s.AtHead (ruleRoot rules) := by
    intro ys b
    simpa only [patterns, result] using ruleRoot_fresh_selected rules s.d original rhs π
      apps present only ys b
  obtain ⟨vars, ctor⟩ := ConstructorVariants.constructor_normal rules apps
  exact ⟨s.observed_complete atHead vars (fun i => by
    simpa using ctor (s.p i) (constructors i) Substitution.identity vars) indices,
    s.safe _ (by simp [observations]) avoid fresh⟩

end Tamarin.Rewriting.OpenNarrowing.Schema
