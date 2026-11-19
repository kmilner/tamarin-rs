import Tamarin.SpecializedRule
import Tamarin.SpecializedFresh

/-! A unique rule with a ground constructor result, specialized at constructor
arguments of a packed query. An anchored rule variable denotes the entire
argument at that position, including all its caller variables. -/
namespace Tamarin.Rewriting.GroundNarrowing
open SpecializedRule
variable {sig : Signature}

structure Plan (sig : Signature) where
  d : sig.FreeSym
  arg : Fin (sig.arity d) → Term sig
  pat : Fin (sig.arity d) → Term sig
  rhs : Term sig
  typed : HasSort rhs (sig.outputSort d)
  inputTyped : ∀ i, HasSort (arg i) (sig.inputSort d i)
  ground : ∀ v, ¬ rhs.Occurs v
  hole : Variable → Option (Fin (sig.arity d))
  anchor : Substitution sig
  solution : Substitution sig
  /-- A hole expands to the specialized pattern at its argument position. -/
  image : ∀ v, solution.image v = (hole v).elim (.var v) (fun i => anchor.apply (pat i))
  holeArg : ∀ v i, hole v = some i → arg i = .var v
  /-- Each argument is either an independent hole or a constructor term
  that binds a bare rule parameter. Captured terms contain no holes. -/
  position : ∀ i, (∃ v, hole v = some i) ∨
    (∃ w, pat i = .var w ∧ anchor.image w = arg i)
  parameter : ∀ w, anchor.image w = .var w ∨ ∃ j, pat j = .var w ∧ anchor.image w = arg j
  openAt : ∃ i v, arg i = .var v ∧ ConstructorVariants.Application (pat i)

namespace Plan
variable (s : Plan sig)

def input (part : Option (Term sig)) : Term sig := part.getD (.free s.d s.arg)
def values (σ : Substitution sig) : Option (Term sig) → Term sig
  | none => s.rhs
  | some t => σ.apply t

def Local (v : Variable) := ∃ i, (s.pat i).Occurs v

/-- An occurrence copied from a fixed argument must remain independent of the
flexible variables that receive the specialized patterns. -/
def Separated := ∀ i, (¬ ∃ v, s.hole v = some i) → ∀ v, (s.arg i).Occurs v → s.hole v = none

theorem separated_of_ids (holes deps : Array UInt64) (encode : Variable → UInt64)
    (disjoint : ∀ w ∈ holes.toList, w ∉ deps.toList)
    (holesLive : ∀ v i, s.hole v = some i → encode v ∈ holes.toList)
    (depsLive : ∀ i, (¬ ∃ v, s.hole v = some i) → ∀ v, (s.arg i).Occurs v →
      encode v ∈ deps.toList) : s.Separated := by
  intro i fixed v hv
  cases e : s.hole v with
  | none => rfl
  | some j => exact False.elim (disjoint _ (holesLive v j e) (depsLive i fixed v hv))

theorem specializes (disjoint : s.Separated) (i : Fin (sig.arity s.d)) :
    s.solution.apply (s.arg i) = s.anchor.apply (s.pat i) := by
  by_cases h : ∃ v, s.hole v = some i
  · obtain ⟨v,hv⟩ := h
    rw [s.holeArg v i hv]; exact (s.image v).trans (by simp [hv])
  · obtain ⟨w, hp, hθ⟩ := (s.position i).resolve_left h
    rw [hp]; change _ = s.anchor.image w; rw [hθ]
    exact (Term.subst_eq_of_agree _ Term.var _ fun v hv => by
      rw [s.image, disjoint i h v hv]; rfl).trans (Term.subst_id _)

/-- The witness for completeness must also instantiate unrelated observed
variables. Use the rule match only on actual pattern variables. -/
noncomputable def combine (ρ μ : Substitution sig) : Substitution sig := by
  classical
  exact { image := fun v => if s.Local v then μ.image v else ρ.image v
          support := μ.support ++ ρ.support
          outside := by
            intro v hv
            simp only [List.mem_append, not_or] at hv
            simp [μ.outside v hv.1, ρ.outside v hv.2]
          sorted := by intro v; split <;> first | exact μ.sorted v | exact ρ.sorted v }

private theorem arg_observed (q : List (Option (Term sig))) (hq : none ∈ q)
    (i) (v) (hv : (s.arg i).Occurs v) : Observed (q.map s.input) v :=
  ⟨_, List.mem_map.mpr ⟨none, hq, rfl⟩, i, hv⟩

theorem factors {R : Root sig} (q : List (Option (Term sig))) (hq : none ∈ q)
    (apart : ∀ v, Observed (q.map s.input) v → ¬ s.Local v)
    {ρ μ : Substitution sig} (hn : Normalized R ρ) (ha : ∀ i, Normal R (ρ.apply (s.arg i)))
    (hit : Matches s.arg s.pat ρ μ) :
    Normalized R (s.combine ρ μ) ∧ ∀ v, Observed (q.map s.input) v →
      EquivB (ρ.image v) ((s.combine ρ μ).apply (s.solution.image v)) := by
  classical
  let δ := s.combine ρ μ
  have ambient (v) (hv : Observed (q.map s.input) v) : δ.image v = ρ.image v := by
    simp [δ, combine, apart v hv]
  have bindings (i) : EquivB (δ.apply (s.anchor.apply (s.pat i))) (μ.apply (s.pat i)) := by
    rw [← Substitution.apply_compose]
    apply Term.subst_equiv
    intro w hw
    change EquivB (δ.apply (s.anchor.image w)) (μ.image w)
    rcases s.parameter w with hw' | ⟨j, hp, hθ⟩
    · rw [hw']; change EquivB (δ.image w) _
      simp [δ, combine, show s.Local w from ⟨i, hw⟩, EquivB.refl]
    · rw [hθ]
      have e : δ.apply (s.arg j) = ρ.apply (s.arg j) :=
        Term.subst_eq_of_agree _ _ _ fun v hv => ambient v (s.arg_observed q hq j v hv)
      rw [e]; simpa only [hp, Substitution.apply, Term.subst] using hit j
  constructor
  · intro v
    by_cases hl : s.Local v
    · obtain ⟨i, hi⟩ := hl
      have nv := RulePattern.image_normal ((normal_equiv _ (hit i)).mp (ha i)) hi
      simpa [combine, show s.Local v from ⟨i, hi⟩] using nv
    · simpa [combine, hl] using hn v
  · intro v hv
    rw [s.image]
    cases e : s.hole v with
    | none => exact (ambient v hv).symm ▸ EquivB.refl _
    | some i =>
      have h := hit i; rw [s.holeArg v i e] at h
      exact h.trans (bindings i).symm

def identityArm (q : List (Option (Term sig))) : Variant sig :=
  ⟨Substitution.identity, q.map s.input⟩

def ruleArm (q : List (Option (Term sig))) : Variant sig :=
  ⟨s.solution, q.map (s.values s.solution)⟩

/-- Preconditions below are inventories of the actual finite rule/query trees.
All normality and completeness conclusions are derived from these inventories. -/
structure Domain (rules : List (Equation sig)) (q : List (Option (Term sig))) : Prop where
  apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs
  argConstructors : ∀ i, ∀ f ∈ ConstructorVariants.operators (s.arg i), f ∉ ConstructorVariants.ruleHeads rules
  patternConstructors : ∀ i, ∀ f ∈ ConstructorVariants.operators (s.pat i), f ∉ ConstructorVariants.ruleHeads rules
  resultConstructors : ∀ f ∈ ConstructorVariants.operators s.rhs, f ∉ ConstructorVariants.ruleHeads rules
  observers : ∀ t, some t ∈ q → ∀ f ∈ ConstructorVariants.operators t, f ∉ ConstructorVariants.ruleHeads rules
  containsApp : none ∈ q
  apart : ∀ v, Observed (q.map s.input) v → ¬ s.Local v

theorem raw_complete {rules : List (Equation sig)} {q : List (Option (Term sig))}
    (dom : s.Domain rules q) (disjoint : s.Separated) (atHead : AtHead (ruleRoot rules) s.d s.pat s.rhs) :
    CompleteVariants (ruleRoot rules) (q.map s.input) [s.identityArm q, s.ruleArm q] := by
  let R := ruleRoot rules
  obtain ⟨vars, ctor⟩ := ConstructorVariants.constructor_normal rules dom.apps
  have normArg (ρ) (hn : Normalized R ρ) (i) := ctor _ (dom.argConstructors i) ρ hn
  have normAnchor : Normalized R s.anchor := by
    intro v; rcases s.parameter v with h | ⟨j, _, h⟩
    · rw [h]; exact vars v
    · rw [h]; simpa using normArg Substitution.identity vars j
  have normSol : Normalized R s.solution := by
    intro v; rw [s.image]; cases s.hole v with
    | none => exact vars v
    | some i => exact ctor _ (dom.patternConstructors i) s.anchor normAnchor
  have normResult : Normal R s.rhs := by simpa using ctor _ dom.resultConstructors Substitution.identity vars
  obtain ⟨i, x, hx, rigid⟩ := s.openAt
  have oi := noMatch atHead (normArg Substitution.identity vars) (openMiss i x hx rigid)
  constructor
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · refine ⟨vars, aligned_maps q s.input s.input ?_⟩
      intro part hp
      change NormalForm R (Substitution.identity.apply _) _
      rw [Substitution.apply_identity]
      refine ⟨.basis (.refl _), ?_, fun _ hs => hs⟩
      cases part with
      | none => simpa [input] using oi
      | some t => simpa [input] using ctor t (dom.observers t hp) Substitution.identity vars
    · obtain rfl := List.mem_singleton.mp h
      refine ⟨normSol, aligned_maps q s.input (s.values s.solution) ?_⟩
      intro part hp
      cases part with
      | none =>
        have hit : Matches s.arg s.pat s.solution s.anchor := fun i => by
          rw [s.specializes disjoint]; exact .refl _
        exact matchedNormalForm atHead hit normResult s.typed
      | some t => exact ⟨.basis (.refl _), ctor t (dom.observers t hp) _ normSol, fun _ hs => hs⟩
  · intro ρ hn normalValues hv
    by_cases hit : ∃ μ, Matches s.arg s.pat ρ μ
    · obtain ⟨μ, hit⟩ := hit
      obtain ⟨nδ, agree⟩ := s.factors q dom.containsApp dom.apart hn (normArg ρ hn) hit
      let δ := s.combine ρ μ
      refine ⟨s.ruleArm q, by simp, δ, nδ, agree, aligned_values q s.input (s.values s.solution) _ hv ?_⟩
      intro part hp u nf
      cases part with
      | none =>
        change EquivB u (δ.apply s.rhs)
        rw [apply_ground s.ground]
        exact uniqueEq atHead hit (normArg ρ hn) normResult nf
      | some t =>
        have he := (normal_reduces_equiv nf.1 (ctor t (dom.observers t hp) ρ hn)).symm
        apply he.trans
        change EquivB (ρ.apply t) (δ.apply (s.solution.apply t))
        rw [← Substitution.apply_compose]
        exact Term.subst_equiv _ _ _ fun v ht => agree v
          ⟨_, List.mem_map.mpr ⟨some t, hp, rfl⟩, ht⟩
    · refine ⟨s.identityArm q, by simp, ρ, hn, fun _ _ => .refl _, aligned_values q s.input s.input _ hv ?_⟩
      intro part hp u nf
      apply (normal_reduces_equiv nf.1 _).symm
      cases part with
      | none => exact noMatch atHead (normArg ρ hn) hit
      | some t => exact ctor t (dom.observers t hp) ρ hn

/-- The ABI uses a two-branch mask. Its narrowed branch explicitly rebinds
all observed variables, renaming the shared range of the whole packet once. -/
def decode (q : List (Option (Term sig))) (vs : List Variable) (π : VariablePermutation)
    (mask : UInt8) : Option (List (Variant sig)) :=
  if mask = 3 then some [s.identityArm q, SpecializedFresh.renameArm vs π (s.ruleArm q)] else none

/-- Public acceptance obligation. Replacing the search algorithm does not
require preserving an enumeration order or choosing particular fresh names. -/
def Admissible (R : Root sig) (q : List (Option (Term sig))) (avoid : List Variable)
    (answers : List (Variant sig)) :=
  CompleteVariants R (q.map s.input) answers ∧ ∀ a ∈ answers,
    a.Safe (q.map s.input) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

theorem table_correct (rules : List (Equation sig)) (original : Fin (sig.arity s.d) → Term sig)
    (rename : VariablePermutation) (q : List (Option (Term sig))) (dom : s.Domain rules q)
    (present : (⟨.free s.d original, s.rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d → r = ⟨.free s.d original, s.rhs⟩)
    (renamed : ∀ i, s.pat i = (rename.subst sig).apply (original i))
    (vs avoid : List Variable) (π : VariablePermutation)
    (inventory : ∀ v, v ∈ vs ↔ Observed (q.map s.input) v)
    (fresh : ∀ v ∈ vs, ∀ w, (s.solution.image v).Occurs w → π.forward w ∉ vs ++ avoid)
    (disjoint : s.Separated) (mask : UInt8) (both : mask = 3) :
    ∃ answers, s.decode q vs π mask = some answers ∧ s.Admissible (ruleRoot rules) q avoid answers := by
  subst mask
  have root : AtHead (ruleRoot rules) s.d s.pat s.rhs := by
    simpa only [funext renamed] using ground_at_head_fresh rules s.d original s.rhs rename
      dom.apps present only s.ground
  refine ⟨_, rfl, SpecializedFresh.complete_rename_last rules vs (q.map s.input) [s.identityArm q]
    (s.ruleArm q) π (ConstructorVariants.constructor_normal rules dom.apps).1
    (fun v => (inventory v).mpr) (s.raw_complete dom disjoint root), ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | h
  · exact ⟨Variant.safe_identity _ _, fun _ => Substitution.apply_identity _⟩
  · obtain rfl := List.mem_singleton.mp h
    apply SpecializedFresh.safe_idempotent vs s.solution π _ avoid inventory fresh _
    intro t ht w hw
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp ht
    obtain ⟨n, hn, rfl⟩ := (Term.occurs_rename raw π.forward w).mp hw
    obtain ⟨part, hp, rfl⟩ := List.mem_map.mp hraw
    cases part with
    | none => exact False.elim (s.ground n hn)
    | some observer =>
      obtain ⟨v, hv, hi⟩ := s.solution.occurs_in_image observer n hn
      have seen : Observed (q.map s.input) v := ⟨_, List.mem_map.mpr ⟨some observer, hp, rfl⟩, hv⟩
      exact Or.inr (fun he => fresh v ((inventory v).mpr seen) n hi (List.mem_append_right _ he))

end Plan
end Tamarin.Rewriting.GroundNarrowing
