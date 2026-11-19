import Tamarin.RuleAtHead
import Tamarin.RootNormalForms
import Tamarin.SortCheck
import Tamarin.RulePattern
import Tamarin.VariablePermutation

/-! Narrowing one open defined application inside a packed query. The theorem
describes the answers by their values and denotation across the whole query.
Rule variables are local to a branch. They may repeat anywhere in its patterns. -/
namespace Tamarin.Rewriting.OpenNarrowing
variable {sig : Signature}

/-- The selected rule has already been freshened. The output variable must occur
in its left side. An application in a pattern ensures the open input itself
does not fire the rule. Substitution-only decoding uses free patterns for
unique reconstruction. A caller that carries the selected value can use a
broader pattern class. No global confluence or termination hypothesis is used. -/
structure Schema (sig : Signature) (patternClass : Term sig → Prop := RulePattern.Free) where
  d : sig.FreeSym
  p : Fin (sig.arity d) → Term sig
  z : Variable
  x : Fin (sig.arity d) → Variable
  distinct : Function.Injective x
  inputSort : ∀ i, Subsort (x i).sort (sig.inputSort d i)
  typed : ∀ i, HasSort (p i) (x i).sort
  resultSort : Subsort z.sort (sig.outputSort d)
  pattern_mem : ∀ i, patternClass (p i)
  rigid : ∃ i, ConstructorVariants.Application (p i)
  outputOccurs : ∃ i, (p i).Occurs z

namespace Schema
variable {P : Term sig → Prop} (s : Schema sig P)

abbrev Index := Fin (sig.arity s.d)
def input : Option s.Index → Term sig
  | none => .free s.d (fun i => .var (s.x i))
  | some i => .var (s.x i)

def value : Option s.Index → Term sig
  | none => .var s.z
  | some i => s.p i

noncomputable def split : Substitution sig := by
  classical
  exact {
    image := fun v => if h : ∃ i, s.x i = v then s.p h.choose else .var v
    support := List.ofFn s.x
    outside := by
      intro v h
      exact dite_eq_right (fun hex => h (List.mem_ofFn.mpr hex))
    sorted := by
      intro v
      split
      · next h => exact Eq.mp (congrArg (fun v : Variable => HasSort (s.p h.choose) v.sort) h.choose_spec) (s.typed _)
      · exact .var _ }

@[simp] theorem split_owned (i : s.Index) : s.split.image (s.x i) = s.p i := by
  classical
  have h : ∃ j, s.x j = s.x i := ⟨i, rfl⟩
  simp [split, h, s.distinct h.choose_spec]

theorem split_other (v : Variable) (h : ¬ ∃ i, s.x i = v) :
    s.split.image v = .var v := by classical simp [split, h]

def identityArm (q : List (Option s.Index)) : Variant sig :=
  ⟨Substitution.identity, q.map s.input⟩

noncomputable def ruleArm (q : List (Option s.Index)) : Variant sig :=
  ⟨s.split, q.map s.value⟩

theorem observed_iff (q : List (Option s.Index)) (hq : none ∈ q) (v : Variable) :
    Observed (q.map s.input) v ↔ ∃ i, s.x i = v := by
  constructor
  · rintro ⟨_, ht, hv⟩
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp ht
    cases o with
    | none => obtain ⟨i, he⟩ := hv; exact ⟨i, he.symm⟩
    | some i => exact ⟨i, hv.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨none, hq, rfl⟩, i, rfl⟩

def Local (v : Variable) := ∃ i, (s.p i).Occurs v

noncomputable def restrict (σ : Substitution sig) : Substitution sig := by
  classical
  exact {
    image := fun v => if s.Local v then σ.image v else .var v
    support := σ.support
    outside := by intro v h; simp [σ.outside v h]
    sorted := by intro v; split <;> first | exact σ.sorted v | exact .var v }

theorem restrict_pattern (σ : Substitution sig) (i : s.Index) :
    (s.restrict σ).apply (s.p i) = σ.apply (s.p i) := by
  apply Term.subst_eq_of_agree
  intro v hv
  simp [restrict, show s.Local v from ⟨i, hv⟩]

/-- This is a root rewrite condition. It quantifies over actual steps at d,
including absence of any additional rules at d in the admitted fragment. -/
def AtHead (R : Root sig) := ∀ ys b, R (.free s.d ys) b ↔
  ∃ σ : Substitution sig, (∀ i, ys i = σ.apply (s.p i)) ∧ b = σ.image s.z

def Matches (ρ σ : Substitution sig) := ∀ i, EquivB (ρ.image (s.x i)) (σ.apply (s.p i))

theorem noMatch {R : Root sig} (atHead : s.AtHead R) {ρ : Substitution sig}
    (hn : Normalized R ρ) (miss : ¬ ∃ σ, s.Matches ρ σ) :
    Normal R (ρ.apply (s.input none)) := by
  apply normal_free_no_root (fun i => hn (s.x i))
  intro ys he b hr
  obtain ⟨σ, hy, _⟩ := (atHead _ _).mp hr
  exact miss ⟨σ, fun i => hy i ▸ he i⟩

theorem openMiss : ¬ ∃ σ, s.Matches Substitution.identity σ := by
  rintro ⟨σ, hm⟩
  obtain ⟨i, hi⟩ := s.rigid
  have e := (hm i).head_eq
  change Head.var (s.x i) = ConstructorVariants.head (σ.apply (s.p i)) at e
  cases h : s.p i <;> simp_all [ConstructorVariants.Application, ConstructorVariants.head,
    Substitution.apply, Term.subst, Model.eval, headModel]

private theorem matched (s : Schema sig) {R : Root sig} (atHead : s.AtHead R) {ρ σ : Substitution sig}
    (hn : Normalized R ρ) (hm : s.Matches ρ σ) {u}
    (nf : NormalForm R (ρ.apply (s.input none)) u) : EquivB u (σ.image s.z) := by
  obtain ⟨j, hj⟩ := s.outputOccurs
  have zn := RulePattern.image_normal ((normal_equiv _ (hm j)).mp (hn (s.x j))) hj
  have fires : StepModulo R (ρ.apply (s.input none)) (σ.image s.z) :=
    ⟨_, _, .free _ _ _ hm, .root ((atHead _ _).mpr ⟨σ, fun _ => rfl, rfl⟩), .refl _⟩
  apply normalForm_free_root_unique (fun i => hn (s.x i)) zn fires _ nf
  intro ys he b hb
  obtain ⟨τ, hy, rfl⟩ := (atHead _ _).mp hb
  exact RulePattern.image_equiv (s.pattern_mem j) (((hy j ▸ he j).symm).trans (hm j)) hj

/-- Repeated observations of a projection can select one local value under
any normalized caller assignment. Unrelated rules need no confluence proof. -/
theorem unique (s : Schema sig) {R : Root sig} (atHead : s.AtHead R)
    (ρ : Substitution sig) (hn : Normalized R ρ) {u v}
    (hu : NormalForm R (ρ.apply (s.input none)) u)
    (hv : NormalForm R (ρ.apply (s.input none)) v) : EquivB u v := by
  by_cases hit : ∃ μ, s.Matches ρ μ
  · obtain ⟨μ,hm⟩ := hit
    exact (s.matched atHead hn hm hu).trans (s.matched atHead hn hm hv).symm
  · have normal := s.noMatch atHead hn hit
    exact (normal_reduces_equiv hu.1 normal).symm.trans (normal_reduces_equiv hv.1 normal)

theorem arms_sound {R : Root sig} (atHead : s.AtHead R) (vars : Normalized R Substitution.identity)
    (patterns : ∀ i, Normal R (s.p i)) (q : List (Option s.Index)) :
    ∀ a ∈ [s.identityArm q, s.ruleArm q], a.Sound R (q.map s.input) := by
  classical
  have ns : Normalized R s.split := by
    intro v
    by_cases hx : ∃ i, s.x i = v
    · obtain ⟨i, rfl⟩ := hx; simpa using patterns i
    · rw [s.split_other _ hx]; exact vars v
  have openNormal := s.noMatch atHead vars s.openMiss
  intro ans ha
  rcases List.mem_cons.mp ha with rfl | ha
  · refine ⟨vars, aligned_maps q s.input s.input ?_⟩
    intro a _
    change NormalForm R (Substitution.identity.apply _) _
    rw [Substitution.apply_identity]
    refine ⟨.basis (.refl _), ?_, fun _ h => h⟩
    cases a with
    | none => simpa using openNormal
    | some i => exact vars (s.x i)
  · obtain rfl := List.mem_singleton.mp ha
    refine ⟨ns, aligned_maps q s.input s.value ?_⟩
    intro a _
    cases a with
    | some i =>
      change NormalForm R (s.split.image (s.x i)) (s.p i)
      rw [s.split_owned]; exact ⟨.basis (.refl _), patterns i, fun _ h => h⟩
    | none =>
      have hr : R (.free s.d fun i => s.split.image (s.x i)) (.var s.z) :=
        (atHead _ _).mpr ⟨Substitution.identity, fun i => (s.split_owned i).trans
          (Substitution.apply_identity _).symm, rfl⟩
      refine ⟨.step ⟨_, _, .refl _, .root hr, .refl _⟩, vars s.z, ?_⟩
      exact fun _ hs => .widen (.var _) (s.resultSort.trans (Term.rootSort_le hs))

/-- Independently checkable derivation of the two branches. Covers every
normalized substitution, with one common instantiation for all components. -/
theorem complete (s : Schema sig) {R : Root sig} (atHead : s.AtHead R) (vars : Normalized R Substitution.identity)
    (patterns : ∀ i, Normal R (s.p i)) (q : List (Option s.Index)) (hq : none ∈ q) :
    CompleteVariants R (q.map s.input) [s.identityArm q, s.ruleArm q] := by
  classical
  constructor
  · exact s.arms_sound atHead vars patterns q
  · intro ρ hn values hv
    by_cases hm : ∃ σ, s.Matches ρ σ
    · obtain ⟨σ, hm⟩ := hm
      let δ := s.restrict σ
      have hδ : Normalized R δ := by
        intro v
        by_cases hl : s.Local v
        · obtain ⟨j, hj⟩ := hl
          simpa [δ, restrict, show s.Local v from ⟨j, hj⟩] using
            RulePattern.image_normal ((normal_equiv _ (hm j)).mp (hn (s.x j))) hj
        · change Normal R (if s.Local v then σ.image v else .var v)
          rw [ite_eq_right hl]; exact vars v
      refine ⟨s.ruleArm q, by simp, δ, hδ, ?_, aligned_values q s.input s.value values hv ?_⟩
      · intro v h
        obtain ⟨i, rfl⟩ := (s.observed_iff q hq v).mp h
        change EquivB _ (δ.apply (s.split.image (s.x i)))
        rw [s.split_owned, s.restrict_pattern]; exact hm i
      · intro a _ u nf
        cases a with
        | none =>
          simpa [δ, value, Substitution.apply, Term.subst, restrict, show s.Local s.z from s.outputOccurs]
            using s.matched atHead hn hm nf
        | some i =>
          change EquivB u (δ.apply (s.p i))
          rw [s.restrict_pattern]
          exact (normal_reduces_equiv nf.1 (hn (s.x i))).symm.trans (hm i)
    · refine ⟨s.identityArm q, by simp, ρ, hn, fun _ _ => .refl _,
        aligned_values q s.input s.input values hv ?_⟩
      intro a _ u nf
      apply (normal_reduces_equiv nf.1 _).symm
      cases a with
      | some i => exact hn (s.x i)
      | none => exact s.noMatch atHead hn hm

theorem safe (q : List (Option s.Index)) (hq : none ∈ q) (avoid : List Variable)
    (fresh : ∀ v, s.Local v → v ∉ avoid ∧ ¬ ∃ i, s.x i = v) :
    ∀ ans ∈ [s.identityArm q, s.ruleArm q], ans.Safe (q.map s.input) avoid ∧
      ∀ v, ans.subst.apply (ans.subst.image v) = ans.subst.image v := by
  intro ans ha
  rcases List.mem_cons.mp ha with rfl | h
  · exact ⟨Variant.safe_identity _ _, fun v => Substitution.apply_identity _⟩
  · obtain rfl := List.mem_singleton.mp h
    refine ⟨⟨fun v hv => s.split_other _ (fun h => hv ((s.observed_iff q hq v).mpr h)), ?_, ?_⟩, ?_⟩
    · intro v hv w hw
      obtain ⟨i, rfl⟩ := (s.observed_iff q hq v).mp hv
      change (s.split.image (s.x i)).Occurs w at hw
      rw [s.split_owned] at hw
      exact Or.inr (fresh _ ⟨i, hw⟩).1
    · intro t ht w hw
      obtain ⟨part, _, rfl⟩ := List.mem_map.mp ht
      apply Or.inr (fresh w ?_).1
      cases part with
      | none => exact hw ▸ s.outputOccurs
      | some i => exact ⟨i, hw⟩
    · intro v
      change s.split.apply (s.split.image v) = s.split.image v
      by_cases h : ∃ i, s.x i = v
      · obtain ⟨i, rfl⟩ := h
        rw [s.split_owned]
        exact (Term.subst_eq_of_agree _ Term.var _ fun w hw => s.split_other w (fresh _ ⟨i, hw⟩).2).trans (Term.subst_id _)
      · rw [s.split_other _ h]; exact s.split_other _ h

/-- A search candidate may return any answer set satisfying this contract.
The order of branches and the choice of fresh names have no semantic meaning. -/
def Admissible (R : Root sig) (q : List (Option s.Index)) (avoid : List Variable)
    (answers : List (Variant sig)) : Prop :=
  CompleteVariants R (q.map s.input) answers ∧
  ∀ a ∈ answers, a.Safe (q.map s.input) avoid ∧
    ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

theorem admissible_reorder {R : Root sig} {q : List (Option s.Index)} {avoid : List Variable}
    {as bs : List (Variant sig)} (same : ∀ a, a ∈ as ↔ a ∈ bs) :
    s.Admissible R q avoid as ↔ s.Admissible R q avoid bs := by
  unfold Admissible CompleteVariants
  simp only [same]

/-- Meaning of the scalar reply on this input domain. Rust constructs the
second branch from the actual freshened rule patterns in argument order. -/
noncomputable def decode (q : List (Option s.Index)) (mask : UInt8) : Option (List (Variant sig)) :=
  if mask = 3 then some [s.identityArm q, s.ruleArm q] else none

theorem table_correct (s : Schema sig) (rules : List (Equation sig)) (original : s.Index → Term sig)
    (rhs : Variable) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free s.d original, .var rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free s.d →
      r = ⟨.free s.d original, .var rhs⟩)
    (patterns : ∀ i, s.p i = (π.subst sig).apply (original i)) (result : s.z = π.forward rhs)
    (constructors : ∀ i, ∀ f ∈ ConstructorVariants.operators (s.p i), f ∉ ConstructorVariants.ruleHeads rules)
    (q : List (Option s.Index)) (hq : none ∈ q) (avoid : List Variable)
    (fresh : ∀ v, s.Local v → v ∉ avoid ∧ ¬ ∃ i, s.x i = v) :
    s.Admissible (ruleRoot rules) q avoid [s.identityArm q, s.ruleArm q] := by
  obtain ⟨vars, safeConstructor⟩ := ConstructorVariants.constructor_normal rules apps
  have atHead : s.AtHead (ruleRoot rules) := by
    intro ys b
    simpa only [patterns, result] using ruleRoot_fresh_selected rules s.d original rhs π
      apps present only ys b
  exact ⟨s.complete atHead vars (fun i => by
    simpa using safeConstructor (s.p i) (constructors i) Substitution.identity vars) q hq,
    s.safe q hq avoid fresh⟩

end Schema
end Tamarin.Rewriting.OpenNarrowing
