import Tamarin.RulePattern
import Tamarin.SpecializedFresh
import Tamarin.VariablePermutation

/-! Simultaneous variants via ordinary unification modulo B. Open the two
local answers in disjoint scopes, equate their images of the caller variables,
and keep only joint rows whose images and output values are already normal.
This also applies when two observations share both a base and an exponent. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {I A B : Type}

structure Row (sig : Signature) (I A : Type) where
  input : I → Term sig
  value : A → Term sig

def Row.Uses (q : Row sig I A) (v : Variable) : Prop :=
  (∃ i, (q.input i).Occurs v) ∨ ∃ a, (q.value a).Occurs v

def Row.IsNormal (q : Row sig I A) (R : Root sig) : Prop :=
  (∀ i, Normal R (q.input i)) ∧ ∀ a, Normal R (q.value a)

/-- One and the same specialization explains every domain image and value. -/
structure Fits (q : Row sig I A) (x : I → Term sig) (y : A → Term sig)
    (δ : Substitution sig) : Prop where
  inputs : ∀ i, EquivB (x i) (δ.apply (q.input i))
  values : ∀ a, EquivB (y a) (δ.apply (q.value a))

def Denotes (R : Root sig) (q : Row sig I A) (x : I → Term sig) (y : A → Term sig) : Prop :=
  ∃ δ, Normalized R δ ∧ Fits q x y δ

def join (q : Row sig I A) (r : Row sig I B) (μ : Substitution sig) : Row sig I (Sum A B) where
  input i := μ.apply (q.input i)
  value := Sum.elim (fun i => μ.apply (q.value i)) (fun j => μ.apply (r.value j))

noncomputable def choose (p : Variable → Prop) (left right : Substitution sig) :
    Substitution sig := by
  classical
  exact {
    image := fun v => if p v then left.image v else right.image v
    support := left.support ++ right.support
    outside := fun v h => by
      simp only [List.mem_append,not_or] at h
      split <;> first | exact left.outside _ h.1 | exact right.outside _ h.2
    sorted := fun v => by split <;> first | exact left.sorted _ | exact right.sorted _
  }

theorem choose_apply (p : Variable → Prop) (left right : Substitution sig) (t : Term sig) :
    ((∀ v, t.Occurs v → p v) → (choose p left right).apply t = left.apply t) ∧
    ((∀ v, t.Occurs v → ¬p v) → (choose p left right).apply t = right.apply t) := by
  constructor <;> intro h <;> apply Term.subst_eq_of_agree <;> intro v hv <;> simp [choose,h v hv]

/-- A candidate that already has a redex cannot acquire a normal instance. -/
theorem normal_of_instance {rules : List (Equation sig)} {σ : Substitution sig} {t : Term sig}
    (h : Normal (ruleRoot rules) (σ.apply t)) : Normal (ruleRoot rules) t :=
  fun _ st => h _ (SpecializedFresh.stepModulo_subst rules σ st)

/-- Restrict a specialization to just the variables in the answer. Its values
there are normal subterms of normal instances. Unused images may be discarded. -/
theorem normal_witness {rules : List (Equation sig)} (vars : Normalized (ruleRoot rules) Substitution.identity)
    {q : Row sig I A} {x y} {δ : Substitution sig} (nx : ∀ i, Normal (ruleRoot rules) (x i))
    (ny : ∀ a, Normal (ruleRoot rules) (y a)) (hit : Fits q x y δ) :
    q.IsNormal (ruleRoot rules) ∧ Denotes (ruleRoot rules) q x y := by
  classical
  let normI := fun i => (normal_equiv _ (hit.inputs i)).mp (nx i)
  let normV := fun a => (normal_equiv _ (hit.values a)).mp (ny a)
  refine ⟨⟨fun i => normal_of_instance (normI i),fun a => normal_of_instance (normV a)⟩,?_⟩
  refine ⟨choose q.Uses δ Substitution.identity,?_,?_⟩
  · intro v
    change Normal _ (if q.Uses v then _ else _)
    split
    · next hv =>
      rcases hv with ⟨i,hi⟩|⟨a,ha⟩
      · exact RulePattern.image_normal (normI i) hi
      · exact RulePattern.image_normal (normV a) ha
    · exact vars v
  · constructor
    · intro i; rw [(choose_apply q.Uses δ Substitution.identity (q.input i)).1 (fun _ h => Or.inl ⟨i,h⟩)]; exact hit.inputs i
    · intro a; rw [(choose_apply q.Uses δ Substitution.identity (q.value a)).1 (fun _ h => Or.inr ⟨a,h⟩)]; exact hit.values a

/-- Unify shared input images. Reflexive equations for output terms make the
CSU's factorization cover even variables occurring only in returned values.
A solver with a wider observable domain can omit the reflexive equations. -/
def problem (q : Row sig I A) (r : Row sig I B) (keys : List I) (vs : List (Term sig)) : Problem sig :=
  keys.map (fun i => ⟨q.input i,r.input i⟩) ++ vs.map (fun t => ⟨t,t⟩)

/-- The normal joint rows denote exactly the intersection of the locally
admissible input assignments, with all output correlations preserved. -/
theorem exact_join {rules : List (Equation sig)} (vars : Normalized (ruleRoot rules) Substitution.identity)
    (q : Row sig I A) (r : Row sig I B) (apart : ∀ v, q.Uses v → ¬r.Uses v)
    (keys : List I) (allKeys : ∀ i, i ∈ keys) (anchors : List (Term sig))
    (tracked : ∀ v, q.Uses v ∨ r.Uses v → (problem q r keys anchors).Occurs v)
    (answers : List (Substitution sig)) (csu : CompleteSet (problem q r keys anchors) answers)
    (x : I → Term sig) (y : A → Term sig) (z : B → Term sig)
    (nx : ∀ i, Normal (ruleRoot rules) (x i))
    (ny : ∀ a, Normal (ruleRoot rules) (y a)) (nz : ∀ b, Normal (ruleRoot rules) (z b)) :
    Denotes (ruleRoot rules) q x y ∧ Denotes (ruleRoot rules) r x z ↔
      ∃ μ ∈ answers, (join q r μ).IsNormal (ruleRoot rules) ∧
        Denotes (ruleRoot rules) (join q r μ) x (Sum.elim y z) := by
  constructor
  · rintro ⟨⟨δ,_,lhs⟩,⟨ε,_,rhs⟩⟩
    let σ := choose q.Uses δ ε
    have left {t : Term sig} (used : ∀ v, t.Occurs v → q.Uses v) : σ.apply t = δ.apply t :=
      (choose_apply _ _ _ _).1 used
    have right {t : Term sig} (used : ∀ v, t.Occurs v → r.Uses v) : σ.apply t = ε.apply t :=
      (choose_apply _ _ _ _).2 (fun v hv hq => apart v hq (used v hv))
    have sol : (problem q r keys anchors).Solves σ := by
      intro e he
      rcases List.mem_append.mp he with h|h
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
        change EquivB (σ.apply (q.input i)) (σ.apply (r.input i))
        rw [left (fun _ h => Or.inl ⟨i,h⟩),right (fun _ h => Or.inl ⟨i,h⟩)]
        exact (lhs.inputs i).symm.trans (rhs.inputs i)
      · obtain ⟨t,_,rfl⟩ := List.mem_map.mp h; exact .refl _
    obtain ⟨μ,mem,η,agree⟩ := csu.covers σ sol
    have factor {t : Term sig} (used : ∀ v, t.Occurs v → q.Uses v ∨ r.Uses v) :
        EquivB (σ.apply t) (η.apply (μ.apply t)) := by
      rw [← Substitution.apply_compose]
      exact t.subst_equiv _ _ fun v hv => agree v (tracked _ (used v hv))
    refine ⟨μ,mem,normal_witness (δ := η) vars nx (fun a => by cases a <;> first | apply ny | apply nz) ?_⟩
    constructor
    · intro i
      have occ : ∀ v, (q.input i).Occurs v → q.Uses v := fun _ h => .inl ⟨i,h⟩
      have e := factor (fun v h => Or.inl (occ v h)); rw [left occ] at e; exact (lhs.inputs i).trans e
    · intro a; cases a with
      | inl a =>
        have occ : ∀ v, (q.value a).Occurs v → q.Uses v := fun _ h => .inr ⟨a,h⟩
        have e := factor (fun v h => Or.inl (occ v h)); rw [left occ] at e; exact (lhs.values a).trans e
      | inr b =>
        have occ : ∀ v, (r.value b).Occurs v → r.Uses v := fun _ h => .inr ⟨b,h⟩
        have e := factor (fun v h => Or.inr (occ v h)); rw [right occ] at e; exact (rhs.values b).trans e
  · rintro ⟨μ,mem,_,δ,_,both⟩
    have shared (i : I) : EquivB (μ.apply (q.input i)) (μ.apply (r.input i)) :=
      csu.sound _ mem _ (List.mem_append_left _ (List.mem_map_of_mem (f := fun k => (⟨q.input k,r.input k⟩ : Equation sig)) (allKeys i)))
    have inputs (i) : EquivB (x i) ((δ.compose μ).apply (q.input i)) := by
      rw [Substitution.apply_compose]; exact both.inputs i
    constructor
    · apply (normal_witness vars nx ny (δ := δ.compose μ) _).2
      exact ⟨inputs,fun a => by rw [Substitution.apply_compose]; exact both.values (.inl a)⟩
    · apply (normal_witness vars nx nz (δ := δ.compose μ) _).2
      exact ⟨fun i => (inputs i).trans (by rw [Substitution.apply_compose,Substitution.apply_compose]; exact (shared i).subst δ.image),
        fun b => by rw [Substitution.apply_compose]; exact both.values (.inr b)⟩

end Tamarin.Rewriting.VariantJoin
