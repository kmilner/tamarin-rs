import Tamarin.RuleAtHead
import Tamarin.RootNormalForms
import Tamarin.RulePattern
import Tamarin.SortCheck

/-! Specializing free rules with a fixed ground result to constructor arguments
of an open query. All matching and conclusions are relative to the full table. -/
namespace Tamarin.Rewriting.SpecializedRule
variable {sig : Signature} {R : Root sig} {d : sig.FreeSym}

def AtHead (R : Root sig) (d : sig.FreeSym) (p : Fin (sig.arity d) → Term sig) (rhs : Term sig) :=
  ∀ ys b, R (.free d ys) b ↔ ∃ σ : Substitution sig, (∀ i, ys i = σ.apply (p i)) ∧ b = rhs

def Matches {d : sig.FreeSym} (arg p : Fin (sig.arity d) → Term sig)
    (ρ μ : Substitution sig) := ∀ i, EquivB (ρ.apply (arg i)) (μ.apply (p i))

theorem apply_ground {t : Term sig} (ground : ∀ v, ¬ t.Occurs v) (σ : Substitution sig) :
    σ.apply t = t :=
  (Term.subst_eq_of_agree σ.image Term.var t (fun v hv => False.elim (ground v hv))).trans t.subst_id

theorem ground_at_head (rules : List (Equation sig)) (d : sig.FreeSym)
    (p : Fin (sig.arity d) → Term sig) (rhs : Term sig)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free d → r = ⟨.free d p, rhs⟩)
    (ground : ∀ v, ¬ rhs.Occurs v) : AtHead (ruleRoot rules) d p rhs := by
  intro ys b
  simpa only [apply_ground ground] using ruleRoot_unique_free_iff rules d p rhs apps present only ys b

theorem ground_at_head_fresh (rules : List (Equation sig)) (d : sig.FreeSym)
    (p : Fin (sig.arity d) → Term sig) (rhs : Term sig) (π : VariablePermutation)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (only : ∀ r ∈ rules, ConstructorVariants.head r.lhs = .free d → r = ⟨.free d p, rhs⟩)
    (ground : ∀ v, ¬ rhs.Occurs v) :
    AtHead (ruleRoot rules) d (fun i => (π.subst sig).apply (p i)) rhs := by
  intro ys b
  simpa only [apply_ground ground] using ruleRoot_fresh_free rules d p rhs π apps present only ys b

variable {arg p : Fin (sig.arity d) → Term sig} {result : Term sig} {ρ μ : Substitution sig}

/-- One exposed query variable opposite an application pattern suffices to
keep the open application normal before any instantiation. -/
theorem openMiss (i : Fin (sig.arity d)) (x : Variable) (hx : arg i = .var x)
    (rigid : ConstructorVariants.Application (p i)) :
    ¬ ∃ μ, Matches arg p Substitution.identity μ := by
  rintro ⟨μ, hm⟩
  have he := (hm i).head_eq
  rw [Substitution.apply_identity, hx] at he
  cases h : p i <;> simp_all [ConstructorVariants.Application, Substitution.apply,
    Term.subst, Model.eval, headModel]

theorem fires (atHead : AtHead R d p result) (hit : Matches arg p ρ μ) :
    StepModulo R (ρ.apply (.free d arg)) result :=
  ⟨_, _, .free _ _ _ hit, .root ((atHead _ _).mpr ⟨μ, fun _ => rfl, rfl⟩), .refl _⟩

theorem noMatch (atHead : AtHead R d p result) (hn : ∀ i, Normal R (ρ.apply (arg i)))
    (miss : ¬ ∃ μ, Matches arg p ρ μ) : Normal R (ρ.apply (.free d arg)) := by
  apply normal_free_no_root hn
  intro ys he b hr
  obtain ⟨μ, hμ, _⟩ := (atHead _ _).mp hr
  exact miss ⟨μ, fun i => hμ i ▸ he i⟩

theorem normal_iff (atHead : AtHead R d p result) (hn : ∀ i, Normal R (ρ.apply (arg i))) :
    Normal R (ρ.apply (.free d arg)) ↔ ¬ ∃ μ, Matches arg p ρ μ :=
  ⟨fun h ⟨_, hm⟩ => h result (fires atHead hm), noMatch atHead hn⟩

theorem matchedNormalForm (atHead : AtHead R d p result) (hit : Matches arg p ρ μ)
    (hn : Normal R result) (hs : HasSort result (sig.outputSort d)) :
    NormalForm R (ρ.apply (.free d arg)) result :=
  ⟨.step (fires atHead hit), hn, fun _ hi => .widen hs (Term.rootSort_le hi)⟩

theorem uniqueEq (atHead : AtHead R d p result) (hit : Matches arg p ρ μ)
    (hna : ∀ i, Normal R (ρ.apply (arg i))) (hn : Normal R result) {u : Term sig}
    (nf : NormalForm R (ρ.apply (.free d arg)) u) : EquivB u result := by
  apply normalForm_free_root_unique hna hn (fires atHead hit) _ nf
  intro ys _ b hb
  obtain ⟨_, _, rfl⟩ := (atHead _ _).mp hb
  exact .refl _

end Tamarin.Rewriting.SpecializedRule
