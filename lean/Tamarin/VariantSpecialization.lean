import Tamarin.VariantJoinFamily
import Tamarin.StableVariants

namespace Tamarin.Rewriting.VariantJoin
variable {s : Signature} {I K A : Type}

/-- The left row observes the caller variables and uses the actual operands
as its join keys. The right row comes from the generic operation family. -/
def operands (arg : I → Term s) (caller : K → Variable) : Row s I K :=
  ⟨arg, fun k => .var (caller k)⟩

def specialize (caller : K → Variable) (r : Row s I A) (μ : Substitution s) : Row s K A :=
  ⟨fun k => μ.image (caller k), fun a => μ.apply (r.value a)⟩

/-- Dropping the intermediate operand images loses no information. Their
variables are still tracked, together, in the projected caller images. -/
theorem specialize_denotes {R : Root s} (arg : I → Term s) (caller : K → Variable)
    (scope : ∀ i v, (arg i).Occurs v → ∃ k, caller k = v) (r : Row s I A)
    (μ ρ : Substitution s) (y : A → Term s) :
    Denotes R (join (operands arg caller) r μ) (fun i => ρ.apply (arg i))
      (Sum.elim (fun k => ρ.image (caller k)) y) ↔
    Denotes R (specialize caller r μ) (fun k => ρ.image (caller k)) y := by
  constructor
  · rintro ⟨δ,hn,h⟩
    exact ⟨δ,hn,fun k => h.values (.inl k),fun a => h.values (.inr a)⟩
  · rintro ⟨δ,hn,h⟩
    refine ⟨δ,hn,?_,?_⟩
    · intro i
      change EquivB _ (δ.apply (μ.apply (arg i)))
      rw [← Substitution.apply_compose]
      apply Term.subst_equiv
      intro v occ
      obtain ⟨k,rfl⟩ := scope i v occ
      exact h.inputs k
    · intro key; cases key with
      | inl k => exact h.inputs k
      | inr a => exact h.values a

/-- Specialize a complete family by a sorted operand substitution. Operands
must stay normal under normalized caller assignments; otherwise narrowing
within an operand can contribute extra answers. Every opened schema row is
unified with the full operand vector and every normal joint result retained. -/
theorem Exact.specialize {rules : List (Equation s)} (formal : I → Variable)
    (op : A → Term s) (rows : List (Row s I A)) (family : Exact (ruleRoot rules) formal op rows)
    (β : Substitution s) (stable : ∀ v, StableVariants.Stable (ruleRoot rules) (β.image v))
    (caller : K → Variable) (scope : ∀ i v, (β.image (formal i)).Occurs v → ∃ k, caller k = v)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (keys : List I) (allKeys : ∀ i, i ∈ keys) (anchors : Row s I A → List (Term s))
    (sols : Row s I A → List (Substitution s))
    (out : List (Row s K A))
    (apart : let left := operands (fun i => β.image (formal i)) caller
     ∀ r ∈ rows, ∀ v, left.Uses v → ¬ r.Uses v)
    (tracked : let left := operands (fun i => β.image (formal i)) caller
     ∀ r ∈ rows, ∀ v, left.Uses v ∨ r.Uses v → (problem left r keys (anchors r)).Occurs v)
    (solved : ∀ r ∈ rows, CompleteSet (problem (operands (fun i => β.image (formal i)) caller)
      r keys (anchors r)) (sols r))
    (members : ∀ q, q ∈ out ↔ ∃ r ∈ rows, ∃ μ ∈ sols r,
      (join (operands (fun i => β.image (formal i)) caller) r μ).IsNormal (ruleRoot rules) ∧
      q = VariantJoin.specialize caller r μ) :
    Exact (ruleRoot rules) caller (fun a => β.apply (op a)) out := by
  intro ρ hn y ny
  let arg := fun i => β.image (formal i)
  let left := operands arg caller
  have onLeft : Denotes (ruleRoot rules) left (fun i => ρ.apply (arg i)) (fun k => ρ.image (caller k)) :=
    ⟨ρ,hn,fun _ => .refl _,fun _ => .refl _⟩
  have forms := family (ρ.compose β) (fun v => stable v ρ hn) y ny
  simp only [Substitution.apply_compose] at forms
  rw [forms]
  have both r hr := exact_join vars left r (apart r hr) keys allKeys (anchors r)
    (tracked r hr) (sols r) (solved r hr) (fun i => ρ.apply (arg i)) (fun k => ρ.image (caller k)) y
    (fun i => stable (formal i) ρ hn) (fun k => hn (caller k)) ny
  constructor
  · rintro ⟨r,hr,h⟩
    obtain ⟨μ,hm,n,hit⟩ := (both r hr).mp ⟨onLeft,h⟩
    exact ⟨_,(members _).mpr ⟨r,hr,μ,hm,n,rfl⟩,(specialize_denotes arg caller scope r μ ρ y).mp hit⟩
  · rintro ⟨q,hq,hit⟩
    obtain ⟨r,hr,μ,hm,n,rfl⟩ := (members _).mp hq
    exact ⟨r,hr,((both r hr).mpr ⟨μ,hm,n,(specialize_denotes arg caller scope r μ ρ y).mpr hit⟩).2⟩

/-- The specialized substitution-only answer can use the same uniqueness
hypothesis as the generic operation when reconstructing packed values. -/
theorem specialize_unique {R : Root s} {op : A → Term s}
    (unique : ∀ ρ : Substitution s, Normalized R ρ → ∀ a u v,
      NormalForm R (ρ.apply (op a)) u → NormalForm R (ρ.apply (op a)) v → EquivB u v)
    (β : Substitution s) (stable : ∀ v, StableVariants.Stable R (β.image v))
    (ρ : Substitution s) (hn : Normalized R ρ) (a : A) (u v : Term s) :
    NormalForm R (ρ.apply (β.apply (op a))) u →
      NormalForm R (ρ.apply (β.apply (op a))) v → EquivB u v := by
  simpa only [Substitution.apply_compose] using
    unique (ρ.compose β) (fun w => stable w ρ hn) a u v

end Tamarin.Rewriting.VariantJoin
