import Tamarin.TotalFree
import Tamarin.InertProductVariants

namespace Tamarin.Rewriting.TotalFree
variable {s : Signature} {rules : List (Equation s)} {f : s.FreeSym}

/-- Contracting before or after a caller substitution uses the same variables
from the original children, including when they also occur elsewhere. -/
theorem contract_apply (rule : Rule rules f) (xs : Fin (s.arity f) → Term s) (ρ : Substitution s) :
    ρ.apply (contract rule xs) = contract rule (fun i => ρ.apply (xs i)) := by
  change (rule.rhs.subst (lookup rule.keys xs)).subst ρ.image = _
  rw [Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v hv
  obtain ⟨i,rfl⟩ := rule.bound _ hv
  simp only [lookup_key rule.distinct]
  rfl

theorem variant_forms (rule : Rule rules f) (xs : Fin (s.arity f) → Term s)
    (args : ∀ i, HasSort (xs i) (s.inputSort f i)) (value : Term s)
    (repr : EquivB (contract rule xs) value)
    (slot : VariantJoin.InertProduct.Admits (ruleRoot rules) (s.outputSort f) value)
    (ρ : Substitution s) (normalized : Normalized (ruleRoot rules) ρ) (u : Term s) :
    NormalForm (ruleRoot rules) (ρ.apply (.free f xs)) u ↔
      NormalForm (ruleRoot rules) (ρ.apply value) u := by
  let args' := fun i => ρ.apply (xs i)
  have typed i : HasSort (args' i) (s.inputSort f i) := (args i).subst ρ.image ρ.sorted
  have equal : EquivB (contract rule args') (ρ.apply value) := by
    rw [← contract_apply]; exact repr.subst ρ.image
  have out := slot.1.subst ρ.image ρ.sorted
  change NormalForm (ruleRoot rules) (.free f args') u ↔ _
  constructor
  · rintro ⟨red,n,hs⟩
    have well := hs _ (.free f args' typed)
    have path := (Reduces.basis equal.symm).trans ((terminal_iff rule args' typed n well).mp red)
    refine ⟨path,n,?_⟩
    rcases slot.2 ρ normalized with stable|principal
    · intro k h
      exact Term.checkSort_sound _ _ (SortClash.check_equiv (normal_reduces_equiv path stable) k ▸
        Term.checkSort_complete h)
    · exact fun _ h => .widen well (principal ▸ Term.rootSort_le h)
  · rintro ⟨red,n,hs⟩
    have well := hs _ out
    exact ⟨(terminal_iff rule args' typed n well).mpr ((Reduces.basis equal).trans red), n,
      fun _ h => .widen well (Term.rootSort_le h)⟩

/-- The caller's complete image vector is unchanged, even for a rule that
erases all occurrences of a caller key or duplicates another one. -/
theorem exact_variants {I : Type} (rule : Rule rules f) (xs : Fin (s.arity f) → Term s)
    (args : ∀ i, HasSort (xs i) (s.inputSort f i)) (value : Term s) (repr : EquivB (contract rule xs) value)
    (slot : VariantJoin.InertProduct.Admits (ruleRoot rules) (s.outputSort f) value)
    (ids : I → Variable) (rows : List (VariantJoin.Row s I Unit))
    (family : VariantJoin.Exact (ruleRoot rules) ids (fun _ => value) rows) :
    VariantJoin.Exact (ruleRoot rules) ids (fun _ => .free f xs) rows := by
  intro ρ hn y normal
  apply Iff.trans _ (family ρ hn y normal)
  exact forall_congr' (fun i => variant_forms rule xs args value repr slot ρ hn (y i))

/-- The identity bindings and a stably normal contractum form one complete
row, with every original caller variable still present. -/
theorem stable_row {I : Type} (rule : Rule rules f) (xs : Fin (s.arity f) → Term s)
    (args : ∀ i, HasSort (xs i) (s.inputSort f i)) (value : Term s) (repr : EquivB (contract rule xs) value)
    (typed : HasSort value (s.outputSort f)) (stable : StableVariants.Stable (ruleRoot rules) value)
    (ids : I → Variable) (covers : ∀ v, value.Occurs v → ∃ i, ids i = v) :
    VariantJoin.Exact (ruleRoot rules) ids (fun _ : Unit => .free f xs)
      [⟨fun i => .var (ids i),fun _ => value⟩] := by
  apply exact_variants rule xs args value repr (VariantJoin.InertProduct.admits_of_check _ _ _ typed (.inl stable))
  intro ρ hn y ny
  constructor
  · intro forms
    refine ⟨_,List.mem_singleton_self _,ρ,hn,⟨fun _ => .refl _,?_⟩⟩
    exact fun i => (normal_reduces_equiv (forms i).1 (stable ρ hn)).symm
  · rintro ⟨arm,ha,δ,_,fit⟩ i
    obtain rfl := List.mem_singleton.mp ha
    have agree := value.subst_equiv ρ.image δ.image (fun v hv => by
      obtain ⟨j,rfl⟩ := covers v hv
      exact fit.inputs j)
    have eq := agree.trans (fit.values i).symm
    exact ⟨.basis eq,ny i,fun k h => Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸
      Term.checkSort_complete h)⟩

end Tamarin.Rewriting.TotalFree
