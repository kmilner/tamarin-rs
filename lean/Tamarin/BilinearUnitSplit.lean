import Tamarin.BilinearRoots
import Tamarin.VariantJoin

/-! A complete scalar-product family may expose its output as a bare witness.
When that witness specializes to the group unit, the outer point action or
power disappears. Specialize every input image with the same binding before
checking normality. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer
variable {sig : Signature} {s : Symbols sig}

/-- Only a bare message witness can acquire the nullary unit head. -/
theorem unit_instance_cases {t : Term sig} (δ : Substitution sig)
    (h : EquivB (δ.apply t) s.product.one) :
    t = s.product.one ∨ ∃ v, t = .var v ∧ v.sort = .msg ∧ δ.image v = s.product.one := by
  have eq : δ.apply t = s.product.one := nullary s.oneArity h.head_eq
  cases t with
  | var v =>
    change δ.image v = s.product.one at eq
    have sorted := δ.sorted v
    rw [eq] at sorted
    have sub := Term.rootSort_le sorted
    change Subsort (sig.outputSort s.one) v.sort at sub
    rw [s.oneSort] at sub
    have msg {a : SortId} (hs : Subsort .msg a) : a = .msg := by cases hs; rfl
    exact Or.inr ⟨v,rfl,msg sub,eq⟩
  | free f xs => exact Or.inl (nullary s.oneArity (by exact h.head_eq))
  | atom a => cases eq
  | ac f a b => cases eq
  | comm f a b => cases eq

/-- The witnessed unit branch changes no concrete column. Raw images, output
and all correlations factor through the same sorted simultaneous binding. -/
theorem unit_binding_factor (δ : Substitution sig) {v : Variable}
    (unit : δ.image v = s.product.one) (t : Term sig) :
    let κ := Substitution.binding v s.product.one (unit ▸ δ.sorted v)
    δ.apply (κ.apply t) = δ.apply t := by
  dsimp only
  rw [← Substitution.apply_compose]
  apply Term.subst_eq_of_agree
  intro w _
  change δ.apply ((Substitution.binding v s.product.one _).image w) = δ.image w
  by_cases same : w = v
  · subst w
    rw [Substitution.binding_image_self,unit]
    exact congrArg (Term.free s.one) (funext fun i => Fin.elim0 (s.oneArity ▸ i))
  · rw [Substitution.binding_image_other _ _ _ _ same]
    rfl

/-- Normal, nonunit scalar inputs are never lost by rejecting a reducible or
unit image after the output witness is set to one. This holds for any number
of columns under any additional rules. -/
theorem unit_binding_inputs {I : Type} {rules : List (Equation sig)} (δ : Substitution sig)
    {v : Variable} (unit : δ.image v = s.product.one) (columns : I → Term sig)
    (normal : ∀ i, Normal (ruleRoot rules) (δ.apply (columns i)))
    (nonunit : ∀ i, δ.apply (columns i) ≠ s.product.one) :
    let κ := Substitution.binding v s.product.one (unit ▸ δ.sorted v)
    ∀ i, Normal (ruleRoot rules) (κ.apply (columns i)) ∧ κ.apply (columns i) ≠ s.product.one := by
  intro κ i
  have same := unit_binding_factor δ unit (columns i)
  change δ.apply (κ.apply (columns i)) = δ.apply (columns i) at same
  refine ⟨VariantJoin.normal_of_instance (same ▸ normal i), ?_⟩
  intro h
  apply nonunit i
  rw [← same,h]
  exact congrArg (Term.free s.one) (funext fun j => Fin.elim0 (s.oneArity ▸ j))

open VariantJoin
variable {I : Type} {rules : List (Equation sig)}

private theorem one_fixed (s : Symbols sig) (δ : Substitution sig) :
    δ.apply s.product.one = s.product.one :=
  congrArg (Term.free s.one) (funext fun j => Fin.elim0 (s.oneArity ▸ j))

/-- The only extra scalar row carries the same specialization throughout
the input columns. Its output is folded to the unit. -/
def unitRow (s : Symbols sig) (r : Row sig I Unit) (v : Variable)
    (typed : HasSort s.product.one v.sort) : Row sig I Unit where
  input i := (Substitution.binding v s.product.one typed).apply (r.input i)
  value _ := s.product.one

/-- Candidate rows before subsumption. The boolean records whether to strip
the outer point operator or exponent. Concrete scalar inputs are nonunits. -/
inductive UnitCase (s : Symbols sig) (rules : List (Equation sig)) (r : Row sig I Unit) :
    Bool → Row sig I Unit → Prop where
  | literal (h : r.value () = s.product.one) : UnitCase s rules r true r
  | ordinary (h : r.value () ≠ s.product.one) : UnitCase s rules r false r
  | specialize (v : Variable) (hs : v.sort = .msg) (h : r.value () = .var v)
      (typed : HasSort s.product.one v.sort)
      (clean : ∀ i, Normal (ruleRoot rules) ((unitRow s r v typed).input i) ∧
          (unitRow s r v typed).input i ≠ s.product.one) :
      UnitCase s rules r true (unitRow s r v typed)

/-- Every fitted row for a concrete scalar product with normal nonunit
operands survives the input checks and has a candidate with the correct
output fold, using exactly its original specialization. -/
theorem unit_cases_cover (r : Row sig I Unit) {x : I → Term sig} {m : Term sig} {δ : Substitution sig}
    (fit : Fits r x (fun _ => m) δ) (normal : ∀ i, Normal (ruleRoot rules) (x i))
    (nonunit : ∀ i, x i ≠ s.product.one) :
    (∀ i, r.input i ≠ s.product.one) ∧
    ∃ k q, UnitCase s rules r k q ∧ Fits q x (fun _ => m) δ ∧ (k = true ↔ m = s.product.one) := by
  have n i := (normal_equiv _ (fit.inputs i)).mp (normal i)
  have nu i : δ.apply (r.input i) ≠ s.product.one := by
    intro h
    have eq := fit.inputs i
    rw [h] at eq
    exact nonunit i (nullary s.oneArity eq.head_eq)
  refine ⟨fun i h => nu i (h ▸ one_fixed s δ),?_⟩
  by_cases h : m = s.product.one
  · subst m
    rcases unit_instance_cases δ (fit.values ()).symm with raw|⟨v,raw,sort,unit⟩
    · exact ⟨true,r,.literal raw,fit,by simp⟩
    · let typed : HasSort s.product.one v.sort := unit ▸ δ.sorted v
      have checks := unit_binding_inputs δ unit r.input n nu
      refine ⟨true,unitRow s r v typed,.specialize v sort raw typed checks,⟨?_,?_⟩,by simp⟩
      · intro i
        change EquivB (x i) (δ.apply ((Substitution.binding v s.product.one typed).apply (r.input i)))
        rw [unit_binding_factor δ unit]
        exact fit.inputs i
      · intro z
        change EquivB s.product.one (δ.apply s.product.one)
        rw [one_fixed]; exact .refl _
  · have apart : r.value () ≠ s.product.one := by
      intro raw
      have e := fit.values ()
      rw [raw,one_fixed] at e
      exact h (nullary s.oneArity e.head_eq)
    exact ⟨false,r,.ordinary apart,fit,by simp [h]⟩

/-- Specializing a scalar candidate preserves the original scalar reduction
and the same input/output correlations. The folded case substitutes in the
actual positive reduction rather than introducing a new scalar endpoint. -/
theorem UnitCase.instance {r q : Row sig I Unit} {k : Bool} (h : UnitCase s rules r k q) :
    ∃ κ : Substitution sig, (∀ i, q.input i = κ.apply (r.input i)) ∧
      (∀ a, q.value a = κ.apply (r.value a)) ∧ (k = true ↔ q.value () = s.product.one) := by
  cases h with
  | literal e => exact ⟨.identity,by simp,by simp,by simp [e]⟩
  | ordinary e => exact ⟨.identity,by simp,by simp,by simp [e]⟩
  | specialize v _ raw typed _ =>
    refine ⟨.binding v _ typed,fun _ => rfl,?_,by simp [unitRow]⟩
    intro a
    cases a
    change s.product.one = (Substitution.binding v s.product.one typed).apply (r.value ())
    rw [raw]; exact (Substitution.binding_image_self ..).symm

end Tamarin.Rewriting.Bilinear
