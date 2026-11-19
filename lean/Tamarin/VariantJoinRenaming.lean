import Tamarin.VariantJoinFamily
import Tamarin.CallerFreshening

/-! Opening or canonicalizing a whole answer uses a single finite,
sort-preserving permutation. Rebuilding a term may reorder its AC operands.
Both operations preserve the correlations carried by a joined row. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {I A : Type} {R : Root sig}

/-- The same range renaming must apply to every input image and value.
Each rebuilt term may use any B-equivalent representation. -/
def Row.Relabels (l r : Row sig I A) : Prop :=
  ∃ π : VariablePermutation, (∀ i, EquivB ((π.subst sig).apply (l.input i)) (r.input i)) ∧
    ∀ a, EquivB ((π.subst sig).apply (l.value a)) (r.value a)

private def exchange (a b v : Variable) := if v = a then b else if v = b then a else v

private theorem exchange_twice (a b v : Variable) : exchange a b (exchange a b v) = v := by
  by_cases same : a = b
  · subst b; by_cases h : v = a <;> simp [exchange,h]
  · by_cases l : v = a
    · subst v; simp [exchange,Ne.symm same]
    · by_cases r : v = b
      · subst v; simp [exchange,Ne.symm same]
      · simp [exchange,l,r]

private def swapAfter (π : VariablePermutation) (a b : Variable) (same : a.sort = b.sort) : VariablePermutation where
  forward v := exchange a b (π.forward v)
  backward v := π.backward (exchange a b v)
  support := a :: b :: π.support
  outside := by
    intro v outside
    simp only [List.mem_cons,not_or] at outside
    simp [π.outside _ outside.2.2,exchange,outside.1,outside.2.1]
  left_inverse := by intro v; simp only [exchange_twice,π.left_inverse]
  right_inverse := by intro v; simp only [π.right_inverse,exchange_twice]
  sorted := by
    intro v
    apply Eq.trans _ (π.sorted v)
    unfold exchange
    split <;> rename_i h
    · rw [h]; exact same.symm
    · split <;> rename_i h
      · rw [h]; exact same
      · rfl

/-- A first-use allocation only assigns the names in a finite row. Every
such sorted injection extends to a finite permutation, including allocations
whose destinations overlap source names. -/
theorem extendAllocation (sources : List Variable) (f : Variable → Variable)
    (sorts : ∀ v ∈ sources, (f v).sort = v.sort)
    (inj : ∀ v ∈ sources, ∀ w ∈ sources, f v = f w → v = w) :
    ∃ π : VariablePermutation, ∀ v ∈ sources, π.forward v = f v := by
  induction sources with
  | nil =>
    exact ⟨⟨id,id,[],fun _ _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩,by simp⟩
  | cons x xs ih =>
    obtain ⟨π,fixes⟩ := ih (fun v hv => sorts v (List.mem_cons_of_mem _ hv))
      (fun v hv w hw => inj v (List.mem_cons_of_mem _ hv) w (List.mem_cons_of_mem _ hw))
    let q := swapAfter π (π.forward x) (f x) ((π.sorted x).trans (sorts x List.mem_cons_self).symm)
    refine ⟨q,?_⟩
    intro v mem
    by_cases e : v = x
    · subst v; simp [q,swapAfter,exchange]
    · have hx := (List.mem_cons.mp mem).resolve_left e
      have differ : π.forward v ≠ π.forward x := fun h => e
        ((π.left_inverse v).symm.trans ((congrArg π.backward h).trans (π.left_inverse x)))
      have noTarget : π.forward v ≠ f x := fun h => e (inj v mem x List.mem_cons_self ((fixes v hx).symm.trans h))
      change exchange _ _ _ = _
      simp only [exchange,ite_eq_right differ,ite_eq_right noTarget]
      exact fixes v hx

theorem Row.Relabels.of_allocation {l r : Row sig I A} (sources : List Variable)
    (alloc : CallerFreshening.Allocation sources) (covers : ∀ v, l.Uses v → v ∈ sources)
    (inputs : ∀ i, EquivB ((l.input i).subst (fun w => .var (alloc.assign w))) (r.input i))
    (values : ∀ a, EquivB ((l.value a).subst (fun w => .var (alloc.assign w))) (r.value a)) :
    l.Relabels r := by
  obtain ⟨π,same⟩ := extendAllocation sources _ alloc.sorted alloc.injective
  have term (t : Term sig) (scope : ∀ w, t.Occurs w → l.Uses w) :
      (π.subst sig).apply t = t.subst (fun w => .var (alloc.assign w)) :=
    Term.subst_eq_of_agree _ _ _ (fun w occ => congrArg Term.var (same w (covers w (scope w occ))))
  refine ⟨π,?_,?_⟩
  · intro i; rw [term (l.input i) (fun _ h => Or.inl ⟨i,h⟩)]; exact inputs i
  · intro i; rw [term (l.value i) (fun _ h => Or.inr ⟨i,h⟩)]; exact values i

theorem Row.Relabels.denotes {l r : Row sig I A} (label : l.Relabels r) (x : I → Term sig) (y : A → Term sig) :
    Denotes R l x y ↔ Denotes R r x y := by
  obtain ⟨π,inputs,values⟩ := label
  constructor
  · rintro ⟨δ,nd,fit⟩
    let η := δ.compose (π.inverse.subst sig)
    have changeLabel {a b : Term sig} (eq : EquivB ((π.subst sig).apply a) b) :
        EquivB (δ.apply a) (η.apply b) := by
      rw [← SpecializedFresh.inverse_comp_apply δ π a]
      exact eq.subst η.image
    exact ⟨η,SpecializedFresh.inverse_comp_normal π nd,
      fun i => (fit.inputs i).trans (changeLabel (inputs i)),
      fun a => (fit.values a).trans (changeLabel (values a))⟩
  · rintro ⟨δ,nd,fit⟩
    let η := δ.compose (π.subst sig)
    have changeLabel {a b : Term sig} (eq : EquivB ((π.subst sig).apply a) b) :
        EquivB (δ.apply b) (η.apply a) := by
      rw [show η.apply a = δ.apply ((π.subst sig).apply a) from Substitution.apply_compose ..]
      exact eq.symm.subst δ.image
    exact ⟨η,fun v => nd (π.forward v),
      fun i => (fit.inputs i).trans (changeLabel (inputs i)),
      fun a => (fit.values a).trans (changeLabel (values a))⟩

theorem Row.Relabels.normal {rules : List (Equation sig)} {l r : Row sig I A} (label : l.Relabels r) :
    l.IsNormal (ruleRoot rules) ↔ r.IsNormal (ruleRoot rules) := by
  obtain ⟨π,inputs,values⟩ := label
  have normal {a b : Term sig} (eq : EquivB ((π.subst sig).apply a) b) :
      Normal (ruleRoot rules) a ↔ Normal (ruleRoot rules) b :=
    (SpecializedFresh.normal_rename rules π a).symm.trans (normal_equiv _ eq)
  exact ⟨fun h => ⟨fun i => (normal (inputs i)).mp (h.1 i),fun j => (normal (values j)).mp (h.2 j)⟩,
    fun h => ⟨fun i => (normal (inputs i)).mpr (h.1 i),fun j => (normal (values j)).mpr (h.2 j)⟩⟩

/-- Rows can be opened independently and deduplicated modulo their entire
range. The membership tests allow the implementation to choose its order. -/
theorem Exact.relabel {ids : I → Variable} {op : A → Term sig} {rows out : List (Row sig I A)}
    (source : Exact R ids op rows) (all : ∀ r ∈ rows, ∃ s ∈ out, r.Relabels s)
    (only : ∀ s ∈ out, ∃ r ∈ rows, r.Relabels s) : Exact R ids op out := by
  intro ρ hρ y ny
  rw [source ρ hρ y ny]
  constructor
  · rintro ⟨r,mem,hit⟩
    obtain ⟨s,sm,changeLabel⟩ := all r mem
    exact ⟨s,sm,(changeLabel.denotes _ _).mp hit⟩
  · rintro ⟨s,mem,hit⟩
    obtain ⟨r,rm,changeLabel⟩ := only s mem
    exact ⟨r,rm,(changeLabel.denotes _ _).mpr hit⟩

end Tamarin.Rewriting.VariantJoin
