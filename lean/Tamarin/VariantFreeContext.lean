import Tamarin.ObservationRepresentative
import Tamarin.VariantJoinSubsumption

/-! Replace any block of joint observations by one inert free constructor
applied to that block. Other observations and all caller images stay in the
same row. Iterating this step builds a forest of nested free constructors. -/
namespace Tamarin.Rewriting.VariantJoin
open ConstructorVariants
variable {s : Signature} {I A : Type}

def wrapFree (f : s.FreeSym) (terms : Sum A (Fin (s.arity f)) → Term s) : Option A → Term s
  | none => .free f (fun i => terms (.inr i))
  | some a => terms (.inl a)

def Row.wrapFree (f : s.FreeSym) (q : Row s I (Sum A (Fin (s.arity f)))) : Row s I (Option A) :=
  ⟨q.input,VariantJoin.wrapFree f q.value⟩

/-- Assembling the children cannot identify distinct alternatives: free
constructors are injective in their ordered arguments modulo the basis. -/
theorem fits_wrapFree_iff (f : s.FreeSym) (q : Row s I (Sum A (Fin (s.arity f))))
    (x : I → Term s) (y : Sum A (Fin (s.arity f)) → Term s) (δ : Substitution s) :
    Fits (q.wrapFree f) x (wrapFree f y) δ ↔ Fits q x y δ := by
  constructor
  · intro h
    refine ⟨h.inputs,?_⟩
    intro k
    cases k with
    | inl a => exact h.values (some a)
    | inr i => exact (Matching.free_equiv_iff ..).mp (h.values none) i
  · intro h
    refine ⟨h.inputs,?_⟩
    intro k
    cases k with
    | some a => exact h.values (.inl a)
    | none => exact .free _ _ _ fun i => h.values (.inr i)

theorem irredundant_wrapFree (f : s.FreeSym) (rows : List (Row s I (Sum A (Fin (s.arity f)))))
    (h : Irredundant rows) : Irredundant (rows.map (Row.wrapFree f)) := by
  apply List.pairwise_map.mpr
  apply h.imp
  intro g t pair
  have lift {g t : Row s I (Sum A (Fin (s.arity f)))} : (g.wrapFree f).Subsumes (t.wrapFree f) → g.Subsumes t :=
    fun ⟨δ,fit⟩ => ⟨δ,(fits_wrapFree_iff f g t.input t.value δ).mp fit⟩
  exact ⟨fun sub => pair.1 (lift sub),fun sub => pair.2 (lift sub)⟩

theorem Row.IsNormal.wrapFree {rules : List (Equation s)} (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads rules) {q : Row s I (Sum A (Fin (s.arity f)))}
    (h : q.IsNormal (ruleRoot rules)) : (q.wrapFree f).IsNormal (ruleRoot rules) := by
  refine ⟨h.1,?_⟩
  intro k
  cases k with
  | some a => exact h.2 (.inl a)
  | none => exact constructor_node_normal rules apps _ absent (fun i => h.2 (.inr i))

variable {rules : List (Equation s)} (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads rules)
    (terms : Sum A (Fin (s.arity f)) → Term s)
    (typed : ∀ i, HasSort (terms (.inr i)) (s.inputSort f i))
    (slots : ∀ i, StableVariants.Stable (ruleRoot rules) (terms (.inr i)) ∨ ∀ ρ : Substitution s,
      (ρ.apply (terms (.inr i))).rootSort = s.inputSort f i)

include apps absent typed slots

theorem Exact.wrapFree {ids : I → Variable} {rows : List (Row s I (Sum A (Fin (s.arity f))))}
    (family : Exact (ruleRoot rules) ids terms rows) :
    Exact (ruleRoot rules) ids (VariantJoin.wrapFree f terms) (rows.map (Row.wrapFree f)) := by
  intro ρ hn y ny
  constructor
  · intro forms
    obtain ⟨us,hu,hform⟩ := StableVariants.normalForm_free_view rules apps f absent _ typed slots ρ hn (forms none)
    let ys := Sum.elim (fun a => y (some a)) us
    have child : ∀ k, NormalForm (ruleRoot rules) (ρ.apply (terms k)) (ys k) :=
      fun k => by cases k with | inl a => exact forms (some a) | inr i => exact hform i
    obtain ⟨q,mem,δ,nδ,fit⟩ := (family ρ hn ys (fun k => (child k).2.1)).mp child
    have eq : y = VariantJoin.wrapFree f ys := funext fun k => by cases k <;> first | exact hu | rfl
    exact ⟨_,List.mem_map_of_mem mem,δ,nδ,eq ▸ (fits_wrapFree_iff f q _ ys δ).mpr fit⟩
  · rintro ⟨_,mem,δ,nδ,fit⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp mem
    obtain ⟨us,hu,_⟩ := free_equiv_view (fit.values none).symm
    let ys := Sum.elim (fun a => y (some a)) us
    have eq : y = VariantJoin.wrapFree f ys := funext fun k => by cases k <;> first | exact hu | rfl
    have normals : ∀ k, Normal (ruleRoot rules) (ys k) := fun k => by
      cases k with
      | inl a => exact ny (some a)
      | inr i => exact normal_free_child f us (hu ▸ ny none) i
    have forms := (family ρ hn ys normals).mpr ⟨q,hq,δ,nδ,(fits_wrapFree_iff f q _ ys δ).mp (eq ▸ fit)⟩
    intro k
    cases k with
    | some a => exact forms (.inl a)
    | none => rw [hu]; exact free_normalForm rules apps f absent _ _ (fun i => forms (.inr i))

theorem wrapFree_unique (unique : ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → ∀ k u v,
      NormalForm (ruleRoot rules) (ρ.apply (terms k)) u →
      NormalForm (ruleRoot rules) (ρ.apply (terms k)) v → EquivB u v)
    (ρ : Substitution s) (hn : Normalized (ruleRoot rules) ρ) (k : Option A) (u v : Term s)
    (left : NormalForm (ruleRoot rules) (ρ.apply (wrapFree f terms k)) u)
    (right : NormalForm (ruleRoot rules) (ρ.apply (wrapFree f terms k)) v) : EquivB u v := by
  cases k with
  | some a => exact unique ρ hn (.inl a) u v left right
  | none =>
    obtain ⟨_,rfl,l⟩ := StableVariants.normalForm_free_view rules apps f absent _ typed slots ρ hn left
    obtain ⟨_,rfl,r⟩ := StableVariants.normalForm_free_view rules apps f absent _ typed slots ρ hn right
    exact .free _ _ _ fun i => unique ρ hn (.inr i) _ _ (l i) (r i)

end Tamarin.Rewriting.VariantJoin
