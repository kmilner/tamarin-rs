import Tamarin.MatchingConjunction

/-! What a caller can observe from a complete list of directional matches. -/
namespace Tamarin.Matching
variable {sig : Signature} {p : Problem sig} {bindable : Variable → Prop}
  {xs ys : List (Substitution sig)}

/-- Reordering or removing duplicate entries preserves the matching contract. -/
theorem Complete.of_same_members (h : Complete p bindable xs)
    (members : ∀ σ, σ ∈ xs ↔ σ ∈ ys) : Complete p bindable ys := by
  constructor
  · exact fun σ hy => h.sound σ ((members σ).mpr hy)
  · intro ρ hm hs
    obtain ⟨σ,hx,agree⟩ := h.covers ρ hm hs
    exact ⟨σ,(members σ).mp hx,agree⟩

theorem Complete.nonempty_iff (h : Complete p bindable xs) :
    xs ≠ [] ↔ ∃ σ, Matches p σ ∧ Scoped p bindable σ := by
  cases xs with
  | nil => simpa using (empty_iff p bindable).mp h
  | cons σ rest => exact ⟨fun _ => ⟨σ,h.sound σ List.mem_cons_self⟩, by simp⟩

/-- A caller's key may inspect any pattern variables. Its value must respect
agreement modulo B on those variables. The key need not distinguish all matches. -/
theorem Complete.key_mem_iff {α : Type} (h : Complete p bindable xs)
    (key : Substitution sig → α)
    (invariant : ∀ σ τ, Substitution.AgreesOn (Observed p) σ τ → key σ = key τ)
    (a : α) :
    a ∈ xs.map key ↔ ∃ σ, Matches p σ ∧ Scoped p bindable σ ∧ key σ = a := by
  constructor
  · intro hm
    obtain ⟨σ,hs,hk⟩ := List.mem_map.mp hm
    exact ⟨σ,(h.sound σ hs).1,(h.sound σ hs).2,hk⟩
  · rintro ⟨σ,hm,hs,hk⟩
    obtain ⟨τ,ht,agree⟩ := h.covers σ hm hs
    exact List.mem_map.mpr ⟨τ,ht,(invariant σ τ agree).symm.trans hk⟩

/-- A complete singleton forces the observable value of any other complete
enumerator's first match, including an enumerator emitting redundant arms. -/
theorem Complete.head_key_of_singleton {α : Type} {σ : Substitution sig}
    (one : Complete p bindable [σ]) (other : Complete p bindable ys)
    (key : Substitution sig → α)
    (invariant : ∀ ρ τ, Substitution.AgreesOn (Observed p) ρ τ → key ρ = key τ) :
    ys.head?.map key = some (key σ) := by
  cases ys with
  | nil =>
    exact False.elim ((empty_iff p bindable).mp other ⟨σ,one.sound σ (by simp)⟩)
  | cons τ _ =>
    obtain ⟨hm,hs⟩ := other.sound τ List.mem_cons_self
    obtain ⟨ρ,member,agree⟩ := one.covers τ hm hs
    obtain rfl := List.mem_singleton.mp member
    exact congrArg some (invariant τ ρ agree)

/-- Taking the least observable key gives a deterministic caller policy even
when two implementations return different representatives or different numbers
of entries. Selecting a particular substitution needs a key that distinguishes
the caller's desired answers. -/
theorem Complete.min_key_eq {α : Type} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] (hx : Complete p bindable xs) (hy : Complete p bindable ys)
    (key : Substitution sig → α)
    (invariant : ∀ σ τ, Substitution.AgreesOn (Observed p) σ τ → key σ = key τ) :
    (xs.map key).min? = (ys.map key).min? := by
  apply Option.ext
  intro a
  have same (v : α) := (hx.key_mem_iff key invariant v).trans (hy.key_mem_iff key invariant v).symm
  simp only [List.min?_eq_some_iff, same]

/-- The caller fixes the same list of pattern variables for every row. Reading
each image includes identity bindings and keeps subject variables rigid. -/
def bindingImages {α : Type} (repr : Term sig → α) (vars : List Variable)
    (σ : Substitution sig) : List α := vars.map (fun v => repr (σ.image v))

theorem bindingImages_eq_iff {α : Type} (repr : Term sig → α) (vars : List Variable)
    (σ τ : Substitution sig) (faithful : ∀ v ∈ vars,
      repr (σ.image v) = repr (τ.image v) ↔ EquivB (σ.image v) (τ.image v)) :
    bindingImages repr vars σ = bindingImages repr vars τ ↔
      ∀ v ∈ vars, EquivB (σ.image v) (τ.image v) := by
  simp only [bindingImages, List.map_inj_left]
  exact ⟨fun eq v mem => (faithful v mem).mp (eq v mem),
    fun eq v mem => (faithful v mem).mpr (eq v mem)⟩

/-- Taking the least restored binding list agrees across complete search
implementations for any shared total caller order on the lists.
`bindingImages_eq_iff` identifies tied rows when their representations are faithful. -/
theorem Complete.min_bindingImages_eq {α : Type} [Min (List α)] [LE (List α)]
    [Std.IsLinearOrder (List α)] [Std.LawfulOrderMin (List α)]
    (hx : Complete p bindable xs) (hy : Complete p bindable ys) (repr : Term sig → α)
    (invariant : ∀ a b, EquivB a b → repr a = repr b)
    (vars : List Variable) (observed : ∀ v ∈ vars, Observed p v) :
    (xs.map (bindingImages repr vars)).min? = (ys.map (bindingImages repr vars)).min? := by
  apply hx.min_key_eq hy
  intro σ τ agree
  exact List.map_congr_left (fun v mem => invariant _ _ (agree v (observed v mem)))

/-- Directional matching substitutes the variable only on the left. The
subject can itself contain that variable or another variable bound elsewhere. -/
theorem variable_match (v : Variable) (t : Term sig) (ht : HasSort t v.sort) :
    Complete [⟨.var v,t⟩] (fun _ => True) [Substitution.binding v t ht] := by
  let q : Problem sig := [⟨.var v,t⟩]
  have obs (w : Variable) : Observed q w ↔ w = v := by simp [q,Observed,Term.Occurs]
  constructor
  · intro σ member
    obtain rfl := List.mem_singleton.mp member
    constructor
    · intro e he
      obtain rfl := List.mem_singleton.mp he
      change EquivB ((Substitution.binding v t ht).image v) t
      rw [Substitution.binding_image_self]
      exact .refl _
    · intro w hw
      exact Substitution.binding_image_other v w t ht (fun eq => hw ⟨(obs w).mpr eq,trivial⟩)
  · intro ρ hm _
    refine ⟨_,List.mem_singleton_self _,fun w hw => ?_⟩
    obtain rfl := (obs w).mp hw
    rw [Substitution.binding_image_self]
    exact hm _ List.mem_cons_self

/-- Moving equations or coalescing repeated identical side conditions keeps
both the original scope and the conjunction a match solves. -/
theorem Complete.of_same_equations {q : Problem sig} (h : Complete p bindable xs)
    (members : ∀ e, e ∈ p ↔ e ∈ q) : Complete q bindable xs := by
  have obs (w : Variable) : Observed p w ↔ Observed q w := by simp only [Observed,members]
  have sc (σ : Substitution sig) : Scoped p bindable σ ↔ Scoped q bindable σ := by
    simp only [Scoped,obs]
  have mt (σ : Substitution sig) : Matches p σ ↔ Matches q σ := by simp only [Matches,members]
  constructor
  · intro σ mem
    exact ⟨(mt _).mp (h.sound σ mem).1,(sc _).mp (h.sound σ mem).2⟩
  · intro ρ hm hs
    obtain ⟨σ,mem,agree⟩ := h.covers ρ ((mt _).mpr hm) ((sc _).mpr hs)
    exact ⟨σ,mem,fun w hw => agree w ((obs w).mpr hw)⟩

/-- Append one fixed binding to every residual answer. Disjointness is
required only on pattern variables. Even if a subject mentions a variable
from the other part, a directional match leaves that occurrence rigid. -/
theorem Complete.with_variable_side {original : Problem sig}
    (h : Complete p (fun _ => True) xs) (v : Variable) (subject : Term sig)
    (ht : HasSort subject v.sort) (disjoint : ¬ Observed p v)
    (layout : (⟨.var v,subject⟩ :: p).Perm original) :
    let side : Problem sig := [⟨.var v,subject⟩]
    Complete original (fun _ => True)
      (xs.map (merge side (Substitution.binding v subject ht))) := by
  intro side
  have compat (σ τ : Substitution sig) : Compatible side p σ τ := by
    intro w hw hp
    have eq : w = v := by simpa [side,Observed,Term.Occurs] using hw
    exact False.elim (disjoint (eq ▸ hp))
  have joined := join_complete side p _ _ (variable_match v subject ht) h
  have same (e : Equation sig) : e ∈ side ++ p ↔ e ∈ original := layout.mem_iff
  have reorder := joined.of_same_equations same
  simpa [join,compat] using reorder

end Tamarin.Matching
