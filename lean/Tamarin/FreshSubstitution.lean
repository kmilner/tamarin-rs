import Tamarin.VariablePermutation

/-!
Reference representation for substitutions whose stored range variables are
fresh. Encoding stores an entry for EVERY observed input variable, including
identity entries. Decoding renames all stored ranges together. This models the
correlation obligation at Rust's SubstVFresh boundary; it is not yet a theorem
about the Rust encoder or its fixed-width allocation arithmetic.
-/
namespace Tamarin

namespace Substitution
variable {sig : Signature}

def lookupBinding : List (Variable × Term sig) → Variable → Term sig
  | [], v => .var v
  | (w, t) :: rest, v => if v = w then t else lookupBinding rest v

theorem lookupBinding_outside (bindings : List (Variable × Term sig)) (v : Variable)
    (hv : v ∉ bindings.map Prod.fst) : lookupBinding bindings v = .var v := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨w, t⟩ := entry
    have hn : v ≠ w := by intro h; exact hv (by simp [h])
    have hr : v ∉ rest.map Prod.fst := fun h => hv (by simp [h])
    simp only [lookupBinding, ite_eq_right hn, ih hr]

theorem lookupBinding_sorted (bindings : List (Variable × Term sig))
    (hs : ∀ v t, (v, t) ∈ bindings → HasSort t v.sort) (v : Variable) :
    HasSort (lookupBinding bindings v) v.sort := by
  induction bindings with
  | nil => exact .var v
  | cons entry rest ih =>
    obtain ⟨w, t⟩ := entry
    unfold lookupBinding
    split
    · next he => subst v; exact hs w t (by simp)
    · exact ih (fun u t h => hs u t (List.mem_cons_of_mem _ h))

def fromBindings (bindings : List (Variable × Term sig))
    (hs : ∀ v t, (v, t) ∈ bindings → HasSort t v.sort) : Substitution sig where
  image := lookupBinding bindings
  support := bindings.map Prod.fst
  outside := lookupBinding_outside bindings
  sorted := lookupBinding_sorted bindings hs

theorem lookupBinding_tabulate (observed : List Variable) (image : Variable → Term sig)
    (v : Variable) :
    lookupBinding (observed.map fun w => (w, image w)) v =
      if v ∈ observed then image v else .var v := by
  induction observed with
  | nil => rfl
  | cons w ws ih =>
    by_cases he : v = w
    · subst v; simp [lookupBinding]
    · simp [lookupBinding, he, ih]

/-- Consistent repeated keys give the same result under first/last insertion
and reordering. A bridge may not silently choose between conflicting entries. -/
theorem lookupBinding_eq_of_mem (bindings : List (Variable × Term sig))
    (hc : ∀ v t u, (v, t) ∈ bindings → (v, u) ∈ bindings → t = u)
    (v : Variable) (t : Term sig) (hm : (v, t) ∈ bindings) :
    lookupBinding bindings v = t := by
  induction bindings with
  | nil => simp at hm
  | cons entry rest ih =>
    obtain ⟨w, head⟩ := entry
    by_cases he : v = w
    · subst v
      simp only [lookupBinding, ↓reduceIte]
      exact hc w head t (by simp) hm
    · have hr : (v, t) ∈ rest := by
        rcases List.mem_cons.mp hm with hp | hp
        · exact False.elim (he (congrArg Prod.fst hp))
        · exact hp
      simp only [lookupBinding, ite_eq_right he]
      exact ih (fun u a b ha hb => hc u a b
        (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)) hr

end Substitution

/-- A finite fresh-range packet. Identity entries are significant here.
Repeated keys must agree, so decoding cannot diverge from Rust's last-entry
map insertion. The packet stores explicit term entries rather than an
unrestricted variable-to-term substitution function; ABI encoding is separate. -/
structure FreshAnswer (sig : Signature) where
  bindings : List (Variable × Term sig)
  sorted : ∀ v t, (v, t) ∈ bindings → HasSort t v.sort
  consistent : ∀ v t u, (v, t) ∈ bindings → (v, u) ∈ bindings → t = u

namespace FreshAnswer
variable {sig : Signature}

def encode (observed : List Variable) (σ : Substitution sig) : FreshAnswer sig where
  bindings := observed.map fun v => (v, σ.image v)
  sorted := by
    intro v t h
    obtain ⟨w, _, he⟩ := List.mem_map.mp h
    cases he
    exact σ.sorted _
  consistent := by
    intro v t u ht hu
    obtain ⟨w, _, he⟩ := List.mem_map.mp ht
    cases he
    obtain ⟨z, _, he⟩ := List.mem_map.mp hu
    have hz := congrArg Prod.fst he
    cases hz
    exact congrArg Prod.snd he

def decode (answer : FreshAnswer sig) (π : VariablePermutation) : Substitution sig :=
  Substitution.fromBindings
    (answer.bindings.map fun entry => (entry.1, (π.subst sig).apply entry.2)) (by
      intro v t h
      obtain ⟨⟨w, original⟩, hm, he⟩ := List.mem_map.mp h
      cases he
      exact (answer.sorted w original hm).subst (π.subst sig).image (π.subst sig).sorted)

/-- Explicitly stored identities are renamed along with every other image. -/
theorem decode_encode_image (observed : List Variable) (σ : Substitution sig)
    (π : VariablePermutation) (v : Variable) :
    ((encode observed σ).decode π).image v =
      if v ∈ observed then (π.subst sig).apply (σ.image v) else .var v := by
  simp only [decode, encode, Substitution.fromBindings, List.map_map, Function.comp_def]
  exact Substitution.lookupBinding_tabulate observed _ v

theorem decode_instance (observed : List Variable) (σ : Substitution sig)
    (π : VariablePermutation) :
    Substitution.InstanceOn (· ∈ observed) ((encode observed σ).decode π) σ := by
  refine ⟨π.subst sig, ?_⟩
  intro v hv
  rw [decode_encode_image, ite_eq_left hv]
  exact .refl _

theorem encode_instance (observed : List Variable) (σ : Substitution sig)
    (π : VariablePermutation) :
    Substitution.InstanceOn (· ∈ observed) σ ((encode observed σ).decode π) := by
  refine ⟨π.inverse.subst sig, ?_⟩
  intro v hv
  change EquivB (σ.image v)
    ((π.inverse.subst sig).apply (((encode observed σ).decode π).image v))
  rw [decode_encode_image, ite_eq_left hv, π.inverse_apply]
  exact .refl _

/-- One shared instantiator still covers all observed variables; the rename
and its finite inverse establish both directions for arbitrary candidates. -/
theorem instance_iff (observed : List Variable) (σ ρ : Substitution sig)
    (π : VariablePermutation) :
    Substitution.InstanceOn (· ∈ observed) ρ σ ↔
      Substitution.InstanceOn (· ∈ observed) ρ ((encode observed σ).decode π) := by
  constructor
  · intro h
    exact Substitution.instanceOn_trans _ h (encode_instance observed σ π)
  · intro h
    exact Substitution.instanceOn_trans _ h (decode_instance observed σ π)

/-- Composing a decoded fresh answer with an earlier factored substitution
preserves its instances on the original variables. The packet must cover every
variable read by the factor, including retained identities. The same range
renaming is used under every constructor and in every alias. -/
theorem compose_instance_iff (observed : List Variable) (original : Variable → Prop)
    (σ m ρ : Substitution sig) (π : VariablePermutation)
    (included : ∀ v, original v → ∀ w, (m.image v).Occurs w → w ∈ observed) :
    Substitution.InstanceOn original ρ (σ.compose m) ↔
      Substitution.InstanceOn original ρ (((encode observed σ).decode π).compose m) := by
  let d := (encode observed σ).decode π
  have eq (v) (hv : original v) :
      (d.compose m).image v = (π.subst sig).apply ((σ.compose m).image v) := by
    change (m.image v).subst d.image = ((m.image v).subst σ.image).subst _
    rw [Term.subst_comp]
    apply Term.subst_eq_of_agree
    intro w hw
    exact (decode_encode_image observed σ π w).trans (ite_eq_left (included v hv w hw))
  constructor
  · intro h
    apply Substitution.instanceOn_trans original h
    refine ⟨π.inverse.subst sig, ?_⟩
    intro v hv
    change EquivB _ ((π.inverse.subst sig).apply ((d.compose m).image v))
    rw [eq v hv, π.inverse_apply]
    exact .refl _
  · intro h
    apply Substitution.instanceOn_trans original h
    exact ⟨π.subst sig, fun v hv => (eq v hv) ▸ EquivB.refl _⟩

def rangeVariables (observed : List Variable) (σ : Substitution sig) : List Variable :=
  observed.flatMap fun v => (σ.image v).variables

/-- Fresh names avoid input variables as well as the caller's context. This
per-answer allocation may be reused by different answers because their witness
names have independent scopes; callers must never merge those scopes. -/
def freshPermutation (observed avoid : List Variable) (σ : Substitution sig) : VariablePermutation :=
  VariablePermutation.ofBlock (rangeVariables observed σ)
    (VariablePermutation.freshBound (avoid ++ observed ++ rangeVariables observed σ)) (by
      intro v hv
      apply VariablePermutation.lt_freshBound
      simp [hv])

theorem renaming_forward (observed avoid : List Variable) (σ : Substitution sig)
    (v : Variable) (hv : v ∈ rangeVariables observed σ) :
    (freshPermutation observed avoid σ).forward v = VariablePermutation.shift
      (VariablePermutation.freshBound (avoid ++ observed ++ rangeVariables observed σ)) v :=
  VariablePermutation.swapBlock_source _ _ v hv

theorem renaming_avoids (observed avoid : List Variable) (σ : Substitution sig)
    (v : Variable) (hv : v ∈ rangeVariables observed σ) :
    (freshPermutation observed avoid σ).forward v ∉ avoid ++ observed := by
  intro hmem
  have low := VariablePermutation.lt_freshBound
    (avoid ++ observed ++ rangeVariables observed σ) _
    (show (freshPermutation observed avoid σ).forward v ∈
        avoid ++ observed ++ rangeVariables observed σ from by
      simpa only [List.append_assoc] using List.mem_append_left _ hmem)
  rw [renaming_forward observed avoid σ v hv] at low
  simp only [VariablePermutation.shift] at low
  omega

/-- Executable reference conversion, including domain closure and a fresh
finite renaming. It handles arbitrary sorted finite substitutions, not only
ground or idempotent ones. -/
def freshen (p : Problem sig) (avoid : List Variable) (σ : Substitution sig) :
    Substitution sig :=
  (encode p.variables σ).decode (freshPermutation p.variables avoid σ)

theorem freshen_instance_iff (p : Problem sig) (avoid : List Variable)
    (σ ρ : Substitution sig) :
    Substitution.InstanceOn p.Occurs ρ σ ↔
      Substitution.InstanceOn p.Occurs ρ (freshen p avoid σ) := by
  have predicates : (fun v => v ∈ p.variables) = p.Occurs := by
    funext v
    exact propext (p.mem_variables v)
  simpa only [predicates, freshen] using
    instance_iff p.variables σ ρ (freshPermutation p.variables avoid σ)

theorem freshen_domain (p : Problem sig) (avoid : List Variable) (σ : Substitution sig) :
    DomainRestricted p (freshen p avoid σ) := by
  intro v hv
  change ((encode p.variables σ).decode _).image v = .var v
  rw [decode_encode_image]
  exact ite_eq_right (by simpa using hv)

theorem freshen_range_avoids (p : Problem sig) (avoid : List Variable) (σ : Substitution sig)
    (v : Variable) (hv : p.Occurs v) (w : Variable)
    (hw : ((freshen p avoid σ).image v).Occurs w) : w ∉ avoid ++ p.variables := by
  have hobs : v ∈ p.variables := (p.mem_variables v).mpr hv
  change (((encode p.variables σ).decode (freshPermutation p.variables avoid σ)).image v).Occurs w at hw
  rw [decode_encode_image, ite_eq_left hobs] at hw
  change ((σ.image v).subst
    (fun u => .var ((freshPermutation p.variables avoid σ).forward u))).Occurs w at hw
  obtain ⟨u, hu, he⟩ := ((σ.image v).occurs_rename _ w).mp hw
  have hrange : u ∈ rangeVariables p.variables σ :=
    List.mem_flatMap.mpr ⟨v, hobs, ((σ.image v).mem_variables u).mpr hu⟩
  rw [he]
  exact renaming_avoids p.variables avoid σ u hrange

theorem freshen_fresh (p : Problem sig) (avoid : List Variable) (σ : Substitution sig) :
    FreshFor p avoid (freshen p avoid σ) := by
  intro v hv w hw _ hmem
  exact freshen_range_avoids p avoid σ v hv w hw (List.mem_append_left _ hmem)

/-- All stored range variables are outside the input domain. Reapplying the
decoded answer cannot accidentally chase or capture one of its witnesses. -/
theorem freshen_image_fixed (p : Problem sig) (avoid : List Variable)
    (σ : Substitution sig) (v : Variable) :
    (freshen p avoid σ).apply ((freshen p avoid σ).image v) =
      (freshen p avoid σ).image v := by
  by_cases hv : p.Occurs v
  · calc
      (freshen p avoid σ).apply ((freshen p avoid σ).image v) =
          ((freshen p avoid σ).image v).subst Term.var := by
        apply Term.subst_eq_of_agree
        intro w hw
        apply freshen_domain p avoid σ w
        intro hp
        exact freshen_range_avoids p avoid σ v hv w hw
          (List.mem_append_right _ ((p.mem_variables w).mpr hp))
      _ = (freshen p avoid σ).image v := Term.subst_id _
  · rw [freshen_domain p avoid σ v hv]
    change (freshen p avoid σ).image v = .var v
    exact freshen_domain p avoid σ v hv

theorem freshen_idempotent (p : Problem sig) (avoid : List Variable)
    (σ : Substitution sig) (t : Term sig) :
    (freshen p avoid σ).apply ((freshen p avoid σ).apply t) =
      (freshen p avoid σ).apply t := by
  change (t.subst (freshen p avoid σ).image).subst (freshen p avoid σ).image = _
  rw [Term.subst_comp]
  apply Term.subst_eq_of_agree
  intro v _
  exact freshen_image_fixed p avoid σ v

/-- Whole-answer-set refinement, including caller noninterference and
freshness. Each branch uses a single shared renaming for all its bindings. -/
theorem output_refinement (request : Request sig) (answers : List (Substitution sig)) :
    OutputRefinement request answers
      (answers.map (freshen request.problem request.avoid)) := by
  constructor
  · intro ρ
    constructor
    · rintro ⟨σ, hσ, hi⟩
      exact ⟨freshen request.problem request.avoid σ,
        List.mem_map.mpr ⟨σ, hσ, rfl⟩,
        (freshen_instance_iff request.problem request.avoid σ ρ).mp hi⟩
    · rintro ⟨represented, hr, hi⟩
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hr
      exact ⟨σ, hσ, (freshen_instance_iff request.problem request.avoid σ ρ).mpr hi⟩
  · intro represented hr
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hr
    exact freshen_domain request.problem request.avoid σ
  · intro represented hr
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hr
    exact freshen_fresh request.problem request.avoid σ

theorem freshen_correct (request : Request sig) (answers : List (Substitution sig))
    (hc : CompleteSet request.problem answers) :
    (Outcome.complete (answers.map (freshen request.problem request.avoid))).CorrectIn
      request.problem request.avoid :=
  (output_refinement request answers).preserves_correct hc

end FreshAnswer
end Tamarin
