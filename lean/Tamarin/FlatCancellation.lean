import Tamarin.FlatMatching
import Tamarin.GroundSideUnification

/-! Cancel a common multiset before solving a flat AC unification problem.
An empty remainder is an inventory, never a term or an AC unit. -/
namespace Tamarin.FlatCancellation
open FlatMatching
variable {sig : Signature}

theorem inventory_iff (f : sig.ACSym) (σ : Substitution sig) (xs ys : List (Leaf sig))
    (hx : xs ≠ []) (hy : ys ≠ []) :
    EquivB (σ.apply (pattern f xs)) (σ.apply (pattern f ys)) ↔
      (xs.flatMap (parts f σ)).Perm (ys.flatMap (parts f σ)) := by
  rw [← flatten_pattern f σ xs hx, ← flatten_pattern f σ ys hy]
  exact ⟨Cancellation.flatten_equiv f, Cancellation.equiv_of_flatten_perm f⟩

/-- Cancelled variables may occur again in a remainder or in another equation.
The equivalence quantifies over every sorted substitution. -/
theorem cancel_iff (f : sig.ACSym) (σ : Substitution sig)
    (xs ys common left right : List (Leaf sig)) (hx : xs ≠ []) (hy : ys ≠ [])
    (hl : xs.Perm (left ++ common)) (hr : ys.Perm (right ++ common)) :
    EquivB (σ.apply (pattern f xs)) (σ.apply (pattern f ys)) ↔
      (left.flatMap (parts f σ)).Perm (right.flatMap (parts f σ)) := by
  rw [inventory_iff f σ xs ys hx hy]
  have l := hl.flatMap_right (parts f σ)
  have r := hr.flatMap_right (parts f σ)
  rw [List.flatMap_append] at l r
  constructor
  · intro h
    exact (List.perm_append_right_iff _).mp (l.symm.trans (h.trans r))
  · intro h
    exact l.trans ((h.append_right _).trans r.symm)

/-- Interpret an occurrence-ID subtraction packet. Both sides use the same
variable table. Literal tails can appear on either side in any order. -/
theorem cancel_variables (f : sig.ACSym) (σ : Substitution sig) (decode : UInt64 → Variable)
    (big small rest : List UInt64) (left right : List (Leaf sig))
    (hp : big.Perm (rest ++ small))
    (hb : big.map (fun i => Sum.inl (decode i)) ++ left ≠ [])
    (hs : small.map (fun i => Sum.inl (decode i)) ++ right ≠ []) :
    let var : UInt64 → Leaf sig := fun i => .inl (decode i)
    EquivB (σ.apply (pattern f (big.map var ++ left)))
      (σ.apply (pattern f (small.map var ++ right))) ↔
    ((rest.map var ++ left).flatMap (parts f σ)).Perm (right.flatMap (parts f σ)) := by
  let var : UInt64 → Leaf sig := fun i => .inl (decode i)
  apply cancel_iff f σ _ _ (small.map var) _ _ hb hs
  · have h := (hp.map var).append_right left
    rw [List.map_append, List.append_assoc] at h
    simpa only [List.append_assoc] using h.trans
      ((List.perm_append_comm (l₁ := small.map var) (l₂ := left)).append_left (rest.map var))
  · exact List.perm_append_comm

/-- No finite substitution can supply zero AC factors for a leaf. -/
theorem inventory_empty_iff (f : sig.ACSym) (σ : Substitution sig) (xs : List (Leaf sig)) :
    xs.flatMap (parts f σ) = [] ↔ xs = [] := by
  constructor
  · intro he
    cases xs with
    | nil => rfl
    | cons x xs =>
      have hx := (List.flatMap_eq_nil_iff.mp he) x (by simp)
      have hf := Cancellation.fold_flatten f (σ.apply (leaf x))
      change Cancellation.flatten _ _ = [] at hx
      rw [hx] at hf
      cases hf
  · rintro rfl; rfl

/-- Lift ground matches on the reduced variables back to the original
conjunction. One instantiation (ρ itself) handles *all* cancelled variables,
including identities shared by different equations. -/
theorem lift_ground_answers (p reduced : Problem sig) (answers : List (Substitution sig))
    (equivalent : ∀ σ, p.Solves σ ↔ reduced.Solves σ)
    (included : ∀ v, reduced.Occurs v → p.Occurs v)
    (ground : ∀ e ∈ reduced, e.rhs.Ground)
    (matchesAll : Matching.Complete reduced (fun _ => True) answers)
    (avoid : List Variable) : (Outcome.complete answers).CorrectIn p avoid := by
  have hc := matchesAll.groundSide ground
  have hg (σ) (hs : σ ∈ answers) := (matchesAll.sound σ hs).1.groundOn ground
  have hd (σ) (hs : σ ∈ answers) : DomainRestricted reduced σ := by
    intro v hv
    apply (matchesAll.sound σ hs).2
    rintro ⟨⟨e, he, ho⟩, _⟩
    exact hv ⟨e, he, Or.inl ho⟩
  constructor
  · constructor
    · intro σ hs; exact (equivalent σ).mpr (hc.sound σ hs)
    · intro ρ hρ
      obtain ⟨σ, hs, δ, ha⟩ := hc.covers ρ ((equivalent ρ).mp hρ)
      refine ⟨σ, hs, ρ, ?_⟩
      intro v _
      by_cases hv : reduced.Occurs v
      · simpa only [Substitution.compose, (hg σ hs v hv).apply_eq] using ha v hv
      · change EquivB (ρ.image v) (ρ.apply (σ.image v))
        rw [hd σ hs v hv]
        exact .refl _
  · intro σ hs v hv; exact hd σ hs v (fun h => hv (included v h))
  · intro σ hs v hv w hw hn
    by_cases h : reduced.Occurs v
    · exact False.elim (hg σ hs v h w hw)
    · rw [hd σ hs v h] at hw
      exact False.elim (hn (hw ▸ hv))

/-- An otherwise unresolved conjunction may be tested after other equations
have fixed every variable it observes. This preserves coverage of arbitrary
nonground instances of the original answers and the same caller context. -/
theorem filter_ground_constraints (p q : Problem sig) (answers : List (Substitution sig))
    (avoid : List Variable) (hc : (Outcome.complete answers).CorrectIn p avoid)
    (ground : ∀ σ ∈ answers, σ.GroundOn q.Occurs)
    (keep : Substitution sig → Bool) (test : ∀ σ ∈ answers, keep σ = true ↔ q.Solves σ) :
    (Outcome.complete (answers.filter keep)).CorrectIn (p ++ q) avoid := by
  have occurs (v : Variable) : (p ++ q).Occurs v ↔ p.Occurs v ∨ q.Occurs v := by
    simp [Problem.Occurs, List.mem_append, or_and_right, exists_or]
  constructor
  · constructor
    · intro σ hs e he
      obtain ⟨hm, hk⟩ := List.mem_filter.mp hs
      exact (List.mem_append.mp he).elim (hc.mathematical.sound σ hm e) ((test σ hm).mp hk e)
    · intro ρ hρ
      obtain ⟨σ, hs, δ, ha⟩ := hc.mathematical.covers ρ
        (fun e he => hρ e (List.mem_append_left _ he))
      have included (v : Variable) (hv : q.Occurs v) : p.Occurs v := by
        apply Classical.byContradiction
        intro hn
        have hg := ground σ hs v hv v
        rw [hc.domain σ hs v hn] at hg
        exact hg rfl
      have agree (v : Variable) (hv : q.Occurs v) : EquivB (ρ.image v) (σ.image v) := by
        simpa only [Substitution.compose, (ground σ hs v hv).apply_eq] using ha v (included v hv)
      have hq : q.Solves σ := by
        intro e he
        have hl := e.lhs.subst_equiv ρ.image σ.image (fun v hv => agree v ⟨e, he, Or.inl hv⟩)
        have hr := e.rhs.subst_equiv ρ.image σ.image (fun v hv => agree v ⟨e, he, Or.inr hv⟩)
        exact hl.symm.trans ((hρ e (List.mem_append_right _ he)).trans hr)
      exact ⟨σ, List.mem_filter.mpr ⟨hs, (test σ hs).mpr hq⟩, δ,
        fun v hv => ha v (((occurs v).mp hv).elim id (included v))⟩
  · intro σ hs v hn
    exact hc.domain σ (List.mem_filter.mp hs).1 v (fun h => hn ((occurs v).mpr (.inl h)))
  · intro σ hs v hv w hw hn
    have hm := (List.mem_filter.mp hs).1
    rcases (occurs v).mp hv with hp | hq
    · exact hc.fresh σ hm v hp w hw (fun h => hn ((occurs w).mpr (.inl h)))
    · exact False.elim (ground σ hm v hq w hw)

end Tamarin.FlatCancellation
