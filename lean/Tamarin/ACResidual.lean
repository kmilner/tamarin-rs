import Tamarin.ACRepresentation
import Tamarin.Cancellation
import Tamarin.CommonCancellation
import Tamarin.Unification

/-! Semantics of cancelling equal AC children. Words can denote open compound
terms. A substitution may split a child into several factors or identify two
different words, so disjoint output IDs alone never prove a clash. -/
namespace Tamarin.ACResidual
variable {sig : Signature}

/-- Empty inventories are interpreted only in an equation, never as terms. -/
def Holds (f : sig.ACSym) (σ : Substitution sig) (xs ys : List (Term sig)) : Prop :=
  match ACRepresentation.decode f xs, ACRepresentation.decode f ys with
  | none, none => True
  | some a, some b => EquivB (σ.apply a) (σ.apply b)
  | _, _ => False

private theorem flatten_fold (f : sig.ACSym) (σ : Substitution sig)
    (a : Term sig) (xs : List (Term sig)) :
    Cancellation.flatten f (σ.apply (ACRepresentation.fold f a xs)) =
      (a :: xs).flatMap (fun t => Cancellation.flatten f (σ.apply t)) := by
  induction xs generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih =>
    change Cancellation.flatten f (.ac f (σ.apply a) (σ.apply (ACRepresentation.fold f b bs))) = _
    rw [Cancellation.flatten_ac, ih]
    rfl

private theorem parts_ne_nil (f : sig.ACSym) (σ : Substitution sig)
    (a : Term sig) (xs : List (Term sig)) :
    (a :: xs).flatMap (fun t => Cancellation.flatten f (σ.apply t)) ≠ [] := by
  intro h
  have e := List.flatMap_eq_nil_iff.mp h a (by simp)
  have k := Cancellation.fold_flatten f (σ.apply a)
  rw [e] at k
  cases k

theorem holds_iff (f : sig.ACSym) (σ : Substitution sig) (xs ys : List (Term sig)) :
    Holds f σ xs ys ↔ (xs.flatMap (fun t => Cancellation.flatten f (σ.apply t))).Perm
      (ys.flatMap (fun t => Cancellation.flatten f (σ.apply t))) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
    | cons b bs => exact ⟨False.elim, fun h => parts_ne_nil f σ b bs h.symm.eq_nil⟩
  | cons a as =>
    cases ys with
    | nil => exact ⟨False.elim, fun h => parts_ne_nil f σ a as h.eq_nil⟩
    | cons b bs =>
      rw [← flatten_fold, ← flatten_fold]
      exact ⟨Cancellation.flatten_equiv f, Cancellation.equiv_of_flatten_perm f⟩

/-- Equivalence holds for every sorted substitution and every decoding of
the live IDs into terms, irrespective of the order chosen for either row. -/
theorem run_correct {run} (hc : CommonCancellation.Correct run)
    (decode : UInt64 → Term sig) (f : sig.ACSym) (lhs rhs : Array UInt64) :
    ∃ left right : List UInt64, run lhs rhs = #[left.toArray, right.toArray] ∧
      ∀ σ, Holds f σ (lhs.toList.map decode) (rhs.toList.map decode) ↔
        Holds f σ (left.map decode) (right.map decode) := by
  obtain ⟨common, left, right, hp, hl, hr, _⟩ := hc lhs rhs
  refine ⟨left, right, hp, fun σ => ?_⟩
  let parts := fun t : Term sig => Cancellation.flatten f (σ.apply t)
  have l := (hl.map decode).flatMap_right parts
  have r := (hr.map decode).flatMap_right parts
  simp only [List.map_append, List.flatMap_append] at l r
  rw [holds_iff, holds_iff]
  exact ⟨fun h => (List.perm_append_left_iff _).mp (l.symm.trans (h.trans r)),
    fun h => l.trans ((h.append_left _).trans r.symm)⟩

/-- Equivalent residual conjunctions can drop original variables. Reserve those
variables when solving the residual so a fresh witness cannot capture them.
Then any context-correct complete solver for the residual suffices. -/
theorem lift_complete (p q : Problem sig) (avoid erased : List Variable)
    (answers : List (Substitution sig)) (equivalent : ∀ σ, p.Solves σ ↔ q.Solves σ)
    (included : ∀ v, q.Occurs v → p.Occurs v)
    (reserved : ∀ v, p.Occurs v → ¬ q.Occurs v → v ∈ erased)
    (hc : (Outcome.complete answers).CorrectIn q (erased ++ avoid)) :
    (Outcome.complete answers).CorrectIn p avoid := by
  classical
  constructor
  · constructor
    · intro σ hs; exact (equivalent σ).mpr (hc.mathematical.sound σ hs)
    · intro ρ hρ
      obtain ⟨σ, hs, δ, ha⟩ := hc.mathematical.covers ρ ((equivalent ρ).mp hρ)
      let missing := fun w => p.Occurs w ∧ ¬ q.Occurs w
      let δ' : Substitution sig := {
        image := fun w => if missing w then ρ.image w else δ.image w
        support := ρ.support ++ δ.support
        outside := by
          intro w hw
          split
          · exact ρ.outside w (fun h => hw (List.mem_append_left _ h))
          · exact δ.outside w (fun h => hw (List.mem_append_right _ h))
        sorted := by intro w; split <;> first | exact ρ.sorted w | exact δ.sorted w }
      refine ⟨σ, hs, δ', fun v hv => ?_⟩
      change EquivB (ρ.image v) ((σ.image v).subst δ'.image)
      by_cases hq : q.Occurs v
      · apply (ha v hq).trans
        apply Term.subst_equiv
        intro w hw
        have hn : ¬ missing w := fun h =>
          hc.fresh σ hs v hq w hw h.2 (List.mem_append_left _ (reserved w h.1 h.2))
        simp only [δ', ite_eq_right hn]
        exact .refl _
      · rw [hc.domain σ hs v hq]
        change EquivB (ρ.image v) (if missing v then ρ.image v else δ.image v)
        rw [ite_eq_left (show missing v from ⟨hv, hq⟩)]
        exact .refl _
  · intro σ hs v hv
    exact hc.domain σ hs v (fun h => hv (included v h))
  · intro σ hs v hv w hw hn ha
    by_cases h : q.Occurs v
    · exact hc.fresh σ hs v h w hw (fun hq => hn (included w hq)) (List.mem_append_right _ ha)
    · rw [hc.domain σ hs v h] at hw
      exact hn (hw ▸ hv)

end Tamarin.ACResidual
