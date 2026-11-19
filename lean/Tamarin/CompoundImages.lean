import Tamarin.CompoundMatching

/-! Equality used to reconcile bindings across different ground matching leaves. -/
namespace Tamarin.CompoundImages
open CompoundMatching
variable {sig : Signature}

private noncomputable def representative (c : Cancellation.Class sig) : Term sig :=
  (Quotient.exists_rep c).choose

private theorem recover (t : Term sig) (rigid : FreeGround t) :
    representative (Cancellation.classOf t) = t :=
  (rigid.rigid _ (Quotient.exact (Quotient.exists_rep (Cancellation.classOf t)).choose_spec.symm)).symm

private theorem parts (f : sig.ACSym) (ts : List (Term sig))
    (h : ∀ t ∈ ts, FreeGround t) :
    ts.flatMap (fun t => Cancellation.flatten f (Substitution.identity.apply t)) =
      ts.map Cancellation.classOf := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, Substitution.apply_identity, List.map_cons]
    rw [(h t (.head _)).factor, ← ih (fun u hu => h u (.tail _ hu))]
    simp [Substitution.apply_identity]

/-- At a shared AC head it suffices to count *full closed free terms*. Even in a
signature containing other C/AC symbols, distinct such factors cannot coalesce. -/
theorem product_iff (f : sig.ACSym) (a b : Term sig) (xs ys : List (Term sig))
    (l : ∀ t ∈ a::xs, FreeGround t) (r : ∀ t ∈ b::ys, FreeGround t) :
    EquivB (ACRepresentation.fold f a xs) (ACRepresentation.fold f b ys) ↔ (a::xs).Perm (b::ys) := by
  have h := ACResidual.holds_iff f (Substitution.identity (sig := sig)) (a::xs) (b::ys)
  rw [parts f _ l, parts f _ r] at h
  simp only [ACResidual.Holds, ACRepresentation.decode, Substitution.apply_identity] at h
  refine h.trans ⟨?_, fun hp => hp.map Cancellation.classOf⟩
  intro hp
  have back (ts : List (Term sig)) (free : ∀ t ∈ ts, FreeGround t) :
      (ts.map Cancellation.classOf).map representative = ts := by
    rw [List.map_map]
    exact (List.map_congr_left (g := id) (fun t ht => recover t (free t ht))).trans (List.map_id _)
  simpa only [back _ l, back _ r] using hp.map representative

end Tamarin.CompoundImages
