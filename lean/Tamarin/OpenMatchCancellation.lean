import Tamarin.CompoundMatching

namespace Tamarin.OpenMatchCancellation
open Cancellation
variable {sig : Signature}

private theorem pieces (f : sig.ACSym) (d : UInt64 → Term sig) (xs : List UInt64)
    (closed : ∀ i ∈ xs, (d i).Ground ∧ flatten f (d i) = [classOf (d i)]) (σ : Substitution sig) :
    (xs.map d).flatMap (fun t => flatten f (σ.apply t)) = xs.map (fun i => classOf (d i)) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    have rigid := closed i (List.mem_cons_self ..)
    simp only [List.map_cons, List.flatMap_cons, rigid.1.apply_eq, rigid.2,
      List.singleton_append, ih (fun j hj => closed j (List.mem_cons_of_mem _ hj))]

/-- Cancel all closed factors before selecting occurrences for the remaining open
patterns. Patterns in the remainder may share variables, split into several AC
factors under substitution, or occur anywhere in the original operand order. -/
def Correct (cancel : Array UInt64 → Array UInt64 → Array (Array UInt64)) : Prop :=
  ∀ {s : Signature} (f : s.ACSym) (d : UInt64 → Term s) (fixed subject : Array UInt64),
    (∀ i ∈ fixed.toList ++ subject.toList, CompoundMatching.FreeGround (d i)) →
    (∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, d i = d j → i = j) →
    ∃ missing rest : List UInt64, cancel fixed subject = #[missing.toArray, rest.toArray] ∧
      ∀ (pattern extra : List (Term s)), pattern.Perm (fixed.toList.map d ++ extra) →
      ∀ σ : Substitution s, ACResidual.Holds f σ pattern (subject.toList.map d) ↔
        missing = [] ∧ ACResidual.Holds f σ extra (rest.map d)

theorem cancel_factors {cancel} (verified : CommonCancellation.Correct cancel) (f : sig.ACSym)
    (d : UInt64 → Term sig) (fixed subject : Array UInt64)
    (closed : ∀ i ∈ fixed.toList ++ subject.toList, (d i).Ground ∧ flatten f (d i) = [classOf (d i)])
    (unique : ∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, EquivB (d i) (d j) → i = j) :
    ∃ missing rest : List UInt64, cancel fixed subject = #[missing.toArray, rest.toArray] ∧
      ∀ (pattern extra : List (Term sig)), pattern.Perm (fixed.toList.map d ++ extra) →
      ∀ σ : Substitution sig, ACResidual.Holds f σ pattern (subject.toList.map d) ↔
        missing = [] ∧ ACResidual.Holds f σ extra (rest.map d) := by
  obtain ⟨common,l,r,out,hl,hr,apart⟩ := verified fixed subject
  refine ⟨l,r,out,?_⟩
  intro pat extra perm σ
  let part := fun t : Term sig => flatten f (σ.apply t)
  let cls := fun i => classOf (d i)
  have cf (i) (hi : i ∈ fixed.toList) := closed i (List.mem_append_left subject.toList hi)
  have cs (i) (hi : i ∈ subject.toList) := closed i (List.mem_append_right fixed.toList hi)
  have liveL (i) (hi : i ∈ l) := hl.mem_iff.mpr (List.mem_append_right common hi)
  have liveR (j) (hj : j ∈ r) := hr.mem_iff.mpr (List.mem_append_right common hj)
  have tailP : ((fixed.toList.map d).flatMap part).Perm (common.map cls ++ l.map cls) := by
    simpa only [part,pieces f d fixed.toList cf σ,List.map_append] using (hl.map cls :
      (fixed.toList.map cls).Perm ((common ++ l).map cls))
  have left : (pat.flatMap part).Perm (common.map cls ++ (l.map cls ++ extra.flatMap part)) := by
    have p := perm.flatMap_right part
    rw [List.flatMap_append] at p
    simpa only [List.append_assoc] using p.trans (tailP.append_right _)
  have right : ((subject.toList.map d).flatMap part).Perm (common.map cls ++ r.map cls) := by
    rw [show (subject.toList.map d).flatMap part = subject.toList.map cls from pieces f d _ cs σ]
    simpa only [List.map_append] using hr.map cls
  rw [ACResidual.holds_iff, ACResidual.holds_iff]
  change (pat.flatMap part).Perm _ ↔ l = [] ∧ _
  rw [pieces f d r (fun i h => cs i (liveR i h)) σ]
  constructor
  · intro whole
    have residual := (List.perm_append_left_iff _).mp (left.symm.trans (whole.trans right))
    have noLeft : l = [] := by
      cases l with
      | nil => rfl
      | cons i is =>
        have hi := liveL i (List.mem_cons_self ..)
        have found := residual.mem_iff.mp (List.mem_append_left _ (List.mem_map_of_mem (f := cls) (List.mem_cons_self ..)))
        obtain ⟨j,hj,eq⟩ := List.mem_map.mp found
        have id := unique i hi j (liveR _ hj) (Quotient.exact eq.symm)
        exact False.elim (apart i (List.mem_cons_self ..) (id ▸ hj))
    exact ⟨noLeft, by simpa [noLeft,part] using residual⟩
  · rintro ⟨rfl,tail⟩
    exact left.trans ((tail.append_left _).trans right.symm)

theorem correct {cancel} (verified : CommonCancellation.Correct cancel) : Correct cancel := by
  intro s f d fixed subject closed unique
  exact cancel_factors verified f d fixed subject (fun i hi => ⟨(closed i hi).ground,(closed i hi).factor f⟩)
    (fun i hi j hj he => unique i hi j hj ((closed i (List.mem_append_left _ hi)).rigid _ he))

end Tamarin.OpenMatchCancellation
