import Tamarin.ACResidual
import Tamarin.MatchingFree
import Tamarin.GroundACEquality

/-! Matching x + tail against ground AC children. Each ID denotes a full
term. The residual argument only needs single factors with distinguishable
B-classes, so additional ground term representations can use the same kernel. -/
namespace Tamarin.CompoundMatching
variable {sig : Signature}

/-- A closed tree of free symbols and literals is rigid under B, including
when the signature also contains C and AC operators. -/
inductive FreeGround : Term sig → Prop where
  | atom (a : sig.Atom) : FreeGround (.atom a)
  | free (f : sig.FreeSym) {args} (children : ∀ i, FreeGround (args i)) : FreeGround (.free f args)

theorem FreeGround.ground {t : Term sig} (h : FreeGround t) : t.Ground := by
  induction h with
  | atom => intro v; exact id
  | free _ _ ih => intro v ⟨i, hi⟩; exact ih i v hi

theorem FreeGround.rigid {t : Term sig} (h : FreeGround t) (u : Term sig) (he : EquivB t u) :
    t = u := by
  induction h generalizing u with
  | atom a =>
    cases u <;> cases he.head_eq
    rfl
  | free f ha ih =>
    cases u <;> cases he.head_eq
    rename_i args
    congr
    funext i
    exact ih i _ ((Matching.free_equiv_iff _ _ _).mp he i)

theorem FreeGround.factor {t : Term sig} (h : FreeGround t) (f : sig.ACSym) :
    Cancellation.flatten f t = [Cancellation.classOf t] := by cases h <;> rfl

theorem fold_ground (f : sig.ACSym) (a : Term sig) (xs : List (Term sig))
    (hg : ∀ t ∈ a :: xs, t.Ground) : (ACRepresentation.fold f a xs).Ground := by
  induction xs generalizing a with
  | nil => exact hg a (by simp)
  | cons b bs ih =>
    intro v hv
    exact hv.elim (hg a (by simp) v) (ih b (fun t ht => hg t (.tail _ ht)) v)

private theorem residual_iff (f : sig.ACSym) (v : Variable) (σ : Substitution sig)
    (d : UInt64 → Term sig) (l r : List UInt64)
    (ground : ∀ i ∈ l ++ r, (d i).Ground)
    (factor : ∀ i ∈ l ++ r, Cancellation.flatten f (d i) = [Cancellation.classOf (d i)])
    (apart : ∀ i ∈ l, ∀ j ∈ r, ¬ EquivB (d i) (d j)) :
    ACResidual.Holds f σ (.var v :: l.map d) (r.map d) ↔
      l = [] ∧ ∃ t, ACRepresentation.decode f (r.map d) = some t ∧ EquivB (σ.image v) t := by
  cases l with
  | nil =>
    cases r with
    | nil => simp [ACResidual.Holds, ACRepresentation.decode]
    | cons j js =>
      have hg : (ACRepresentation.fold f (d j) (js.map d)).Ground := by
        apply fold_ground
        intro t ht
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (show t ∈ (j :: js).map d from ht)
        exact ground i (by simpa using hi)
      simp [ACResidual.Holds, ACRepresentation.decode, ACRepresentation.fold, hg.apply_eq]
      rfl
  | cons i is =>
    simp only [List.cons_ne_nil, false_and, iff_false]
    intro h
    have perm := (ACResidual.holds_iff ..).mp h
    let cls := Cancellation.classOf (d i)
    have hp (j) (hj : j ∈ (i :: is) ++ r) :
        Cancellation.flatten f (σ.apply (d j)) = [Cancellation.classOf (d j)] := by
      rw [(ground j hj).apply_eq, factor j hj]
    have hm : cls ∈ ((Term.var v :: (i :: is).map d).flatMap
        (fun t => Cancellation.flatten f (σ.apply t))) := by
      apply List.mem_flatMap.mpr
      exact ⟨d i, by simp, by simp [hp i (by simp), cls]⟩
    obtain ⟨t, ht, hh⟩ := List.mem_flatMap.mp (perm.mem_iff.mp hm)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    rw [hp j (List.mem_append_right _ hj), List.mem_singleton] at hh
    exact apart i (by simp) j hj (Quotient.exact hh)

/-- A shared live-word interner only needs to reflect B-equivalence on the
input. Orders and representative choices in the two output rows are free. -/
theorem run_correct {run} (hc : CommonCancellation.Correct run) (f : sig.ACSym)
    (v : Variable) (d : UInt64 → Term sig) (tail subject : Array UInt64)
    (ground : ∀ i ∈ tail.toList ++ subject.toList, (d i).Ground)
    (factor : ∀ i ∈ tail.toList ++ subject.toList,
      Cancellation.flatten f (d i) = [Cancellation.classOf (d i)])
    (reflects : ∀ i ∈ tail.toList, ∀ j ∈ subject.toList, EquivB (d i) (d j) → i = j) :
    ∃ l r : List UInt64, run tail subject = #[l.toArray, r.toArray] ∧
      ∀ σ, ACResidual.Holds f σ (.var v :: tail.toList.map d) (subject.toList.map d) ↔
        l = [] ∧ ∃ t, ACRepresentation.decode f (r.map d) = some t ∧ EquivB (σ.image v) t := by
  obtain ⟨common, l, r, packet, hl, hr, disj⟩ := hc tail subject
  have left i (hi : i ∈ l) := hl.mem_iff.mpr (List.mem_append_right _ hi)
  have right i (hi : i ∈ r) := hr.mem_iff.mpr (List.mem_append_right _ hi)
  have live i (hi : i ∈ l ++ r) : i ∈ tail.toList ++ subject.toList := by
    rcases List.mem_append.mp hi with h | h
    · exact List.mem_append_left _ (left i h)
    · exact List.mem_append_right _ (right i h)
  refine ⟨l, r, packet, fun σ => ?_⟩
  rw [← residual_iff f v σ d l r (fun i hi => ground i (live i hi))
    (fun i hi => factor i (live i hi))
    (fun i hi j hj he => disj i hi ((reflects i (left i hi) j (right j hj) he) ▸ hj))]
  rw [ACResidual.holds_iff, ACResidual.holds_iff]
  let parts := fun t : Term sig => Cancellation.flatten f (σ.apply t)
  have a := (hl.map d).flatMap_right parts
  have b := (hr.map d).flatMap_right parts
  simp only [List.map_append, List.flatMap_append] at a b
  let x := parts (.var v)
  change (x ++ _).Perm _ ↔ (x ++ _).Perm _
  have rearrange := (a.append_left x).trans
    ((List.perm_append_comm (l₁ := x) (l₂ := (common.map d).flatMap parts)).append_right
      ((l.map d).flatMap parts) |> fun h => by simpa [List.append_assoc] using h)
  exact ⟨fun h => (List.perm_append_left_iff _).mp (rearrange.symm.trans (h.trans b)),
    fun h => rearrange.trans ((h.append_left _).trans b.symm)⟩

/-- The decoder may return an empty set for a missing factor, an empty
remainder, or an incompatible variable sort. A sorted forced image yields
exactly one matcher on the original observed variable. -/
def AnswersCorrect (p : Problem sig) (v : Variable) : Option (Term sig) → Prop
  | none => Matching.Complete p (fun _ => True) []
  | some t =>
      (∀ hs : HasSort t v.sort, Matching.Complete p (fun _ => True) [Substitution.binding v t hs]) ∧
      (¬ Subsort t.rootSort v.sort → Matching.Complete p (fun _ => True) [])

private theorem forced_complete (p : Problem sig) (v : Variable) (out : Option (Term sig))
    (obs : ∀ w, Matching.Observed p w ↔ w = v)
    (forced : ∀ σ, Matching.Matches p σ ↔ ∃ t, out = some t ∧ EquivB (σ.image v) t) :
    AnswersCorrect p v out := by
  cases out with
  | none =>
    apply (Matching.empty_iff ..).mpr
    rintro ⟨σ, hm, _⟩
    obtain ⟨_, h, _⟩ := (forced σ).mp hm
    cases h
  | some t =>
    constructor
    · intro hs
      constructor
      · intro σ hm; obtain rfl := List.mem_singleton.mp hm
        constructor
        · apply (forced _).mpr
          exact ⟨t, rfl, by rw [Substitution.binding_image_self]; exact .refl _⟩
        · intro w hw
          exact Substitution.binding_image_other _ _ _ _ (fun e => hw ⟨(obs w).mpr e, trivial⟩)
      · intro ρ hm _
        obtain ⟨_, he, hi⟩ := (forced ρ).mp hm
        cases he
        refine ⟨_, List.mem_singleton_self _, fun w hw => ?_⟩
        obtain rfl := (obs w).mp hw
        simpa using hi
    · intro wrong; apply (Matching.empty_iff ..).mpr
      rintro ⟨σ, hm, _⟩
      obtain ⟨_, he, hi⟩ := (forced σ).mp hm
      cases he
      exact wrong ((Term.rootSort_equiv hi) ▸ Term.rootSort_le (σ.sorted v))

theorem matching_correct {run} (hc : CommonCancellation.Correct run) (f : sig.ACSym)
    (v : Variable) (d : UInt64 → Term sig) (tail subject : Array UInt64) (s : Term sig)
    (decodeSubject : ACRepresentation.decode f (subject.toList.map d) = some s)
    (free : ∀ i ∈ tail.toList ++ subject.toList, FreeGround (d i))
    (unique : ∀ i ∈ tail.toList, ∀ j ∈ subject.toList, d i = d j → i = j) :
    ∃ l r : List UInt64, run tail subject = #[l.toArray, r.toArray] ∧
      AnswersCorrect [⟨ACRepresentation.fold f (.var v) (tail.toList.map d), s⟩] v
        (if l = [] then ACRepresentation.decode f (r.map d) else none) := by
  obtain ⟨l, r, hp, he⟩ := run_correct hc f v d tail subject
    (fun i hi => (free i hi).ground) (fun i hi => (free i hi).factor f)
    (fun i hi j hj eq => unique i hi j hj ((free i (List.mem_append_left _ hi)).rigid _ eq))
  have groundTail (t) (ht : t ∈ tail.toList.map d) : t.Ground := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact (free _ (List.mem_append_left _ hi)).ground
  have gs : s.Ground := by
    generalize hx : subject.toList.map d = terms at decodeSubject
    cases terms with
    | nil => cases decodeSubject
    | cons a xs =>
      obtain rfl := Option.some.inj decodeSubject
      apply fold_ground
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hx ▸ ht : t ∈ subject.toList.map d)
      exact (free i (List.mem_append_right _ hi)).ground
  refine ⟨l, r, hp, forced_complete _ v _ ?_ ?_⟩
  · intro w
    simp only [Matching.Observed, List.mem_singleton, exists_eq_left]
    cases hx : tail.toList.map d with
    | nil => rfl
    | cons a as =>
      have hg := fold_ground f a as (fun t ht => groundTail t (hx ▸ ht))
      exact ⟨fun h => h.elim id (False.elim ∘ hg w), Or.inl⟩
  · intro σ
    have hh := he σ
    unfold ACResidual.Holds at hh
    rw [decodeSubject] at hh
    change EquivB _ (σ.apply s) ↔ _ at hh
    rw [gs.apply_eq] at hh
    simp only [Matching.Matches, List.mem_singleton, forall_eq]
    rw [hh]
    by_cases hn : l = [] <;> simp [hn]

end Tamarin.CompoundMatching
