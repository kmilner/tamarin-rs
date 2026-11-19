import Tamarin.CollectorMultiplicity
import Tamarin.OpenMatch

/-! A necessary multiplicity condition for directional matching under AC.
The subject is kept fixed, even when a subject factor contains variables. -/
namespace Tamarin.CollectorMultiplicity
open Cancellation Classical
variable {sig : Signature}

private theorem count_images {α β : Type} [DecidableEq α] [DecidableEq β] (images : α → List β)
    (i : α) (k : β) (hit : k ∈ images i) (occ : List α) :
    occ.count i ≤ (occ.flatMap images).count k := by
  induction occ with
  | nil => simp
  | cons a as ih =>
    rw [List.flatMap_cons,List.count_append]
    by_cases e : a = i
    · subst a
      rw [List.count_cons_self]
      have h := List.count_pos_iff.mpr hit
      omega
    · rw [List.count_cons_of_ne e]
      omega

/-- Every single factor of the captured image contributes at least one copy
per occurrence of the collector. Other pattern factors can add further copies. -/
theorem factor_bound {α : Type} [DecidableEq α] (f : sig.ACSym) (keys : α → Variable)
    (occ : List α) (extra pattern subject : List (Term sig))
    (layout : pattern.Perm (extra ++ occ.map (fun j => Term.var (keys j))))
    (σ : Substitution sig) (sol : OpenMatch.Holds f pattern subject σ)
    (i : α) (k : Class sig) (hit : k ∈ flatten f (σ.image (keys i))) :
    occ.count i ≤ (subject.flatMap (flatten f)).count k := by
  classical
  let image := fun t : Term sig => flatten f (σ.apply t)
  have perm := (layout.flatMap_right image).symm.trans ((OpenMatch.holds_iff ..).mp sol)
  rw [← perm.count_eq k,List.flatMap_append,List.count_append]
  apply Nat.le_add_left_of_le
  simpa [image,List.flatMap_map,Substitution.apply,Term.subst] using count_images (fun j => flatten f (σ.image (keys j))) i k hit occ

private theorem count_id {α β : Type} [DecidableEq α] [DecidableEq β]
    (ids : List α) (toClass : α → β) (j : α)
    (reflects : ∀ i ∈ ids, toClass i = toClass j → i = j) :
    (ids.map toClass).count (toClass j) = ids.count j := by
  induction ids with
  | nil => simp
  | cons i is ih =>
    have tail := ih (fun a ha => reflects a (List.mem_cons_of_mem _ ha))
    rw [List.map_cons]
    by_cases e : i = j
    · subst i
      simp [tail]
    · have ne : toClass i ≠ toClass j := fun h => e (reflects i List.mem_cons_self h)
      rw [List.count_cons_of_ne ne,List.count_cons_of_ne e,tail]

/-- An interner may assign any words and the input arrays can use any order.
Only live subject factors need to reflect equality of structural classes. The
additional patterns may remain unassigned, so the same test is valid before
selecting rigid occurrences or after selection on the exact remainder. -/
theorem possible_of_match (f : sig.ACSym) (keys : UInt64 → Variable) (d : UInt64 → Term sig)
    (occ rhs : List UInt64) (extra pattern subject : List (Term sig))
    (pl : pattern.Perm (extra ++ occ.map (fun i => Term.var (keys i))))
    (sl : subject.Perm (rhs.map d))
    (atom : ∀ i ∈ rhs, flatten f (d i) = [classOf (d i)])
    (reflects : ∀ i ∈ rhs, ∀ j ∈ rhs, EquivB (d i) (d j) → i = j)
    (σ : Substitution sig) (sol : OpenMatch.Holds f pattern subject σ) :
    Possible occ rhs := by
  classical
  let cls := fun i => classOf (d i)
  have factors : (rhs.map d).flatMap (flatten f) = rhs.map cls := by
    simp only [List.flatMap_map]
    rw [List.map_eq_flatMap,List.flatMap_def,List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun i hi => atom i hi)
  intro i hi
  obtain ⟨k,hk⟩ : ∃ k, k ∈ flatten f (σ.image (keys i)) := by
    cases h : flatten f (σ.image (keys i)) with
    | cons k ks => exact ⟨k,List.mem_cons_self⟩
    | nil =>
      have e := fold_flatten f (σ.image (keys i))
      rw [h] at e; cases e
  have bound := factor_bound f keys occ extra pattern subject pl σ sol i k hk
  rw [(sl.flatMap_right (flatten f)).count_eq k,factors] at bound
  have pos := List.count_pos_iff.mpr hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp (Nat.lt_of_lt_of_le pos bound))
  refine ⟨j,hj,?_⟩
  rwa [count_id rhs cls j (fun b hb e => reflects b hb j hj (Quotient.exact e))] at bound

/-- A negative kernel answer refutes the entire residual branch, independently
of earlier bindings or the order in which the remaining patterns are solved. -/
theorem refutes {test : Kernel} (verified : Correct test) (f : sig.ACSym)
    (keys : UInt64 → Variable) (d : UInt64 → Term sig) (occ rhs : Array UInt64)
    (extra pattern subject : List (Term sig))
    (pl : pattern.Perm (extra ++ occ.toList.map (fun i => Term.var (keys i))))
    (sl : subject.Perm (rhs.toList.map d))
    (atom : ∀ i ∈ rhs.toList, flatten f (d i) = [classOf (d i)])
    (reflects : ∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, EquivB (d i) (d j) → i = j)
    (rejected : test occ rhs = false) (σ : Substitution sig) : ¬ OpenMatch.Holds f pattern subject σ := by
  intro sol
  have accepted := (verified occ rhs).mpr (possible_of_match f keys d _ _ extra pattern subject pl sl atom reflects σ sol)
  simp [rejected] at accepted

/-- The public contract for a branch guard. A candidate may reject any
impossible exact residual and must detect the multiplicity failures. Passing a
residual delegates its solution to the ordinary matcher. -/
structure Admissible (test : Kernel) : Prop where
  sound : ∀ {s : Signature} (f : s.ACSym) (keys : UInt64 → Variable) (d : UInt64 → Term s)
    (occ rhs : Array UInt64) (pattern subject : List (Term s)),
    pattern.Perm (occ.toList.map (fun i => Term.var (keys i))) →
    subject.Perm (rhs.toList.map d) →
    (∀ i ∈ rhs.toList, flatten f (d i) = [classOf (d i)]) →
    (∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, EquivB (d i) (d j) → i = j) →
    test occ rhs = false → ∀ σ : Substitution s, ¬ OpenMatch.Holds f pattern subject σ
  rejects : ∀ occ rhs, ¬ Possible occ.toList rhs.toList → test occ rhs = false

theorem of_correct {test : Kernel} (verified : Correct test) : Admissible test where
  sound f keys d occ rhs pattern subject pl sl atom reflects rejected σ :=
    refutes verified f keys d occ rhs [] pattern subject pl sl atom reflects rejected σ
  rejects occ rhs rejected := by
    cases eq : test occ rhs with
    | false => rfl
    | true => exact False.elim (rejected ((verified occ rhs).mp eq))

/-- At an exact residual AC node the same certificate rules out every
matching substitution, for every order and association of its operands. -/
theorem refutes_term {test : Kernel} (verified : Admissible test) [DecidableEq sig.ACSym]
    (f : sig.ACSym) (keys : UInt64 → Variable) (d : UInt64 → Term sig) (occ rhs : Array UInt64)
    (p t : Term sig)
    (pl : (occ.toList.map (fun i => Term.var (keys i))).Perm (ACRepresentation.flatten f p))
    (sl : (rhs.toList.map d).Perm (ACRepresentation.flatten f t))
    (atom : ∀ i ∈ rhs.toList, flatten f (d i) = [classOf (d i)])
    (reflects : ∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, EquivB (d i) (d j) → i = j)
    (rejected : test occ rhs = false) (σ : Substitution sig) : ¬ EquivB (σ.apply p) t := by
  intro eq
  exact verified.sound f keys d occ rhs _ _ (.refl _) (.refl _) atom reflects rejected σ
    ((OpenMatch.layout_iff f σ p t _ _ pl sl).mp eq)

end Tamarin.CollectorMultiplicity
