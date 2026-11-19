import Tamarin.OpenMatch
import Tamarin.MatchPrefilter

/-! At an AC root, a nonvariable factor retains its head after matching.
Buckets of subject factors at one head give necessary occurrence counts
and force ordinary child matches when only one candidate exists. -/
namespace Tamarin.Matching.Prefilter
open Rewriting.ConstructorVariants Cancellation
variable {s : Signature}

private def classHead : Class s → Head s :=
  Quotient.lift head fun _ _ eq => EquivB.head_eq eq

private theorem atom_layout {f : s.ACSym} {t : Term s} (h : head t ≠ .ac f) :
    flatten f t = [classOf t] := by
  cases t with
  | ac g a b =>
    have ne : f ≠ g := fun eq => h (congrArg Head.ac eq.symm)
    simp [flatten, ne]
  | _ => rfl

private theorem rigid_head {h : Head s} {p : Term s} (nonvar : ∀ v, h ≠ .var v)
    (hp : head p = h) (σ : Substitution s) : head (σ.apply p) = h := by
  cases p with
  | var v => exact False.elim (nonvar v hp.symm)
  | _ => exact hp

private theorem map_singletons {α β} (xs : List α) (g : α → List β) (v : α → β)
    (one : ∀ x ∈ xs, g x = [v x]) : xs.flatMap g = xs.map v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [one x (by simp), ih (fun t h => one t (by simp [h]))]

/-- Each pattern occurrence in a fixed-head bucket consumes one distinct
subject occurrence. The other pattern factors can consume further occurrences
in this bucket, including when an open collector expands under substitution. -/
theorem rigid_bucket_count {f : s.ACSym} {ps ts : List (Term s)}
    {σ : Substitution s} (hit : OpenMatch.Holds f ps ts σ)
    (flat : ∀ t ∈ ts, head t ≠ .ac f)
    (h : Head s) (rigid : ∀ v, h ≠ .var v) (apart : h ≠ .ac f)
    (atHead : Term s → Bool) (check : ∀ t, atHead t = true ↔ head t = h) :
    ps.countP atHead ≤ ts.countP atHead := by
  classical
  let isHead := fun c : Class s => decide (classHead c = h)
  let part := fun p : Term s => flatten f (σ.apply p)
  have occ : ∀ xs : List (Term s), xs.countP atHead ≤ (xs.flatMap part).countP isHead := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.countP_append,List.countP_cons]
      split
      next yes =>
        have same := rigid_head rigid ((check x).mp yes) σ
        have one : (part x).countP isHead = 1 := by
          rw [show part x = [classOf (σ.apply x)] from atom_layout (fun eq => apart (same.symm.trans eq))]
          have yes : isHead (classOf (σ.apply x)) = true := by
            change decide (head (σ.apply x) = h) = true
            exact decide_eq_true same
          simp [yes]
        omega
      next no => omega
  have perm := (OpenMatch.holds_iff ..).mp hit
  rw [map_singletons ts (flatten f) classOf (fun t ht => atom_layout (flat t ht))] at perm
  have eq := List.Perm.countP_eq isHead perm
  rw [List.countP_map] at eq
  have proj : isHead ∘ classOf = atHead := by
    funext t
    change decide (head t = h) = atHead t
    cases hv : atHead t
    · apply decide_eq_false; intro he; have := (check t).mpr he; simp_all
    · exact decide_eq_true ((check t).mp hv)
  rw [proj] at eq
  exact eq ▸ occ ps

/-- A sole subject factor with the required head must satisfy the pattern
factor under the same substitution used for the whole AC equation. -/
theorem rigid_bucket_unique {f : s.ACSym} {ps ts : List (Term s)}
    {σ : Substitution s} (hit : OpenMatch.Holds f ps ts σ) (flat : ∀ t ∈ ts, head t ≠ .ac f)
    {p candidate : Term s} (hp : p ∈ ps) (nonvar : ∀ v, head p ≠ .var v)
    (apart : head p ≠ .ac f) (unique : ∀ t ∈ ts, head t = head p → t = candidate) :
    EquivB (σ.apply p) candidate := by
  have same := rigid_head nonvar rfl σ
  have occurs : classOf (σ.apply p) ∈ ps.flatMap (fun t => flatten f (σ.apply t)) := by
    apply List.mem_flatMap.mpr
    exact ⟨p,hp,by rw [atom_layout (fun e => apart (same.symm.trans e))]; simp⟩
  have perm := (OpenMatch.holds_iff ..).mp hit
  rw [map_singletons ts (flatten f) classOf (fun t ht => atom_layout (flat t ht))] at perm
  obtain ⟨t,ht,e⟩ := List.mem_map.mp (perm.mem_iff.mp occurs)
  have eq : EquivB (σ.apply p) t := Quotient.exact e.symm
  exact unique t ht (eq.head_eq.symm.trans same) ▸ eq

/-- A comparison can alternate free argument positions and forced AC
occurrences at any depth before discovering a binding. -/
inductive Forced [DecidableEq s.ACSym] (q : Problem s) : Equation s → Prop where
  | origin {e} : ConjunctRefutation.Part q e → Forced q e
  | free {f : s.FreeSym} {xs ys : Fin (s.arity f) → Term s}
      (i : Fin (s.arity f)) : Forced q ⟨.free f xs,.free f ys⟩ → Forced q ⟨xs i,ys i⟩
  | ac {f : s.ACSym} {a b p t : Term s} {ps ts : List (Term s)} :
      Forced q ⟨a,b⟩ → ps.Perm (ACRepresentation.flatten f a) →
      ts.Perm (ACRepresentation.flatten f b) → (∀ x ∈ ts, head x ≠ .ac f) →
      p ∈ ps → (∀ v, head p ≠ .var v) → head p ≠ .ac f →
      (∀ x ∈ ts, head x = head p → x = t) → Forced q ⟨p,t⟩

theorem Forced.matches [DecidableEq s.ACSym] {q : Problem s} {e : Equation s}
    (forced : Forced q e) {σ : Substitution s} (hit : Matches q σ) :
    EquivB (σ.apply e.lhs) e.rhs := by
  induction forced with
  | origin part => exact part_matches part hit
  | free i _ ih => exact (free_equiv_iff ..).mp ih i
  | ac _ pl sl flat hp nonvar apart unique ih =>
    exact rigid_bucket_unique ((OpenMatch.layout_iff _ _ _ _ _ _ pl sl).mp ih) flat hp nonvar apart unique

/-- These implied equations can seed a continuation through the ordinary
capture contract even if the dynamic search retains the whole parent AC
equation and discards nested duplicates. The solution set stays identical. -/
theorem force_equations [DecidableEq s.ACSym] (q derived : Problem s)
    (cert : ∀ e ∈ derived, Forced q e) (σ : Substitution s) :
    Matches (q ++ derived) σ ↔ Matches q σ := by
  constructor
  · exact fun h e he => h _ (List.mem_append_left _ he)
  · intro h e he
    rcases List.mem_append.mp he with l|r
    · exact h _ l
    · exact (cert _ r).matches h

end Tamarin.Matching.Prefilter
