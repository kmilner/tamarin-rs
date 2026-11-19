import Tamarin.ACUnifierExclusion
import Tamarin.ConjunctRefutation
import Tamarin.RigidSubject

/-! Necessary rigid-subject checks for the one simultaneous match used by
variant row subsumption. Free argument positions determine captures. C and
AC positions retain their ordinary matching semantics. -/
namespace Tamarin.Matching.Prefilter
open ConjunctRefutation
variable {s : Signature}

def rigidSize : Term s → Nat
  | .var _ => 0
  | .atom _ => 1
  | .free _ args => (List.ofFn fun i => rigidSize (args i)).sum + 1
  | .comm _ a b | .ac _ a b => rigidSize a + rigidSize b + 1

theorem size_equiv {a b : Term s} (eq : EquivB a b) : rigidSize a = rigidSize b := by
  induction eq with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free _ _ _ _ ih => simp only [rigidSize,ih]
  | comm_congr _ _ _ ih ik | ac_congr _ _ _ ih ik => simp only [rigidSize,ih,ik]
  | comm_swap | ac_swap | ac_assoc => simp only [rigidSize]; omega

private theorem sum_mono {n : Nat} (a b : Fin n → Nat) (le : ∀ i, a i ≤ b i) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (le 0) (ih _ _ (fun i => le i.succ))

theorem size_subst (σ : Substitution s) (t : Term s) : rigidSize t ≤ rigidSize (σ.apply t) := by
  induction t with
  | var => exact Nat.zero_le _
  | atom => exact Nat.le_refl _
  | free f xs ih => exact Nat.succ_le_succ (sum_mono _ _ ih)
  | ac f a b ia ib | comm f a b ia ib => exact Nat.succ_le_succ (Nat.add_le_add ia ib)

/-- The array representation charges one rigid symbol for every binary AC
node. Rebracketing, sorting and flattening preserve this size. -/
theorem size_fold (f : s.ACSym) (a : Term s) (ts : List (Term s)) :
    rigidSize (ACRepresentation.fold f a ts) = rigidSize a + (ts.map rigidSize).sum + ts.length := by
  induction ts generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih => simp only [ACRepresentation.fold,rigidSize,ih,List.map_cons,List.sum_cons,List.length_cons]; omega

/-- Saturating every addition counts the minimum of the true size and the
machine bound, so saturation cannot introduce a spurious refutation. -/
theorem saturating_add (limit a b : Nat) :
    min (min a limit + min b limit) limit = min (a+b) limit := by omega

theorem size_match {p t : Term s} {σ : Substitution s} (matched : EquivB (σ.apply p) t) (limit : Nat) :
    min (rigidSize p) limit ≤ min (rigidSize t) limit := by
  have h := size_subst σ p
  rw [size_equiv matched] at h
  omega

/-- The directional analogue of Part.solves: only the pattern is instantiated,
even if a variable identity occurs both in a pattern and in a subject. -/
theorem part_matches {q : Problem s} {e : Equation s} (part : Part q e) {σ : Substitution s}
    (hit : Matches q σ) : EquivB (σ.apply e.lhs) e.rhs := by
  induction part with
  | member mem => exact hit _ mem
  | child i _ ih => exact (Matching.free_equiv_iff ..).mp ih i

theorem capture_sort {q : Problem s} {v t} (part : Part q ⟨.var v,t⟩)
    {σ : Substitution s} (hit : Matches q σ) : Subsort t.rootSort v.sort := by
  have eq : EquivB (σ.image v) t := part_matches part hit
  apply Term.rootSort_le
  apply Term.checkSort_sound
  rw [←SortClash.check_equiv eq]
  exact Term.checkSort_complete (σ.sorted v)

theorem repeated_capture {q : Problem s} {v a b} (first : Part q ⟨.var v,a⟩)
    (second : Part q ⟨.var v,b⟩) {σ : Substitution s} (hit : Matches q σ) : EquivB a b :=
  (part_matches first hit).symm.trans (part_matches second hit)

/-- The compared representatives include rigid subject variables. Freezing
those occurrences gives ground canonical trees, so structural equality
decides B-equivalence even for forced images containing open C/AC terms. -/
theorem canonical_eq_iff {a b : Term s} {le : Term (RigidSubject.frozenSig s) → Term (RigidSubject.frozenSig s) → Prop}
    (anti : ∀ x y, le x y → le y x → x = y)
    (ha : CanonicalTree.Canonical le (RigidSubject.freeze s a))
    (hb : CanonicalTree.Canonical le (RigidSubject.freeze s b)) : EquivB a b ↔ a = b :=
  ⟨fun h => RigidSubject.freeze_inj s (ha.unique anti hb (RigidSubject.freeze_equiv s h)),
   fun h => h ▸ .refl _⟩

/-- A determined obligation can be compared under the seed alone. Open
images are used simultaneously, so their own variables are never rebound. -/
theorem determined {q : Problem s} {p : Term s} {seed σ : Substitution s}
    (seedFits : Matches q seed) (hit : Matches q σ)
    (all : ∀ v, p.Occurs v → ∃ t, Part q ⟨.var v,t⟩) :
    EquivB (σ.apply p) (seed.apply p) := by
  apply Term.subst_equiv
  intro v hv
  obtain ⟨t,part⟩ := all v hv
  exact (part_matches part hit).trans (part_matches part seedFits).symm

/-- The remaining matcher can carry a single seed as a table of bindings.
Agreement on its observed variables expresses all the captured equations. -/
theorem matches_seed_iff (caps : Problem s) {seed σ : Substitution s}
    (seedFits : Matches caps seed)
    (forced : ∀ v, Observed caps v → ∃ t, Part caps ⟨.var v,t⟩) :
    Matches caps σ ↔ Substitution.AgreesOn (Observed caps) σ seed := by
  constructor
  · intro hit v seen
    obtain ⟨t,part⟩ := forced v seen
    exact (part_matches part hit).trans (part_matches part seedFits).symm
  · exact matches_of_agrees seedFits

/-- Keep the forced bindings alive in every remaining search branch. A
completed match comprises the same seed assignments, all determined checks,
and a simultaneous solution to the pending equations. -/
theorem discharge (caps known pending : Problem s) (seed : Substitution s)
    (seedFits : Matches caps seed)
    (closed : ∀ e ∈ known, ∀ v, e.lhs.Occurs v → ∃ t, Part caps ⟨.var v,t⟩) :
    (∃ σ, Matches (caps ++ known ++ pending) σ) ↔
      Matches known seed ∧ ∃ σ, Matches caps σ ∧ Matches pending σ := by
  have split (qs rs : Problem s) (σ : Substitution s) :
      Matches (qs ++ rs) σ ↔ Matches qs σ ∧ Matches rs σ := by
    simp only [Matches,List.mem_append,or_imp,forall_and]
  constructor
  · rintro ⟨σ,matchAll⟩
    obtain ⟨both,rest⟩ := (split _ _ _).mp matchAll
    obtain ⟨fixed,done⟩ := (split _ _ _).mp both
    refine ⟨fun e he => ?_,σ,fixed,rest⟩
    exact (determined seedFits fixed (closed e he)).symm.trans (done e he)
  · rintro ⟨done,σ,fixed,rest⟩
    refine ⟨σ,(split _ _ _).mpr ⟨(split _ _ _).mpr ⟨fixed,fun e he => ?_⟩,rest⟩⟩
    exact (determined seedFits fixed (closed e he)).trans (done e he)

end Tamarin.Matching.Prefilter
