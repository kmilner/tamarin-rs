import Tamarin.Commutative
import Tamarin.CompoundOffset

/-! A binary application of an AC operator admits commutative alignment when
both terms on either side always contribute one factor. Nonempty AC products
force the opposite two terms to contribute exactly one factor each as well. -/
namespace Tamarin.AtomicACPair
open Cancellation
variable {sig : Signature}

def Atomic (f : sig.ACSym) (t : Term sig) : Prop :=
  ∀ σ : Substitution sig, flatten f (σ.apply t) = [classOf (σ.apply t)]

theorem atomic_of_fixed (f : sig.ACSym) (t : Term sig) (ht : CompoundOffset.Fixed f t) :
    Atomic f t := CompoundOffset.fixed_factor f t ht

theorem atomic_of_sort {f : sig.ACSym} {s : SortId} {t : Term sig}
    (typed : HasSort t s) (apart : ¬ Subsort (sig.acSort f) s) : Atomic f t := by
  intro σ
  have hs : HasSort (σ.apply t) s := typed.subst σ.image σ.sorted
  cases ht : σ.apply t with
  | var | atom | free | comm => rfl
  | ac g a b =>
    have ne : f ≠ g := by
      intro he; subst g; rw [ht] at hs
      exact apart (Term.rootSort_le hs)
    simp only [flatten, ite_eq_right ne]

theorem fresh_atomic {f : sig.ACSym} (msg : sig.acSort f = .msg) {v : Variable}
    (fresh : v.sort = .fresh) : Atomic f (.var v) := by
  apply atomic_of_sort (HasSort.var v)
  rw [msg, fresh]
  intro h; cases h

private theorem factor_nonempty (f : sig.ACSym) (t : Term sig) : flatten f t ≠ [] := by
  intro he
  have h := fold_flatten f t
  rw [he] at h; cases h

/-- A matrix assignment that maps an indivisible input column to two or
more AC witnesses cannot extend to a solution of its residual equations. -/
theorem atomic_ne_product {f : sig.ACSym} {t : Term sig} (atom : Atomic f t)
    (a b : Term sig) (σ : Substitution sig) : ¬ EquivB (σ.apply (.ac f a b)) (σ.apply t) := by
  intro eq
  have same := (flatten_equiv f eq).length_eq
  change (flatten f (.ac f (σ.apply a) (σ.apply b))).length = _ at same
  rw [flatten_ac,atom σ,List.length_append] at same
  have l := List.length_pos_iff.mpr (factor_nonempty f (σ.apply a))
  have r := List.length_pos_iff.mpr (factor_nonempty f (σ.apply b))
  simp only [List.length_singleton] at same
  omega

private theorem singleton_of_length {f : sig.ACSym} {t : Term sig} (length : (flatten f t).length = 1) :
    flatten f t = [classOf t] := by
  obtain ⟨w, he⟩ := List.length_eq_one_iff.mp length
  have h := fold_flatten f t
  rw [he] at h
  exact he.trans (congrArg (fun a => [a]) (Option.some.inj h))

private theorem align_classes {a b c d : Term sig}
    (h : [classOf a,classOf b].Perm [classOf c,classOf d]) :
    (EquivB a c ∧ EquivB b d) ∨ (EquivB a d ∧ EquivB b c) := by
  have hm := h.mem_iff.mp (List.mem_cons_self ..)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with ha | ha
  · have last : [classOf b].Perm [classOf d] := List.Perm.cons_inv (ha ▸ h)
    exact Or.inl ⟨Quotient.exact ha, Quotient.exact (List.cons.inj (List.perm_singleton.mp last)).1⟩
  · have rev := h.trans (List.Perm.swap (classOf d) (classOf c) [])
    have last : [classOf b].Perm [classOf c] := List.Perm.cons_inv (ha ▸ rev)
    exact Or.inr ⟨Quotient.exact ha, Quotient.exact (List.cons.inj (List.perm_singleton.mp last)).1⟩

/-- Invert an equation when the two factors on the left are indivisible.
The terms on the right can have any head and can contain further AC terms. -/
theorem equiv_iff (f : sig.ACSym) (a b c d : Term sig)
    (ha : flatten f a = [classOf a]) (hb : flatten f b = [classOf b]) :
    EquivB (.ac f a b) (.ac f c d) ↔
      (EquivB a c ∧ EquivB b d) ∨ (EquivB a d ∧ EquivB b c) := by
  constructor
  · intro he
    have hp := flatten_equiv f he
    rw [flatten_ac, flatten_ac, ha, hb] at hp
    have len := hp.length_eq
    have sum : 2 = (flatten f c).length + (flatten f d).length := by simpa using len
    have hc := List.length_pos_iff.mpr (factor_nonempty f c)
    have hd := List.length_pos_iff.mpr (factor_nonempty f d)
    rw [singleton_of_length (f := f) (t := c) (by omega),
      singleton_of_length (f := f) (t := d) (by omega)] at hp
    exact align_classes hp
  · rintro (⟨ac,bd⟩ | ⟨ad,bc⟩)
    · exact .ac_congr f ac bd
    · exact (EquivB.ac_congr f ad bc).trans (.ac_swap f _ _)

structure Query (sig : Signature) where
  f : sig.ACSym
  a : Term sig
  b : Term sig
  c : Term sig
  d : Term sig
  rest : Problem sig

namespace Query
variable (q : Query sig)

def problem : Problem sig := ⟨.ac q.f q.a q.b, .ac q.f q.c q.d⟩ :: q.rest

def branch (cross : Bool) : Problem sig :=
  if cross then ⟨q.a,q.d⟩ :: ⟨q.b,q.c⟩ :: q.rest
  else ⟨q.a,q.c⟩ :: ⟨q.b,q.d⟩ :: q.rest

def Admitted := (Atomic q.f q.a ∧ Atomic q.f q.b) ∨ (Atomic q.f q.c ∧ Atomic q.f q.d)

theorem solves_iff (admitted : q.Admitted) (σ : Substitution sig) :
    q.problem.Solves σ ↔ (q.branch false).Solves σ ∨ (q.branch true).Solves σ := by
  have main : EquivB (.ac q.f (σ.apply q.a) (σ.apply q.b)) (.ac q.f (σ.apply q.c) (σ.apply q.d)) ↔
      (EquivB (σ.apply q.a) (σ.apply q.c) ∧ EquivB (σ.apply q.b) (σ.apply q.d)) ∨
      (EquivB (σ.apply q.a) (σ.apply q.d) ∧ EquivB (σ.apply q.b) (σ.apply q.c)) := by
    rcases admitted with ⟨a,b⟩ | ⟨c,d⟩
    · exact equiv_iff _ _ _ _ _ (a σ) (b σ)
    · have rev := equiv_iff q.f (σ.apply q.c) (σ.apply q.d) (σ.apply q.a) (σ.apply q.b) (c σ) (d σ)
      constructor
      · intro he
        rcases rev.mp he.symm with ⟨u,v⟩ | ⟨u,v⟩
        · exact Or.inl ⟨u.symm,v.symm⟩
        · exact Or.inr ⟨v.symm,u.symm⟩
      · intro he; apply EquivB.symm; apply rev.mpr
        rcases he with ⟨u,v⟩ | ⟨u,v⟩
        · exact Or.inl ⟨u.symm,v.symm⟩
        · exact Or.inr ⟨v.symm,u.symm⟩
  simp [problem, branch, Problem.Solves, Substitution.apply, Term.subst] at *
  grind

theorem occurs_iff (b : Bool) (v : Variable) : (q.branch b).Occurs v ↔ q.problem.Occurs v := by
  cases b <;> simp [branch, problem, Problem.Occurs, Term.Occurs] <;> grind

theorem branch_wellFormed (hp : q.problem.WellFormed) (cross : Bool) :
    (q.branch cross).WellFormed := by
  obtain ⟨⟨_, hl⟩, ⟨_, hr⟩⟩ := hp _ (List.mem_cons_self ..)
  have left := Term.checkSort_complete hl
  have right := Term.checkSort_complete hr
  simp only [Term.checkSort, Bool.and_eq_true] at left right
  have ha := Term.checkSort_sound _ _ left.1.2
  have hb := Term.checkSort_sound _ _ left.2
  have hc := Term.checkSort_sound _ _ right.1.2
  have hd := Term.checkSort_sound _ _ right.2
  intro e he
  cases cross <;> simp [branch] at he <;> rcases he with rfl | rfl | hm
  · exact ⟨⟨_,ha⟩,⟨_,hc⟩⟩
  · exact ⟨⟨_,hb⟩,⟨_,hd⟩⟩
  · exact hp _ (List.mem_cons_of_mem _ hm)
  · exact ⟨⟨_,ha⟩,⟨_,hd⟩⟩
  · exact ⟨⟨_,hb⟩,⟨_,hc⟩⟩
  · exact hp _ (List.mem_cons_of_mem _ hm)

structure Priority (p : UInt8) : Prop where
  direct : (p = 1 ∨ p = 3) → q.a = q.b ∨ q.c = q.d ∨ q.a = q.c ∨ q.b = q.d
  crossed : (p = 2 ∨ p = 3) → q.a = q.b ∨ q.c = q.d ∨ q.a = q.d ∨ q.b = q.c

end Query

private theorem viable (key : Head sig → UInt64) (σ : Substitution sig) {a b : Term sig}
    (he : EquivB (σ.apply a) (σ.apply b)) :
    Commutative.Viable (Commutative.headCode key a) (Commutative.headCode key b) := by
  have hh := congrArg key he.head_eq
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr hh)

private theorem dominates (q : Query sig) (p : UInt8) (hp : q.Priority p) (σ : Substitution sig) :
    ((p = 1 ∨ p = 3) → (q.branch true).Solves σ → (q.branch false).Solves σ) ∧
    ((p = 2 ∨ p = 3) → (q.branch false).Solves σ → (q.branch true).Solves σ) := by
  have align {a b c d : Term sig} (eq : a = b ∨ c = d ∨ a = c ∨ b = d)
      (ad : EquivB a d) (bc : EquivB b c) : EquivB a c ∧ EquivB b d := by
    rcases eq with rfl | rfl | rfl | rfl
    · exact ⟨bc, ad⟩
    · exact ⟨ad, bc⟩
    · exact ⟨.refl _, bc.trans ad⟩
    · exact ⟨ad.trans bc,.refl _⟩
  constructor
  · intro h sol; have eq := hp.direct h
    simp [Query.branch, Problem.Solves] at sol ⊢
    have both := align (by grind) sol.1 sol.2.1
    exact ⟨both.1,both.2,sol.2.2⟩
  · intro h sol; have eq := hp.crossed h
    simp [Query.branch, Problem.Solves] at sol ⊢
    have both := align (by grind) sol.1 sol.2.1
    exact ⟨both.1,both.2,sol.2.2⟩

theorem run_solves {run} (hc : Commutative.Correct run) (q : Query sig) (admitted : q.Admitted)
    (key : Head sig → UInt64) (p : UInt8) (hp : q.Priority p) (σ : Substitution sig) :
    let word := Commutative.headCode key
    let bs := Commutative.orientations (run (word q.a) (word q.b) (word q.c) (word q.d) p)
    q.problem.Solves σ ↔ ∃ b ∈ bs, (q.branch b).Solves σ := by
  dsimp only
  rw [q.solves_iff admitted]
  have select := (hc _ _ _ _ p).2 ((q.branch false).Solves σ) ((q.branch true).Solves σ)
    (fun h => by
      simp [Query.branch, Problem.Solves] at h
      exact ⟨viable key σ h.1, viable key σ h.2.1⟩)
    (fun h => by
      simp [Query.branch, Problem.Solves] at h
      exact ⟨viable key σ h.1, viable key σ h.2.1⟩)
    (dominates q p hp σ).1 (dominates q p hp σ).2
  refine select.trans ⟨?_, ?_⟩
  · rintro (⟨hm,hs⟩ | ⟨hm,hs⟩)
    · exact ⟨false, (Commutative.mem_orientations ..).mpr hm, hs⟩
    · exact ⟨true, (Commutative.mem_orientations ..).mpr hm, hs⟩
  · rintro ⟨b, hm, hs⟩
    cases b <;> first
      | exact Or.inl ⟨(Commutative.mem_orientations ..).mp hm,hs⟩
      | exact Or.inr ⟨(Commutative.mem_orientations ..).mp hm,hs⟩

/-- The branch continuation sees the original tail and caller's avoid set.
The exported orientation decision controls the exact set of continuations. -/
theorem assemble {run} (hc : Commutative.Correct run) (q : Query sig) (admitted : q.Admitted)
    (key : Head sig → UInt64) (p : UInt8) (hp : q.Priority p) (avoid : List Variable)
    (answers : Bool → List (Substitution sig)) :
    let word := Commutative.headCode key
    let bs := Commutative.orientations (run (word q.a) (word q.b) (word q.c) (word q.d) p)
    (∀ b ∈ bs, (Outcome.complete (answers b)).CorrectIn (q.branch b) avoid) →
    (Outcome.complete (bs.flatMap answers)).CorrectIn q.problem avoid := by
  intro word bs complete
  have branches := run_solves hc q admitted key p hp
  constructor
  · constructor
    · intro σ hs
      obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
      exact (branches σ).mpr ⟨b,hb,(complete b hb).mathematical.sound σ ha⟩
    · intro ρ hρ
      obtain ⟨b,hb,hr⟩ := (branches ρ).mp hρ
      obtain ⟨σ,hs,δ,he⟩ := (complete b hb).mathematical.covers ρ hr
      exact ⟨σ, List.mem_flatMap.mpr ⟨b,hb,hs⟩, δ, fun v hv => he v ((q.occurs_iff b v).mpr hv)⟩
  · intro σ hs v hn
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
    exact (complete b hb).domain σ ha v (fun hv => hn ((q.occurs_iff b v).mp hv))
  · intro σ hs v hv w hw hn
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
    exact (complete b hb).fresh σ ha v ((q.occurs_iff b v).mpr hv) w hw (fun h => hn ((q.occurs_iff b w).mp h))

end Tamarin.AtomicACPair
