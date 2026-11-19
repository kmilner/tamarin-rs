import Tamarin.ACRepresentation
import Tamarin.Unification

/-! A term built in a Maude kind may fail to inhabit an operator's declared
sort. A sort failure on the open term alone cannot refute unification: a
variable may acquire a narrower sort. The certificates below concern every
sorted substitution. They do not change ordinary B-equivalence. -/
namespace Tamarin.SortClash
variable {sig : Signature}

theorem check_equiv {a b : Term sig} (h : EquivB a b) :
    ∀ s, a.checkSort s = b.checkSort s := by
  induction h with
  | refl => intros; rfl
  | symm _ ih => exact fun s => (ih s).symm
  | trans _ _ ih ik => exact fun s => (ih s).trans (ik s)
  | free f a b _ ih => intro s; simp only [Term.checkSort, ih]
  | comm_congr _ _ _ ia ib | ac_congr _ _ _ ia ib =>
    intro s; simp only [Term.checkSort, ia, ib]
  | comm_swap | ac_swap => intro s; simp only [Term.checkSort]; grind
  | ac_assoc f =>
    intro s
    simp only [Term.checkSort, (Subsort.check_iff _ _).mpr (.refl (sig.acSort f))]
    grind

/-- 1 means every instance inhabits s, 2 means none does, 0 is unknown. -/
def Describes (s : SortId) (t : Term sig) (word : UInt64) : Prop :=
  (word = 1 → ∀ σ : Substitution sig, HasSort (σ.apply t) s) ∧
  (word = 2 → ∀ σ : Substitution sig, ¬ HasSort (σ.apply t) s)

theorem typed {s : SortId} {t : Term sig} (h : HasSort t s) : Describes s t 1 :=
  ⟨fun _ σ => h.subst σ.image σ.sorted, by intro e; contradiction⟩

theorem rigid (s : SortId) (t : Term sig) (fixed : ∀ v, t ≠ .var v)
    (apart : ¬ Subsort t.rootSort s) : Describes s t 2 := by
  refine ⟨by intro e; contradiction, fun _ σ h => ?_⟩
  have same : (σ.apply t).rootSort = t.rootSort := by
    cases t with
    | var v => exact False.elim (fixed v rfl)
    | _ => rfl
  exact apart (same ▸ Term.rootSort_le h)

theorem disjoint_var (s : SortId) (v : Variable)
    (apart : ∀ k, Subsort k v.sort → ¬ Subsort k s) :
    Describes (sig := sig) s (.var v) 2 := by
  refine ⟨by intro e; contradiction, fun _ σ h => ?_⟩
  exact apart _ (Term.rootSort_le (σ.sorted v)) (Term.rootSort_le h)

theorem nat_name_var (v : Variable) (hv : v.sort = .fresh ∨ v.sort = .pub) :
    Describes (sig := sig) .nat (.var v) 2 := by
  apply disjoint_var
  intro k h n
  rcases hv with e | e <;> rw [e] at h <;> cases h <;> cases n

theorem unknown (s : SortId) (t : Term sig) : Describes s t 0 := by
  constructor <;> intro h <;> contradiction

theorem fold_typed (f : sig.ACSym) (σ : Substitution sig) (a : Term sig) (ts : List (Term sig)) :
    HasSort (σ.apply (ACRepresentation.fold f a ts)) (sig.acSort f) ↔
      ∀ t ∈ a :: ts, HasSort (σ.apply t) (sig.acSort f) := by
  induction ts generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih =>
    change HasSort (.ac f (σ.apply a) (σ.apply (ACRepresentation.fold f b bs))) _ ↔ _
    have child (x y : Term sig) :
        HasSort (.ac f x y) (sig.acSort f) ↔ HasSort x (sig.acSort f) ∧ HasSort y (sig.acSort f) := by
      simp only [← Term.checkSort_iff, Term.checkSort, Bool.and_eq_true,
        (Subsort.check_iff _ _).mpr (.refl (sig.acSort f)), true_and]
    rw [child, ih]; simp

def Correct (run : Array UInt64 → Array UInt64 → Bool) : Prop :=
  ∀ a b, run a b = true ↔
    (2 ∈ a.toList ∧ b.size ≠ 0 ∧ ∀ w ∈ b.toList, w = 1) ∨
    (2 ∈ b.toList ∧ a.size ≠ 0 ∧ ∀ w ∈ a.toList, w = 1)

/-- The wire evidence refers to whether the whole instantiated term has
any declared sort. A nontrivial malformed product can have none. -/
structure Side (sig : Signature) where
  term : Term sig
  words : Array UInt64
  good : (∀ w ∈ words.toList, w = 1) → ∀ σ : Substitution sig, ∃ s, HasSort (σ.apply term) s
  bad : 2 ∈ words.toList → ∀ σ : Substitution sig, ¬ ∃ s, HasSort (σ.apply term) s

def Side.sorted {t : Term sig} {s : SortId} (h : HasSort t s) : Side sig where
  term := t
  words := #[1]
  good := fun _ σ => ⟨s, h.subst σ.image σ.sorted⟩
  bad := by simp

/-- At least two factors are required. A single wrongly sorted variable on its
own still has its declared sort. -/
def Side.product (f : sig.ACSym) (a b : Term sig) (ts : List (Term sig))
    (code : Term sig → UInt64)
    (live : ∀ t ∈ a :: b :: ts, Describes (sig.acSort f) t (code t)) : Side sig where
  term := ACRepresentation.fold f a (b :: ts)
  words := ((a :: b :: ts).map code).toArray
  good all σ := ⟨sig.acSort f, (fold_typed ..).mpr fun t ht =>
    (live t ht).1 (all _ (by simpa only [List.toList_toArray] using List.mem_map_of_mem (f := code) ht)) σ⟩
  bad := by
    intro hm σ ⟨s, h⟩
    simp only [List.mem_map] at hm
    obtain ⟨t, ht, bad⟩ := hm
    have both := Term.checkSort_complete h
    change (Term.ac f (σ.apply a) (σ.apply (ACRepresentation.fold f b ts))).checkSort s = true at both
    simp only [Term.checkSort, Bool.and_eq_true] at both
    have atRoot := HasSort.ac f _ _ (Term.checkSort_sound _ _ both.1.2) (Term.checkSort_sound _ _ both.2)
    exact (live t ht).2 bad σ ((fold_typed f σ a (b :: ts)).mp atRoot t ht)

theorem refutes {run} (correct : Correct run) (a b : Side sig)
    (p : Problem sig) (avoid : List Variable) (mem : ⟨a.term, b.term⟩ ∈ p)
    (h : run a.words b.words = true) :
    (Outcome.complete []).CorrectIn p avoid := by
  refine ⟨(complete_empty_iff _).mpr ?_, by simp [Outcome.answers], by simp [Outcome.answers]⟩
  rintro ⟨σ, solves⟩
  have eq : EquivB (σ.apply a.term) (σ.apply b.term) := solves _ mem
  have transport {u v : Term sig} (e : EquivB u v) : (∃ s, HasSort u s) → ∃ s, HasSort v s := by
    rintro ⟨s, hs⟩
    exact ⟨s, Term.checkSort_sound _ _ ((check_equiv e s) ▸ Term.checkSort_complete hs)⟩
  rcases (correct _ _).mp h with ⟨bad, _, good⟩ | ⟨bad, _, good⟩
  · exact a.bad bad σ (transport eq.symm (b.good good σ))
  · exact b.bad bad σ (transport eq (a.good good σ))

end Tamarin.SortClash
