import Tamarin.ConstructorVariants
import Tamarin.FreshSubstitution
import Tamarin.SortCheck
import Tamarin.GroundConjunction

/-! Contract for selecting the RHS of an instantiated rule. No ordering,
sorting strategy or representation of internal match bindings is required. -/
namespace Tamarin.Rewriting.RuleReduction

abbrev Rows := List (UInt64 × UInt64)

def Consistent (rows : Rows) : Prop :=
  ∀ k a b, (k, a) ∈ rows → (k, b) ∈ rows → a = b

def Correct (run : UInt64 → Array UInt64 → Array UInt64 → Array UInt64) : Prop :=
  ∀ slot keys subjects,
    let rows := keys.toList.zip subjects.toList
    let out := run slot keys subjects
    (out = #[] ∨ ∃ w, out = #[w]) ∧
      (∀ w, out = #[w] ↔
        keys.size = subjects.size ∧ Consistent rows ∧ (slot, w) ∈ rows)

variable {sig : Signature}

/-- The term traversal preserves all application heads and pairs every rule
variable with the entire subject term at the same position. -/
inductive Skeleton (key : UInt64 → Variable) (subject : UInt64 → Term sig) (rows : Rows) : Term sig → Term sig → Prop
  | var (k v) : (k, v) ∈ rows → Skeleton key subject rows (.var (key k)) (subject v)
  | atom (a) : Skeleton key subject rows (.atom a) (.atom a)
  | free (f p q) : (∀ i, Skeleton key subject rows (p i) (q i)) →
      Skeleton key subject rows (.free f p) (.free f q)
  | comm (f) {a b x y} : Skeleton key subject rows a x → Skeleton key subject rows b y →
      Skeleton key subject rows (.comm f a b) (.comm f x y)
  | ac (f) {a b x y} : Skeleton key subject rows a x → Skeleton key subject rows b y →
      Skeleton key subject rows (.ac f a b) (.ac f x y)

theorem Skeleton.instantiate {key subject rows} {p q : Term sig}
    (shape : Skeleton key subject rows p q) (σ : Substitution sig)
    (agree : ∀ k v, (k, v) ∈ rows → σ.image (key k) = subject v) :
    σ.apply p = q := by
  induction shape with
  | var k v hm => exact agree k v hm
  | atom => rfl
  | free f p q _ ih => exact congrArg (Term.free f) (funext ih)
  | comm f _ _ ih ik => simp only [Substitution.apply, Term.subst] at ih ik ⊢; rw [ih, ik]
  | ac f _ _ ih ik => simp only [Substitution.apply, Term.subst] at ih ik ⊢; rw [ih, ik]

theorem consistent_substitution (rows : Rows) (key : UInt64 → Variable) (subject : UInt64 → Term sig)
    (live : ∀ i a j b, (i, a) ∈ rows → (j, b) ∈ rows → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ rows → HasSort (sig := sig) (subject v) (key k).sort)
    (consistent : Consistent rows) :
    ∃ σ : Substitution sig, ∀ k v, (k, v) ∈ rows → σ.image (key k) = subject v := by
  let bindings := rows.map (fun row => (key row.1, subject row.2))
  have ht : ∀ v t, (v, t) ∈ bindings → HasSort t v.sort := by
    intro v t h
    obtain ⟨⟨k, w⟩, hm, he⟩ := List.mem_map.mp h
    cases he
    exact typed k w hm
  refine ⟨Substitution.fromBindings bindings ht, fun k v hm => ?_⟩
  apply Substitution.lookupBinding_eq_of_mem
  · intro w a b ha hb
    obtain ⟨⟨i, x⟩, hi, ei⟩ := List.mem_map.mp ha
    obtain ⟨⟨j, y⟩, hj, ej⟩ := List.mem_map.mp hb
    cases ei
    obtain rfl := live i x j y hi hj (congrArg Prod.fst ej).symm
    have hxy := consistent i x y hi hj
    cases hxy
    exact congrArg Prod.snd ej
  · exact List.mem_map.mpr ⟨(k,v), hm, rfl⟩

/-- A successful reply certifies a single sorted match for the entire rule,
including occurrences of the same parameter in different arguments. -/
theorem matched {run} (correct : Correct run) (d : sig.FreeSym)
    (p ys : Fin (sig.arity d) → Term sig)
    (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable)
    (subject : UInt64 → Term sig) (ok : run slot keys subjects = #[w])
    (shape : ∀ i, Skeleton key subject (keys.toList.zip subjects.toList) (p i) (ys i))
    (live : ∀ i a j b, (i, a) ∈ keys.toList.zip subjects.toList →
      (j, b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ keys.toList.zip subjects.toList →
      HasSort (subject v) (key k).sort) :
    ∃ σ : Substitution sig, (∀ i, σ.apply (p i) = ys i) ∧ σ.image (key slot) = subject w := by
  obtain ⟨_, consistent, hm⟩ := ((correct slot keys subjects).2 w).mp ok
  obtain ⟨σ, agree⟩ := consistent_substitution _ key subject live typed consistent
  exact ⟨σ, fun i => (shape i).instantiate σ agree, agree slot w hm⟩

/-- Any actual match yields a root rewrite. Ground or selected RHSes
subsequently supply their own irreducibility and sorting evidence. -/
private theorem normal_match (rules : List (Equation sig)) (d : sig.FreeSym)
    (p ys : Fin (sig.arity d) → Term sig) (rhs value : Term sig) (σ : Substitution sig)
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (lhs : ∀ i, σ.apply (p i) = ys i) (result : σ.apply rhs = value)
    (irreducible : Normal (ruleRoot rules) value) (typed : HasSort value (sig.outputSort d)) :
    NormalForm (ruleRoot rules) (.free d ys) value := by
  have step : ruleRoot rules (.free d ys) value :=
    ⟨_, present, σ, congrArg (Term.free d) (funext fun i => (lhs i).symm), result.symm⟩
  exact ⟨.step ⟨_, _, .refl _, .root step, .refl _⟩, irreducible,
    fun _ hs => .widen typed (Term.rootSort_le hs)⟩

private theorem constructor_irreducible (rules : List (Equation sig)) (result : Term sig)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (absent : ∀ f ∈ ConstructorVariants.operators result, f ∉ ConstructorVariants.ruleHeads rules) :
    Normal (ruleRoot rules) result := by
  obtain ⟨vars, hc⟩ := ConstructorVariants.constructor_normal rules apps
  simpa using hc result absent Substitution.identity vars

/-- The output slot selects a whole normal subject from a concrete match.
The subject may be a name, variable, or compound constructor term. -/
theorem normalForm {run} (correct : Correct run) (rules : List (Equation sig))
    (d : sig.FreeSym) (p ys : Fin (sig.arity d) → Term sig)
    (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable)
    (subject : UInt64 → Term sig) (ok : run slot keys subjects = #[w])
    (present : (⟨.free d p, .var (key slot)⟩ : Equation sig) ∈ rules)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (resultSort : Subsort (key slot).sort (sig.outputSort d))
    (absent : ∀ f ∈ ConstructorVariants.operators (subject w), f ∉ ConstructorVariants.ruleHeads rules)
    (shape : ∀ i, Skeleton key subject (keys.toList.zip subjects.toList) (p i) (ys i))
    (live : ∀ i a j b, (i, a) ∈ keys.toList.zip subjects.toList →
      (j, b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ keys.toList.zip subjects.toList →
      HasSort (subject v) (key k).sort) :
    NormalForm (ruleRoot rules) (.free d ys) (subject w) := by
  obtain ⟨σ, hs, he⟩ := matched correct d p ys slot w keys subjects key subject ok shape live typed
  have hm := (((correct slot keys subjects).2 w).mp ok).2.2
  exact normal_match rules d p ys _ _ σ present hs he
    (constructor_irreducible rules _ apps absent) (.widen (typed slot w hm) resultSort)

/-- For a ground constructor RHS the export supplies evidence of one consistent
match. The result is the rule's actual closed term, independent of the
selected slot and of the order in which rule variables were collected. -/
theorem groundNormalForm {run} (correct : Correct run) (rules : List (Equation sig))
    (d : sig.FreeSym) (p ys : Fin (sig.arity d) → Term sig) (rhs : Term sig)
    (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable)
    (subject : UInt64 → Term sig) (ok : run slot keys subjects = #[w])
    (present : (⟨.free d p, rhs⟩ : Equation sig) ∈ rules)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (ground : rhs.Ground) (resultSort : HasSort rhs (sig.outputSort d))
    (absent : ∀ f ∈ ConstructorVariants.operators rhs, f ∉ ConstructorVariants.ruleHeads rules)
    (shape : ∀ i, Skeleton key subject (keys.toList.zip subjects.toList) (p i) (ys i))
    (live : ∀ i a j b, (i, a) ∈ keys.toList.zip subjects.toList →
      (j, b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k, v) ∈ keys.toList.zip subjects.toList →
      HasSort (subject v) (key k).sort) :
    NormalForm (ruleRoot rules) (.free d ys) rhs := by
  obtain ⟨σ, hs, _⟩ := matched correct d p ys slot w keys subjects key subject ok shape live typed
  exact normal_match rules d p ys rhs rhs σ present hs (ground.apply_eq σ)
    (constructor_irreducible rules rhs apps absent) resultSort

end Tamarin.Rewriting.RuleReduction
