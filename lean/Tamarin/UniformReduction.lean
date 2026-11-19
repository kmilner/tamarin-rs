import Tamarin.RuleReduction
import Tamarin.RulePattern
import Tamarin.StableVariants
import Tamarin.RuleAtHead

/-! A checked ordinary rewrite can also discharge an entire narrowing query
when its unique normal result commutes with every normalized substitution. -/
namespace Tamarin.Rewriting.UniformReduction
variable {sig : Signature} {R : Root sig}

/-- One successful slot verifies consistency even for variables absent from
the right side. Both skeletons are interpreted with that same substitution. -/
theorem instance_of_rows {run} (hc : RuleReduction.Correct run)
    {slot w : UInt64} {keys subjects : Array UInt64} {key : UInt64 → Variable}
    {subject : UInt64 → Term sig} (ok : run slot keys subjects = #[w])
    {lhs rhs input result : Term sig}
    (left : RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) lhs input)
    (right : RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) rhs result)
    (live : ∀ i a j b, (i,a) ∈ keys.toList.zip subjects.toList →
      (j,b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j)
    (typed : ∀ k v, (k,v) ∈ keys.toList.zip subjects.toList → HasSort (subject v) (key k).sort) :
    ∃ σ : Substitution sig, σ.apply lhs = input ∧ σ.apply rhs = result := by
  obtain ⟨_, consistent, _⟩ := ((hc ..).2 w).mp ok
  obtain ⟨σ, agree⟩ := RuleReduction.consistent_substitution _ _ _ live typed consistent
  exact ⟨σ, left.instantiate σ agree, right.instantiate σ agree⟩

private theorem occurs_apply (σ : Substitution sig) (t : Term sig) (v : Variable) :
    (σ.apply t).Occurs v ↔ ∃ w, t.Occurs w ∧ (σ.image w).Occurs v := by
  induction t with
  | var w => simp [Substitution.apply, Term.subst, Term.Occurs]
  | atom a => simp [Substitution.apply, Term.subst, Term.Occurs]
  | free f xs ih =>
    change (∃ i, (σ.apply (xs i)).Occurs v) ↔ ∃ w, (∃ i, (xs i).Occurs w) ∧ _
    simp only [ih]; grind
  | ac f a b ia ib | comm f a b ia ib =>
    change (σ.apply a).Occurs v ∨ (σ.apply b).Occurs v ↔ ∃ w, (a.Occurs w ∨ b.Occurs w) ∧ _
    rw [ia,ib]; grind

/-- A missing rigid child head in each competing row rules out every one
of its instances. The adapter can split the table around the selected row. -/
theorem excluded {run} (check : RootExclusion.Correct run)
    {f : sig.FreeSym} (code : Head sig → UInt64) (xs : Fin (sig.arity f) → Term sig)
    (rows : Array (Array UInt64)) (p : Fin (sig.arity f) → Term sig)
    (included : (Array.ofFn fun i => RootExclusion.required code (p i)) ∈ rows)
    (ok : run rows (Array.ofFn fun i => code (ConstructorVariants.head (xs i))) = true)
    (ρ τ : Substitution sig)
    (fixed : ∀ i, code (ConstructorVariants.head (ρ.apply (xs i))) = code (ConstructorVariants.head (xs i))) :
    ¬ (∀ i, EquivB (ρ.apply (xs i)) (τ.apply (p i))) := by
  intro matched
  obtain ⟨_, i, nz, diff⟩ := ((check ..).mp ok) _ included
  let j : Fin (sig.arity f) := ⟨i.val, by simpa using i.isLt⟩
  have keep (t : Term sig) (hn : RootExclusion.required code t ≠ 0) :
      RootExclusion.required code t = code (ConstructorVariants.head (τ.apply t)) := by
    cases t <;> simp [RootExclusion.required] at hn ⊢ <;> rfl
  have bound : j.val < (Array.ofFn fun i => code (ConstructorVariants.head (xs i))).size := by simp
  rw [getElem!_pos (Array.ofFn fun i => code (ConstructorVariants.head (xs i))) i.val bound] at diff
  apply diff
  simpa [j] using (keep (p j) (by simpa [j] using nz)).trans
    ((congrArg code (matched j).head_eq.symm).trans (fixed j))

/-- Other rules at this head may exist. They must be excluded for each
normalized instance; the left-hand free skeleton then determines every
variable of the right side, even when the result introduces AC structure. -/
theorem free_rule (rules : List (Equation sig)) (f : sig.FreeSym)
    (ps xs : Fin (sig.arity f) → Term sig) (rhs value : Term sig)
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (present : (⟨.free f ps,rhs⟩ : Equation sig) ∈ rules)
    (free : RulePattern.Free (.free f ps))
    (range : ∀ v, rhs.Occurs v → (Term.free f ps).Occurs v)
    (matchRule : ∃ σ : Substitution sig, σ.apply (.free f ps) = .free f xs ∧ EquivB (σ.apply rhs) value)
    (typed : HasSort value (sig.outputSort f))
    (children : ∀ ρ, Normalized (ruleRoot rules) ρ → ∀ i, Normal (ruleRoot rules) (ρ.apply (xs i)))
    (stable : ∀ ρ, Normalized (ruleRoot rules) ρ → Normal (ruleRoot rules) (ρ.apply value))
    (other : ∀ ρ, Normalized (ruleRoot rules) ρ → ∀ p r, (⟨.free f p,r⟩ : Equation sig) ∈ rules →
      ∀ τ : Substitution sig, (∀ i, EquivB (ρ.apply (xs i)) (τ.apply (p i))) → p = ps ∧ r = rhs) :
    StableVariants.Representative (ruleRoot rules) (.free f xs) value := by
  obtain ⟨σ, lhs, result⟩ := matchRule
  have law (ρ : Substitution sig) (hn : Normalized (ruleRoot rules) ρ) :
      NormalForm (ruleRoot rules) (ρ.apply (.free f xs)) (ρ.apply value) ∧
        ∀ u, NormalForm (ruleRoot rules) (ρ.apply (.free f xs)) u → EquivB u (ρ.apply value) := by
    let μ := ρ.compose σ
    have l : μ.apply (.free f ps) = ρ.apply (.free f xs) := by
      rw [Substitution.apply_compose, lhs]
    have r : EquivB (μ.apply rhs) (ρ.apply value) := by
      rw [Substitution.apply_compose]
      exact result.subst ρ.image
    have fires : StepModulo (ruleRoot rules) (ρ.apply (.free f xs)) (ρ.apply value) :=
      ⟨_, _, .refl _, .root ⟨_, present, μ, l.symm, rfl⟩, r⟩
    refine ⟨⟨.step fires, stable ρ hn, fun _ hs => .widen (typed.subst ρ.image ρ.sorted)
      (Term.rootSort_le hs)⟩, ?_⟩
    intro u normal
    apply normalForm_free_root_unique (children ρ hn) (stable ρ hn) fires _ normal
    intro ys equal b root
    obtain ⟨p, rr, mem, τ, e, rfl⟩ := (ruleRoot_free_iff rules f apps ys b).mp root
    have eqs i := (e i) ▸ equal i
    obtain ⟨rfl, rfl⟩ := other ρ hn p rr mem τ eqs
    have inputs : EquivB (μ.apply (.free f p)) (τ.apply (.free f p)) := l ▸ EquivB.free _ _ _ eqs
    exact (Term.subst_equiv _ _ _ fun v hv => (RulePattern.image_equiv free inputs (range v hv)).symm).trans r

  refine ⟨fun ρ hn => (law ρ hn).1, fun ρ hn => (law ρ hn).2, ?_⟩
  intro v hv
  obtain ⟨w, hw, mem⟩ := (occurs_apply σ rhs v).mp ((result.occurs_iff v).mpr hv)
  rw [← lhs]
  exact (occurs_apply σ (.free f ps) v).mpr ⟨w, range w hw, mem⟩

/-- Concrete normalization also accepts variables treated rigidly. A checked
rule instance followed by a whole-table normality test gives a normal form. -/
theorem normal {rules : List (Equation sig)} {lhs rhs input result value : Term sig}
    (present : (⟨lhs,rhs⟩ : Equation sig) ∈ rules)
    (instanceOf : ∃ σ : Substitution sig, σ.apply lhs = input ∧ σ.apply rhs = result)
    (canonical : EquivB result value) (irreducible : Normal (ruleRoot rules) value)
    (typed : HasSort value input.rootSort) : NormalForm (ruleRoot rules) input value := by
  obtain ⟨σ, h, k⟩ := instanceOf
  exact ⟨.step ⟨_, _, .refl _, .root ⟨_,present,σ,h.symm,k.symm⟩, canonical⟩,
    irreducible, fun _ hs => .widen typed (Term.rootSort_le hs)⟩

/-- Interpret the two numeric calls together. Every competing rule must have
its row in a checked bucket. Both sides of the chosen rule use the same
captured terms, including variables which occur only on the left. -/
def Correct (matchSlot : UInt64 → Array UInt64 → Array UInt64 → Array UInt64)
    (exclude : Array (Array UInt64) → Array UInt64 → Bool) : Prop :=
  ∀ {s : Signature} (rules : List (Equation s)) (f : s.FreeSym)
    (ps xs : Fin (s.arity f) → Term s) (rhs result value : Term s)
    (slot w : UInt64) (keys subjects : Array UInt64) (key : UInt64 → Variable) (subject : UInt64 → Term s)
    (code : Head s → UInt64) (buckets : List (Array (Array UInt64))),
    (∀ r ∈ rules, ConstructorVariants.Application r.lhs) →
    (⟨.free f ps,rhs⟩ : Equation s) ∈ rules → RulePattern.Free (.free f ps) →
    (∀ v, rhs.Occurs v → (Term.free f ps).Occurs v) →
    matchSlot slot keys subjects = #[w] →
    RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) (.free f ps) (.free f xs) →
    RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) rhs result →
    (∀ i a j b, (i,a) ∈ keys.toList.zip subjects.toList → (j,b) ∈ keys.toList.zip subjects.toList →
      key i = key j → i = j) →
    (∀ k v, (k,v) ∈ keys.toList.zip subjects.toList → HasSort (subject v) (key k).sort) →
    EquivB result value → HasSort value (s.outputSort f) →
    (∀ i, StableVariants.Stable (ruleRoot rules) (xs i)) →
    StableVariants.Stable (ruleRoot rules) value →
    (∀ ρ : Substitution s, ∀ i, code (ConstructorVariants.head (ρ.apply (xs i))) =
      code (ConstructorVariants.head (xs i))) →
    (∀ p r, (⟨.free f p,r⟩ : Equation s) ∈ rules → (p = ps ∧ r = rhs) ∨
      ∃ rows ∈ buckets, (Array.ofFn fun i => RootExclusion.required code (p i)) ∈ rows) →
    (∀ rows ∈ buckets, exclude rows (Array.ofFn fun i => code (ConstructorVariants.head (xs i))) = true) →
    StableVariants.Representative (ruleRoot rules) (.free f xs) value

theorem correct {matchSlot exclude} (hc : RuleReduction.Correct matchSlot)
    (he : RootExclusion.Correct exclude) : Correct matchSlot exclude := by
  intro s rules f ps xs rhs result value slot w keys subjects key subject code buckets
    apps present free range ok left right live typed canon sort children stable fixed competitors checked
  obtain ⟨σ, l, r⟩ := instance_of_rows hc ok left right live typed
  refine free_rule rules f ps xs rhs value apps present free range ⟨σ,l,r ▸ canon⟩ sort
    (fun ρ hn i => children i ρ hn) stable ?_
  intro ρ _ p rr mem τ aligned
  rcases competitors p rr mem with equal | ⟨rows, hr, inRows⟩
  · exact equal
  · exact False.elim (excluded he code xs rows p inRows (checked rows hr) ρ τ (fixed ρ) aligned)

end Tamarin.Rewriting.UniformReduction
