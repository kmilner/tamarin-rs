import Tamarin.Pairing

/-! Finite variants for the first pairing fragment. Completeness ranges over
finite sorted NORMALIZED substitutions, including nonground ones. Both input
images and all query components must factor through ONE shared substitution;
the instantiated variant value is not normalized again. -/
namespace Tamarin.Pairing

def Normalized (σ : PSubst) : Prop := ∀ v, Normal (σ.image v)
def Observed (q : List PTerm) (v : Variable) : Prop := ∃ t ∈ q, t.Occurs v

def Covers (q : List PTerm) (ρ σ : PSubst) : Prop :=
  ∃ δ : PSubst, Normalized δ ∧
    (∀ v, Observed q v → ρ.image v = δ.apply (σ.image v)) ∧
    ∀ t ∈ q, normalize (ρ.apply t) = δ.apply (normalize (σ.apply t))

/-- Sound variant values are the unique normal forms of instantiated queries.
The substitution itself is finite and sorted by its type. Restricting domains,
freshness, and idempotence are additional obligations at the output boundary. -/
def CompleteVariants (q : List PTerm) (answers : List PSubst) : Prop :=
  (∀ σ ∈ answers, Normalized σ) ∧
  ∀ ρ : PSubst, Normalized ρ → ∃ σ ∈ answers, Covers q ρ σ

theorem identity_normalized : Normalized (Substitution.identity : PSubst) :=
  fun v => .var v

inductive Constructor : PTerm → Prop where
  | var (v) : Constructor (.var v)
  | atom (a) : Constructor (.atom a)
  | pair {a b} : Constructor a → Constructor b → Constructor (pair a b)
  | other (id n : Nat) (args : Fin n → PTerm) : (∀ i, Constructor (args i)) → Constructor (.free (.other id n) args)
  | comm (f : Nat) {a b} : Constructor a → Constructor b → Constructor (.comm f a b)
  | ac (f : Nat) {a b} : Constructor a → Constructor b → Constructor (.ac f a b)

theorem constructor_subst_normal {t : PTerm} (ht : Constructor t)
    (σ : PSubst) (hσ : Normalized σ) : Normal (σ.apply t) := by
  induction ht with
  | var v => exact hσ v
  | atom a => exact .atom a
  | pair ha hb ia ib =>
    simpa only [Substitution.apply, subst_pair] using Normal.pair ia ib
  | ac f ha hb ia ib => exact .ac f ia ib
  | comm f ha hb ia ib => exact .comm f ia ib
  | other id n args hn ih => exact .other id n _ ih

theorem constructor_variants_complete (q : List PTerm)
    (hq : ∀ t ∈ q, Constructor t) : CompleteVariants q [Substitution.identity] := by
  constructor
  · intro σ h; simpa using List.mem_singleton.mp h ▸ identity_normalized
  · intro ρ hρ
    refine ⟨Substitution.identity, by simp, ρ, hρ, ?_, ?_⟩
    · intro v _; rfl
    · intro t ht
      rw [Substitution.apply_identity,
        normal_fixed (constructor_subst_normal (hq t ht) _ hρ),
        normal_fixed (by simpa using constructor_subst_normal (hq t ht) _ identity_normalized)]

def projection (first : Bool) (t : PTerm) : PTerm := if first then fst t else snd t

@[simp] theorem subst_projection (first : Bool) (t : PTerm) (σ : Variable → PTerm) :
    (projection first t).subst σ = projection first (t.subst σ) := by
  cases first <;> rfl

@[simp] theorem normalize_projection (first : Bool) (t : PTerm) :
    normalize (projection first t) = project first (normalize t) := by
  cases first <;> rfl

/-- A packed query may repeat the same variable/projection arbitrarily. The
single shared input identity is significant: mixed variables are not accepted. -/
def ProjectionQuery (first : Bool) (x : Variable) (q : List PTerm) : Prop :=
  ∀ t ∈ q, t = .var x ∨ t = projection first (.var x)

theorem projection_occurs (first : Bool) (x v : Variable) :
    (projection first (.var x)).Occurs v ↔ v = x := by
  cases first <;> simp [projection, fst, snd, Term.Occurs]

theorem projection_observed {first : Bool} {x : Variable} {q : List PTerm}
    (hq : ProjectionQuery first x q) {v : Variable} (hv : Observed q v) : v = x := by
  obtain ⟨t, ht, hv⟩ := hv
  rcases hq t ht with rfl | rfl
  · exact hv
  · exact (projection_occurs first x v).mp hv

def splitSubst (x a b : Variable) (hx : x.sort = .msg)
    (ha : a.sort = .msg) (hb : b.sort = .msg) : PSubst :=
  Substitution.binding x (pair (.var a) (.var b))
    (hx ▸ pair_sorted (ha ▸ HasSort.var a) (hb ▸ HasSort.var b))

theorem split_normalized (x a b : Variable) (hx : x.sort = .msg)
    (ha : a.sort = .msg) (hb : b.sort = .msg) : Normalized (splitSubst x a b hx ha hb) := by
  intro v
  by_cases h : v = x
  · subst v; simp only [splitSubst, Substitution.binding_image_self]; exact .pair (.var _) (.var _)
  · simp only [splitSubst, Substitution.binding_image_other _ _ _ _ h]; exact .var _

/-- Simultaneous parameter binding, so occurrences of a or b inside the image
of the other parameter are preserved rather than recursively substituted. -/
def parameters (a b : Variable) (l r : PTerm) (hl : HasSort l a.sort)
    (hr : HasSort r b.sort) : PSubst where
  image := fun v => if v = a then l else if v = b then r else .var v
  support := [a, b]
  outside := by intro v h; simp only [List.mem_cons, not_or] at h; simp [h.1, h.2]
  sorted := by intro v; split; next h => subst v; exact hl
               split; next h => subst v; exact hr
               exact .var _

theorem parameters_normalized (a b : Variable) (l r : PTerm)
    (hl : HasSort l a.sort) (hr : HasSort r b.sort) (nl : Normal l) (nr : Normal r) :
    Normalized (parameters a b l r hl hr) := by
  intro v; change Normal (if v = a then l else if v = b then r else .var v); split
  · exact nl
  · split
    · exact nr
    · exact .var _

theorem normal_pair_children {args : Fin 2 → PTerm} (h : Normal (.free .pair args)) :
    Normal (args 0) ∧ Normal (args 1) := by
  cases h with | pair ha hb => exact ⟨ha, hb⟩

theorem project_not_pair (first : Bool) {t : PTerm}
    (ht : ∀ args, t ≠ .free .pair args) : project first t = projection first t := by
  cases t with
  | free f args => cases f <;> first | exact False.elim (ht _ rfl) | rfl
  | _ => rfl

theorem projection_variants_complete (first : Bool) (x a b : Variable)
    (hx : x.sort = .msg) (ha : a.sort = .msg) (hb : b.sort = .msg) (hab : a ≠ b)
    (q : List PTerm) (hq : ProjectionQuery first x q) :
    CompleteVariants q [Substitution.identity, splitSubst x a b hx ha hb] := by
  constructor
  · intro σ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact identity_normalized
    · exact split_normalized x a b hx ha hb
  · intro ρ hρ
    classical
    by_cases hp : ∃ args, ρ.image x = .free .pair args
    · obtain ⟨args, he⟩ := hp
      have hs := pair_children (he ▸ ρ.sorted x)
      have hn := normal_pair_children (he ▸ hρ x)
      let δ := parameters a b (args 0) (args 1) (ha ▸ hs 0) (hb ▸ hs 1)
      have da : δ.image a = args 0 := by simp [δ, parameters]
      have db : δ.image b = args 1 := by simp [δ, parameters, Ne.symm hab]
      have ds : δ.apply ((splitSubst x a b hx ha hb).image x) = ρ.image x := by
        simp only [splitSubst, Substitution.binding_image_self, Substitution.apply,
          subst_pair, Term.subst, da, db, pair_eta, he]
      refine ⟨splitSubst x a b hx ha hb, by simp, δ,
        parameters_normalized _ _ _ _ _ _ hn.1 hn.2, ?_, ?_⟩
      · intro v hv; have := projection_observed hq hv; subst v; exact ds.symm
      · intro t ht
        rcases hq t ht with rfl | rfl
        · change normalize (ρ.image x) = δ.apply (normalize ((splitSubst x a b hx ha hb).image x))
          rw [normal_fixed (split_normalized x a b hx ha hb x)]
          exact (normal_fixed (hρ x)).trans ds.symm
        · simp only [Substitution.apply, subst_projection, Term.subst]
          change normalize (projection first (ρ.image x)) =
            δ.apply (normalize (projection first ((splitSubst x a b hx ha hb).image x)))
          rw [normalize_projection, normal_fixed (hρ x), he]
          simp only [splitSubst, Substitution.binding_image_self]
          cases first
          · change args 1 = δ.image b; exact db.symm
          · change args 0 = δ.image a; exact da.symm
    · have hn : ∀ args, ρ.image x ≠ .free .pair args := by
        intro args he; exact hp ⟨args, he⟩
      refine ⟨Substitution.identity, by simp, ρ, hρ, ?_, ?_⟩
      · intro v _; rfl
      · intro t ht
        rcases hq t ht with rfl | rfl
        · exact normal_fixed (hρ x)
        · rw [Substitution.apply_identity]
          simp only [Substitution.apply, subst_projection, Term.subst]
          change normalize (projection first (ρ.image x)) =
            ρ.apply (normalize (projection first (.var x)))
          rw [normalize_projection, normal_fixed (hρ x)]
          cases first <;> exact project_not_pair _ hn

/-- Output safety is separate from completeness. Fresh variables may not
capture the caller's context; domains are restricted to the observed input. -/
def OutputSafe (q : List PTerm) (avoid : List Variable) (σ : PSubst) : Prop :=
  (∀ v, ¬ Observed q v → σ.image v = .var v) ∧
  (∀ v, Observed q v → ∀ w, (σ.image v).Occurs w →
    Observed q w ∨ w ∉ avoid) ∧
  (∀ v, σ.apply (σ.image v) = σ.image v)

theorem identity_safe (q : List PTerm) (avoid : List Variable) :
    OutputSafe q avoid Substitution.identity := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro v hv w hw; exact Or.inl (hw ▸ hv)
  · intro v; exact Substitution.apply_identity _

theorem occurs_pair {l r : PTerm} {v : Variable} :
    (pair l r).Occurs v ↔ l.Occurs v ∨ r.Occurs v := by
  constructor
  · intro ⟨i, hi⟩
    refine Fin.cases (fun h => Or.inl h) (fun j h => ?_) i hi
    have : j = 0 := Subsingleton.elim j 0
    subst j; exact Or.inr h
  · intro h
    rcases h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

theorem split_safe (first : Bool) (x a b : Variable)
    (hx : x.sort = .msg) (ha : a.sort = .msg) (hb : b.sort = .msg)
    (hax : a ≠ x) (hbx : b ≠ x) (q : List PTerm)
    (hq : ProjectionQuery first x q) (hqx : Observed q x)
    (avoid : List Variable) (haa : a ∉ avoid) (hba : b ∉ avoid) :
    OutputSafe q avoid (splitSubst x a b hx ha hb) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact Substitution.binding_image_other _ _ _ _ (fun he => hv (he ▸ hqx))
  · intro v hv w hw
    have he := projection_observed hq hv; subst v
    simp only [splitSubst, Substitution.binding_image_self, occurs_pair, Term.Occurs] at hw
    rcases hw with rfl | rfl
    · exact Or.inr haa
    · exact Or.inr hba
  · intro v
    by_cases he : v = x
    · subst v
      simp only [splitSubst, Substitution.binding_image_self, Substitution.apply,
        subst_pair, Term.subst, Substitution.binding_image_other _ _ _ _ hax,
        Substitution.binding_image_other _ _ _ _ hbx]
    · simp only [splitSubst, Substitution.binding_image_other _ _ _ _ he,
        Substitution.apply, Term.subst]

end Tamarin.Pairing
