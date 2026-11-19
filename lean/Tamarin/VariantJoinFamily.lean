import Tamarin.VariantJoin
import Tamarin.SortClash

/-! Lift ordinary unification of rows to complete, reconstructible variants
of a packed query. Observation indices can repeat and can occur in any
caller-selected order. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {I A B : Type}

/-- Indexed form of the variant contract used during a join. A normalized
caller assignment and normal proposed outputs describe a real answer exactly
when they are simultaneous instances of a row. -/
def Exact (R : Root sig) (ids : I → Variable) (query : A → Term sig)
    (rows : List (Row sig I A)) : Prop :=
  ∀ ρ : Substitution sig, Normalized R ρ → ∀ y, (∀ a, Normal R (y a)) →
    ((∀ a, NormalForm R (ρ.apply (query a)) (y a)) ↔
      ∃ q ∈ rows, Denotes R q (fun i => ρ.image (ids i)) y)

/-- Join two complete families. The membership condition allows duplicate
removal and any traversal order. It requires a completed unifier search
for every pair, including pairs with no compatible input assignment. -/
theorem Exact.joined {rules : List (Equation sig)} {ids : I → Variable} {qa : A → Term sig} {qb : B → Term sig}
    {ls : List (Row sig I A)} {rs : List (Row sig I B)} (hl : Exact (ruleRoot rules) ids qa ls)
    (hr : Exact (ruleRoot rules) ids qb rs) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (keys : List I) (allKeys : ∀ i, i ∈ keys)
    (openRight : Row sig I A → Row sig I B → Row sig I B)
    (reopened : ∀ l ∈ ls, ∀ r ∈ rs, ∀ x z,
      Denotes (ruleRoot rules) (openRight l r) x z ↔ Denotes (ruleRoot rules) r x z)
    (anchors : Row sig I A → Row sig I B → List (Term sig))
    (solver : Row sig I A → Row sig I B → List (Substitution sig))
    (apart : ∀ l ∈ ls, ∀ r ∈ rs, ∀ v, l.Uses v → ¬(openRight l r).Uses v)
    (tracked : ∀ l ∈ ls, ∀ r ∈ rs, ∀ v, l.Uses v ∨ (openRight l r).Uses v →
      (problem l (openRight l r) keys (anchors l r)).Occurs v)
    (solved : ∀ l ∈ ls, ∀ r ∈ rs, CompleteSet (problem l (openRight l r) keys (anchors l r)) (solver l r))
    (out : List (Row sig I (Sum A B)))
    (members : ∀ t, t ∈ out ↔ ∃ l ∈ ls, ∃ r ∈ rs, ∃ μ ∈ solver l r,
      (join l (openRight l r) μ).IsNormal (ruleRoot rules) ∧ t = join l (openRight l r) μ) :
    Exact (ruleRoot rules) ids (Sum.elim qa qb) out := by
  intro ρ hρ values normal
  let y := fun a => values (.inl a)
  let z := fun b => values (.inr b)
  have eta : Sum.elim y z = values := funext (fun a => by cases a <;> rfl)
  have left := hl ρ hρ y (fun a => normal (.inl a))
  have right := hr ρ hρ z (fun b => normal (.inr b))
  have both l (lm : l ∈ ls) r (rm : r ∈ rs) :=
    exact_join vars l (openRight l r) (apart l lm r rm) keys allKeys (anchors l r) (tracked l lm r rm)
      _ (solved l lm r rm) (fun i => ρ.image (ids i)) y z (fun i => hρ _) (fun a => normal (.inl a))
      (fun b => normal (.inr b))
  constructor
  · intro forms
    obtain ⟨l,lm,h1⟩ := left.mp (fun a => forms (.inl a))
    obtain ⟨r,rm,h2⟩ := right.mp (fun b => forms (.inr b))
    obtain ⟨μ,mem,hn,hit⟩ := (both l lm r rm).mp ⟨h1,(reopened l lm r rm _ _).mpr h2⟩
    exact ⟨_,(members _).mpr ⟨l,lm,r,rm,μ,mem,hn,rfl⟩,eta ▸ hit⟩
  · rintro ⟨t,mem,hit⟩
    obtain ⟨l,lm,r,rm,μ,um,norm,rfl⟩ := (members t).mp mem
    rw [← eta] at hit
    obtain ⟨h1,h2⟩ := (both l lm r rm).mpr ⟨μ,um,norm,hit⟩
    intro a; cases a with
    | inl a => exact left.mpr ⟨l,lm,h1⟩ a
    | inr b => exact right.mpr ⟨r,rm,(reopened l lm r rm _ _).mp h2⟩ b

private theorem transport_sort {a b : Term sig} (eq : EquivB a b) {k} (h : HasSort a k) : HasSort b k :=
  Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete h)

/-- Specializing a genuine local variant reduction gives an actual normal
form whenever its instantiated output is still normal. A variable observation
may narrow in sort and its normal image is preserved modulo B. -/
theorem form_of_instance {rules : List (Equation sig)} {t u out : Term sig}
    {ρ σ δ : Substitution sig} (hρ : Normalized (ruleRoot rules) ρ) (typed : HasSort t t.rootSort)
    (agree : ∀ v, t.Occurs v → EquivB (ρ.image v) ((δ.compose σ).image v))
    (nf : NormalForm (ruleRoot rules) (σ.apply t) u)
    (value : EquivB out (δ.apply u)) (norm : Normal (ruleRoot rules) out) :
    NormalForm (ruleRoot rules) (ρ.apply t) out := by
  have eq := t.subst_equiv _ _ agree
  change EquivB (ρ.apply t) ((δ.compose σ).apply t) at eq
  rw [Substitution.apply_compose] at eq
  have red := (Reduces.basis eq).trans ((SpecializedFresh.reduces_subst rules δ nf.1).trans (.basis value.symm))
  refine ⟨red,norm,?_⟩
  have sorted : HasSort out t.rootSort :=
    transport_sort value.symm ((nf.2.2 _ (typed.subst σ.image σ.sorted)).subst δ.image δ.sorted)
  cases t with
  | var v => exact fun _ h => transport_sort (normal_reduces_equiv red (hρ v)) h
  | atom | free | comm | ac => intro k h; have hk := Term.rootSort_le h; exact .widen sorted hk

/-- Each local leaf is an ordinary complete variant call observing the
requested power and the full set of original variables. The leaf may open its
witnesses first using a sort-preserving renaming. -/
theorem singleton {rules : List (Equation sig)} (ids : I → Variable) (keys : List I) (allKeys : ∀ i, i ∈ keys)
    (t : Term sig) (typed : HasSort t t.rootSort) (includes : ∀ v, t.Occurs v → ∃ i, ids i = v)
    (variants : List (Variant sig)) (complete : CompleteVariants (ruleRoot rules)
      (t :: keys.map (fun i => .var (ids i))) variants)
    (rows : List (Row sig I Unit))
    (members : ∀ q, q ∈ rows ↔ ∃ a ∈ variants, ∃ u rest, a.values = u :: rest ∧
      (∀ i, q.input i = a.subst.image (ids i)) ∧ q.value () = u) :
    Exact (ruleRoot rules) ids (fun _ => t) rows := by
  intro ρ hρ y norm
  let ctx := keys.map fun i => (Term.var (ids i) : Term sig)
  let vals := keys.map fun i => ρ.image (ids i)
  have ctxForms : Aligned (fun v u => NormalForm (ruleRoot rules) (ρ.apply v) u) ctx vals :=
    aligned_maps keys _ _ (fun i _ => ⟨.basis (.refl _),hρ _,fun _ h => h⟩)
  constructor
  · intro forms
    obtain ⟨a,mem,δ,nd,agree,values⟩ := complete.2 ρ hρ (y () :: vals) ⟨forms (),ctxForms⟩
    cases hv : a.values with
    | nil => rw [hv] at values; contradiction
    | cons u rest =>
      let q : Row sig I Unit := ⟨fun i => a.subst.image (ids i),fun _ => u⟩
      refine ⟨q,(members q).mpr ⟨a,mem,u,rest,hv,fun _ => rfl,rfl⟩,δ,nd,?_,?_⟩
      · intro i
        apply agree
        exact ⟨.var (ids i),List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun j => Term.var (ids j)) (allKeys i)),rfl⟩
      · intro k; cases k; rw [hv] at values; exact values.1
  · rintro ⟨q,mem,δ,_,fit⟩ k
    obtain ⟨a,am,u,rest,hv,hi,hu⟩ := (members q).mp mem
    have sound := (complete.1 a am).2
    rw [hv] at sound
    cases k
    apply form_of_instance hρ typed (δ := δ) (σ := a.subst) _ sound.1 _ (norm ())
    · intro v h; obtain ⟨i,rfl⟩ := includes v h
      change EquivB _ (δ.apply (a.subst.image (ids i)))
      simpa only [hi] using fit.inputs i
    · simpa only [hu] using fit.values ()

end Tamarin.Rewriting.VariantJoin
