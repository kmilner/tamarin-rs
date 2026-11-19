import Tamarin.XorFlat

/-! The parity invariant survives every contextual rewrite, including a
compound cancellation exposed only by AC reassociation. -/
namespace Tamarin.Rewriting.FreshXor.Flat.Table
open Cancellation ConstructorVariants
variable {sig : Signature} (T : Flat.Table sig)

noncomputable section
open Classical
abbrev bag := Cancellation.flatten T.f
abbrev zeroClass := classOf T.zero

theorem bag_zero : T.bag T.zero = [T.zeroClass] := by
  obtain ⟨g,args,h⟩ := T.zeroFree
  unfold zeroClass; rw [h]; rfl

theorem bag_nonempty (t : Term sig) : T.bag t ≠ [] := by
  intro eq
  have h := fold_flatten T.f t
  change fold T.f (T.bag t) = _ at h
  rw [eq] at h
  contradiction

include T in
theorem leaf_eq {a b : Term sig} (h : HasSort a .fresh) (e : EquivB a b) : a = b := by
  have := T.toTable.fresh_leaf h
  cases a <;> cases b <;> first | contradiction | (cases e.head_eq <;> rfl)

theorem bag_leaf {t : Term sig} (ht : HasSort t .fresh) : T.bag t = [classOf t] := by
  have := T.toTable.fresh_leaf ht
  cases t <;> first | contradiction | rfl

theorem not_zero {t : Term sig} (ht : HasSort t .fresh) : classOf t ≠ T.zeroClass := by
  intro eq
  have he := T.leaf_eq ht (Quotient.exact eq)
  obtain ⟨g,args,ez⟩ := T.zeroFree
  have := T.toTable.fresh_leaf ht
  rw [he,ez] at this
  exact this

/-- Each opaque factor is either the unit or a normalized Fresh leaf. -/
def Pure (t : Term sig) : Prop := ∀ k ∈ T.bag t, k = T.zeroClass ∨
  ∃ a : Term sig, HasSort a .fresh ∧ Normal T.R a ∧ classOf a = k

def Preserved (s t : Term sig) : Prop := T.Pure t ∧
  ∀ k, k ≠ T.zeroClass → (T.bag s).count k % 2 = (T.bag t).count k % 2

theorem pure_zero : T.Pure T.zero := by
  intro k hk
  exact Or.inl (by simpa [T.bag_zero] using hk)

theorem pure_ac (a b : Term sig) : T.Pure (.ac T.f a b) ↔ T.Pure a ∧ T.Pure b := by
  simp [Pure,bag,flatten_ac,List.mem_append,or_imp,forall_and]

theorem pure_normal {t : Term sig} (p : T.Pure t) (alien : T.bag t = [classOf t]) : Normal T.R t := by
  rcases p _ (alien ▸ List.mem_cons_self) with h | ⟨a,_,ha,h⟩
  · exact (normal_equiv _ (Quotient.exact h)).mpr T.toTable.zero_normal
  · exact (normal_equiv _ (Quotient.exact h)).mp ha

theorem kept {s t : Term sig} (p : T.Pure s) (e : EquivB s t) : T.Preserved s t :=
  ⟨fun k hk => p k ((flatten_equiv T.f e).mem_iff.mpr hk),
   fun k _ => congrArg (· % 2) ((flatten_equiv T.f e).count_eq k)⟩

theorem combine {a b c d : Term sig} (pa : T.Preserved a c) (pb : T.Preserved b d) :
    T.Preserved (.ac T.f a b) (.ac T.f c d) := by
  refine ⟨(T.pure_ac ..).mpr ⟨pa.1,pb.1⟩,?_⟩
  intro k ne
  have ha := pa.2 k ne
  have hb := pb.2 k ne
  simp only [bag,flatten_ac,List.count_append] at *
  omega

theorem through {a b c : Term sig} (p : T.Preserved a b) (q : T.Preserved b c) :
    T.Preserved a c := ⟨q.1, fun k ne => (p.2 k ne).trans (q.2 k ne)⟩

theorem root_cases {p q : Term sig} (atXor : head p = .ac T.f) (step : T.R p q) :
    (∃ a, p = .ac T.f a a ∧ q = T.zero) ∨
    (∃ a, p = .ac T.f a T.zero ∧ q = a) ∨
    (∃ a b, p = .ac T.f a (.ac T.f a b) ∧ q = b) ∨
    (∃ a b, p = .ac T.f (.ac T.f a a) b ∧ q = b) := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := step
  rw [instance_head r (T.apps r hr) σ] at atXor
  rcases T.inventory r hr atXor with rfl | ⟨v,rfl⟩ | ⟨u,v,rfl⟩ | ⟨u,v,rfl⟩
  · exact Or.inl ⟨_,rfl,T.toTable.fixes_zero σ⟩
  · exact Or.inr (.inl ⟨_,congrArg (Term.ac T.f _) (T.toTable.fixes_zero σ),rfl⟩)
  · exact Or.inr (.inr (.inl ⟨_,_,rfl,rfl⟩))
  · exact Or.inr (.inr (.inr ⟨_,_,rfl,rfl⟩))

theorem root_kept {p q : Term sig} (pure : T.Pure p) (atXor : head p = .ac T.f) (step : T.R p q) :
    T.Preserved p q := by
  rcases T.root_cases atXor step with ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
  all_goals constructor
  · exact T.pure_zero
  · intro k ne; simp [bag,flatten_ac,T.bag_zero,Ne.symm ne]; omega
  · exact ((T.pure_ac ..).mp pure).1
  · intro k ne; simp only [bag,flatten_ac,List.count_append]; rw [← bag, T.bag_zero]; simp [Ne.symm ne]
  · exact ((T.pure_ac ..).mp ((T.pure_ac ..).mp pure).2).2
  · intro k ne; simp only [bag,flatten_ac,List.count_append]; omega
  · exact ((T.pure_ac ..).mp pure).2
  · intro k ne; simp only [bag,flatten_ac,List.count_append]; omega

private theorem alien_bag {t : Term sig} (h : head t ≠ .ac T.f) : T.bag t = [classOf t] := by
  cases t with
  | ac f a b =>
    have ne : T.f ≠ f := fun e => h (e ▸ rfl)
    simp [bag,flatten,ne]
  | _ => rfl

theorem step_kept {a b : Term sig} (step : Step T.R a b) (pure : T.Pure a) : T.Preserved a b := by
  by_cases he : head a = .ac T.f
  · induction step with
    | root hr => exact T.root_kept pure he hr
    | @ac_left g childTerm result c st ih =>
      have h : g = T.f := Head.ac.inj he
      subst g
      obtain ⟨pl,pr⟩ := (T.pure_ac ..).mp pure
      apply T.combine _ (T.kept pr (.refl _))
      by_cases child : head childTerm = .ac T.f
      · exact ih pl child
      · exact False.elim ((T.pure_normal pl (T.alien_bag child)) _ ⟨_,_,.refl _,st,.refl _⟩)
    | @ac_right g c childTerm result st ih =>
      have h : g = T.f := Head.ac.inj he
      subst g
      obtain ⟨pl,pr⟩ := (T.pure_ac ..).mp pure
      apply T.combine (T.kept pl (.refl _))
      by_cases child : head childTerm = .ac T.f
      · exact ih pr child
      · exact False.elim ((T.pure_normal pr (T.alien_bag child)) _ ⟨_,_,.refl _,st,.refl _⟩)
    | free | comm_left | comm_right => contradiction
  · exact False.elim ((T.pure_normal pure (T.alien_bag he)) _ ⟨_,_,.refl _,step,.refl _⟩)

theorem reduces_kept {a b : Term sig} (red : Reduces T.R a b) (pure : T.Pure a) : T.Preserved a b := by
  induction red with
  | basis e => exact T.kept pure e
  | step hs =>
    obtain ⟨p,q,e,st,d⟩ := hs
    have one := T.kept pure e
    have two := T.step_kept st one.1
    exact T.through one (T.through two (T.kept two.1 d))
  | trans _ _ ia ib => exact T.through (ia pure) (ib (ia pure).1)
  | ac f l r il ir =>
    by_cases eq : f = T.f
    · subst f; obtain ⟨a,b⟩ := (T.pure_ac ..).mp pure; exact T.combine (il a) (ir b)
    · exact T.kept pure (normal_reduces_equiv (.ac _ l r) (T.pure_normal pure (T.alien_bag (fun e => eq (Head.ac.inj e)))))
  | free f a b reds ih =>
    exact T.kept pure (normal_reduces_equiv (.free _ _ _ reds) (T.pure_normal pure rfl))
  | comm f l r il ir =>
    exact T.kept pure (normal_reduces_equiv (.comm _ l r) (T.pure_normal pure rfl))

end
end Tamarin.Rewriting.FreshXor.Flat.Table
