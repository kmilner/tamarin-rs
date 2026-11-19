import Tamarin.ConstructorReduction
import Tamarin.SortClash
import Tamarin.SpecializedRule
import Tamarin.StableVariants

namespace Tamarin.Rewriting.StableVariants
open ConstructorVariants
variable {s : Signature} {R : Root s}

/-- A unique closed normal value is uniform under every caller substitution. -/
theorem Representative.ground {t n : Term s} (closed : ∀ v, ¬ t.Occurs v)
    (valueClosed : ∀ v, ¬ n.Occurs v) (form : NormalForm R t n)
    (unique : ∀ u, NormalForm R t u → EquivB u n) : Representative R t n := by
  refine ⟨fun ρ _ => ?_, fun ρ _ => ?_, fun v h => (valueClosed v h).elim⟩
  · simpa only [SpecializedRule.apply_ground closed, SpecializedRule.apply_ground valueClosed] using form
  · simpa only [SpecializedRule.apply_ground closed, SpecializedRule.apply_ground valueClosed] using unique

/-- If the root cannot rewrite, every reduction projects to reductions in the
original argument positions, even when children take different rewrite paths. -/
theorem reduces_free_view (f : s.FreeSym) (inert : ∀ xs b, ¬ R (.free f xs) b)
    {xs : Fin (s.arity f) → Term s} {u : Term s} (red : Reduces R (.free f xs) u) :
    ∃ ys, u = .free f ys ∧ ∀ i, Reduces R (xs i) (ys i) := by
  have go {a b : Term s} (h : Reduces R a b) : ∀ xs, a = .free f xs →
      ∃ ys, b = .free f ys ∧ ∀ i, Reduces R (xs i) (ys i) := by
    induction h with
    | basis e =>
      rintro xs rfl
      obtain ⟨ys,eq,h⟩ := free_equiv_view e
      exact ⟨ys,eq,fun i => .basis (h i)⟩
    | step st =>
      rintro xs rfl
      obtain ⟨a,b,ea,step,eb⟩ := st
      obtain ⟨as,rfl,ha⟩ := free_equiv_view ea
      cases step with
      | root hr => exact (inert _ _ hr).elim
      | free _ _ k child =>
        obtain ⟨bs,rfl,hb⟩ := free_equiv_view eb
        refine ⟨bs,rfl,fun i => .trans (.basis (ha i)) (.trans ?_ (.basis (hb i)))⟩
        by_cases eq : i = k
        · subst i; simpa using (Reduces.step ⟨_,_,.refl _,child,.refl _⟩)
        · simp [eq]; exact .basis (.refl _)
    | trans _ _ ih ik =>
      intro xs eq
      obtain ⟨ys,mid,l⟩ := ih xs eq
      obtain ⟨zs,last,r⟩ := ik ys mid
      exact ⟨zs,last,fun i => (l i).trans (r i)⟩
    | free _ _ _ children _ => rintro _ ⟨⟩; exact ⟨_,rfl,children⟩
    | comm | ac => rintro _ ⟨⟩
  exact go red xs rfl

/-- Project an arbitrary normal form back to its child normal forms. The
parent's slot gives the sort of a changing child. A stable child's reduction
is a basis equivalence and hence preserves even a narrower input sort. -/
theorem normalForm_free_view (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads rules) (xs : Fin (s.arity f) → Term s)
    (typed : ∀ i, HasSort (xs i) (s.inputSort f i))
    (slots : ∀ i, Stable (ruleRoot rules) (xs i) ∨ ∀ ρ : Substitution s,
      (ρ.apply (xs i)).rootSort = s.inputSort f i)
    (ρ : Substitution s) (hn : Normalized (ruleRoot rules) ρ) {u : Term s}
    (nf : NormalForm (ruleRoot rules) (ρ.apply (.free f xs)) u) :
    ∃ us, u = .free f us ∧ ∀ i, NormalForm (ruleRoot rules) (ρ.apply (xs i)) (us i) := by
  have inert as b : ¬ ruleRoot rules (.free f as) b := by
    rintro ⟨r,mem,σ,eq,_⟩
    apply absent
    have hh := (congrArg head eq).trans (instance_head r (apps r mem) σ)
    change head (.free f as) ∈ ruleHeads rules
    rw [hh]
    exact List.mem_map_of_mem mem
  obtain ⟨us,rfl,red⟩ := reduces_free_view f inert nf.1
  have out := Term.checkSort_complete (nf.2.2 _ ((HasSort.free f xs typed).subst ρ.image ρ.sorted))
  simp only [Term.checkSort, Bool.and_eq_true, List.all_eq_true] at out
  refine ⟨us,rfl,fun i => ⟨red i,normal_free_child f us nf.2.1 i,?_⟩⟩
  intro sort hs
  rcases slots i with stable | same
  · have eq := normal_reduces_equiv (red i) (stable ρ hn)
    exact Term.checkSort_sound _ _ ((SortClash.check_equiv eq sort) ▸ Term.checkSort_complete hs)
  · apply HasSort.widen _ (Term.rootSort_le hs)
    rw [same ρ]
    exact Term.checkSort_sound _ _ (out.2 i (List.mem_finRange i))

/-- Representatives compose below an inert free symbol. An already-stable
child may have a narrower sort. For a changing child, the slot must certify
every sort needed to project a full normal form back to that child. -/
theorem Representative.free (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads rules) (xs ys : Fin (s.arity f) → Term s)
    (typed : ∀ i, HasSort (xs i) (s.inputSort f i))
    (reps : ∀ i, Representative (ruleRoot rules) (xs i) (ys i))
    (slots : ∀ i, Stable (ruleRoot rules) (xs i) ∨ ∀ ρ : Substitution s,
      (ρ.apply (xs i)).rootSort = s.inputSort f i) :
    Representative (ruleRoot rules) (.free f xs) (.free f ys) := by
  refine ⟨fun ρ hn => free_normalForm rules apps f absent _ _ (fun i => (reps i).normal ρ hn), ?_, ?_⟩
  · intro ρ hn u nf
    obtain ⟨us,rfl,forms⟩ := normalForm_free_view rules apps f absent xs typed slots ρ hn nf
    exact .free _ _ _ (fun i => (reps i).unique ρ hn _ (forms i))
  · rintro v ⟨i,occ⟩
    exact ⟨i,(reps i).variables v occ⟩

end Tamarin.Rewriting.StableVariants
