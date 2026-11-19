import Tamarin.ContextualReduction
import Tamarin.RuleAtHead
import Tamarin.VariableElimination

/-! Outermost contraction of a total left-linear rule at a free head.
Arguments may take arbitrary reductions first, including in erased positions. -/
namespace Tamarin.Rewriting.TotalFree
open ConstructorVariants
variable {s : Signature} {R : Root s} {f : s.FreeSym}

noncomputable def lookup (key : Fin (s.arity f) → Variable)
    (xs : Fin (s.arity f) → Term s) (v : Variable) : Term s := by
  classical
  exact if h : ∃ i, key i = v then xs h.choose else .var v

theorem lookup_key {key : Fin (s.arity f) → Variable} (inj : Function.Injective key)
    (xs : Fin (s.arity f) → Term s) (i) : lookup key xs (key i) = xs i := by
  classical
  have h : ∃ j, key j = key i := ⟨i,rfl⟩
  simp only [lookup, dite_eq_left h, inj h.choose_spec]

private theorem lift_term (p : Term s) (a b : Variable → Term s)
    (h : ∀ v, Reduces R (a v) (b v)) : Reduces R (p.subst a) (p.subst b) := by
  induction p with
  | var v => exact h v
  | atom _ => exact .basis (.refl _)
  | free d _ children => exact .free d _ _ children
  | comm d _ _ x y => exact .comm d x y
  | ac d _ _ x y => exact .ac d x y

/-- All term-level premises follow from a single complete rule bucket. Other
heads, and the right-hand side, may use any part of the ambient rewrite theory. -/
structure Rule (rules : List (Equation s)) (f : s.FreeSym) where
  keys : Fin (s.arity f) → Variable
  distinct : Function.Injective keys
  accepts : ∀ i, Subsort (s.inputSort f i) (keys i).sort
  rhs : Term s
  bound : ∀ v, rhs.Occurs v → ∃ i, keys i = v
  apps : ∀ r ∈ rules, Application r.lhs
  present : (⟨.free f (fun i => .var (keys i)),rhs⟩ : Equation s) ∈ rules
  only : ∀ r ∈ rules, head r.lhs = .free f → r = ⟨.free f (fun i => .var (keys i)),rhs⟩

variable {rules : List (Equation s)} (rule : Rule rules f)

noncomputable def contract (xs : Fin (s.arity f) → Term s) := rule.rhs.subst (lookup rule.keys xs)

private theorem contract_mono {xs ys : Fin (s.arity f) → Term s}
    (h : ∀ i, Reduces R (xs i) (ys i)) : Reduces R (contract rule xs) (contract rule ys) := by
  apply lift_term
  intro v
  classical
  unfold lookup
  split
  · exact h _
  · exact .basis (.refl _)

theorem enabled (xs : Fin (s.arity f) → Term s) (typed : ∀ i, HasSort (xs i) (s.inputSort f i)) :
    ruleRoot rules (.free f xs) (contract rule xs) := by
  classical
  let σ : Substitution s := {
    image := lookup rule.keys xs
    support := List.ofFn rule.keys
    outside := by
      intro v hv
      simp only [List.mem_ofFn] at hv
      simp [lookup,hv]
    sorted := by
      intro v
      unfold lookup
      split
      next h => simpa only [h.choose_spec] using HasSort.widen (typed h.choose) (rule.accepts h.choose)
      next => exact .var _ }
  apply (ruleRoot_unique_free_iff rules f _ _ rule.apps rule.present rule.only xs _).mpr
  exact ⟨σ, fun i => (lookup_key rule.distinct xs i).symm, rfl⟩

private theorem root_eq {xs : Fin (s.arity f) → Term s} {b}
    (hit : ruleRoot rules (.free f xs) b) : contract rule xs = b := by
  obtain ⟨σ,hs,rfl⟩ := (ruleRoot_unique_free_iff rules f _ _ rule.apps rule.present rule.only xs b).mp hit
  apply Term.subst_eq_of_agree
  intro v hv
  obtain ⟨i,rfl⟩ := rule.bound _ hv
  exact (lookup_key rule.distinct xs i).trans (hs i)

/-- Before the first root contraction only the original children change.
After the first root contraction every visited state descends from the
immediate contractum, even through duplicating, reordering or erasing rules. -/
theorem factors {xs : Fin (s.arity f) → Term s} {u}
    (path : Reduces (ruleRoot rules) (.free f xs) u) :
    (∃ ys, u = .free f ys ∧ ∀ i, Reduces (ruleRoot rules) (xs i) (ys i)) ∨
      Reduces (ruleRoot rules) (contract rule xs) u := by
  let P (t : Term s) := (∃ ys, t = .free f ys ∧ ∀ i, Reduces (ruleRoot rules) (xs i) (ys i)) ∨
    Reduces (ruleRoot rules) (contract rule xs) t
  apply RootNarrowing.reduction_invariant P _ _ path (Or.inl ⟨xs,rfl,fun _ => .basis (.refl _)⟩)
  · intro _ _ state eq
    rcases state with ⟨ys,rfl,h⟩|r
    · obtain ⟨zs,rfl,aligned⟩ := free_equiv_view eq
      exact Or.inl ⟨zs,rfl,fun i => (h i).trans (.basis (aligned i))⟩
    · exact Or.inr (r.trans (.basis eq))
  · intro _ _ state step
    rcases state with ⟨ys,rfl,h⟩|r
    · rcases (ContextualReduction.free_iff f ys _).mp step with ⟨_,_,pre,hit,post⟩|⟨i,v,change,out⟩
      · obtain ⟨zs,rfl,aligned⟩ := free_equiv_view pre
        exact Or.inr ((contract_mono rule (fun i => (h i).trans (.basis (aligned i)))).trans
          (.basis ((root_eq rule hit) ▸ post)))
      · obtain ⟨zs,rfl,aligned⟩ := free_equiv_view out
        refine Or.inl ⟨zs,rfl,fun j => (h j).trans (?_ : Reduces _ (ys j) (zs j))⟩
        by_cases e : j = i
        · subst j; exact (.step change : Reduces _ _ _).trans (.basis (by simpa using aligned i))
        · exact .basis (by simpa [e] using aligned j)
    · exact Or.inr (r.trans (.step step))

/-- The exact reachable normal endpoints at the declared output sort survive
outermost contraction. No global termination, subject-reduction or confluence
assumption is needed for the ambient theory. -/
theorem terminal_iff (xs : Fin (s.arity f) → Term s) (typed : ∀ i, HasSort (xs i) (s.inputSort f i))
    {u : Term s} (normal : Normal (ruleRoot rules) u) (well : HasSort u (s.outputSort f)) :
    Reduces (ruleRoot rules) (.free f xs) u ↔ Reduces (ruleRoot rules) (contract rule xs) u := by
  constructor
  · intro red
    rcases factors rule red with ⟨ys,rfl,_⟩|red
    · have slots := Term.checkSort_complete well
      simp only [Term.checkSort,Bool.and_eq_true,List.all_eq_true] at slots
      exact (normal _ ⟨_,_,.refl _,.root (enabled rule ys (fun i =>
        Term.checkSort_sound _ _ (slots.2 i (List.mem_finRange i)))),.refl _⟩).elim
    · exact red
  · exact fun red => (.step ⟨_,_,.refl _,.root (enabled rule xs typed),.refl _⟩ :
      Reduces _ (.free f xs) (contract rule xs)).trans red

/-- A directly normal contractum can have a narrower sort than the free
head. Its uniqueness still follows from the untyped reachability statement. -/
theorem normal_contract (xs : Fin (s.arity f) → Term s) (typed : ∀ i, HasSort (xs i) (s.inputSort f i))
    (out : HasSort (contract rule xs) (s.outputSort f)) (n : Normal (ruleRoot rules) (contract rule xs)) :
    NormalForm (ruleRoot rules) (.free f xs) (contract rule xs) ∧
      ∀ u, NormalForm (ruleRoot rules) (.free f xs) u → EquivB (contract rule xs) u := by
  refine ⟨⟨(terminal_iff rule xs typed n out).mpr (.basis (.refl _)),n,
    fun _ h => .widen out (Term.rootSort_le h)⟩, ?_⟩
  intro u nf
  exact normal_reduces_equiv ((terminal_iff rule xs typed nf.2.1 (nf.2.2 _ (.free f xs typed))).mp nf.1) n

theorem normal_iff (xs : Fin (s.arity f) → Term s) (typed : ∀ i, HasSort (xs i) (s.inputSort f i))
    (out : HasSort (contract rule xs) (s.outputSort f))
    (principal : (contract rule xs).rootSort = s.outputSort f) (u : Term s) :
    NormalForm (ruleRoot rules) (.free f xs) u ↔ NormalForm (ruleRoot rules) (contract rule xs) u := by
  have sorts (k) : HasSort (.free f xs) k ↔ HasSort (contract rule xs) k := by
    constructor
    · exact fun h => .widen out (Term.rootSort_le h)
    · exact fun h => .widen (.free f xs typed) (principal ▸ Term.rootSort_le h)
  constructor <;> rintro ⟨red,n,hs⟩
  · exact ⟨(terminal_iff rule xs typed n (hs _ (.free f xs typed))).mp red,n,
      fun k h => hs k ((sorts k).mpr h)⟩
  · exact ⟨(terminal_iff rule xs typed n (hs _ out)).mpr red,n,
      fun k h => hs k ((sorts k).mp h)⟩

end Tamarin.Rewriting.TotalFree
