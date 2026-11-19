import Tamarin.VariantSaturation
import Tamarin.ReductionHeight
import Tamarin.UnifierSorts

/-! Maude normalizes the seed and the value of each variant before inserting
it into the folder. This reference normalizes all slots of the packed tuple.
The finite variant property proves termination from genuine, complete local
narrowing alone. -/
namespace Tamarin.FoldingNarrowing
open Rewriting VariantJoin MaudeOperations ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature} {n : Nat} {rules : List (Equation s)} {query : Fin n → Term s}

/-- Local narrowing may choose any branch representation or enumeration.
The soundness obligation replays a single rewrite at that slot. The lifting
obligation covers concrete specializations while preserving the visible names. -/
structure Narrower (rules : List (Equation s)) (query : Fin n → Term s) where
  branches : Point s n → Fin n → List (RootNarrowing.Branch s)
  genuine : ∀ p, VariantSaturation.Sound rules query p → ∀ i b, b ∈ branches p i →
    StepModulo (ruleRoot rules) (b.subst.apply (p.value i)) b.value
  lifts : ∀ p, VariantSaturation.Sound rules query p → ∀ i,
    RootNarrowing.Search (ruleRoot rules) (p.row (keysOf query)).Uses
      (fun δ => ∀ k : Key (keysOf query), Normal (ruleRoot rules) (δ.apply (p.assignment.image k.val)))
      (p.value i) (· ∈ branches p i)

private def normalized (r : VerifiedReducer (ruleRoot rules)) (p : Point s n) : Point s n :=
  ⟨p.assignment,fun i => r.reduce (p.value i)⟩

private theorem projected (p : Point s n) (query : Fin n → Term s) (i : Fin n) :
    (p.answer (keysOf query)).subst.apply (query i) = p.assignment.apply (query i) := by
  apply Term.subst_eq_of_agree
  intro v hv
  have mem := (observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
  exact (p.row _).project_key (fun k => p.assignment.sorted k.val) ⟨v,mem⟩

private theorem sound_normalized (r : VerifiedReducer (ruleRoot rules))
    (canonical : CanonicalPresentation (ruleRoot rules)) (vars : Normalized (ruleRoot rules) Substitution.identity)
    (p : Point s n) (normal : ∀ i : Key (keysOf query), Normal (ruleRoot rules) (p.assignment.image i.val))
    (replay : ∀ i, Reduces (ruleRoot rules) (p.assignment.apply (query i)) (p.value i)) :
    VariantSaturation.Sound rules query (normalized r p) := by
  let q := normalized r p
  have values (i) := (r.correct (p.value i)).normalForm
  refine ⟨(q.row _).project_normal (fun k => p.assignment.sorted k.val) vars ⟨normal,fun i => (values i).2.1⟩,
    alignedFn query q.value (fun i => ?_)⟩
  rw [projected q query i]
  have source := (r.correct (p.assignment.apply (query i))).normalForm
  have red := (replay i).trans (values i).1
  obtain ⟨_,left,right⟩ := canonical.confluent source.1 red
  have same := (normal_reduces_equiv left source.2.1).trans (normal_reduces_equiv right (values i).2.1).symm
  exact ⟨red,(values i).2.1,fun k hk => Term.checkSort_sound _ _ (SortClash.check_equiv same k ▸
    Term.checkSort_complete (source.2.2 k hk))⟩

private theorem replay_child (p : Point s n) (good : VariantSaturation.Sound rules query p)
    (m : Narrower rules query) (c : Point s n) (mem : c ∈ expand p (m.branches p)) (i : Fin n) :
    Reduces (ruleRoot rules) (c.assignment.apply (query i)) (c.value i) := by
  obtain ⟨j,_,h⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
  have source := (VariantSaturation.atFn query p.value good.2 i).1
  rw [projected p query i] at source
  have red := SpecializedFresh.reduces_subst rules b.subst source
  rw [← Substitution.apply_compose] at red
  by_cases same : i = j
  · subst j
    exact (by simpa [replace] using red.trans (.step (m.genuine p good i b hb)))
  · simpa [replace,same] using red

private theorem sum_mono {a b : Fin n → Nat} (le : ∀ i, a i ≤ b i) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := b),List.sum_cons,List.sum_cons]
    exact Nat.add_le_add (le 0) (ih (fun i => le i.succ))

private theorem sum_strict {a b : Fin n → Nat} (le : ∀ i, a i ≤ b i) (j : Fin n) (lt : a j < b j) :
    (List.ofFn a).sum < (List.ofFn b).sum := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := b),List.sum_cons,List.sum_cons]
    cases j using Fin.cases with
    | zero => exact Nat.add_lt_add_of_lt_of_le lt (sum_mono (fun i => le i.succ))
    | succ k => exact Nat.add_lt_add_of_le_of_lt (le 0) (ih (fun i => le i.succ) k lt)

section
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def admissible (rules : List (Equation s)) (query : Fin n → Term s) (p : Point s n) :=
  (keysOf query).all (fun v => (ReferenceReduction.successors rules (p.assignment.image v)).isEmpty)

private theorem admissible_iff (bound : ReferenceReduction.Bound rules) (p : Point s n) :
    admissible rules query p = true ↔ ∀ i : Key (keysOf query), Normal (ruleRoot rules) (p.assignment.image i.val) := by
  constructor
  · intro h i u step
    obtain ⟨v,hv,_⟩ := (ReferenceReduction.exactSteps rules bound _ _).mpr step
    rw [List.isEmpty_iff.mp (List.all_eq_true.mp h i.val i.property)] at hv
    exact List.not_mem_nil hv
  · intro h
    apply List.all_eq_true.mpr
    intro v hv
    exact List.isEmpty_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr (fun u hu =>
      h ⟨v,hv⟩ u ((ReferenceReduction.exactSteps rules bound ..).mp ⟨u,hu,.refl _⟩)))

def expansion (bound : ReferenceReduction.Bound rules) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (r : VerifiedReducer (ruleRoot rules))
    (m : Narrower rules query) : VariantSaturation.Expansion rules query where
  seed := normalized r (seed query)
  next p := ((expand p (m.branches p)).filter (admissible rules query)).map (normalized r)
  identity _ _ := rfl
  initial := sound_normalized r canonical vars _ (fun i => vars i.val)
    (fun i => by simp [seed]; exact .basis (.refl _))
  preserves p good c mem := by
    obtain ⟨raw,hm,rfl⟩ := List.mem_map.mp mem
    obtain ⟨member,ok⟩ := List.mem_filter.mp hm
    exact sound_normalized r canonical vars raw ((admissible_iff bound raw).mp ok) (replay_child p good m _ member)
  measure y := (List.ofFn (fun i => ReductionHeight.height bound canonical.terminating (y i))).sum
  invariant x y same := by
    simp only [show (fun i => ReductionHeight.height bound canonical.terminating (x i)) =
      (fun i => ReductionHeight.height bound canonical.terminating (y i)) from
        funext (fun i => ReductionHeight.equiv bound _ (same i))]
  progress p good δ hn := by
    classical
    by_cases done : ∀ i, Normal (ruleRoot rules) (δ.apply (p.value i))
    · exact .inl done
    · obtain ⟨j,u,step⟩ : ∃ j u, StepModulo (ruleRoot rules) (δ.apply (p.value j)) u := by
        simpa only [Normal,Classical.not_forall,Classical.not_not] using done
      have coverage := expand_covers (keysOf query) p (m.branches p) (m.lifts p good)
      obtain ⟨_,hm,η,fit⟩ := coverage δ hn j u step
      obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp hm
      have live := (admissible_iff (query := query) bound raw).mpr fun i =>
        normal_of_instance ((normal_equiv _ (fit.inputs i)).mp (hn i))
      refine .inr ⟨_,List.mem_map_of_mem (List.mem_filter.mpr ⟨hr,live⟩),η,fit.inputs,?_⟩
      let height := ReductionHeight.height bound canonical.terminating
      have each (i) : height (η.apply ((normalized r raw).value i)) ≤
          height (replace (fun k => δ.apply (p.value k)) j u i) := by
        exact Nat.le_trans (ReductionHeight.reduces bound canonical.terminating
          (SpecializedFresh.reduces_subst rules η (r.correct (raw.value i)).normalForm.1))
          (Nat.le_of_eq (ReductionHeight.equiv bound canonical.terminating (fit.values i)).symm)
      have strict : height (η.apply ((normalized r raw).value j)) < height (δ.apply (p.value j)) :=
        Nat.lt_of_le_of_lt (by simpa [replace] using each j) (ReductionHeight.step bound _ step)
      apply sum_strict _ j strict
      intro i
      by_cases same : i = j
      · exact same ▸ Nat.le_of_lt strict
      · simpa [replace,same] using each i

/-- Given a complete local narrower for each query, this implements the whole
Maude variants command. Finiteness is used only to prove the loop terminates. -/
def generator (bound : ReferenceReduction.Bound rules) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (finite : FiniteVariantProperty (ruleRoot rules))
    (m : ∀ (q : List (Term s)), Narrower rules (fun i : Fin q.length => q[i.val])) :
    VerifiedVariantGenerator (ruleRoot rules) := by
  let r := ReferenceReduction.reducer rules bound canonical
  let run (q : List (Term s)) (avoid : List Variable) :=
    VariantSaturation.solve (expansion bound canonical vars r (m q)) canonical vars r
      (by simpa only [List.ofFn_getElem] using finite q) avoid
  exact ⟨fun q avoid => (run q avoid).val,fun q avoid => by simpa only [List.ofFn_getElem] using (run q avoid).property⟩

/-- Assemble the four semantic command implementations for one active table.
The two remaining algorithmic inputs are the raw mixed unifier and local
narrowing. Presentation properties are about the caller’s equation table. -/
def reference (raw : Problem s → List (UnifierSorts.Template s))
    (complete : ∀ p, UnifierSorts.CompleteTemplates p (raw p))
    (bound : ReferenceReduction.Bound rules) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (finite : FiniteVariantProperty (ruleRoot rules))
    (m : ∀ (q : List (Term s)), Narrower rules (fun i : Fin q.length => q[i.val])) :
    MaudeOperations.Reference s rules where
  unify := UnifierSorts.unifier raw complete
  matchTerms := ReferenceMatching.matcher s
  reduce := ReferenceReduction.reducer rules bound canonical
  variants := generator bound canonical vars finite m

end
end Tamarin.FoldingNarrowing
