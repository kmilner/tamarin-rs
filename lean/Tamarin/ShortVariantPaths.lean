import Tamarin.CompleteNarrowing

/-! A finite variant family only needs one bounded normalization per instance.
Other rewrites from the same instance may follow arbitrarily long detours. -/
namespace Tamarin.ShortVariantPaths
open Rewriting MaudeOperations VariantJoin ReferenceVariantFrontier TupleNarrowingFrontier

variable {s : Signature} {R : Root s}

/-- At most `k` genuine rewrites, allowing any basis rearrangement for free. -/
inductive Path (R : Root s) : Nat → Term s → Term s → Prop where
  | basis {k a b} : EquivB a b → Path R k a b
  | step {k a b c} : StepModulo R a b → Path R k b c → Path R (k+1) a c

theorem Path.rebase {k a b c} (eq : EquivB a b) (p : Path R k b c) : Path R k a c := by
  cases p with
  | basis h => exact .basis (eq.trans h)
  | step h p =>
    obtain ⟨x,y,e,st,e'⟩ := h
    exact .step ⟨x,y,eq.trans e,st,e'⟩ p

private def prefixTree {α : Type} (next : α → List α) (p : α) : Nat → List α
  | 0 => [p]
  | k+1 => p :: (next p).flatMap (fun q => prefixTree next q k)

private theorem root_mem {α} (next : α → List α) (p) (k) : p ∈ prefixTree next p k := by
  cases k <;> simp [prefixTree]

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable {rs : List (Equation s)} {n : Nat} (bound : ReferenceReduction.Bound rs)
  (can : CanonicalPresentation (ruleRoot rs)) (q : Fin n → Term s)

private abbrev steps (p : Point s n) := let u := MixedUnification.verified (s := s)
  TableNarrowing.atPoint u bound (TableNarrowing.groups u bound (TableNarrowing.variablesNormal can))
    (keysOf q) p

private abbrev next (p : Point s n) := expand p (steps bound can q p).branches

private def Replay (p : Point s n) := ∀ i, Reduces (ruleRoot rs) (p.assignment.apply (q i)) (p.value i)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
include bound in
private theorem tracked {p : Point s n} (r : Replay (rs := rs) q p) : TableNarrowing.Tracked (keysOf q) p := by
  intro i v hv
  obtain ⟨w,hw,occ⟩ := p.assignment.occurs_in_image _ _ (TableNarrowing.reducesUses bound (r i) v hv)
  exact ⟨⟨w,(observed q w).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hw⟩⟩,occ⟩

private theorem child {p c : Point s n} (r : Replay (rs := rs) q p) (mem : c ∈ next bound can q p) :
    Replay (rs := rs) q c := by
  obtain ⟨j,_,hs⟩ := List.mem_flatMap.mp mem
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  intro i
  have red := SpecializedFresh.reduces_subst rs b.subst (r i)
  rw [← Substitution.apply_compose] at red
  by_cases same : i = j
  · subst j
    exact (by simpa [replace] using red.trans (.step ((steps bound can q p).genuine i b hb)))
  · simpa [replace,same] using red

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
include can in
private theorem completed {p : Point s n} (r : Replay (rs := rs) q p)
    (norm : (p.row (keysOf q)).IsNormal (ruleRoot rs)) : VariantSaturation.Sound rs q p := by
  let a := p.answer (keysOf q)
  refine ⟨(p.row _).project_normal (fun k => p.assignment.sorted k.val)
    (TableNarrowing.variablesNormal can) norm,alignedFn q p.value (fun i => ?_)⟩
  have eq : a.subst.apply (q i) = p.assignment.apply (q i) :=
    Term.subst_eq_of_agree _ _ _ fun v hv => (p.row _).project_key (fun k => p.assignment.sorted k.val)
      ⟨v,(observed q v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩⟩
  change NormalForm _ (a.subst.apply (q i)) _
  rw [eq]
  refine ⟨r i,norm.2 i,fun k h => ?_⟩
  exact RootNarrowing.reduction_invariant (fun t => HasSort t k)
    (fun h e => Term.checkSort_sound _ _ (SortClash.check_equiv e k ▸ Term.checkSort_complete h))
    (fun h st => can.sortPreserving st k h) (r i) h

private theorem sum_strict {a b : Fin n → Nat} (le : ∀ i, a i ≤ b i) (j : Fin n) (lt : a j < b j) :
    (List.ofFn a).sum < (List.ofFn b).sum := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ (f := b),List.sum_cons,List.sum_cons]
    cases j using Fin.cases with
    | zero => exact Nat.add_lt_add_of_lt_of_le lt (FoldingNarrowing.sum_mono (fun i => le i.succ))
    | succ k => exact Nat.add_lt_add_of_le_of_lt (le 0) (ih (fun i => le i.succ) k lt)

private theorem lift (fuel : Nat) (p : Point s n) (r : Replay (rs := rs) q p)
    (x : Key (keysOf q) → Term s) (nx : ∀ i, Normal (ruleRoot rs) (x i))
    (y : Fin n → Term s) (ny : ∀ i, Normal (ruleRoot rs) (y i))
    (δ : Substitution s) (agree : ∀ i : Key (keysOf q), EquivB (x i) (δ.apply (p.assignment.image i.val)))
    (depth : Fin n → Nat) (budget : (List.ofFn depth).sum ≤ fuel)
    (paths : ∀ i, Path (ruleRoot rs) (depth i) (δ.apply (p.value i)) (y i)) :
    ∃ c ∈ prefixTree (next bound can q) p fuel, VariantSaturation.Sound rs q c ∧
      ∃ η, Fits (c.row (keysOf q)) x y η := by
  classical
  by_cases done : ∀ i, EquivB (δ.apply (p.value i)) (y i)
  · have fit : Fits (p.row (keysOf q)) x y δ := ⟨agree,fun i => (done i).symm⟩
    have normal := (normal_witness (TableNarrowing.variablesNormal can) nx ny fit).1
    exact ⟨p,root_mem ..,completed can q r normal,δ,fit⟩
  · obtain ⟨j,more⟩ := Classical.not_forall.mp done
    obtain ⟨k,u,e,fire,rest⟩ : ∃ k u, depth j = k+1 ∧
        StepModulo (ruleRoot rs) (δ.apply (p.value j)) u ∧ Path (ruleRoot rs) k u (y j) := by
      generalize hs : depth j = d at *
      have pp := paths j
      rw [hs] at pp
      cases pp with
      | basis h => contradiction
      | step h t => exact ⟨_,_,rfl,h,t⟩
    let dk (i : Fin n) := if i=j then k else depth i
    have less : (List.ofFn dk).sum < (List.ofFn depth).sum := sum_strict
      (fun i => by by_cases h : i=j <;> simp [dk,h,e]) j (by simp [dk,e])
    obtain ⟨row,hr,η,fit⟩ := expand_covers (keysOf q) p _ ((steps bound can q p).covers (tracked bound q r))
      δ (fun i => (normal_equiv _ (agree i)).mp (nx i)) j u fire
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
    have along (i) : Path (ruleRoot rs) (dk i) (η.apply (c.value i)) (y i) := by
      by_cases same : i = j
      · subst i
        simpa [dk] using rest.rebase (by simpa [replace,Point.row] using (fit.values j).symm)
      · simpa [dk,same] using (paths i).rebase (by simpa [replace,same,Point.row] using (fit.values i).symm)
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨c',mem,res⟩ := lift fuel c (child bound can q r hc) x nx y ny η
        (fun i => (agree i).trans (fit.inputs i)) dk (by omega) along
      exact ⟨c',List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c,hc,mem⟩),res⟩
termination_by fuel

include bound can in
/-- It suffices to bound the length of one path to the normal form for each
normalized instance. The bound can depend on the open term. This criterion
allows presentations with unbounded maximal derivation heights on such instances. -/
theorem completeTuple (query : List (Term s)) (paths : ∀ t ∈ query, ∃ k, ∀ ρ : Substitution s,
    Normalized (ruleRoot rs) ρ → ∀ y, NormalForm (ruleRoot rs) (ρ.apply t) y →
    Path (ruleRoot rs) k (ρ.apply t) y) : ∃ rows, CompleteVariants (ruleRoot rs) query rows := by
  classical
  let terms (i : Fin query.length) := query[i.val]
  have path i := paths (terms i) (List.getElem_mem (l := query) i.isLt)
  let depth i := (path i).choose
  let fuel := (List.ofFn depth).sum
  let tree := prefixTree (next bound can terms) (seed terms) fuel
  let kept := tree.filter fun p => decide (VariantSaturation.Sound rs terms p)
  have sufficient := @VariantSaturation.complete_of_points s query.length rs terms (TableNarrowing.variablesNormal can) kept (fun p h => of_decide_eq_true (List.mem_filter.mp h).2)
  refine ⟨kept.map (Point.answer · (keysOf terms)),?_⟩
  simp only [show List.ofFn terms = query from List.ofFn_getElem] at sufficient
  apply sufficient
  intro ρ norm y forms
  have rp : Replay (rs := rs) terms (seed terms) := fun i => by simp [seed]; exact .basis (.refl _)
  obtain ⟨p,hp,ok,fit⟩ := lift bound can terms fuel (seed terms) rp (fun i => ρ.image i.val) (fun i => norm i.val)
    y (fun i => (forms i).2.1) ρ (fun i => .refl _) depth (Nat.le_refl _)
    (fun i => (path i).choose_spec ρ norm _ (forms i))
  exact ⟨p,List.mem_filter.mpr ⟨hp,decide_eq_true ok⟩,fit⟩

include bound can in
theorem finiteVariantProperty (paths : ∀ t : Term s, ∃ k, ∀ ρ : Substitution s,
    Normalized (ruleRoot rs) ρ → ∀ y, NormalForm (ruleRoot rs) (ρ.apply t) y →
    Path (ruleRoot rs) k (ρ.apply t) y) : FiniteVariantProperty (ruleRoot rs) :=
  fun q => completeTuple bound can q (fun t _ => paths t)

end Tamarin.ShortVariantPaths
