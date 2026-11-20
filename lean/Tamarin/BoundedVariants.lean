import Tamarin.SymbolWeight
import Tamarin.CompleteNarrowing

/-! A bound shared by all normalized substitutions of an open term gives
a finite complete family of variants. Individual ground termination alone
only gives a bound after choosing the substitution. -/
namespace Tamarin.BoundedVariants
open Rewriting MaudeOperations VariantJoin ReferenceVariantFrontier VariantSaturation
variable {s : Signature} {rules : List (Equation s)} {n : Nat} {query : Fin n → Term s}

private theorem prefix_covers (g : Expansion rules query) (canonical : CanonicalPresentation (ruleRoot rules))
    (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) (out : Fin n → Term s)
    (forms : ∀ i, NormalForm (ruleRoot rules) (ρ.apply (query i)) (out i))
    (limit : Nat) (bounded : g.measure (fun i => ρ.apply (g.seed.value i)) ≤ limit) :
    ∃ p ∈ (VariantLayers.after g.seed g.next limit).rows, ∃ δ,
      Fits (p.row (keysOf query)) (fun i => ρ.image i.val) out δ := by
  let keys := keysOf query
  have go (remaining : Nat) : ∀ depth, depth + remaining = limit → ∀ p,
      p ∈ (VariantLayers.after g.seed g.next depth).frontier → ∀ δ : Substitution s,
      (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply (p.assignment.image i.val))) →
      g.measure (fun i => δ.apply (p.value i)) ≤ remaining →
      ∃ q ∈ (VariantLayers.after g.seed g.next limit).rows, ∃ η,
        Fits (q.row keys) (fun i => ρ.image i.val) out η := by
    induction remaining using Nat.strongRecOn with
    | ind remaining smaller =>
      intro depth depthEq p front δ fit before
      have mem := List.mem_append_left (VariantLayers.after g.seed g.next depth).earlier front
      have good := sound_reached g (VariantLayers.reached depth mem)
      rcases g.progress p good δ (fun i => (normal_equiv _ (fit i)).mp (norm i.val)) with
        done | ⟨c,hc,η,agree,less⟩
      · exact ⟨p,VariantLayers.persists (by omega : depth ≤ limit) mem,δ,fit,
          endpoint canonical p good ρ δ out forms fit done⟩
      · exact smaller (remaining - 1) (by omega) (depth + 1) (by omega) c
          (List.mem_flatMap.mpr ⟨p,front,hc⟩) η (fun i => (fit i).trans (agree i)) (by omega)
  exact go limit 0 (Nat.zero_add _) g.seed List.mem_cons_self ρ
    (fun i => by rw [g.identity _ i.property]; exact .refl _) bounded

/-- A finite prefix suffices for all normalized specializations of this tuple.
The measure may decrease by different amounts for different specializations. -/
theorem completePrefix (g : Expansion rules query) (canonical : CanonicalPresentation (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (limit : Nat)
    (bounded : ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ →
      g.measure (fun i => ρ.apply (g.seed.value i)) ≤ limit) :
    CompleteVariants (ruleRoot rules) (List.ofFn query)
      ((VariantLayers.after g.seed g.next limit).rows.map (Point.answer · (keysOf query))) :=
  complete_of_points vars _ (fun _ hp => sound_reached g (VariantLayers.reached limit hp))
    (fun ρ norm out nf => prefix_covers g canonical ρ norm out nf limit (bounded ρ norm))

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A sufficient table-wide finite variant criterion. The rank may depend on
the rewrite theory; the uniform bound for a query must hold before the caller
chooses any of its normalized, potentially nonground variable images. -/
theorem finiteVariantProperty (bound : ReferenceReduction.Bound rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) (rank : Term s → Nat)
    (decreases : ∀ {a b}, StepModulo (ruleRoot rules) a b → rank b < rank a)
    (uniform : ∀ t, ∃ k, ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → rank (ρ.apply t) ≤ k) :
    FiniteVariantProperty (ruleRoot rules) := by
  intro terms
  let query := fun i : Fin terms.length => terms[i.val]
  let r := ReferenceReduction.reducer rules bound canonical
  let vars := TableNarrowing.variablesNormal canonical
  let g := FoldingNarrowing.expansion bound canonical vars r (TableNarrowing.narrower bound vars query)
  let budget := fun i => (uniform (query i)).choose
  let limit := (List.ofFn budget).sum
  have bounded (ρ : Substitution s) (norm : Normalized (ruleRoot rules) ρ) :
      g.measure (fun i => ρ.apply (g.seed.value i)) ≤ limit := by
    let height := ReductionHeight.height bound canonical.terminating
    change (List.ofFn (fun i => height (ρ.apply (r.reduce (query i))))).sum ≤ (List.ofFn budget).sum
    apply FoldingNarrowing.sum_mono
    intro i
    exact Nat.le_trans (ReductionHeight.reduces bound canonical.terminating
      (SpecializedFresh.reduces_subst rules ρ (r.correct (query i)).normalForm.1))
      (Nat.le_trans (ReductionHeight.le_rank bound canonical.terminating rank decreases _)
        ((uniform (query i)).choose_spec ρ norm))
  exact ⟨_,by simpa only [query,List.ofFn_getElem] using completePrefix g canonical vars limit bounded⟩

/-- An executable weight/multiplicity check plus a semantic exclusion of
positive weight in normal forms supplies the uniform bound for all queries. -/
theorem ofSymbolWeight {w : Head s → Nat} (ok : SymbolWeight.decreasing w rules)
    (canonical : CanonicalPresentation (ruleRoot rules)) (zero : ∀ {u}, Normal (ruleRoot rules) u → SymbolWeight.rank w u = 0) :
    FiniteVariantProperty (ruleRoot rules) :=
  finiteVariantProperty (SymbolWeight.bound ok) canonical _ (SymbolWeight.step_lt ok)
    (fun t => ⟨_,fun ρ norm => Nat.le_of_eq (SymbolWeight.rank_apply zero ρ norm t)⟩)

end Tamarin.BoundedVariants
