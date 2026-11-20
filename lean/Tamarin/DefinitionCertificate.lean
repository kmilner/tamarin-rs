import Tamarin.BoundedVariants
import Tamarin.ConstantDefinitions
import Tamarin.SymbolWeight
import Tamarin.CheckedVariantOverlap
import Tamarin.StableVariants

/-! Concrete admission for ground constructor definitions of nullary free
symbols. Their count decreases even when expanding a definition grows a term.
Normalized caller substitutions cannot introduce any further defined heads. -/
namespace Tamarin.DefinitionCertificate
open Rewriting MaudeOperations ConstantDefinitions
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable {rs : Problem s}

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem sorted_iff (cls : Presentation rs) :
    TableDecrease.sorted rs ↔ ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort := by
  have row (r) (hr : r ∈ rs) : TableDecrease.sortRule r ↔ HasSort r.rhs r.lhs.rootSort := by
    obtain ⟨f,xs,h,_⟩ := cls.shapes r hr
    simp only [TableDecrease.sortRule,h,Term.checkSort_iff]
  exact ⟨fun ok r hr => (row r hr).mp (List.all_eq_true.mp ok r hr),
    fun typed => List.all_eq_true.mpr (fun r hr => (row r hr).mpr (typed r hr))⟩

theorem canonical (ok : accepts rs) (sorted : TableDecrease.sorted rs) :
    CanonicalPresentation (ruleRoot rs) :=
  ⟨SymbolWeight.terminating (decreases ok),confluent ok,TableDecrease.sortPreserving sorted⟩

private theorem normal_zero (ok : accepts rs) {t : Term s} (nf : Normal (ruleRoot rs) t) :
    SymbolWeight.rank (weight rs) t = 0 := by
  induction t with
  | var _ | atom _ => rfl
  | free f xs ih =>
    cases found : entry rs f with
    | some r => exact (nf _ (entry_step ok found xs)).elim
    | none =>
      change (List.ofFn fun i => SymbolWeight.rank _ (xs i)).sum + weight rs (.free f) = 0
      simp [weight,found,List.sum_eq_zero_iff_forall_eq_nat,fun i => ih i (normal_free_child f xs nf i)]
  | ac f a b l r =>
    change SymbolWeight.rank _ a + SymbolWeight.rank _ b + 0 = 0
    obtain ⟨ha,hb⟩ := normal_ac_children f nf
    simp [l ha,r hb]
  | comm f a b l r =>
    change SymbolWeight.rank _ a + SymbolWeight.rank _ b + 0 = 0
    obtain ⟨ha,hb⟩ := normal_comm_children f nf
    simp [l ha,r hb]

theorem finiteVariants (ok : accepts rs) (sorted : TableDecrease.sorted rs) :
    FiniteVariantProperty (ruleRoot rs) :=
  BoundedVariants.ofSymbolWeight (decreases ok) (canonical ok sorted) (normal_zero ok)

/-- All four operations on this presentation, with no search hypotheses
or executable admission decisions among the caller's premises. -/
def reference (cls : Presentation rs) (typed : ∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) :
    MaudeOperations.Reference s rs :=
  let ok := (accepts_iff rs).mpr cls
  let sorts := (sorted_iff cls).mpr typed
  TableNarrowing.reference (bound ok) (canonical ok sorts) (finiteVariants ok sorts)

private theorem representative (ok : accepts rs) (sorted : TableDecrease.sorted rs) (t : Term s) :
    StableVariants.Representative (ruleRoot rs) t (expand rs t) := by
  have normal (ρ : Substitution s) (hn : Normalized (ruleRoot rs) ρ) :
      NormalForm (ruleRoot rs) (ρ.apply t) (ρ.apply (expand rs t)) := by
    have path := SpecializedFresh.reduces_subst rs ρ (reachable ok t)
    refine ⟨path,?_,?_⟩
    · intro u st
      have lt := SymbolWeight.step_lt (decreases ok) st
      rw [SymbolWeight.rank_apply (normal_zero ok) _ hn,normal_zero ok (normal_expand ok t)] at lt
      exact Nat.not_lt_zero _ lt
    · intro k typed
      exact RootNarrowing.reduction_invariant (fun a => HasSort a k)
        (fun h e => Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h))
        (fun h st => TableDecrease.sortPreserving sorted st _ h) path typed
  refine ⟨normal,?_,TableNarrowing.reducesUses (bound ok) (reachable ok t)⟩
  intro ρ hn u other
  have value := normal ρ hn
  obtain ⟨_,l,r⟩ := confluent ok other.1 value.1
  exact (normal_reduces_equiv l other.2.1).trans (normal_reduces_equiv r value.2.1).symm

/-- One identity row covers arbitrary simultaneous normal substitutions,
including caller names and repeated occurrences of a query variable. -/
theorem reply (ok : accepts rs) (sorted : TableDecrease.sorted rs) (q : List (Term s)) :
    CheckedVariants.Reply (ruleRoot rs) q [⟨.identity,q.map (expand rs)⟩] := by
  have apps r (hr : r ∈ rs) : ConstructorVariants.Application r.lhs := by
    obtain ⟨_,_,h,_⟩ := row_shape ok hr
    rw [h]; trivial
  obtain ⟨complete,safe,recover⟩ := StableVariants.tuple rs apps q (expand rs)
    (fun t _ => representative ok sorted t) []
  refine ⟨⟨complete,List.cons_ne_nil _ _,fun a ha => List.mem_singleton.mp ha ▸ safe,
    fun a ha => List.mem_singleton.mp ha ▸ recover⟩,?_⟩
  clear complete safe recover
  intro ρ hn xs ys left right
  induction q generalizing xs ys with
  | nil => cases xs <;> cases ys <;> simp_all [Aligned]
  | cons t ts ih =>
    cases xs with
    | nil => exact left.elim
    | cons x xs =>
      cases ys with
      | nil => exact right.elim
      | cons y ys =>
        exact ⟨((representative ok sorted t).unique ρ hn x left.1).trans
          ((representative ok sorted t).unique ρ hn y right.1).symm,ih _ _ left.2 right.2⟩

end Tamarin.DefinitionCertificate
