import Tamarin.MatchOrder
import Tamarin.VariablePermutation
import Tamarin.Rewriting

/-! Algebraic observations of the four Maude commands emitted by Tamarin.
The caller fixes the signature and the oriented equations. All equations in
the emitted module are executable and marked [variant]. Tamarin packs a list
of observations under inert list constructors for matching and variants. -/
namespace Tamarin.MaudeOperations
open Rewriting
variable {sig : Signature}

/-- Plain match permits every pattern variable to bind. The restricted caller
can use the underlying matcher with a smaller list after freezing its context. -/
def patternVariables (p : Problem sig) : List Variable :=
  p.flatMap (fun e => e.lhs.variables)

@[simp] theorem mem_patternVariables (p : Problem sig) (v : Variable) :
    v ∈ patternVariables p ↔ Matching.Observed p v := by
  simp [patternVariables, Matching.Observed]

theorem plain_match {inputs} (m : Matching.VerifiedMatcher sig inputs) (p : Problem sig) (hp : inputs p) :
    Matching.Complete p (fun _ => True) (m.run p hp (patternVariables p)) := by
  have h := m.correct p hp (patternVariables p)
  have sameScope (σ : Substitution sig) :
      Matching.Scoped p (fun v => v ∈ patternVariables p) σ ↔ Matching.Scoped p (fun _ => True) σ := by
    simp [Matching.Scoped]
  exact ⟨fun σ hs => ⟨(h.sound σ hs).1, (sameScope σ).mp (h.sound σ hs).2⟩,
    fun ρ hm hr => h.covers ρ hm ((sameScope ρ).mpr hr)⟩

/-- A Boolean caller may stop after a witness. A negative answer has the same
exhaustiveness obligation as an empty complete enumeration. -/
theorem hasMatch_iff {inputs} (m : Matching.VerifiedMatcher sig inputs) (p : Problem sig)
    (hp : inputs p) (bindable : List Variable) :
    (m.run p hp bindable).isEmpty = false ↔
      ∃ σ, Matching.Matches p σ ∧ Matching.Scoped p (fun v => v ∈ bindable) σ := by
  simpa using (m.correct p hp bindable).nonempty_iff

/-- Presentation properties required for arbitrary rewrite strategies on the
source terms. Pure B rearrangements do not count as steps for termination. -/
structure CanonicalPresentation (R : Root sig) : Prop where
  terminating : WellFounded (fun next current => StepModulo R current next)
  confluent : ∀ {t u v}, Reduces R t u → Reduces R t v →
    ∃ w, Reduces R u w ∧ Reduces R v w
  sortPreserving : ∀ {t u}, StepModulo R t u → ∀ k, HasSort t k → HasSort u k

/-- A reduction result usable independently of Maude's choice of rewrite
strategy. Reachability, irreducibility and preservation of sorts come from
NormalForm. All other reachable normal forms must agree modulo B. -/
structure ReductionReply (R : Root sig) (input value : Term sig) : Prop where
  normalForm : NormalForm R input value
  unique : ∀ other, NormalForm R input other → EquivB other value

/-- Total reference for a fixed presentation, including open terms. -/
structure VerifiedReducer (R : Root sig) where
  reduce : Term sig → Term sig
  correct : ∀ t, ReductionReply R t (reduce t)

/-- The total driver may still use a bounded result type internally. Its
completion proof discharges the stopped branch for every input. -/
def VerifiedReducer.ofNormalizer {R : Root sig} (n : Normalizer R (fun _ => True))
    (unique : ∀ t u v, NormalForm R t u → NormalForm R t v → EquivB u v) :
    VerifiedReducer R where
  reduce t := match n.run t with
    | .complete u => u
    | .stopped _ u => u
  correct t := by
    obtain ⟨u, hu⟩ := n.completes t trivial
    have nf := n.correct t trivial
    rw [hu] at nf ⊢
    exact ⟨nf, fun v hv => unique t v u hv nf⟩

/-- The complete family from plain get variants, together with Tamarin's
freshness and substitution-only decoding obligations for each returned row. -/
structure VariantReply (R : Root sig) (q : List (Term sig)) (avoid : List Variable)
    (rows : List (Variant sig)) : Prop where
  complete : CompleteVariants R q rows
  nonempty : rows ≠ []
  safe : ∀ a ∈ rows, a.Safe q avoid
  reconstructible : ∀ a ∈ rows, a.Reconstructible R q

theorem VariantReply.singleton_iff {R : Root sig} {q avoid} {a : Variant sig} :
    VariantReply R q avoid [a] ↔ CompleteVariants R q [a] ∧ a.Safe q avoid ∧ a.Reconstructible R q :=
  ⟨fun h => ⟨h.complete, h.safe a (by simp), h.reconstructible a (by simp)⟩,
    fun ⟨hc, hs, hr⟩ => ⟨hc, List.cons_ne_nil _ _, fun _ ha => List.mem_singleton.mp ha ▸ hs,
      fun _ ha => List.mem_singleton.mp ha ▸ hr⟩⟩

/-- A reducer for the same equations suffices to recover the printed values
from the bindings Tamarin actually retains, even with repeated observations. -/
theorem VariantReply.recover {R : Root sig} {q avoid rows} (h : VariantReply R q avoid rows)
    (r : VerifiedReducer R) {a} (ha : a ∈ rows) :
    Aligned EquivB (q.map (fun t => r.reduce (a.subst.apply t))) a.values :=
  h.reconstructible a ha _ (aligned_map _ q _ (fun t _ => (r.correct (a.subst.apply t)).normalForm))

/-- Canonical reduction implies the local decoding obligation for every sound
row, including those returned by independently implemented variant searches. -/
theorem VariantReply.ofCanonical {R : Root sig} (r : VerifiedReducer R) {q avoid rows}
    (variablesNormal : Normalized R Substitution.identity)
    (hc : CompleteVariants R q rows) (hs : ∀ a ∈ rows, a.Safe q avoid) : VariantReply R q avoid rows := by
  have initial := aligned_map (fun t u => NormalForm R (Substitution.identity.apply t) u) q r.reduce
    (fun t _ => by simpa using (r.correct t).normalForm)
  obtain ⟨row, member, _⟩ := hc.2 .identity variablesNormal _ initial
  exact ⟨hc, List.ne_nil_of_mem member, hs, fun a ha =>
    Variant.reconstructible_of_unique (hc.1 a ha) (fun t _ _ _ hu hv =>
      ((r.correct (a.subst.apply t)).unique _ hu).trans ((r.correct (a.subst.apply t)).unique _ hv).symm)⟩

/-- A finite complete family for every tuple is a property of a presentation.
It does not supply a search procedure or follow from finiteness of the table. -/
def FiniteVariantProperty (R : Root sig) : Prop :=
  ∀ q : List (Term sig), ∃ rows, CompleteVariants R q rows

structure VerifiedVariantGenerator (R : Root sig) where
  variants : List (Term sig) → List Variable → List (Variant sig)
  correct : ∀ q avoid, VariantReply R q avoid (variants q avoid)

theorem VerifiedVariantGenerator.finiteVariantProperty {R : Root sig}
    (g : VerifiedVariantGenerator R) : FiniteVariantProperty R :=
  fun q => ⟨g.variants q [], (g.correct q []).complete⟩

/-- One target per emitted module. All arity-correct input trees are in scope, including
kind-level applications. Substitution images must still have their variable's
declared sort. Ordinary matching and unification see the operator axioms.
Reduction and variants see the same active table.
Constructing this bundle requires total functions on their stated domains. -/
structure Reference (sig : Signature) (rules : List (Equation sig)) where
  unify : VerifiedUnifier sig (fun _ => True)
  matchTerms : Matching.VerifiedMatcher sig (fun _ => True)
  reduce : VerifiedReducer (ruleRoot rules)
  variants : VerifiedVariantGenerator (ruleRoot rules)

end Tamarin.MaudeOperations
