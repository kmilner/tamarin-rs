import Tamarin.CancellationSplicing
import Tamarin.PositionalConvergence

/-! A single closure property for nested native operations. Each operation
is justified against the same live rule table, including when the expression
uses more than one user-declared cancellation symbol. -/
namespace Tamarin.Rewriting.StagedExpression
open ConstructorVariants
variable {s : Signature}

/-- A head accepted by the positional rule compiler. All concrete instances
of all active rules at the head must be accounted for by this one schema. -/
structure Positional (rules : List (Equation s)) (d : s.FreeSym) where
  args : Fin (s.arity d) → Term s
  rhs : Term s
  patterns : ∀ i, PositionalConvergence.Pattern (ruleRoot rules) (args i)
  result : PositionalConvergence.Result (ruleRoot rules) args rhs
  inventory : ∀ ys t, ruleRoot rules (.free d ys) t ↔ ∃ σ : Substitution s,
    (∀ i, ys i = σ.apply (args i)) ∧ t = σ.apply rhs
  slots : ∀ i, s.inputSort d i = .msg
  output : s.outputSort d = .msg
  rhsTyped : HasSort rhs .msg

private theorem ground_normal {R : Root s} {k : Nat} {p : Fin k → Term s} {rhs : Term s}
    (result : PositionalConvergence.Result R p rhs) (closed : ∀ v, ¬rhs.Occurs v) : Normal R rhs := by
  cases result with
  | selected v _ => exact (closed v rfl).elim
  | fixed _ _ hn => exact hn

inductive Admitted (rules : List (Equation s)) : Term s → Prop where
  | stable {t} : HasSort t .msg → StableVariants.Stable (ruleRoot rules) t → Admitted rules t
  | inert (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads rules)
      (slots : ∀ i, s.inputSort f i = .msg) (out : Subsort (s.outputSort f) .msg)
      (xs : Fin (s.arity f) → Term s) (children : ∀ i, Admitted rules (xs i)) : Admitted rules (.free f xs)
  | positional (d : s.FreeSym) (schema : Positional rules d)
      (xs : Fin (s.arity d) → Term s) (children : ∀ i, Admitted rules (xs i)) : Admitted rules (.free d xs)
  | cancellation (T : BinaryXor.Table s) (live : T.rules = rules)
      {a b} : Admitted rules a → Admitted rules b → Admitted rules (.ac T.f a b)

theorem Admitted.hereditary {rules : List (Equation s)} (decl : MessageArguments s)
    (apps : ∀ r ∈ rules, Application r.lhs) {t : Term s} (h : Admitted rules t)
    (ρ : Substitution s) (hn : Normalized (ruleRoot rules) ρ) : Hereditary (ruleRoot rules) (ρ.apply t) := by
  induction h with
  | stable typed safe => exact Hereditary.normal decl (safe ρ hn) (typed.subst ρ.image ρ.sorted)
  | inert f absent slots out xs _ ih => exact Hereditary.free_inert rules apps f absent slots out _ ih
  | positional d schema xs _ ih =>
    apply PositionalConvergence.hereditary d schema.args schema.rhs schema.patterns schema.result
      schema.inventory schema.slots (schema.output ▸ Subsort.refl _) _ _ ih
    exact fun closed => Hereditary.normal decl (ground_normal schema.result closed) schema.rhsTyped
  | cancellation T live _ _ l r =>
    subst rules
    exact BinaryXor.Splicing.hereditary_ac T
      (Hereditary.normal decl T.toTable.zero_normal T.zeroSort) l r

/-- Any strategy that reaches a normal value from an admitted caller
instance produces the same observation modulo the structural equations. -/
theorem Admitted.unique {rules : List (Equation s)} (decl : MessageArguments s)
    (apps : ∀ r ∈ rules, Application r.lhs) {t u v} (h : Admitted rules t)
    (ρ : Substitution s) (hn : Normalized (ruleRoot rules) ρ)
    (nu : NormalForm (ruleRoot rules) (ρ.apply t) u) (nv : NormalForm (ruleRoot rules) (ρ.apply t) v) :
    EquivB u v := by
  obtain ⟨_,_,_,conv⟩ := (h.hereditary decl apps ρ hn).settles
  exact (normal_reduces_equiv (conv _ nu.1) nu.2.1).trans (normal_reduces_equiv (conv _ nv.1) nv.2.1).symm

/-- After any child normalization sequence that preserves the sorts of the
outer application, the parent still has exactly its original normal forms.
This is the local staging condition used by the joined-row refinement. -/
theorem normalize_children_iff {R : Root s} {t intermediate u : Term s} (h : Hereditary R t)
    (red : Reduces R t intermediate) (sorts : ∀ k, HasSort t k ↔ HasSort intermediate k) :
    NormalForm R t u ↔ NormalForm R intermediate u := by
  obtain ⟨n,_,_,conv⟩ := h.settles
  constructor
  · intro nf
    have eq := normal_reduces_equiv (conv _ nf.1) nf.2.1
    exact ⟨(conv _ red).trans (.basis eq.symm),nf.2.1,fun k hk => nf.2.2 k ((sorts k).mpr hk)⟩
  · intro nf
    exact ⟨red.trans nf.1,nf.2.1,fun k hk => nf.2.2 k ((sorts k).mp hk)⟩

end Tamarin.Rewriting.StagedExpression
