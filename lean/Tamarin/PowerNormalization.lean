import Tamarin.UniformReduction

/-! Ordinary normalization can pass through reducible intermediate powers.
Root rewrites, operand normalization and the check on the final root use the
same active rule table. No variant completeness or confluence is required. -/
namespace Tamarin.Rewriting.PowerNormalization
variable {s : Signature}

abbrev MatchSlot := UInt64 → Array UInt64 → Array UInt64 → Array UInt64
abbrev Exclude := Array (Array UInt64) → Array UInt64 → Bool

/-- The word-level consistency check and both term skeletons describe one
instance of the selected rule, before canonicalizing its right side. -/
structure Instance (matcher : MatchSlot) (rules : List (Equation s)) (input value : Term s) where
  rule : Equation s
  present : rule ∈ rules
  keys : Array UInt64
  subjects : Array UInt64
  slot : UInt64
  result : UInt64
  ran : matcher slot keys subjects = #[result]
  key : UInt64 → Variable
  subject : UInt64 → Term s
  raw : Term s
  lhs : RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) rule.lhs input
  rhs : RuleReduction.Skeleton key subject (keys.toList.zip subjects.toList) rule.rhs raw
  canonical : EquivB raw value
  live : ∀ i a j b, (i,a) ∈ keys.toList.zip subjects.toList →
    (j,b) ∈ keys.toList.zip subjects.toList → key i = key j → i = j
  typed : ∀ k v, (k,v) ∈ keys.toList.zip subjects.toList → HasSort (subject v) (key k).sort

/-- The path need not fix how many powers are folded before the exponent
is normalized. A checked operand normalizer can be used under the power. -/
inductive Path (matcher : MatchSlot) (rules : List (Equation s)) : Term s → Term s → Prop where
  | unchanged (t) : Path matcher rules t t
  | rewrite {t u v} (packet : Instance matcher rules t u) (rest : Path matcher rules u v) :
      Path matcher rules t v
  | operands (f : s.FreeSym) (xs ys : Fin (s.arity f) → Term s) {v}
      (children : ∀ i, NormalForm (ruleRoot rules) (xs i) (ys i))
      (rest : Path matcher rules (.free f ys) v) : Path matcher rules (.free f xs) v

theorem reaches {matcher} (mc : RuleReduction.Correct matcher) {rules : List (Equation s)}
    {t v} (p : Path matcher rules t v) : Reduces (ruleRoot rules) t v := by
  induction p with
  | unchanged _ => exact .basis (.refl _)
  | rewrite packet _ ih =>
    obtain ⟨σ, lhs, rhs⟩ := UniformReduction.instance_of_rows mc packet.ran
      packet.lhs packet.rhs packet.live packet.typed
    exact .trans (.step ⟨_, _, .refl _, .root ⟨packet.rule, packet.present, σ, lhs.symm, rhs.symm⟩,
      packet.canonical⟩) ih
  | operands f xs ys children _ ih => exact .trans (.free f xs ys (fun i => (children i).1)) ih

/-- A completed power has normal children and excludes every rule at its
head. If the power collapses to its base, the operand check supplies normality. -/
inductive Final (exclude : Exclude) (rules : List (Equation s)) : Term s → Prop where
  | operand {t} (normal : Normal (ruleRoot rules) t) : Final exclude rules t
  | power (f : s.FreeSym) (xs : Fin (s.arity f) → Term s)
      (children : ∀ i, Normal (ruleRoot rules) (xs i))
      (code : Head s → UInt64) (rows : Array (Array UInt64))
      (allRules : ∀ p rhs, (⟨.free f p, rhs⟩ : Equation s) ∈ rules →
        (Array.ofFn fun i => RootExclusion.required code (p i)) ∈ rows)
      (ran : exclude rows (Array.ofFn fun i => code (ConstructorVariants.head (xs i))) = true) :
      Final exclude rules (.free f xs)

def Correct (matcher : MatchSlot) (exclude : Exclude) : Prop :=
  ∀ {s : Signature} (rules : List (Equation s)) (t v : Term s),
    (∀ r ∈ rules, ConstructorVariants.Application r.lhs) →
    Path matcher rules t v → Final exclude rules v → HasSort v t.rootSort →
    NormalForm (ruleRoot rules) t v

theorem correct {matcher exclude} (mc : RuleReduction.Correct matcher)
    (ec : RootExclusion.Correct exclude) : Correct matcher exclude := by
  intro s rules t v apps path done typed
  refine ⟨reaches mc path, ?_, fun _ h => .widen typed (Term.rootSort_le h)⟩
  cases done with
  | operand hn => exact hn
  | power f xs children code rows allRules ran =>
    exact (RootExclusion.normal ec rules apps f xs children code rows allRules ran).2.1

end Tamarin.Rewriting.PowerNormalization
