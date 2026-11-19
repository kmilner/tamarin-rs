import Tamarin.DHPeerSymbolic
import Tamarin.DHProductUnique

/-! Certified joint variants of a received message raised to a fresh-sorted
exponent or any stable single positive factor. Admission requires syntactic
inventories at the active DH heads.
Other heads may have arbitrary additional rules, subject to stability of any
extra observations supplied by the caller. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

theorem PowerNormalForms.of_buckets [DecidableEq sig.ACSym]
    (power : PowerBucket T) (inverse : InverseBucket E) (mult : MulBucket E)
    (neutral : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.neutral)
    (one : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one) (q : Names) :
    PowerNormalForms s (ruleRoot T.rules) q := by
  have symbolic := symbolicNormal power inverse mult (normalConstant _ power.1 _ s.neutralArity neutral) q
  have inventory := Balance.Inventory.of_buckets mult inverse one
  exact ⟨(constructor_normal _ power.1).1,fun k => (symbolic k).1,fun k => (symbolic k).2,
    classifiedNormal power mult inverse,
    fun sy sr ny nr _ _ => inventory.peer_unique power (normalConstant _ power.1 _ s.oneArity one) sy sr ny nr⟩

/-- Exact finite coverage, scope and reconstruction for all seven arms,
including repeated peer powers sharing a caller variable with other
observations. All theory premises inspect the active rewrite table. -/
theorem certified [DecidableEq sig.ACSym]
    (power : PowerBucket T) (inverse : InverseBucket E) (mult : MulBucket E)
    (neutral : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.neutral)
    (one : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one) (q : Names)
    (os : List (Observation sig)) (occurs : .power ∈ os) (avoid : List Variable)
    (apart : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (reserved : ∀ v, q.witness v → v ∉ avoid)
    (contexts : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t) :
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) (arms.map fun k => q.arm s k os) ∧
    ∀ a ∈ arms.map (fun k => q.arm s k os), a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) ∧
      a.Safe (os.map (q.input s)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  obtain ⟨all,rebuild⟩ := complete T q (.of_buckets power inverse mult neutral one q) os apart contexts
  refine ⟨all, fun a mem => ⟨rebuild a mem,?_⟩⟩
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp mem
  exact ⟨q.safe s os occurs avoid reserved k, q.idempotent s k⟩


/-- Admission for a general exponent depends only on its normalized
instances. The exponent may contain observable variables and complex
constructor subterms, provided it remains one irreducible positive factor. -/
def StableFactor (s : Symbols sig) (R : Root sig) (t : Term sig) : Prop :=
  ∀ ρ : Substitution sig, Normalized R ρ → Normal R (ρ.apply t) ∧ Factor s (ρ.apply t)

theorem Query.forms [DecidableEq sig.ACSym] (q : Query sig)
    (power : PowerBucket T) (inverse : InverseBucket E) (mult : MulBucket E)
    (neutral : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.neutral)
    (one : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one)
    (admit : StableFactor s (ruleRoot T.rules) q.exponent) : q.Forms s (ruleRoot T.rules) := by
  have vars := (constructor_normal _ power.1).1
  have exponent : Normal (ruleRoot T.rules) q.exponent ∧ Factor s q.exponent := by
    simpa using admit .identity vars
  have varOf {t : Term sig} (eq : EquivB (q.symbolic .pos) t) : t.Occurs (q.var .pos) := by
    cases t <;> cases eq.head_eq; rfl
  have apart (eq : EquivB (q.symbolic .pos) q.exponent) : False :=
    q.disjoint _ (varOf eq) (.inr (.inl rfl))
  have symbolic := symbolicNormalFactor power inverse mult (normalConstant _ power.1 _ s.neutralArity neutral)
    q.toNames q.exponent q.sortedExponent exponent.1 exponent.2 apart
  have inventory := Balance.Inventory.of_buckets mult inverse one
  have peerSort (ρ : Substitution sig) : HasSort (ρ.image (q.var .peer)) .msg := by simpa only [q.sorted,Slot.sort] using ρ.sorted (q.var .peer)
  have expSort (ρ : Substitution sig) : HasSort (ρ.apply q.exponent) .msg := q.sortedExponent.subst ρ.image ρ.sorted
  refine ⟨vars,fun k => (symbolic k).1,fun k => (symbolic k).2,?_,?_,?_⟩
  · exact fun ρ hn => classifyMsg s _ _ _ (peerSort ρ) (expSort ρ) (hn _) (admit ρ hn).1
  · exact fun hn _ _ h => classifiedNormalFactor power mult inverse h (admit _ hn).2
  · exact fun {ρ} hn _ _ => inventory.peer_unique_msg power (normalConstant _ power.1 _ s.oneArity one)
      (peerSort ρ) (expSort ρ) (admit ρ hn).2.nonUnit (hn _) (admit ρ hn).1

/-- Semantic certificate for the single received base with any admitted
exponent, including all variables shared by that exponent across the tuple. -/
theorem Query.certified [DecidableEq sig.ACSym] (q : Query sig)
    (power : PowerBucket T) (inverse : InverseBucket E) (mult : MulBucket E)
    (neutral : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.neutral)
    (one : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one) (admit : StableFactor s (ruleRoot T.rules) q.exponent)
    (os : List (Observation sig)) (occurs : .power ∈ os) (avoid : List Variable)
    (apart : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (reserved : ∀ v, q.witness v → v ∉ avoid)
    (contexts : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t) :
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) (arms.map fun k => q.arm s k os) ∧
    ∀ a ∈ arms.map (fun k => q.arm s k os), a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) ∧
      a.Safe (os.map (q.input s)) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  obtain ⟨all,rebuild⟩ := q.complete T (q.forms power inverse mult neutral one admit) os apart contexts
  refine ⟨all, fun a mem => ⟨rebuild a mem,?_⟩⟩
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp mem
  exact ⟨q.safe s os occurs avoid reserved k,q.idempotent s k⟩

end Tamarin.Rewriting.DHPeer
