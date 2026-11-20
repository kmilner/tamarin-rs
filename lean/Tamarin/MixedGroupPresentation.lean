import Tamarin.ActiveAC
import Tamarin.XorProductCanonical
import Tamarin.DHConstructorExtension

/-! Compose Diffie–Hellman, exponent-two cancellation, and constructor rules.
Both groups interpret their operators on normal values of the same presentation.
Either group's normal operands can contain any term of the other theory. -/
namespace Tamarin.MixedGroupPresentation
open Rewriting DHPeer ConstructorVariants MaudeOperations ShortVariantPaths
variable {sig : Signature} {s : Symbols sig} {T : Table s}

structure Evidence (rs : Problem sig) (E : ExtraTable T) (X : BinaryXor.Table sig)
    [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom] : Prop where
  same : X.rules = T.rules
  agrees : TablePresentation.Agrees rs T.rules
  presentation : NormalAlgebra.Presentation T.rules
  scope : ReferenceReduction.Bound T.rules
  dh : ProtectedTable E
  neutral : Normal (ruleRoot T.rules) s.neutralTerm
  typed : ∀ r ∈ X.rules, head r.lhs = .ac X.f → HasSort r.lhs .msg
  inactive : ∀ f, f ≠ s.mul → f ≠ X.f → Head.ac f ∉ ruleHeads T.rules
  other : ∀ r ∈ T.rules, ¬ ChurchRosser.DHHead s (head r.lhs) → head r.lhs ≠ .ac X.f →
    SubtermVariants.Row r ∧ NormalAlgebra.UniqueRow T.rules r

variable [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]
variable {rs : Problem sig} {E : ExtraTable T} {X : BinaryXor.Table sig}

theorem Evidence.sound (e : Evidence rs E X) : ReferenceReduction.Bound rs ∧
    CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  classical
  let dh := e.dh
  have xor : ActiveAC.Operator X.rules X.f := {
    product := BinaryXor.product X e.typed
    unique := fun r hr h => BinaryXor.uniqueRow X r hr h (e.typed r hr h)
    bounded := ⟨2,BinaryXor.kind_paths X (BinaryXor.redex_typed X e.typed)⟩ }
  have mult : ActiveAC.Operator T.rules s.mul := {
    product := ChurchRosser.protectedProduct dh
    unique := fun r hr h => ChurchRosser.protected_unique dh e.neutral r hr (.inr (.inr (.inr h)))
    bounded := kind_product_paths dh.inventory dh.product dh.inverse dh.unit }
  have canAndFinite : CanonicalPresentation (ruleRoot T.rules) ∧ FiniteVariantProperty (ruleRoot T.rules) := by
    apply ActiveAC.complete_of_bounds e.presentation e.scope
    · intro f active
      by_cases hm : f = s.mul
      · subst f; exact mult
      by_cases hx : f = X.f
      · subst f; exact e.same ▸ xor
      exact (e.inactive f hm hx active).elim
    · intro r hr notAC
      by_cases h : ChurchRosser.DHHead s (head r.lhs)
      · exact ChurchRosser.protected_unique dh e.neutral r hr h
      · exact (e.other r hr h (notAC X.f)).2
    · intro can f
      by_cases isDH : f = s.pow ∨ f = s.inv
      · exact free_head_paths dh.inventory dh.product dh.inverse dh.unit dh.power f isDH
      apply SubtermVariants.free_bound e.scope can dh.apps
      intro r hr hd
      apply (e.other r hr ?_ (by rw [hd]; intro eq; cases eq)).1
      rw [hd]
      rintro (pow|inv|unit|ac)
      · exact isDH (.inl (Head.free.inj pow))
      · exact isDH (.inr (Head.free.inj inv))
      · exact dh.noUnit (List.mem_map.mpr ⟨r,hr,hd.trans unit⟩)
      · cases ac
    · intro can f
      apply SubtermVariants.comm_bound e.scope can dh.apps
      intro r hr hd
      apply (e.other r hr ?_ (by rw [hd]; intro eq; cases eq)).1
      rw [hd]
      rintro (eq|eq|eq|eq) <;> cases eq
  exact ⟨TablePresentation.bound_of_agrees e.agrees e.scope,
    (TablePresentation.canonical_iff e.agrees).mpr canAndFinite.1,
    (TablePresentation.finite_iff e.agrees).mpr canAndFinite.2⟩

end Tamarin.MixedGroupPresentation
