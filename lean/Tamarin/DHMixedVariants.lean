import Tamarin.DHKindProducts
import Tamarin.DHCanonical
import Tamarin.SubtermVariants

/-! Combine local normalization proofs in a single equational theory. A rule
returning a ground expression can call DH; a projection can inspect a DH
product or another defined operator. The combined table must be canonical. -/
namespace Tamarin.Rewriting.DHPeer
open MaudeOperations ShortVariantPaths ConstructorVariants Balance
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.FreeSym] [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

/-- The DH equations are present in T and E. These restrictions apply to the
remaining heads, leaving constructor symbols and rule order unrestricted. -/
structure OtherRows (T : Table s) (eligible : Equation sig → Prop := SubtermVariants.Row) : Prop where
  free : ∀ f, f ≠ s.pow → f ≠ s.inv → ∀ r ∈ T.rules, head r.lhs = .free f → eligible r
  comm : ∀ f, ∀ r ∈ T.rules, head r.lhs = .comm f → eligible r
  ac : ∀ f, f ≠ s.mul → Head.ac f ∉ ruleHeads T.rules

omit [DecidableEq sig.CSym] [DecidableEq sig.Atom] in
theorem OtherRows.scope (others : OtherRows T) (dh : ProtectedTable E) :
    ReferenceReduction.Bound T.rules := by
  intro r hr v occ
  have eligible (row : SubtermVariants.Row r) : r.lhs.Occurs v := by
    have cls : SubtermVariants.Presentation [r] := by simpa [SubtermVariants.Presentation] using row
    exact SubtermVariants.bound cls r (by simp) v occ
  have schema (atDH : head r.lhs = .free s.pow ∨ head r.lhs = .free s.inv ∨
      head r.lhs = .free s.one ∨ head r.lhs = .ac s.mul) : r.lhs.Occurs v := by
    rcases dh.atHead r hr atDH with ⟨rule,rfl⟩ | ⟨rule,rfl⟩
    · exact ExactTable.rule_scope s _ rule v occ
    · exact ExactTable.extra_scope s _ rule v occ
  have app := dh.apps r hr
  generalize ht : r.lhs = t at ⊢ app eligible schema
  cases t with
  | var | atom => simp [Application] at app
  | free f xs =>
    by_cases hp : f = s.pow
    · exact schema (.inl (by subst f; rfl))
    by_cases hi : f = s.inv
    · exact schema (.inr (.inl (by subst f; rfl)))
    exact eligible (others.free f hp hi r hr (by rw [ht]; rfl))
  | comm f a b => exact eligible (others.comm f r hr (by rw [ht]; rfl))
  | ac f a b =>
    by_cases hm : f = s.mul
    · exact schema (.inr (.inr (.inr (by subst f; rfl))))
    exact (others.ac f hm (List.mem_map.mpr ⟨r,hr,by rw [ht]; rfl⟩)).elim

theorem mixedResultVariants (scope : ReferenceReduction.Bound T.rules)
    (can : CanonicalPresentation (ruleRoot T.rules)) (dh : ProtectedTable E)
    (others : OtherRows T (SubtermVariants.ResultRow T.rules)) : FiniteVariantProperty (ruleRoot T.rules) := by
  apply finiteVariantProperty_of_operators scope can
  constructor
  · intro f
    by_cases active : f = s.pow ∨ f = s.inv
    · exact free_head_paths dh.inventory dh.product dh.inverse dh.unit dh.power f active
    · exact SubtermVariants.free_result_bound scope can dh.apps f
        (others.free f (fun h => active (.inl h)) (fun h => active (.inr h)))
  · exact fun f => SubtermVariants.comm_result_bound scope can dh.apps f (others.comm f)
  · intro f
    by_cases product : f = s.mul
    · subst f; exact kind_product_paths dh.inventory dh.product dh.inverse dh.unit
    · exact ⟨0,fun a b na nb => ⟨_,.basis (.refl _),
        constructor_node_normal _ dh.apps (.ac f a b) (others.ac f product) ⟨na,nb⟩⟩⟩

theorem mixedFiniteVariants (can : CanonicalPresentation (ruleRoot T.rules)) (dh : ProtectedTable E)
    (others : OtherRows T) : FiniteVariantProperty (ruleRoot T.rules) :=
  mixedResultVariants (others.scope dh) can dh
    ⟨fun f hp hi r hr h => .inl (others.free f hp hi r hr h),
     fun f r hr h => .inl (others.comm f r hr h),others.ac⟩

end Tamarin.Rewriting.DHPeer
