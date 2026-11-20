import Tamarin.DHPresentation
import Tamarin.SortedACPaths

/-! Specialize the typed AC subbag criterion to the DH multiplication rules. -/
namespace Tamarin.Rewriting.DHPeer
open ShortVariantPaths Balance Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.ACSym]

namespace KindProduct

abbrev msg := @SortedAC.msg sig
noncomputable abbrev selected (s : Symbols sig) := SortedAC.selected s.mul

theorem all_msg {t : Term sig} (ht : HasSort t .msg) : selected s t = flatten s.mul t :=
  SortedAC.all_msg s.mulSort ht

theorem core_exists {R : Root sig} (t : Term sig) (nt : Normal R t) :
    ∃ o, bag s o = selected s t ∧ ∀ u, o = some u → HasSort u .msg ∧ Normal R u := by
  obtain ⟨o,ho,h⟩ := SortedAC.core_exists s.mulSort t nt
  exact ⟨o,by cases o <;> exact ho,h⟩

omit [DecidableEq sig.ACSym] in
theorem selected_mul (s : Symbols sig) (a b : Term sig) :
    selected s (s.product.mul a b) = selected s a ++ selected s b := SortedAC.selected_mul s.mul a b

/-- Lift any multiplicative invariant through the untouched kind-level factors. -/
theorem paths (mul : MulBucket E) (P : Term sig → Term sig → Prop)
    (respect : ∀ {a b}, EquivB a b → P a b)
    (rebase : ∀ {a b c}, EquivB a b → P b c → P a c)
    (context : ∀ {a b}, P a b → ∀ r, P (s.product.mul a r) (s.product.mul b r))
    {k} (sorted : ∀ a b : Term sig, HasSort a .msg → HasSort b .msg →
      Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, HasSort u .msg ∧ Path (ruleRoot T.rules) k (s.product.mul a b) u ∧
        Normal (ruleRoot T.rules) u ∧ P (s.product.mul a b) u) :
    ∀ a b : Term sig, Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, Path (ruleRoot T.rules) k (s.product.mul a b) u ∧ Normal (ruleRoot T.rules) u ∧ P (s.product.mul a b) u :=
  SortedAC.paths s.mulSort mul.redex_typed P respect rebase context sorted

end KindProduct

/-- All kind-level products of two normal operands share the sorted operator's
path bound. Only the product of the two maximal sorted subbags can need work. -/
theorem kind_product_paths (inventory : Inventory E) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) :
    ∃ k, ∀ a b : Term sig, Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, Path (ruleRoot T.rules) k (s.product.mul a b) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,sorted⟩ := product_paths inventory mul inv unit
  refine ⟨k,fun a b na nb => ?_⟩
  obtain ⟨u,h,hn,_⟩ := KindProduct.paths mul (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (k := k) (by
      intro x y hx hy nx ny
      obtain ⟨u,tu,hu,nu⟩ := sorted x y hx hy nx ny
      exact ⟨u,tu,hu,nu,trivial⟩) a b na nb
  exact ⟨u,h,hn⟩

end Tamarin.Rewriting.DHPeer
