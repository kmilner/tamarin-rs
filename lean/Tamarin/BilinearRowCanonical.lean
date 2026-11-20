import Tamarin.BilinearPowerSpine
import Tamarin.DHPresentation
import Tamarin.NormalAlgebra

/-! The existing signed point and power spines give uniqueness modulo C/AC
for all bilinear schemas on the entire rule table. A substitution may
identify any of the variables, and its normal images can themselves contain
point actions, pairings, or terms from other active theories. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer NormalAlgebra
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {T : Table s} {E : ExtraTable T}

namespace PowerSpine.PointView
variable {R : Root sig} {a p : Term sig}

/-- Prefix a scalar action to any point view. The scalar may itself require
normalization. All choices of reductions preserve its signed multiplicities. -/
theorem action (view : PowerSpine.PointView s β R p) (ty : HasSort a .msg)
    (sc : Staging.Signed s R a) : PowerSpine.PointView s β R (β.point a p) := by
  obtain ⟨b,tb,nb,plain,trace⟩ := view
  refine ⟨b,tb,nb,plain,fun k => ?_⟩
  obtain ⟨x,h⟩ := trace k
  obtain ⟨y,c⟩ := sc k
  exact ⟨_,.action (.refl _) h ty sc c⟩

theorem unique [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (dh : ProtectedTable E)
    (view : PowerSpine.PointView s β (ruleRoot T.rules) p) : Unique (ruleRoot T.rules) p := by
  obtain ⟨b,tb,_,_,trace⟩ := view
  obtain ⟨_,h⟩ := trace (Cancellation.classOf b)
  intro x y
  exact PointSpine.unique I dh.inventory dh.unit (h.typed tb) trace

end PowerSpine.PointView

private theorem schema_unique [DecidableEq sig.ACSym] (I : Inventory s β T.rules)
    (dh : ProtectedTable E) (r : Rule) (v : Fin 3 → Term sig)
    (ty : ∀ i, HasSort (v i) .msg) (norm : ∀ i, Normal (ruleRoot T.rules) (v i)) :
    Unique (ruleRoot T.rules) (r.equation s β v).lhs := by
  have view (i) : PowerSpine.PointView s β (ruleRoot T.rules) (v i) :=
    PointSpine.view I (ty i) (norm i) [] (by simp) (by simp)
  have sc (i) : Staging.Signed s (ruleRoot T.rules) (v i) := fun k => Balance.defined s _ k (norm i)
  cases r with
  | one =>
    intro x y l r
    exact ((I.point_one dh.inventory (ty 0) (norm 0) dh.unit).mp l).trans
      ((I.point_one dh.inventory (ty 0) (norm 0) dh.unit).mp r).symm
  | nested =>
    intro x y
    exact (((view 2).action (ty 1) (sc 1)).action (ty 0) (sc 0)).unique I dh
  | extract =>
    intro x y
    exact PowerSpine.unique_viewed I dh.power dh.inventory dh.unit (ty 0) (β.point_sorted (ty 1) (ty 2))
      (view 0) ((view 2).action (ty 1) (sc 1)) [] (by simp) (by simp)

/-- Each active point or map row has unique normal forms for every normalized
instance. This proof consumes only the relevant inventories on one shared
table, independently of which other symbols have equations. -/
theorem Inventory.uniqueRow [DecidableEq sig.ACSym] (I : Inventory s β T.rules)
    (dh : ProtectedTable E) (row : Equation sig) (mem : row ∈ T.rules)
    (hd : head row.lhs = .free β.pmult ∨ head row.lhs = .comm β.emap) : UniqueRow T.rules row := by
  have source : ∃ r : Rule, row = r.equation s β (fun i => .var (I.keys r i)) := by
    rcases hd with point | pair
    · obtain ⟨r,_,eq⟩ := I.onlyPoint row mem point; exact ⟨r,eq⟩
    · exact ⟨.extract,I.onlyMap row mem pair⟩
  obtain ⟨r,rfl⟩ := source
  intro ρ hn
  rw [(Rule.instantiate_subst ..).1]
  exact schema_unique I dh r _ (fun i => I.typed r i ▸ ρ.sorted _) (fun i => hn _)

end Tamarin.Rewriting.Bilinear
