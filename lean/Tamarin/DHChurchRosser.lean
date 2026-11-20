import Tamarin.DHChurchRosserAlgebra
import Tamarin.DHStaging

/-! Semantic confluence for the DH rules and additional root equations. Variables in a root rewrite
may denote reducible terms. Interpret them first in the normal-form algebra,
then validate the complete schema on these shared normal message values. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open Cancellation ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- Assumptions on the combined presentation used to build an algebra of
reachable normal values. Additional free and commutative heads may rewrite. -/
structure Extension (E : ExtraTable T) : Prop extends ProtectedTable E where
  terminating : WellFounded fun b a => StepModulo (ruleRoot T.rules) a b
  sortPreserving : ∀ {a b}, StepModulo (ruleRoot T.rules) a b → ∀ k, HasSort a k → HasSort b k
  neutralNormal : Normal (ruleRoot T.rules) s.neutralTerm
  otherAC : ∀ f, f ≠ s.mul → Head.ac f ∉ ruleHeads T.rules

abbrev Unique := @NormalAlgebra.Unique sig
abbrev UniqueRow := @NormalAlgebra.UniqueRow sig

/-- The four protected heads are discharged by the DH schema proofs. -/
def DHHead (s : Symbols sig) (h : Head sig) : Prop :=
  h = .free s.pow ∨ h = .free s.inv ∨ h = .free s.one ∨ h = .ac s.mul

private theorem signed_unique [DecidableEq sig.ACSym] (tab : ProtectedTable E) {t : Term sig}
    (ht : HasSort t .msg) (h : Staging.Signed s (ruleRoot T.rules) t) : Unique (ruleRoot T.rules) t := by
  intro a b l r
  exact Balance.normal_unique tab.inventory E.presentation (fun _ => Balance.plain_of_inverse E) h
    (l.2.2 _ ht) (r.2.2 _ ht) l.2.1 r.2.1 l.1 r.1

private theorem schema_unique [DecidableEq sig.ACSym] (tab : ProtectedTable E) (neutral : Normal (ruleRoot T.rules) s.neutralTerm) (r : Rule)
    (a : Fin 3 → Term sig) (ty : ∀ i, HasSort (a i) .msg) (nf : ∀ i, Normal (ruleRoot T.rules) (a i)) :
    Unique (ruleRoot T.rules) (r.instantiate s a).lhs := by
  have typ := r.equation.1.sorted s a ty
  have signed i : Staging.Signed s (ruleRoot T.rules) (a i) := fun k => Balance.defined s _ k (nf i)
  have unit : Staging.Signed s (ruleRoot T.rules) s.product.one := fun k => ⟨0,Balance.read_one ..⟩
  cases r
  case expOne =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ (nf 0)) unit)
  case tower =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ (nf 0))
        (signed 1)) (signed 2))
  case neutral =>
    intro u v
    exact DHTower.Spine.unique tab.power tab.inventory tab.unit typ
      (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ neutral) (signed 0))
  all_goals
    apply signed_unique tab typ
    solve_by_elim (maxDepth := 12) only [Staging.signed_mul,Staging.signed_inv,signed,unit]

private theorem extra_unique [DecidableEq sig.ACSym] (tab : ProtectedTable E) (r : ExtraRule)
    (a : Fin 3 → Term sig) (ty : ∀ i, HasSort (a i) .msg) (nf : ∀ i, Normal (ruleRoot T.rules) (a i)) :
    Unique (ruleRoot T.rules) (r.instantiate s a).lhs := by
  have typ := r.equation.1.sorted s a ty
  have signed i : Staging.Signed s (ruleRoot T.rules) (a i) := fun k => Balance.defined s _ k (nf i)
  have unit : Staging.Signed s (ruleRoot T.rules) s.product.one := fun k => ⟨0,Balance.read_one ..⟩
  cases r <;> apply signed_unique tab typ <;>
    solve_by_elim (maxDepth := 12) only [Staging.signed_mul,Staging.signed_inv,signed,unit]

/-- Protected DH rows can share their ambient table with other AC theories. -/
theorem protected_unique [DecidableEq sig.ACSym] (tab : ProtectedTable E)
    (neutral : Normal (ruleRoot T.rules) s.neutralTerm)
    (row : Equation sig) (mem : row ∈ T.rules) (hd : DHHead s (head row.lhs)) : UniqueRow T.rules row := by
  intro τ norm
  rcases tab.atHead row mem hd with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · simp only [Rule.instantiate,Expr.subst_eval]
    exact schema_unique tab neutral r _ (fun i => T.actualSort r i ▸ τ.sorted _) (fun i => norm _)
  · simp only [ExtraRule.instantiate,Expr.subst_eval]
    exact extra_unique tab r _ (fun i => E.sorted r i ▸ τ.sorted _) (fun i => norm _)

/-- Prove confluence of the combined table by validating each additional row
on normalized substitution images. Every contextual instance, including one
with repeated reducible arguments, preserves the normal-form interpretation. -/
theorem Extension.canonical_of_rows [DecidableEq sig.ACSym] (tab : Extension E)
    (p : Product s (ruleRoot T.rules))
    (rows : ∀ r ∈ T.rules, ¬ DHHead s (head r.lhs) → UniqueRow T.rules r) :
    MaudeOperations.CanonicalPresentation (ruleRoot T.rules) := by
  let base : NormalAlgebra.Presentation T.rules := ⟨tab.apps,tab.terminating,tab.sortPreserving⟩
  apply base.canonical (fun f => if h : f = s.mul then h ▸ p else NormalAlgebra.inertProduct base f (tab.otherAC f h))
  intro row mem
  by_cases hd : DHHead s (head row.lhs)
  · exact protected_unique tab.toProtectedTable tab.neutralNormal row mem hd
  · exact rows row mem hd

theorem canonical_of_product [DecidableEq sig.ACSym] (tab : ExactTable E)
    (p : Product s (ruleRoot T.rules)) : MaudeOperations.CanonicalPresentation (ruleRoot T.rules) := by
  have ext : Extension E := {
    toProtectedTable := tab.protectedTable
    terminating := tab.terminating
    sortPreserving := tab.sortPreserving
    otherAC := fun f neq => tab.absent (fun eq => neq (Head.ac.inj eq)) (by intro h; cases h) (by intro h; cases h)
    neutralNormal := by
      refine constructor_node_normal _ tab.apps _ ?_ (fun i => Fin.elim0 (s.neutralArity ▸ i))
      apply tab.absent
      · intro h; cases h
      · intro h; have eq := congrArg sig.arity (Head.free.inj h); simp [s.neutralArity,s.invArity] at eq
      · intro h; have eq := congrArg sig.arity (Head.free.inj h); simp [s.neutralArity,s.powArity] at eq }
  apply ext.canonical_of_rows p
  intro r mem no
  rcases tab.heads mem with h | h | h
  · exact (no (.inr (.inr (.inr h)))).elim
  · exact (no (.inr (.inl h))).elim
  · exact (no (.inl h)).elim

end Tamarin.Rewriting.DHPeer.ChurchRosser
