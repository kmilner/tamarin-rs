import Tamarin.MaudeOperations
import Tamarin.SpecializedFresh

/-! Freshen bindings and values together after variant search. This also
protects a witness whose only occurrence is in the returned tuple. -/
namespace Tamarin.VariantFreshening
open Rewriting SpecializedFresh MaudeOperations
variable {s : Signature}

private def witnesses (keys : List Variable) (a : Variant s) :=
  FreshAnswer.rangeVariables keys a.subst ++ a.values.flatMap Term.variables

private def names (keys avoid : List Variable) (a : Variant s) : VariablePermutation :=
  let ws := witnesses keys a
  VariablePermutation.ofBlock ws (VariablePermutation.freshBound (ws ++ keys ++ avoid))
    (fun v hv => VariablePermutation.lt_freshBound _ v (by simp [hv]))

private theorem avoids {keys avoid : List Variable} {a : Variant s} {w}
    (hw : w ∈ witnesses keys a) : (names keys avoid a).forward w ∉ keys ++ avoid := by
  let ws := witnesses keys a
  let vs := ws ++ keys ++ avoid
  have eq : (names keys avoid a).forward w = VariablePermutation.shift (VariablePermutation.freshBound vs) w :=
    VariablePermutation.swapBlock_source _ _ _ hw
  intro bad
  have mem : (names keys avoid a).forward w ∈ vs := by
    simpa only [vs,List.append_assoc] using List.mem_append_right ws bad
  have lt := VariablePermutation.lt_freshBound vs _ mem
  rw [eq] at lt
  simp only [VariablePermutation.shift] at lt
  omega

def freshen (keys avoid : List Variable) (rows : List (Variant s)) : List (Variant s) :=
  rows.map fun a => renameArm keys (names keys avoid a) a

theorem reply {rules : List (Equation s)} (r : VerifiedReducer (ruleRoot rules))
    (vars : Normalized (ruleRoot rules) Substitution.identity) (q : List (Term s))
    (keys avoid : List Variable) (inventory : ∀ v, v ∈ keys ↔ Observed q v) (rows : List (Variant s))
    (complete : CompleteVariants (ruleRoot rules) q rows) :
    VariantReply (ruleRoot rules) q avoid (freshen keys avoid rows) := by
  apply VariantReply.ofCanonical r vars (complete_rename rules keys q rows (names keys avoid) vars
    (fun v => (inventory v).mpr) complete)
  intro b hb
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
  let π := names keys avoid a
  apply (safe_idempotent keys a.subst π q avoid inventory _ _ _).1
  · intro v hv w occurs
    exact avoids (List.mem_append_left _ (List.mem_flatMap.mpr ⟨v,hv,(Term.mem_variables ..).mpr occurs⟩))
  · intro t ht w occurs
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    obtain ⟨v,hv,rfl⟩ := (Term.occurs_rename u π.forward w).mp occurs
    exact .inr (fun bad => avoids (keys := keys) (a := a)
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨u,hu,(u.mem_variables _).mpr hv⟩)) (List.mem_append_right keys bad))

end Tamarin.VariantFreshening
