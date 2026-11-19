import Tamarin.ResidualVariable
import Tamarin.ResidualSearch

/-! Rust pops a substituted pair while retaining raw terms in its pending stack.
A new binding is composed once. Suspended pairs may resume in a different order.
The variable-step transition only needs the permutation of these remaining entries. -/
namespace Tamarin.ResidualVariable
open WholeProblem Residual
variable {sig : Signature}

private theorem composed (p : Problem sig) (β θ : Substitution sig) :
    (p.substitute θ).substitute β = p.substitute (β.compose θ) := by
  simp only [Problem.substitute, List.map_map, Substitution.apply_compose, Function.comp_def]

def Transition (action : UInt8) (a b : Term sig) (observed : Variable → Prop)
    (p resumed : Problem sig) (θ ρ : Substitution sig) : Prop :=
  let before := Denotes observed (⟨a,b⟩ :: p.substitute θ) θ ρ
  let after := fun (sub : Substitution sig) => Denotes observed (resumed.substitute sub) sub ρ
  match action with
  | 1 => ¬ before
  | 2 => before ↔ after θ
  | 3 => ∃ v, a = .var v ∧ ∃ typed : HasSort b v.sort, before ↔ after ((Substitution.binding v b typed).compose θ)
  | 4 => ∃ v, b = .var v ∧ ∃ typed : HasSort a v.sort, before ↔ after ((Substitution.binding v a typed).compose θ)
  | _ => False

private theorem advances {action} {a b : Term sig} (just : Justified action a b)
    (var : kind a = 0 ∨ kind b = 0) (observed) (p resumed : Problem sig) (reorder : p.Perm resumed)
    (θ ρ : Substitution sig) : Transition action a b observed p resumed θ ρ := by
  have perm (sub : Substitution sig) :
      Denotes observed (p.substitute sub) sub ρ ↔ Denotes observed (resumed.substitute sub) sub ρ :=
    Residual.perm observed (reorder.map _) sub ρ
  cases just with
  | clash bad => exact clash observed bad _ θ ρ
  | discard eq => exact (discard observed eq _ θ ρ).trans (perm θ)
  | bindLeft v _ ht absent =>
    refine ⟨v,rfl,ht,?_⟩
    exact (Residual.bind observed v _ ht absent (p.substitute θ) θ ρ).trans
      (by rw [composed]; exact perm _)
  | bindRight v _ ht absent =>
    refine ⟨v,rfl,ht,?_⟩
    exact (Residual.swap observed _ _ _ θ ρ).trans ((Residual.bind observed v _ ht absent (p.substitute θ) θ ρ).trans
      (by rw [composed]; exact perm _))
  | defer | positional | orientations => simp [kind] at var

/-- The selected operands have already been normalized by the accumulated binding.
All other stack entries, including suspended entries, are interpreted lazily. -/
theorem worklist {solve} (verified : Correct solve) (v : Variable) (t : Term sig)
    (typed : HasSort t t.rootSort) (put : Variable → UInt64)
    (faithful : ∀ w ∈ t.variables, put w = put v → w = v) (ids : Array UInt64)
    (inventory : ids.toList.Perm (t.variables.map put)) (right : Bool)
    (observed : Variable → Prop) (p resumed : Problem sig) (reorder : p.Perm resumed)
    (θ ρ : Substitution sig) :
    let action := solve right (put v) (sortWord v.sort) (kind t) (sortWord t.rootSort) ids
    Transition action (if right then t else .var v) (if right then .var v else t)
      observed p resumed θ ρ := by
  have h := verified v t typed put faithful ids inventory right
  cases right
  · exact advances h (Or.inl rfl) observed p resumed reorder θ ρ
  · exact advances h (Or.inr rfl) observed p resumed reorder θ ρ

end Tamarin.ResidualVariable
