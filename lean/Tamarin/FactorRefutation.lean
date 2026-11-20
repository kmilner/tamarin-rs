import Tamarin.TotalUnifyWire
import Tamarin.VariableElimination

/-! Check a proposed factoring failure on the equations before factoring.
Free constructors decompose positionally. A sorted binding can be propagated
through any remaining term, including C and AC applications. Dropping an
equation is safe here because only a refutation of the remainder is accepted. -/
namespace Tamarin.FactorRefutation
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
  [DecidableEq s.ACSym] [DecidableEq s.Atom]

private abbrev Verdict (p : Problem s) := {b : Bool // b = true → ¬ p.Satisfiable}

private def defer (p : Problem s) : Verdict p := ⟨false, by simp⟩

private def fromNecessary {p q : Problem s} (h : ∀ σ, p.Solves σ → q.Solves σ)
    (result : Verdict q) : Verdict p :=
  ⟨result.val, fun hit ⟨σ, sol⟩ => result.property hit ⟨σ, h σ sol⟩⟩

private def variableStep (x : Variable) (t : Term s) (rest : Problem s) (growth : Nat)
    (next : (q : Problem s) → Nat → Verdict q) : Verdict (⟨.var x,t⟩ :: rest) := by
  let skip := fun (t : Term s) => fromNecessary (p := ⟨.var x,t⟩ :: rest)
    (fun _ sol e he => sol e (.tail _ he)) (next rest growth)
  letI := t.occursDecidable x
  if occurs : t.Occurs x then
    if same : t = .var x then exact skip _
    else
      exact ⟨true, fun _ ⟨σ,sol⟩ => FiniteOccurs.not_equiv ⟨occurs,same⟩ σ (sol _ (.head _))⟩
  else if sorted : t.checkSort x.sort then
    -- Substituting this image can multiply the expanded input size by at most its node count.
    let cost := FiniteOccurs.nodes t
    if cost > growth then exact skip _
    else
      let typed := Term.checkSort_sound _ _ sorted
      exact fromNecessary (VariableElimination.eliminate_complete x t typed rest)
        (next (rest.substitute (Substitution.binding x t typed)) (growth / cost))
  else
    -- An alias can be written with the narrower variable on the left.
    match t with
    | .var y =>
      if h : (Term.var x : Term s).checkSort y.sort then
        let binding := Substitution.binding y (.var x) (Term.checkSort_sound _ _ h)
        apply fromNecessary (q := rest.substitute binding) _ (next _ growth)
        intro σ sol
        apply VariableElimination.eliminate_complete
        exact List.forall_mem_cons.mpr ⟨(sol _ (.head _)).symm, fun e he => sol e (.tail _ he)⟩
      else exact skip _
    | _ => exact skip _

private def replay : (fuel growth : Nat) → (p : Problem s) → Verdict p
  | 0, _, p => defer p
  | _ + 1, _, [] => defer []
  | fuel + 1, growth, e :: rest => by
    if bad : NarrowingClash.impossible e then
      exact ⟨true, fun _ => (complete_empty_iff _).mp (NarrowingClash.refutes
        (List.any_eq_true.mpr ⟨e,.head _,bad⟩))⟩
    else
      let next := fun q n => replay fuel n q
      match e with
      | ⟨.var x, t⟩ => exact variableStep x t rest growth next
      | ⟨t, .var x⟩ =>
        exact fromNecessary (fun _ sol => List.forall_mem_cons.mpr
          ⟨(sol _ (.head _)).symm, fun e he => sol e (.tail _ he)⟩) (variableStep x t rest growth next)
      | ⟨.free f xs, .free g ys⟩ =>
        if same : f = g then
          subst g
          let args : Problem s := List.ofFn fun i => ⟨xs i,ys i⟩
          apply fromNecessary (q := args ++ rest) _ (next (args ++ rest) growth)
          intro σ sol e he
          rcases List.mem_append.mp he with arg | tail
          · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp arg
            exact (Matching.free_equiv_iff ..).mp (sol _ (.head _)) i
          · exact sol e (.tail _ tail)
        else exact defer _
      | _ => exact fromNecessary (fun _ sol e he => sol e (.tail _ he)) (next rest growth)

/-- A positive verdict rules out every sorted substitution on the decoded
query. Exhausting either bound gives an inconclusive verdict. -/
def run (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64) : Bool :=
  match TotalUnifyWire.input ds ns es with
  | none => false
  | some ⟨_,p⟩ => (replay 256 256 p).val

theorem correct : TotalUnifyWire.RefutationCorrect run := by
  intro ds ns es hit
  unfold run at hit
  split at hit
  next => contradiction
  next d p dec => exact ⟨d,p,dec,(replay 256 256 p).property hit⟩

end Tamarin.FactorRefutation
