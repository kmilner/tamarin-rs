import Tamarin.ACSpanGraph
import Tamarin.VariantOverlapGraph
import TamarinRuntime.ACSpanOverlap

namespace Tamarin.ACSpanOverlap
open Whole WholeProblem Cancellation Rewriting.VariantOverlapAgreement
variable {s : Signature} {I : Type}

private noncomputable def view (c : Codec s) (σ τ : Substitution s) (e : Tree × Tree) :=
  (evalClass c σ (canonical e.1),evalClass c τ (canonical e.2))

private def image (σ τ : Substitution s) (e : Equation s) :=
  (some (classOf (σ.apply e.lhs)),some (classOf (τ.apply e.rhs)))

private theorem rows_view (c : Codec s) (σ τ : Substitution s) (p : Problem s) {raw}
    (rep : CheckedFactoring.Rows c p raw) : raw.map (view c σ τ) = p.map (image σ τ) := by
  induction p generalizing raw with
  | nil => cases rep.layout; rfl
  | cons e p ih =>
    cases rep.layout with
    | cons l r rest =>
      obtain ⟨sl,sr⟩ := rep.faithful e List.mem_cons_self
      simp only [List.map_cons,List.cons.injEq,view,image,true_and,
        ←l.observations.1,←r.observations.1,evalClass_key c σ _ sl,evalClass_key c τ _ sr]
      exact ih ⟨rest,fun e he => rep.faithful e (List.mem_cons_of_mem _ he)⟩

private theorem head_live (c : Codec s) (σ τ : Substitution s) (obs : List (Tree × Tree))
    (valid : ∀ e ∈ obs, (evalClass c σ e.1).isSome ∧ (evalClass c τ e.2).isSome)
    {id : UInt64} (present : id ∈ ACSpanGraph.heads obs) : ∃ f, c.acs.get id = some f := by
  let head : Tree → List UInt64
    | .app 4 f _ => [f]
    | _ => []
  change id ∈ (obs.flatMap (fun e => head e.1 ++ head e.2)).eraseDups at present
  obtain ⟨e,he,where_⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp present)
  have named (ρ : Substitution s) (t : Tree) (ok : (evalClass c ρ t).isSome)
      (found : id ∈ head t) : ∃ f, c.acs.get id = some f := by
    cases t with
    | leaf => simp [head] at found
    | app k f xs =>
      by_cases hk : k = 4
      · subst k
        obtain rfl : id = f := List.mem_singleton.mp found
        exact ACSpanGraph.ac_named c ρ (Option.isSome_iff_exists.mp ok)
      · simp [head,hk] at found
  rcases List.mem_append.mp where_ with l|r
  · exact named σ e.1 (valid e he).1 l
  · exact named τ e.2 (valid e he).2 r

mutual
  private theorem eval_obligations (c : Codec s) (σ τ : Substitution s) (a b : Tree)
      (agree : ∀ e ∈ obligations a b, evalClass c σ e.1 = evalClass c τ e.2) :
      evalClass c σ a = evalClass c τ b := by
    cases a with
    | leaf => exact agree _ List.mem_cons_self
    | app k i xs =>
      cases b with
      | leaf => exact agree _ List.mem_cons_self
      | app l j ys =>
        by_cases shape : k = l ∧ i = j ∧ xs.length = ys.length
        · obtain ⟨rfl,rfl,len⟩ := shape
          have children := eval_children c σ τ xs ys len (by simpa [obligations,len] using agree)
          simp only [evalClass,children]
        · exact agree (.app k i xs,.app l j ys) (by simp [obligations,shape])
  private theorem eval_children (c : Codec s) (σ τ : Substitution s) (xs ys : List Tree)
      (aligned : xs.length = ys.length)
      (agree : ∀ e ∈ childObligations xs ys, evalClass c σ e.1 = evalClass c τ e.2) :
      evalClasses c σ xs = evalClasses c τ ys := by
    cases xs with
    | nil => cases ys <;> simp_all [evalClasses]
    | cons x xs =>
      cases ys with
      | nil => simp at aligned
      | cons y ys =>
        have h := eval_obligations c σ τ x y (fun e he => agree e (List.mem_append_left _ he))
        have t := eval_children c σ τ xs ys (by simpa using aligned)
          (fun e he => agree e (List.mem_append_right _ he))
        simp only [evalClasses,h,t]
end

private theorem extra_equal (c : Codec s) (σ τ : Substitution s) (raw : Observations) (a b : Tree)
    (valid : ∀ e ∈ canonicalPairs raw, (evalClass c σ e.1).isSome ∧ (evalClass c τ e.2).isSome)
    (agree : ∀ e ∈ canonicalPairs raw, evalClass c σ e.1 = evalClass c τ e.2)
    (accepted : extra raw a b = true) : evalClass c σ (canonical a) = evalClass c τ (canonical b) := by
  have transfer (l r : Tree) (success : ∃ id ∈ ACSpanGraph.heads (canonicalPairs raw),
      ACSpanGraph.linear id (canonicalPairs raw) l r = true) : evalClass c σ l = evalClass c τ r := by
    obtain ⟨id,present,ok⟩ := success
    obtain ⟨f,named⟩ := head_live c σ τ _ valid present
    exact ACSpanGraph.linear_sound c σ τ named _ l r agree ok
  simp only [extra,Bool.and_eq_true,List.any_eq_true,List.all_eq_true,Bool.or_eq_true] at accepted
  rcases accepted.2 with whole|parts
  · exact transfer _ _ whole
  · apply eval_obligations
    intro e he
    exact transfer _ _ (parts.2 e (List.mem_eraseDups.mpr he))

/-- The final pair is the requested pair of outputs. All preceding pairs
refer to the same caller columns in the two rows, including shared caller
variables. Each row can specialize its own private variables independently. -/
theorem extra_agrees (c : Codec s) (ids : List I) (left right : I → Term s) (a b : Term s)
    {obs x y} (rep : CheckedFactoring.Rows c (VariantOverlapGraph.equations ids left right a b)
      (obs ++ [(x,y)])) (accepted : extra obs x y = true) : Agrees left right a b := by
  intro σ τ same
  have split := congrArg List.reverse (rows_view c σ τ _ rep)
  simp only [VariantOverlapGraph.equations,List.map_append,List.map_cons,List.map_nil,List.reverse_append,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.cons.injEq,List.reverse_inj] at split
  obtain ⟨last,first⟩ := split
  have entries (e) (he : e ∈ canonicalPairs obs) : ∃ i,
      evalClass c σ e.1 = some (classOf (σ.apply (left i))) ∧
      evalClass c τ e.2 = some (classOf (τ.apply (right i))) := by
    obtain ⟨⟨l,r⟩,here,rfl⟩ := List.mem_map.mp he
    have occ := List.mem_map_of_mem (f := view c σ τ) here
    rw [first] at occ
    obtain ⟨p,hp,eq⟩ := List.mem_map.mp occ
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨i,congrArg Prod.fst eq.symm,congrArg Prod.snd eq.symm⟩
  have valid (e) (he : e ∈ canonicalPairs obs) :
      (evalClass c σ e.1).isSome ∧ (evalClass c τ e.2).isSome := by
    obtain ⟨_,l,r⟩ := entries e he
    simp only [l,r,Option.isSome_some,true_and]
  have agree (e) (he : e ∈ canonicalPairs obs) : evalClass c σ e.1 = evalClass c τ e.2 := by
    obtain ⟨i,l,r⟩ := entries e he
    exact l.trans ((congrArg some (Quotient.sound (same i))).trans r.symm)
  have result := extra_equal c σ τ obs x y valid agree accepted
  exact Quotient.exact (Option.some.inj (((congrArg Prod.fst last).symm.trans result).trans
    (congrArg Prod.snd last)))

end Tamarin.ACSpanOverlap
