import Tamarin.VariantOverlapAgreement
import Tamarin.ReferenceMatching

/-! Establish overlap agreement directly when corresponding inputs determine
both outputs through free projections and congruence. -/
namespace Tamarin.CheckedVariants
open Rewriting Rewriting.VariantOverlapAgreement
variable {s : Signature} {I : Type} {l r : I → Term s}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private abbrev Derived (l r : I → Term s) :=
  {e : Equation s // FromInputs l r e.lhs e.rhs}

private def project (fuel : Nat) (a b : Term s) (known : FromInputs l r a b) : List (Derived l r) :=
  let here : Derived l r := ⟨⟨a,b⟩,known⟩
  match fuel, a, b with
  | n+1, .free f x, .free g y =>
    if eq : f = g then by
      subst g
      exact here :: (List.finRange (s.arity f)).flatMap (fun i =>
        project n (x i) (y i) (.freeArg f x y i known))
    else [here]
  | _, _, _ => [here]

private def failure (p : Prop) : {ok : Bool // ok → p} :=
  ⟨false,by simp⟩

private def derive (known : List (Derived l r)) (fuel : Nat) (a b : Term s) :
    {ok : Bool // ok → FromInputs l r a b} := by
  if h : known.any (fun e => ReferenceMatching.equal a e.val.lhs && ReferenceMatching.equal b e.val.rhs) then
    exact ⟨true,fun _ => by
      obtain ⟨e,_,both⟩ := List.any_eq_true.mp h
      obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp both
      exact .basis ((ReferenceMatching.equal_iff ..).mp left) ((ReferenceMatching.equal_iff ..).mp right) e.property⟩
  else
    cases fuel with
    | zero => exact failure _
    | succ n =>
      match a, b with
      | .atom x, .atom y =>
        if h : x = y then subst y; exact ⟨true,fun _ => .atom x⟩
        else exact failure _
      | .free f x, .free g y =>
        if h : f = g then
          subst g
          let ds := fun i => derive known n (x i) (y i)
          exact ⟨(List.finRange (s.arity f)).all (fun i => (ds i).val),fun good =>
            .free f x y (fun i => (ds i).property (List.all_eq_true.mp good i (List.mem_finRange _)))⟩
        else exact failure _
      | .comm f a b, .comm g c d =>
        if h : f = g then
          subst g
          let a' := derive known n a c
          let b' := derive known n b d
          exact ⟨a'.val && b'.val,fun h => .comm f (a'.property (Bool.and_eq_true_iff.mp h).1)
            (b'.property (Bool.and_eq_true_iff.mp h).2)⟩
        else exact failure _
      | .ac f a b, .ac g c d =>
        if h : f = g then
          subst g
          let a' := derive known n a c
          let b' := derive known n b d
          exact ⟨a'.val && b'.val,fun h => .ac f (a'.property (Bool.and_eq_true_iff.mp h).1)
            (b'.property (Bool.and_eq_true_iff.mp h).2)⟩
        else exact failure _
      | _, _ => exact failure _

def determined (ks : List I) (p q : RootNarrowing.State s I) (fuel : Nat) :
    {ok : Bool // ok → FromInputs p.input q.input (p.value ()) (q.value ())} :=
  let obs := ks.flatMap (fun i => project fuel (p.input i) (q.input i) (.input i))
  derive obs fuel (p.value ()) (q.value ())

end Tamarin.CheckedVariants
