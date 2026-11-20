import Tamarin.BoundedVariants
import Tamarin.TableDecrease
import Tamarin.Pairing

namespace Tamarin.BoundedVariants.Tests
open Rewriting ConstructorVariants
private abbrev S := Pairing.signature
private abbrev wrap (t : Term S) := Pairing.snd t
private abbrev strip (t : Term S) := Pairing.fst t
private def x : Variable := ⟨0,.msg⟩
private abbrev v := Term.var (sig := S) x
private def rules : List (Equation S) := [⟨strip (wrap v),strip v⟩]
private def chain : Nat → Term S
  | 0 => .atom (0,.msg)
  | n + 1 => wrap (chain n)

-- Every step strictly shrinks the tree, even below a kind-level AC operator.
example : WellFounded (fun b a => StepModulo (ruleRoot rules) a b) :=
  TableDecrease.terminating (by decide)

private theorem typed (n : Nat) : HasSort (chain n) x.sort := by
  induction n with
  | zero => exact .atom _
  | succ n ih => exact .free _ _ (fun _ => ih)

private def image (n : Nat) := Substitution.binding x (chain n) (typed n)
private theorem app : ∀ r ∈ rules, Application r.lhs := by
  simp only [rules,List.mem_singleton,forall_eq]
  trivial

private theorem normal (n : Nat) : Normal (ruleRoot rules) (chain n) := by
  induction n with
  | zero =>
    exact constructor_node_normal rules app (.atom (0,.msg)) (fun h => by
      change Head.atom (0,.msg) ∈ [Head.free (sig := S) .fst] at h
      cases List.mem_singleton.mp h) trivial
  | succ n ih =>
    exact constructor_node_normal rules app (wrap (chain n)) (fun h => by
      change Head.free (sig := S) .snd ∈ [Head.free (sig := S) .fst] at h
      cases List.mem_singleton.mp h) (fun _ => ih)

private theorem normalized (n : Nat) : Normalized (ruleRoot rules) (image n) := by
  intro w
  by_cases e : w = x
  · subst w; simpa [image] using normal n
  · simpa [image,Substitution.identity,Substitution.binding_image_other,Ne.symm e,e] using (constructor_normal rules app).1 w

private theorem descent (n : Nat) :
    StepModulo (ruleRoot rules) (strip (chain (n+1))) (strip (chain n)) := by
  refine ⟨_,_,.refl _,.root ⟨_,List.mem_cons_self, image n,?_,?_⟩,.refl _⟩ <;>
    simp [Substitution.apply,Pairing.subst_fst,Pairing.subst_snd,Term.subst,image,chain]

-- The open query strip(X) can still normalize for arbitrarily many steps,
-- even though every image supplied for X is already normal. No descent rank
-- can be uniformly bounded on all these substitutions.
example (rank : Term S → Nat)
    (decreases : ∀ {a b}, StepModulo (ruleRoot rules) a b → rank b < rank a) :
    ¬ ∃ k, ∀ ρ : Substitution S, Normalized (ruleRoot rules) ρ → rank (ρ.apply (strip v)) ≤ k := by
  have long (n : Nat) : n ≤ rank (strip (chain n)) := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.lt_of_le_of_lt ih (decreases (descent n))
  rintro ⟨k,h⟩
  have limited := h (image (k+1)) (normalized _)
  have short : rank (strip (chain (k+1))) ≤ k := by
    simpa [Substitution.apply,Term.subst,image] using limited
  have lower := long (k+1)
  omega
end Tamarin.BoundedVariants.Tests
