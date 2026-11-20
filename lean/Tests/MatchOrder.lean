import Tamarin.MatchOrder
import Tamarin.CommutativeLinear
import Tamarin.Pairing

namespace Tamarin.Matching.MatchOrderTests
open Pairing

private abbrev x : Variable := ⟨0,.msg⟩
private abbrev y : Variable := ⟨1,.msg⟩
private def a : PTerm := .atom (0,.msg)
private def b : PTerm := .atom (1,.msg)

private def instanceC : Commutative.Linear signature where
  f := 0
  x := x
  y := y
  s := a
  t := b
  distinct := by decide
  sx := rfl
  sy := rfl
  ss := .atom _
  st := .atom _
  independent := by simp [a,b,Term.Occurs]

private abbrev p : Problem signature := instanceC.query.problem
private abbrev direct := instanceC.answer false
private abbrev crossed := instanceC.answer true

private theorem observed (v : Variable) : Observed p v ↔ v = x ∨ v = y := by
  simp [Observed, Commutative.Query.problem, Commutative.Linear.query, instanceC,Term.Occurs]

private theorem images (σ : PSubst) : Matches p σ ↔
    (EquivB (σ.image x) a ∧ EquivB (σ.image y) b) ∨
    (EquivB (σ.image x) b ∧ EquivB (σ.image y) a) := by
  simp [Matches,Commutative.Query.problem,Commutative.Linear.query,instanceC,
    Substitution.apply,Term.subst,Commutative.equiv_iff]

private theorem scoped_answer (swap : Bool) : Scoped p (fun _ => True) (instanceC.answer swap) := by
  intro v hv
  simp [observed] at hv
  simp [Commutative.Linear.answer,instanceC,hv.1,hv.2]

private theorem both : Complete p (fun _ => True) [direct,crossed] := by
  constructor
  · intro σ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨images _ |>.mpr (.inl ⟨.refl _,.refl _⟩),scoped_answer false⟩
    · exact ⟨images _ |>.mpr (.inr ⟨.refl _,.refl _⟩),scoped_answer true⟩
  · intro ρ hm _
    rcases (images ρ).mp hm with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · refine ⟨direct,by simp,fun v hv => ?_⟩
      rcases (observed v).mp hv with rfl | rfl
      · exact hx
      · exact hy
    · refine ⟨crossed,by simp,fun v hv => ?_⟩
      rcases (observed v).mp hv with rfl | rfl
      · exact hx
      · exact hy

private theorem reordered : Complete p (fun _ => True) [crossed,crossed,direct] :=
  both.of_same_members (by intro σ; simp only [List.mem_cons, List.not_mem_nil]; grind)

-- The existence consumer and an explicitly ranked consumer survive both the
-- new order and a duplicate. The order of variables in a binding table is
-- irrelevant for this key, which reads the image of x modulo B.
private noncomputable def key (σ : PSubst) : Nat := by
  classical exact if EquivB (σ.image x) a then 0 else 1

private theorem key_invariant (σ τ : PSubst) (agree : Substitution.AgreesOn (Observed p) σ τ) :
    key σ = key τ := by
  have eq := agree x ((observed _).mpr (.inl rfl))
  have h : EquivB (σ.image x) a ↔ EquivB (τ.image x) a := ⟨eq.symm.trans,eq.trans⟩
  unfold key
  rw [propext h]

example : ([direct,crossed] ≠ []) ↔ ([crossed,crossed,direct] ≠ []) :=
  both.nonempty_iff.trans reordered.nonempty_iff.symm

example : ([direct,crossed].map key).min? = ([crossed,crossed,direct].map key).min? :=
  both.min_key_eq reordered key key_invariant

-- Compare the complete binding vector in the caller's chosen variable order.
-- This representation distinguishes the two subject atoms in the example.
private noncomputable def atomKey (t : Term signature) : Nat := by
  classical exact if EquivB t a then 0 else 1

local instance : Min (List Nat) := minOfLe

example : ([direct,crossed].map (bindingImages atomKey [y,x])).min? =
    ([crossed,crossed,direct].map (bindingImages atomKey [y,x])).min? := by
  apply both.min_bindingImages_eq reordered
  · intro s t eq
    have h : EquivB s a ↔ EquivB t a := ⟨eq.symm.trans,eq.trans⟩
    unfold atomKey
    rw [propext h]
  · intro v mem
    simpa [observed, or_comm] using mem

-- Reading the first arm distinguishes these two complete implementations,
-- even when the observation respects equivalence modulo B.
example : ([direct,crossed].head?.map key) ≠ ([crossed,crossed,direct].head?.map key) := by
  have ne : ¬ EquivB b a := fun rel => by
    have same := rel.head_eq
    cases same
  change some (key direct) ≠ some (key crossed)
  have d : direct.image x = a := rfl
  have c : crossed.image x = b := rfl
  simp [key,d,c,ne,EquivB.refl]

-- Factor z ↦ x alongside C(x,y) matching C(a,b). In the direct arm x
-- matches a, but the image of z is the rigid subject variable x.
private abbrev z : Variable := ⟨2,.msg⟩
private def sideEq : Equation signature := ⟨.var z,.var x⟩
private noncomputable def extend := merge [sideEq] (Substitution.binding z (.var x) (.var x))

example : Complete (p ++ [sideEq]) (fun _ => True) ([direct,crossed].map extend) := by
  exact both.with_variable_side z (.var x) (.var x)
    (fun occurs => by rcases (observed _).mp occurs with h|h <;> cases h)
    (List.perm_append_comm (l₁ := [sideEq]) (l₂ := p))

example : (extend direct).image z = .var x ∧ (extend direct).image x = a := by
  have hz : Observed [sideEq] z := ⟨_,List.mem_cons_self,rfl⟩
  have hx : ¬ Observed [sideEq] x := by simp [Observed,sideEq,Term.Occurs,x,z]
  simp only [extend,merge,hz,hx,↓reduceIte,Substitution.binding_image_self]
  exact ⟨trivial,rfl⟩

end Tamarin.Matching.MatchOrderTests
