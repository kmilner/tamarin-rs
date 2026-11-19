import TamarinCI

namespace Tamarin.Matching.Tests
open Tamarin.Pairing

abbrev x : Variable := ⟨0, .msg⟩
abbrev y : Variable := ⟨1, .msg⟩
def a : PTerm := .atom (0, .pub)
def xy : PSubst := Substitution.binding x (.var y) (.var y)
def xa : PSubst := Substitution.binding x a (.widen (.atom _) .pub_msg)

-- The subject remains rigid, even when its variable occurs in the pattern.
example : Matches ([⟨.var x, .var y⟩] : Problem signature) xy := by
  intro e he
  have he := List.mem_singleton.mp he; subst e
  change EquivB (xy.image x) (.var y)
  rw [xy, Substitution.binding_image_self]
  exact .refl _

example : ¬ Matches ([⟨.var x, .var y⟩] : Problem signature) xa := by
  intro h
  have he := h ⟨.var x, .var y⟩ (by simp)
  change EquivB (xa.image x) (.var y) at he
  rw [xa, Substitution.binding_image_self] at he
  have hm := he.eval_eq (FlatAC.atomCountModel (sig := signature) (0, .pub)) (fun _ => 0)
  simp [Model.eval, FlatAC.atomCountModel, a] at hm

-- Ordinary unification's occurs check is not a valid matching restriction:
-- substitutions are simultaneous and the subject is not substituted.
example : Matches ([⟨.var x, pair (.var x) a⟩] : Problem signature)
    (Substitution.binding x (pair (.var x) a)
      (pair_sorted (.var x) (.widen (.atom _) .pub_msg))) := by
  intro e he
  have he := List.mem_singleton.mp he; subst e
  change EquivB ((Substitution.binding x _ _).image x) _
  rw [Substitution.binding_image_self]
  exact .refl _

example : ¬ Scoped ([⟨.var x, a⟩] : Problem signature) (fun _ => False) xa := by
  intro h
  have he := h x (by simp)
  rw [xa, Substitution.binding_image_self] at he
  cases he

example : Complete ([] : Problem signature) (fun _ => True) [Substitution.identity] := by
  constructor
  · intro σ hs
    have he := List.mem_singleton.mp hs; subst σ
    exact ⟨by simp [Matches], by intro v _; rfl⟩
  · intro ρ _ _
    exact ⟨Substitution.identity, by simp, by simp [Substitution.AgreesOn, Observed]⟩

-- A matcher may choose the ground side independently for each equation.
-- The obligation is ordinary unification coverage on the original variables.
example {sig : Signature} (p : Problem sig) (flip : Equation sig → Bool)
    (answers : List (Substitution sig))
    (ground : ∀ e ∈ p.map (orient flip), e.rhs.Ground)
    (hm : Complete (p.map (orient flip)) (fun _ => True) answers) :
    CompleteSet p answers :=
  (orient_complete_iff flip p answers).mp (hm.groundSide ground)

-- Keep one bindable domain and substitution across the children and the rest
-- of the request, even when a variable occurs under more than one free head.
example {sig : Signature} (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
    (rest : Problem sig) (bindable : Variable → Prop) (answers : List (Substitution sig))
    (h : Complete (children f a b ++ rest) bindable answers) :
    Complete (⟨.free f a, .free f b⟩ :: rest) bindable answers :=
  (free_complete_iff f a b rest bindable answers).mpr h

-- Matching a compound subject can return an image mentioning the very
-- pattern variable being bound. Take the ground solver's actual singleton
-- and decode it through the rigid-subject refinement.
example (s : Signature) (v : Variable) (subject : Term s) (typed : HasSort subject v.sort) :
    Complete [⟨.var v,subject⟩] (fun _ => True)
      [RigidSubject.decode s (Substitution.binding v (RigidSubject.freeze s subject)
        (RigidSubject.freeze_sorted s typed))] :=
  RigidSubject.complete s [⟨.var v,subject⟩] _ (variable_match v _ _)

-- A common variable on opposite sides cannot justify suppressing a C alignment.
example (s : Signature) (v : Variable) : RigidSubject.pattern s (.var v) ≠ RigidSubject.freeze s (.var v) :=
  fun eq => ((RigidSubject.same_across s _ _).mp eq).2 v rfl

end Tamarin.Matching.Tests
