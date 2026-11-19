import Tamarin.VariantFrontier
import Tamarin.GroundConjunction
import Tamarin.ACRepresentation

namespace Tamarin.Rewriting.VariantOverlapAgreement
open RootNarrowing VariantJoin

variable {s : Signature} {I : Type}

/-- A value is determined on overlaps if agreement on corresponding inputs
forces agreement on the value. The two symbolic rows have independent
substitutions, even when the rows themselves are identical. -/
def Agrees (left right : I → Term s) (a b : Term s) : Prop :=
  ∀ σ τ : Substitution s, (∀ i, EquivB (σ.apply (left i)) (τ.apply (right i))) →
    EquivB (σ.apply a) (τ.apply b)

/-- An overlap checker can use any sufficient test for this implication.
The resulting certificate applies in every ambient rewrite theory. -/
theorem Agrees.compatible {R : Root s} {p q : State s I}
    (agree : Agrees p.input q.input (p.value ()) (q.value ())) : CompatibleValues R p q := by
  rintro _ _ _ _ _ _ ⟨σ,_,l⟩ ⟨τ,_,r⟩
  exact (l.values ()).trans ((agree σ τ (fun i => (l.inputs i).symm.trans (r.inputs i))).trans
    (r.values ()).symm)

/-- Construct two instances of the same constructor context using paired
observations as holes. A hole may select a whole compound input, and it
may be used repeatedly. Each row may choose any representative modulo B. -/
inductive FromInputs (left right : I → Term s) : Term s → Term s → Prop where
  | input (i : I) : FromInputs left right (left i) (right i)
  | atom (a : s.Atom) : FromInputs left right (.atom a) (.atom a)
  | free (f : s.FreeSym) (xs ys : Fin (s.arity f) → Term s)
      (children : ∀ i, FromInputs left right (xs i) (ys i)) :
      FromInputs left right (.free f xs) (.free f ys)
  | comm (f : s.CSym) {a b c d}
      (first : FromInputs left right a c) (second : FromInputs left right b d) :
      FromInputs left right (.comm f a b) (.comm f c d)
  | ac (f : s.ACSym) {a b c d}
      (first : FromInputs left right a c) (second : FromInputs left right b d) :
      FromInputs left right (.ac f a b) (.ac f c d)
  | basis {a a' b b'} (lhs : EquivB a a') (rhs : EquivB b b')
      (inner : FromInputs left right a' b') : FromInputs left right a b

variable {left right : I → Term s}

theorem FromInputs.agrees {a b} (h : FromInputs left right a b) : Agrees left right a b := by
  intro σ τ same
  induction h with
  | input i => exact same i
  | atom a => exact .refl _
  | free f _ _ _ ih => exact .free f _ _ ih
  | comm f _ _ h₁ h₂ => exact .comm_congr f h₁ h₂
  | ac f _ _ h₁ h₂ => exact .ac_congr f h₁ h₂
  | basis ha hb _ ih => exact (ha.subst σ.image).trans (ih.trans (hb.subst τ.image).symm)

/-- Rigid outputs may have different associations or orders on the two sides. -/
theorem FromInputs.ground {a b : Term s} (closed : a.Ground) (equal : EquivB a b) :
    FromInputs left right a b := by
  apply FromInputs.basis (.refl a) equal.symm
  clear equal b
  induction a with
  | var v => exact False.elim (closed v rfl)
  | atom a => exact .atom a
  | free f xs ih => exact .free f xs xs (fun i => ih i (fun v hv => closed v ⟨i,hv⟩))
  | comm f _ _ ih ik =>
    exact .comm f (ih (fun v hv => closed v (.inl hv))) (ik (fun v hv => closed v (.inr hv)))
  | ac f _ _ ih ik =>
    exact .ac f (ih (fun v hv => closed v (.inl hv))) (ik (fun v hv => closed v (.inr hv)))

theorem FromInputs.flat {a b : Term s} {pairs : List (Term s × Term s)} (f : s.ACSym)
    (first : FromInputs left right a b) (rest : ∀ p ∈ pairs, FromInputs left right p.1 p.2) :
    FromInputs left right (ACRepresentation.fold f a (pairs.map Prod.fst))
      (ACRepresentation.fold f b (pairs.map Prod.snd)) := by
  induction pairs generalizing a b with
  | nil => exact first
  | cons p ps ih => exact .ac f first (ih (rest p (by simp)) (fun q h => rest q (by simp [h])))

/-- A variable absent from all inputs can receive different images in two
copies of the same row. Even literal equality of such symbolic outputs
fails the overlap contract. -/
theorem unseen_variable {xs : I → Term s} (v : Variable) (absent : ∀ i, ¬(xs i).Occurs v) :
    ¬ Agrees xs xs (.var v) (.var v) := by
  let w : Variable := ⟨v.id + 1,v.sort⟩
  let τ := Substitution.binding v (.var w : Term s) (.var w)
  intro same
  have out := same Substitution.identity τ (fun i => by
    rw [Substitution.apply_identity,Substitution.binding_apply_of_not_occurs _ _ _ _ (absent i)]
    exact .refl _)
  change EquivB (.var v) (τ.image v) at out
  rw [Substitution.binding_image_self] at out
  have eq : v = w := (out.occurs_iff v).mp rfl
  have impossible := congrArg Variable.id eq
  dsimp [w] at impossible
  omega

end Tamarin.Rewriting.VariantOverlapAgreement
