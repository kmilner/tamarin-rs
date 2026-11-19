import Tamarin.Algebra

/-!
# Models of B

These give an independent way to check the strength of `EquivB`. In particular,
countermodels can disprove accidental unit, idempotence, or associativity
laws. They are not implementations of normalization or unification.
-/
namespace Tamarin

/-- Any algebra satisfying exactly the declared C/AC laws is a model of B.
Untyped models suffice to separate terms, including well-sorted terms. -/
structure Model (sig : Signature) where
  Carrier : Type
  atom : sig.Atom → Carrier
  free : (f : sig.FreeSym) → (Fin (sig.arity f) → Carrier) → Carrier
  comm : sig.CSym → Carrier → Carrier → Carrier
  ac : sig.ACSym → Carrier → Carrier → Carrier
  comm_swap : ∀ f a b, comm f a b = comm f b a
  ac_swap : ∀ f a b, ac f a b = ac f b a
  ac_assoc : ∀ f a b c, ac f (ac f a b) c = ac f a (ac f b c)

def Model.eval {sig : Signature} (m : Model sig) (env : Variable → m.Carrier) :
    Term sig → m.Carrier
  | .var v => env v
  | .atom a => m.atom a
  | .free f args => m.free f (fun i => m.eval env (args i))
  | .comm f a b => m.comm f (m.eval env a) (m.eval env b)
  | .ac f a b => m.ac f (m.eval env a) (m.eval env b)

theorem EquivB.eval_eq {sig : Signature} {a b : Term sig} (h : EquivB a b)
    (m : Model sig) (env : Variable → m.Carrier) : m.eval env a = m.eval env b := by
  induction h with
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ha hb => exact ha.trans hb
  | free f a b _ ih => simp only [Model.eval]; exact congrArg (m.free f) (funext ih)
  | comm_congr f _ _ ha hb => simp only [Model.eval, ha, hb]
  | ac_congr f _ _ ha hb => simp only [Model.eval, ha, hb]
  | comm_swap f a b => exact m.comm_swap f _ _
  | ac_swap f a b => exact m.ac_swap f _ _
  | ac_assoc f a b c => exact m.ac_assoc f _ _ _

/-- AC adds weights. C combines them symmetrically but non-associatively.
Free functions count their root and children. -/
abbrev weightModel (sig : Signature) : Model sig where
  Carrier := Nat
  atom := fun _ => 1
  free := fun _ args => 1 + (List.ofFn args).sum
  comm := fun _ a b => (a + b + 1) * (a + b + 1)
  ac := fun _ a b => a + b
  comm_swap := by intros; simp only [Nat.add_comm]
  ac_swap := by intros; apply Nat.add_comm
  ac_assoc := by intros; apply Nat.add_assoc

end Tamarin
