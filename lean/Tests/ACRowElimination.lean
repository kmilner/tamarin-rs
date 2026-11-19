import Tamarin.ACRowElimination
import Tamarin.FiniteOccurs
import Tamarin.MatchingFree

/-! Two PFS packet shapes. All terms below may have arbitrary normalized
or reducible images. These are ordinary unification equations modulo B. -/
namespace Tamarin.ACRowEliminationTests
open ACRowElimination
private abbrev sig : Signature where
  FreeSym := Unit
  CSym := Empty
  ACSym := Unit
  Atom := Unit
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .fresh

private abbrev T := Term sig
private def mul (a b : T) : T := .ac () a b
private def inv (a : T) : T := .free () fun _ => a

private theorem unwrap {a b : T} {σ : Substitution sig}
    (h : EquivB (σ.apply (inv a)) (σ.apply (inv b))) : EquivB (σ.apply a) (σ.apply b) :=
  (Matching.free_equiv_iff ..).mp h 0

private theorem inside {a b : T} {σ : Substitution sig}
    (h : EquivB (σ.apply a) (σ.apply b)) : EquivB (σ.apply (inv a)) (σ.apply (inv b)) :=
  .free _ _ _ fun _ => h

private theorem atomicInv (a : T) : AtomicACPair.Atomic () (inv a) := fun _ => rfl

private theorem extra (a b : T) : ¬EquivB a (mul b a) := by
  intro eq
  have n := FiniteOccurs.nodes_equiv eq
  change FiniteOccurs.nodes a = FiniteOccurs.nodes b + FiniteOccurs.nodes a + 1 at n
  omega

private theorem clash (u h r : T) (σ : Substitution sig) :
    ¬EquivB (σ.apply (inv (mul u h))) (σ.apply (inv (mul (mul r u) h))) :=
  fun eq => extra (σ.apply u) (σ.apply r) (EquivB.ac_cancel_right (sig := sig) () (unwrap eq))

-- PFS packet 84 has precisely the solutions P=Q and U=V. Completeness
-- includes every possible composite image of U, not just ground constants.
example (p q r h u v : T) (σ : Substitution sig) :
    let a := inv (mul (mul r u) h)
    let b := inv (mul (mul r v) h)
    let c := inv (mul u h)
    let d := inv (mul v h)
    let tail : Problem sig := [⟨mul p (inv (mul r u)),mul q (inv (mul r v))⟩]
    Problem.Solves (⟨mul p a,mul q b⟩ :: ⟨mul p c,mul q d⟩ :: tail) σ ↔
      EquivB (σ.apply p) (σ.apply q) ∧ EquivB (σ.apply u) (σ.apply v) := by
  let tail : Problem sig := [⟨mul p (inv (mul r u)),mul q (inv (mul r v))⟩]
  have replaced := shared_forced (sig := sig) () p q _ (inv (mul (mul r v) h)) _ (inv (mul v h)) (atomicInv _) (atomicInv _) (clash u h r) tail σ
  apply replaced.trans
  simp only [Problem.Solves,List.forall_mem_cons]
  constructor
  · rintro ⟨pq,_,cd,_⟩
    exact ⟨pq,EquivB.ac_cancel_right (sig := sig) () (unwrap cd)⟩
  · rintro ⟨pq,uv⟩
    refine ⟨pq,inside (.ac_congr _ (.ac_congr _ (.refl _) uv) (.refl _)),inside (.ac_congr _ uv (.refl _)),?_⟩
    intro eq mem; obtain rfl := List.mem_singleton.mp mem
    exact .ac_congr _ pq (inside (.ac_congr _ (.refl _) uv))

-- In PFS packet 82 deleting the same offset leaves U*H = H. The
-- semigroup has no empty term, ruling this out for every substitution.
example (p q r h u : T) (tail : Problem sig) : ¬ Problem.Satisfiable
    (⟨mul p (inv (mul (mul r u) h)),mul q (inv (mul r h))⟩ ::
      ⟨mul p (inv (mul u h)),mul q (inv h)⟩ :: tail) := by
  rintro ⟨σ,sol⟩
  have h' := (shared_forced (sig := sig) () p q _ (inv (mul r h)) _ (inv h) (atomicInv _) (atomicInv _) (clash u h r) tail σ).mp sol
  have bad := h' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact extra _ _ (unwrap bad).symm

-- A certificate with a multiplicity error cannot justify replacing one
-- of two identical factors by a single occurrence.
example : ¬Certificate (⟨[0],[1]⟩ : Row Nat) ⟨[0,0],[1,2]⟩ ⟨[0],[2,2]⟩ := by unfold Certificate; decide

example (f : sig.ACSym) (x : T) (σ : Substitution sig) : ¬Holds ⟨[x],[]⟩ f id σ :=
  empty_side f id σ x []

end Tamarin.ACRowEliminationTests
