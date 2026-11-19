import Tamarin.ResidualRigid

namespace Tamarin.ResidualRigid
open Residual
variable {sig : Signature}

/-- Meaning of the four rigid transitions and a clash on the whole pending
conjunction. AC cancellation and C pruning may use independent local IDs. -/
def Transition (code : UInt8) (a b : View sig) (observed : Variable → Prop)
    (pending : Problem sig) (θ ρ : Substitution sig) : Prop :=
  let before := Denotes observed (⟨a.term,b.term⟩ :: pending) θ ρ
  match code with
  | 0 => ∃ f : sig.ACSym, a.head = .ac f ∧ b.head = .ac f ∧
      ∀ cancel, CommonCancellation.Correct cancel → ∀ (decode : UInt64 → Term sig) (ls rs : Array UInt64),
      ls.toList.map decode = a.args → rs.toList.map decode = b.args →
      ∃ left right : List UInt64, cancel ls rs = #[left.toArray,right.toArray] ∧
        (before ↔ ∃ q ∈ withFactors f (left.map decode) (right.map decode) pending, Denotes observed q θ ρ)
  | 1 => ¬ before
  | 2 => before ↔ Denotes observed pending θ ρ
  | 5 => ∃ (f : sig.FreeSym) (xs ys : Fin (sig.arity f) → Term sig),
      a.term = .free f xs ∧ b.term = .free f ys ∧ a.args = List.ofFn xs ∧ b.args = List.ofFn ys ∧
      (before ↔ Denotes observed (Matching.children f xs ys ++ pending) θ ρ)
  | 6 => ∃ q : Commutative.Query sig, q.rest = pending ∧
      a.term = .comm q.f q.a q.b ∧ b.term = .comm q.f q.c q.d ∧ a.args = [q.a,q.b] ∧ b.args = [q.c,q.d] ∧
      ∀ orient, Commutative.Correct orient → ∀ (key : Head sig → UInt64) (priority : UInt8),
      Commutative.Priority q priority →
      let k := Commutative.headCode key
      (before ↔ ∃ cross ∈ Commutative.orientations (orient (k q.a) (k q.b) (k q.c) (k q.d) priority),
        Denotes observed (q.branch cross) θ ρ)
  | _ => False

private theorem ac_args {v : View sig} {f x y} (h : v.term = .ac f x y) :
    ACRepresentation.decode f v.args = some v.term := by
  cases v <;> simp_all [View.term, View.args, ACRepresentation.decode, ACRepresentation.fold]

private theorem ac_head {v : View sig} {f x y} (h : v.term = .ac f x y) : v.head = .ac f := by
  cases v <;> simp_all [View.term,View.head]

private theorem free_args {v : View sig} {f xs} (h : v.term = .free f xs) :
    v.args = List.ofFn xs := by
  cases v <;> simp_all [View.term, View.args]
  obtain ⟨rfl, same⟩ := h
  cases same; rfl

private theorem comm_args {v : View sig} {f x y} (h : v.term = .comm f x y) :
    v.args = [x,y] := by cases v <;> simp_all [View.term,View.args]

theorem worklist {solve : Kernel} (verified : Correct solve) (a b : View sig)
    (head : Head sig → UInt64) (faithful : a.kind = b.kind → head a.head = head b.head → a.head = b.head)
    (put : Term sig → UInt64) (get : UInt64 → Option (Term sig))
    (live : ∀ t ∈ a.args ++ b.args, get (put t) = some t)
    (observed : Variable → Prop) (p : Problem sig) (θ ρ : Substitution sig) :
    Transition (solve a.kind (head a.head) (a.words put) b.kind (head b.head) (b.words put))
      a b observed p θ ρ := by
  have just := (verified a b head faithful put get live).1
  generalize hcode : solve a.kind (head a.head) (a.words put) b.kind (head b.head) (b.words put) = code at just ⊢
  generalize ha : a.term = l at just
  generalize hb : b.term = r at just
  cases just with
  | clash bad => exact Residual.clash observed (ha.symm ▸ hb.symm ▸ bad) p θ ρ
  | discard same => exact Residual.discard observed (ha.symm ▸ hb.symm ▸ same) p θ ρ
  | bindLeft v _ _ _ => cases a <;> contradiction
  | bindRight v _ _ _ => cases b <;> contradiction
  | positional f xs ys =>
    refine ⟨f,xs,ys,ha,hb,free_args ha,free_args hb,?_⟩
    rw [ha,hb]
    exact Residual.positional observed f xs ys p θ ρ
  | orientations f x y z w =>
    let q : Commutative.Query sig := ⟨f,x,y,z,w,p⟩
    refine ⟨q,rfl,ha,hb,comm_args ha,comm_args hb,?_⟩
    intro solver correct key priority hp
    rw [ha,hb]
    exact Residual.orient observed correct q key priority hp θ ρ
  | defer f _ _ _ _ =>
    refine ⟨f,ac_head ha,ac_head hb,?_⟩
    intro cancel hc decode ls rs hl hr
    obtain ⟨left,right,packet,eq⟩ := Residual.cancel observed hc decode f ls rs p θ ρ
    refine ⟨left,right,packet,?_⟩
    rw [← eq,hl,hr]
    simp [withFactors, ac_args ha, ac_args hb]

end Tamarin.ResidualRigid
