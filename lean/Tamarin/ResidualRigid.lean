import TamarinRuntime.ResidualRigid
import Tamarin.ResidualSearch

namespace Tamarin.ResidualRigid
open Residual
variable {sig : Signature}

/-- The children of an AC application may already be flattened into a single array. -/
inductive View (s : Signature) where
  | atom (a : s.Atom)
  | free (f : s.FreeSym) (xs : Fin (s.arity f) → Term s)
  | comm (f : s.CSym) (x y : Term s)
  | ac (f : s.ACSym) (x y : Term s) (tail : List (Term s))

def View.term : View sig → Term sig
  | .atom a => .atom a
  | .free f xs => .free f xs
  | .comm f x y => .comm f x y
  | .ac f x y xs => .ac f x (ACRepresentation.fold f y xs)

def View.head : View sig → Head sig
  | .atom a => .atom a
  | .free f _ => .free f
  | .comm f .. => .comm f
  | .ac f .. => .ac f

def View.args : View sig → List (Term sig)
  | .atom _ => []
  | .free _ xs => List.ofFn xs
  | .comm _ x y => [x,y]
  | .ac _ x y xs => x :: y :: xs

abbrev View.kind (v : View sig) := Residual.kind v.term

def View.words (v : View sig) (put : Term sig → UInt64) := (v.args.map put).toArray

private theorem shape_words (v : View sig) (put : Term sig → UInt64) :
    shape v.kind (v.words put).size = true := by
  cases v <;> simp [View.kind, View.term, kind, View.words, View.args, shape]

private theorem same_args {v w : View sig} (put : Term sig → UInt64) (get : UInt64 → Option (Term sig))
    (live : ∀ t ∈ v.args ++ w.args, get (put t) = some t) :
    v.words put = w.words put ↔ v.args = w.args := by
  constructor
  · intro eq
    have recover (xs : List (Term sig)) (h : ∀ t ∈ xs, get (put t) = some t) :
        (xs.map put).filterMap get = xs := by
      induction xs with
      | nil => rfl
      | cons t ts ih => simp [h t (by simp), ih (fun u hu => h u (by simp [hu]))]
    have both := congrArg (fun a : Array UInt64 => a.toList.filterMap get) eq
    simpa only [View.words, List.toList_toArray, recover v.args (fun _ ht => live _ (List.mem_append_left _ ht)),
      recover w.args (fun _ ht => live _ (List.mem_append_right _ ht))] using both
  · intro eq; simp [View.words, eq]

private theorem same_term (a b : View sig) (hh : a.head = b.head) (hc : a.args = b.args) :
    a.term = b.term := by
  cases a <;> cases b <;> simp_all [View.head,View.args,View.term]
  subst_vars
  apply heq_of_eq
  funext i
  have eq := congrArg (fun ts : List (Term sig) => ts[i.val]?) hc
  simpa [List.getElem?_eq_getElem, i.isLt] using eq

private theorem same_kind (a b : View sig) (hh : a.head = b.head) : a.kind = b.kind := by
  cases a <;> cases b <;> simp_all [View.head, View.kind, View.term, kind]

private theorem arity (a b : View sig) (hh : a.head = b.head) (free : a.kind = 2) :
    a.args.length = b.args.length := by
  cases a <;> cases b <;> simp_all [View.head, View.kind, View.term, View.args, kind]

private theorem clash (a b : View sig) (hh : a.head ≠ b.head) : Justified 1 a.term b.term := by
  apply Justified.clash
  intro σ eq
  apply hh
  have stable (v : View sig) :
      (headModel sig).eval Head.var (σ.apply v.term) = v.head := by cases v <;> rfl
  exact (stable a).symm.trans (eq.head_eq.trans (stable b))

private theorem decompose (a b : View sig) (hh : a.head = b.head) (different : a.args ≠ b.args) :
    Justified (if a.kind == 2 then 5 else if a.kind == 3 then 6 else 0) a.term b.term := by
  cases a <;> cases b <;> simp_all [View.head,View.term,View.kind,View.args,kind]
  all_goals subst_vars
  all_goals constructor

/-- Local round trips suffice for all immediate children. The numerals of
unrelated kinds may coincide. Equal heads and child vectors must discharge
directly, preserving the identity fast path across distinct allocations. -/
def Correct (solve : Kernel) : Prop :=
  ∀ {s : Signature} (a b : View s) (head : Head s → UInt64)
    (_faithful : a.kind = b.kind → head a.head = head b.head → a.head = b.head)
    (put : Term s → UInt64) (get : UInt64 → Option (Term s)),
    (∀ t ∈ a.args ++ b.args, get (put t) = some t) →
    let action := solve a.kind (head a.head) (a.words put) b.kind (head b.head) (b.words put)
    Justified action a.term b.term ∧ (a.head = b.head → a.args = b.args → action = 2)

theorem run_correct : Correct run := by
  intro s a b head faithful put get live
  simp only [run, shape_words, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hh : a.head = b.head
  · have kindEq := same_kind a b hh
    have sizes : a.kind = 2 → (a.words put).size = (b.words put).size := by
      intro hf
      simpa [View.words] using arity a b hh hf
    have sizeGuard : (a.kind == 2 && (a.words put).size != (b.words put).size) = false := by
      by_cases hf : a.kind = 2 <;> simp_all
    simp only [← hh, ← kindEq, bne_self_eq_false, Bool.false_or, sizeGuard, Bool.false_eq_true, ↓reduceIte]
    by_cases children : a.args = b.args
    · have eq := (same_args put get live).mpr children
      simp only [eq, BEq.rfl, ↓reduceIte]
      exact ⟨.discard ((same_term a b hh children) ▸ EquivB.refl _), fun _ _ => trivial⟩
    · have ne : a.words put ≠ b.words put := fun eq => children ((same_args put get live).mp eq)
      simpa [ne, children] using decompose a b hh children
  · have diff : (a.kind != b.kind || head a.head != head b.head) = true := by
      by_cases k : a.kind = b.kind
      · have h : head a.head ≠ head b.head := fun e => hh (faithful k e)
        simp [h]
      · simp [k]
    simp [diff, clash a b hh, hh]

/-- Free symbols have signature-defined arity. Equal free symbols in this pair
must agree on it. The other three head kinds have fixed or lower-bounded arity. -/
def Admits (k : UInt8) (n : Nat) : Prop :=
  (k = 1 ∧ n = 0) ∨ k = 2 ∨ (k = 3 ∧ n = 2) ∨ (k = 4 ∧ 2 ≤ n)

private theorem shape_iff (k : UInt8) (n : Nat) : shape k n = true ↔ Admits k n := by
  unfold shape
  split <;> simp_all [Admits]

def RejectsMalformed (solve : Kernel) : Prop :=
  ∀ lk lh ls rk rh rs, (¬Admits lk ls.size ∨ ¬Admits rk rs.size ∨
    (lk = 2 ∧ rk = 2 ∧ lh = rh ∧ ls.size ≠ rs.size)) → solve lk lh ls rk rh rs = 255

theorem run_rejectsMalformed : RejectsMalformed run := by
  intro lk lh ls rk rh rs bad
  rcases bad with bad | bad | ⟨rfl,rfl,rfl,ne⟩
  · have := Bool.eq_false_iff.mpr (fun eq => bad ((shape_iff ..).mp eq))
    simp [run, this]
  · have := Bool.eq_false_iff.mpr (fun eq => bad ((shape_iff ..).mp eq))
    simp [run, this]
  · simp [run, shape, ne]

end Tamarin.ResidualRigid
