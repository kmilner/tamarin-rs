import Tamarin.Rewriting
import Tamarin.VariableElimination

/-! The seven peer-base recipes observed in the ordinary DH theory. Each
recipe names both the base substitution and the power value. The reductions
below use membership of the actual DH equations in the live rule table. -/
namespace Tamarin.Rewriting.DHPeer

variable {sig : Signature} {α : Type}

/-- The two free arguments and the AC factors have the Msg sort. The index
order of a free application is part of the syntax of the signed protocol. -/
structure Symbols (sig : Signature) where
  pow : sig.FreeSym
  inv : sig.FreeSym
  one : sig.FreeSym
  neutral : sig.FreeSym
  mul : sig.ACSym
  powArity : sig.arity pow = 2
  invArity : sig.arity inv = 1
  oneArity : sig.arity one = 0
  neutralArity : sig.arity neutral = 0
  powInput : ∀ i, sig.inputSort pow i = .msg
  invInput : ∀ i, sig.inputSort inv i = .msg
  powSort : sig.outputSort pow = .msg
  invSort : sig.outputSort inv = .msg
  oneSort : sig.outputSort one = .msg
  neutralSort : sig.outputSort neutral = .msg
  mulSort : sig.acSort mul = .msg

/-- Variables are slots shared between both sides of a rule. The same syntax
also represents templates over the caller's base and fresh exponent. -/
inductive Expr (α : Type) where
  | var (i : α)
  | pow (a b : Expr α)
  | mul (a b : Expr α)
  | inv (a : Expr α)
  | one
  | neutral
  deriving DecidableEq

def Expr.eval (s : Symbols sig) (env : α → Term sig) : Expr α → Term sig
  | .var i => env i
  | .pow a b => .free s.pow (fun i => if i.val = 0 then a.eval s env else b.eval s env)
  | .mul a b => .ac s.mul (a.eval s env) (b.eval s env)
  | .inv a => .free s.inv (fun _ => a.eval s env)
  | .one => .free s.one (fun i => Fin.elim0 (s.oneArity ▸ i))
  | .neutral => .free s.neutral (fun i => Fin.elim0 (s.neutralArity ▸ i))

theorem Expr.sorted (s : Symbols sig) (env : α → Term sig)
    (h : ∀ i, HasSort (env i) .msg) (e : Expr α) : HasSort (e.eval s env) .msg := by
  induction e with
  | var i => exact h i
  | pow a b ha hb =>
    rw [← s.powSort]; apply HasSort.free; intro i; rw [s.powInput]; split <;> assumption
  | mul a b ha hb => rw [← s.mulSort]; exact .ac _ _ _ (s.mulSort ▸ ha) (s.mulSort ▸ hb)
  | inv a ha => rw [← s.invSort]; apply HasSort.free; intro i; simpa [s.invInput] using ha
  | one => rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
  | neutral => rw [← s.neutralSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.neutralArity ▸ i)

theorem Expr.subst_eval (s : Symbols sig) (env : α → Term sig) (σ : Substitution sig)
    (e : Expr α) : σ.apply (e.eval s env) = e.eval s (fun i => σ.apply (env i)) := by
  induction e with
  | var => rfl
  | mul _ _ ia ib => exact (congrArg (fun a => Term.ac s.mul a _) ia).trans (congrArg (Term.ac s.mul _) ib)
  | inv _ ih => exact congrArg (fun a => Term.free s.inv (fun _ => a)) ih
  | pow _ _ ia ib =>
    apply congrArg (Term.free s.pow); funext i
    change σ.apply (if _ then _ else _) = (if _ then _ else _)
    split <;> assumption
  | one => apply congrArg (Term.free s.one); funext i; exact Fin.elim0 (s.oneArity ▸ i)
  | neutral => apply congrArg (Term.free s.neutral); funext i; exact Fin.elim0 (s.neutralArity ▸ i)

/-- These are seven of the thirteen DH rewrite equations. Other rules can
still act on the result; reachability alone cannot justify completion. -/
inductive Rule where
  | expOne | tower | neutral | inverse | inverseRest | inside | insideRest
  deriving DecidableEq

private abbrev x : Expr (Fin 3) := .var 0
private abbrev y : Expr (Fin 3) := .var 1
private abbrev z : Expr (Fin 3) := .var 2

def Rule.equation : Rule → Expr (Fin 3) × Expr (Fin 3)
  | .expOne => (.pow x .one, x)
  | .tower => (.pow (.pow x y) z, .pow x (.mul y z))
  | .neutral => (.pow .neutral x, .neutral)
  | .inverse => (.mul x (.inv x), .one)
  | .inverseRest => (.mul x (.mul (.inv x) y), y)
  | .inside => (.mul (.inv (.mul x y)) y, .inv x)
  | .insideRest => (.mul (.inv (.mul x y)) (.mul y z), .mul (.inv x) z)

def Rule.instantiate (r : Rule) (s : Symbols sig) (env : Fin 3 → Term sig) : Equation sig :=
  ⟨r.equation.1.eval s env, r.equation.2.eval s env⟩

/-- Rule-local variable IDs are independent of the caller. Their choice may
vary by rule; their order corresponds to the x/y/z slots of the schema. -/
structure Table (s : Symbols sig) where
  rules : List (Equation sig)
  actual : Rule → Fin 3 → Variable
  actualSort : ∀ r i, (actual r i).sort = .msg
  distinct : ∀ r i j, actual r i = actual r j → i = j
  present : ∀ r : Rule, r.instantiate s (fun i => .var (actual r i)) ∈ rules

private def assign (keys : Fin 3 → Variable) (values : Fin 3 → Term sig)
    (typed : ∀ i, HasSort (values i) (keys i).sort) : Substitution sig where
  image v := if v = keys 0 then values 0 else if v = keys 1 then values 1 else if v = keys 2 then values 2 else .var v
  support := [keys 0, keys 1, keys 2]
  outside := by intro v h; simp_all
  sorted := by intro v; split <;> rename_i h
               · exact h ▸ typed 0
               · split <;> rename_i h
                 · exact h ▸ typed 1
                 · split <;> rename_i h
                   · exact h ▸ typed 2
                   · exact .var _

private theorem assign_get (keys : Fin 3 → Variable) (values : Fin 3 → Term sig)
    (typed : ∀ i, HasSort (values i) (keys i).sort)
    (inj : ∀ i j, keys i = keys j → i = j) (i : Fin 3) :
    (assign keys values typed).image (keys i) = values i := by
  have eq (j : Fin 3) : keys i = keys j ↔ i = j := ⟨inj i j, fun h => congrArg keys h⟩
  simp only [assign, eq]
  split <;> rename_i h
  · rw [h]
  · split <;> rename_i h
    · rw [h]
    · split <;> rename_i h
      · rw [h]
      · exfalso; omega

/-- Replay a pair of schemata with shared rule-local variables. Only membership
and a well-sorted renaming in the active table matter. -/
theorem fireSchema {s : Symbols sig} {rules : List (Equation sig)} (lhs rhs : Expr (Fin 3))
    (keys : Fin 3 → Variable) (sorts : ∀ i, (keys i).sort = .msg)
    (distinct : ∀ i j, keys i = keys j → i = j)
    (present : ⟨lhs.eval s (fun i => .var (keys i)), rhs.eval s (fun i => .var (keys i))⟩ ∈ rules)
    (values : Fin 3 → Term sig) (typed : ∀ i, HasSort (values i) .msg) :
    ruleRoot rules (lhs.eval s values) (rhs.eval s values) := by
  let σ := assign keys values (fun i => sorts i ▸ typed i)
  have atSlot : (fun i => σ.apply (.var (keys i))) = values := by
    funext i; exact assign_get _ _ _ distinct i
  exact ⟨_,present,σ,by simp [Expr.subst_eval,atSlot],by simp [Expr.subst_eval,atSlot]⟩

theorem Table.fireRoot {s : Symbols sig} (T : Table s) (r : Rule)
    (values : Fin 3 → Term sig) (typed : ∀ i, HasSort (values i) .msg) :
    ruleRoot T.rules (r.instantiate s values).lhs (r.instantiate s values).rhs :=
  fireSchema _ _ _ (T.actualSort r) (T.distinct r) (T.present r) values typed

theorem Table.fire {s : Symbols sig} (T : Table s) (r : Rule)
    (values : Fin 3 → Term sig) (typed : ∀ i, HasSort (values i) .msg) :
    Reduces (ruleRoot T.rules) (r.instantiate s values).lhs (r.instantiate s values).rhs :=
  .step ⟨_, _, .refl _, .root (T.fireRoot r values typed), .refl _⟩

/-- Witnesses b,p,n have sort Msg. The original r has sort Fresh.
p also names the existing exponent in the uncomplicated tower branch. -/
inductive Slot where | peer | fresh | base | pos | neg deriving DecidableEq, Repr
inductive Branch where
  | unchanged | neutral | tower | cancelPositive | cancelAll | cancelMixed | cancelNegative
  deriving DecidableEq, Repr

abbrev peer : Expr Slot := .var .peer
abbrev r : Expr Slot := .var .fresh
abbrev b : Expr Slot := .var .base
abbrev p : Expr Slot := .var .pos
abbrev n : Expr Slot := .var .neg

/-- An arm's base image and its *already reduced* output, using the same
slots. In particular the fresh slot in an inverse is the original exponent. -/
def Branch.pair : Branch → Expr Slot × Expr Slot
  | .unchanged => (peer, .pow peer r)
  | .neutral => (.neutral, .neutral)
  | .tower => (.pow b p, .pow b (.mul p r))
  | .cancelPositive => (.pow b (.mul p (.inv r)), .pow b p)
  | .cancelAll => (.pow b (.inv r), b)
  | .cancelMixed => (.pow b (.mul p (.inv (.mul n r))), .pow b (.mul p (.inv n)))
  | .cancelNegative => (.pow b (.inv (.mul n r)), .pow b (.inv n))

def arms : List Branch :=
  [.unchanged,.neutral,.tower,.cancelPositive,.cancelAll,.cancelMixed,.cancelNegative]


private def three {α : Type} (a b c : α) (i : Fin 3) : α :=
  if i = 0 then a else if i = 1 then b else c

private theorem powRight {s : Symbols sig} {R : Root sig} (base e e' : Term sig)
    (h : Reduces R e e') :
    Reduces R (.free s.pow (fun i => if i.val = 0 then base else e))
      (.free s.pow (fun i => if i.val = 0 then base else e')) := by
  apply Reduces.free
  intro i
  split <;> first | exact .basis (.refl _) | exact h

private theorem threeSort (s : Symbols sig) (env : Slot → Term sig)
    (typed : ∀ i, HasSort (env i) .msg) (a b c : Expr Slot) (i : Fin 3) :
    HasSort (three (a.eval s env) (b.eval s env) (c.eval s env) i) .msg := by
  unfold three
  split <;> first | exact a.sorted s env typed | split <;> first | exact b.sorted s env typed | exact c.sorted s env typed

/-- Each advertised value follows from the actual exponent, neutral, unit
and inverse rules. This holds for arbitrary sorted instances, even when a
witness is itself a compound term. -/
theorem Table.reaches {s : Symbols sig} (T : Table s)
    (env : Slot → Term sig) (ht : ∀ i, HasSort (env i) .msg) (arm : Branch) :
    Reduces (ruleRoot T.rules) ((Expr.pow arm.pair.1 r).eval s env) (arm.pair.2.eval s env) := by
  let fire (k : Rule) (a b c : Expr Slot) := T.fire k (three (a.eval s env) (b.eval s env) (c.eval s env))
    (threeSort s env ht a b c)
  cases arm with
  | unchanged => exact .basis (.refl _)
  | neutral => exact fire .neutral r r r
  | tower => exact fire .tower b p r
  | cancelAll =>
    refine (fire .tower b (.inv r) r).trans ?_
    refine (powRight (s := s) _ _ _ (.basis (.ac_swap ..))).trans ?_
    exact (powRight (s := s) _ _ _ (fire .inverse r r r)).trans (fire .expOne b b b)
  | cancelNegative =>
    refine (fire .tower b (.inv (.mul n r)) r).trans ?_
    exact powRight (s := s) _ _ _ (fire .inside n r r)
  | cancelPositive =>
    refine (fire .tower b (.mul p (.inv r)) r).trans (powRight (s := s) _ _ _ ?_)
    have perm : EquivB ((Expr.mul (.mul p (.inv r)) r).eval s env)
        ((Expr.mul r (.mul (.inv r) p)).eval s env) :=
      (EquivB.ac_swap ..).trans (.ac_congr _ (.refl _) (.ac_swap ..))
    exact (.basis perm : Reduces (ruleRoot T.rules) _ _).trans (fire .inverseRest r p p)
  | cancelMixed =>
    refine (fire .tower b (.mul p (.inv (.mul n r))) r).trans (powRight (s := s) _ _ _ ?_)
    have perm : EquivB ((Expr.mul (.mul p (.inv (.mul n r))) r).eval s env)
        ((Expr.mul (.inv (.mul n r)) (.mul r p)).eval s env) :=
      (EquivB.ac_congr _ (.ac_swap ..) (.refl _)).trans
        ((EquivB.ac_assoc ..).trans (.ac_congr _ (.refl _) (.ac_swap ..)))
    exact (.basis perm : Reduces (ruleRoot T.rules) _ _).trans
      ((fire .insideRest n r p).trans (.basis (.ac_swap ..)))

end Tamarin.Rewriting.DHPeer
