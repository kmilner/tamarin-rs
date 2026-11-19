import Tamarin.DHPeer
import Tamarin.DHProduct
import Tamarin.SortClash

namespace Tamarin.Rewriting.DHPeer
variable {sig : Signature}

def Symbols.power (s : Symbols sig) (u v : Term sig) : Term sig :=
  .free s.pow (fun i => if i.val = 0 then u else v)

def Symbols.product (s : Symbols sig) : DHProduct.Ops sig :=
  ⟨s.mul, fun a => .free s.inv (fun _ => a), .free s.one (fun i => Fin.elim0 (s.oneArity ▸ i))⟩

/-- A single positive exponent factor. Its internal syntax and its result
sort are unrestricted by this condition. -/
structure Factor (s : Symbols sig) (t : Term sig) : Prop where
  nonMul : ConstructorVariants.head t ≠ .ac s.mul
  nonInv : ConstructorVariants.head t ≠ .free s.inv
  nonUnit : ConstructorVariants.head t ≠ .free s.one

theorem Factor.of_sort (s : Symbols sig) {r : Term sig} {sort : SortId} (h : HasSort r sort)
    (narrow : ¬Subsort .msg sort) : Factor s r := by
  have sort := Term.rootSort_le h
  have wrong (eq : r.rootSort = .msg) : False := narrow (eq ▸ sort)
  constructor
  · intro hd; cases r <;> cases hd; exact wrong s.mulSort
  · intro hd; cases r <;> cases hd; exact wrong s.invSort
  · intro hd; cases r <;> cases hd; exact wrong s.oneSort

theorem Factor.of_fresh (s : Symbols sig) {r : Term sig} (h : HasSort r .fresh) : Factor s r :=
  .of_sort s h (fun h => by cases h)

/-- Substitution can change every parameter beneath a fixed outer symbol.
It cannot turn a positive factor at that head into a DH group operation. -/
theorem Factor.subst {s : Symbols sig} {r : Term sig} (h : Factor s r)
    (fixed : ∀ v, r ≠ .var v) (σ : Substitution sig) : Factor s (σ.apply r) := by
  have same : ConstructorVariants.head (σ.apply r) = ConstructorVariants.head r := by
    cases r with
    | var v => exact False.elim (fixed v rfl)
    | _ => rfl
  exact ⟨fun eq => h.nonMul (same.symm.trans eq),fun eq => h.nonInv (same.symm.trans eq),
    fun eq => h.nonUnit (same.symm.trans eq)⟩

theorem Factor.single {s : Symbols sig} {r : Term sig} (h : Factor s r) :
    Cancellation.flatten s.mul r = [Cancellation.classOf r] := by
  cases r with
  | ac f a b =>
    classical
    have ne : s.mul ≠ f := fun eq => h.nonMul (eq ▸ rfl)
    simp [Cancellation.flatten,ne]
  | _ => rfl

private theorem power_congr (s : Symbols sig) {u v a b : Term sig} (hu : EquivB u v) (ha : EquivB a b) :
    EquivB (s.power u a) (s.power v b) := by
  apply EquivB.free; intro i; split <;> assumption

private theorem freeTyped {f : sig.FreeSym} {xs : Fin (sig.arity f) → Term sig} {sort : SortId}
    (typed : HasSort (.free f xs) sort) (i : Fin (sig.arity f)) : HasSort (xs i) (sig.inputSort f i) := by
  have h := Term.checkSort_complete typed
  simp only [Term.checkSort, Bool.and_eq_true,List.all_eq_true] at h
  exact Term.checkSort_sound _ _ (h.2 i (List.mem_finRange i))

theorem invChild (s : Symbols sig) {R : Root sig} {t n : Term sig}
    (equal : EquivB t (s.product.inv n)) (typed : HasSort t .msg) (normal : Normal R t) :
    HasSort n .msg ∧ Normal R n := by
  let i : Fin (sig.arity s.inv) := ⟨0, by rw [s.invArity]; decide⟩
  exact ⟨s.invInput i ▸ freeTyped (f := s.inv) (xs := fun _ => n) (Term.checkSort_sound _ _ ((SortClash.check_equiv equal .msg) ▸ Term.checkSort_complete typed)) i,
    normal_free_child s.inv _ ((normal_equiv R equal).mp normal) i⟩

def parameters (Y r b p n : Term sig) : Slot → Term sig
  | .peer => Y | .fresh => r | .base => b | .pos => p | .neg => n

/-- An unchanged power can only represent an actual non-neutral, non-power
base. The generic tower arm appends a factor only when its inverse is absent. -/
def Branch.Guard [DecidableEq sig.ACSym] (s : Symbols sig) (env : Slot → Term sig) : Branch → Prop
  | .unchanged => (∀ u v, env .peer ≠ s.power u v) ∧ env .peer ≠ Expr.neutral.eval s env
  | .tower => ¬ DHProduct.Opposite s.product (env .pos) (env .fresh)
  | _ => True

structure Realizes [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig)
    (Y r : Term sig) (arm : Branch) (env : Slot → Term sig) : Prop where
  peer : env .peer = Y
  fresh : env .fresh = r
  typed : ∀ i, HasSort (env i) .msg
  normal : ∀ i, Normal R (env i)
  guard : arm.Guard s env
  base : EquivB Y (arm.pair.1.eval s env)

private theorem params {Y r b p n : Term sig} (P : Term sig → Prop)
    (hy : P Y) (hr : P r) (hb : P b) (hp : P p) (hn : P n) : ∀ i, P (parameters Y r b p n i) := by
  intro i; cases i <;> assumption

/-- For an arbitrary normalized received base and normalized message exponent,
the seven guarded input schemas exhaust all shapes. Each recovered witness
is a real well-sorted normal term; a nonempty remainder may itself be a
product. This statement characterizes shapes before claiming that a computed
output is a normal form. -/
theorem classifyMsg [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig)
    (Y r : Term sig) (hy : HasSort Y .msg) (hr' : HasSort r .msg) (ny : Normal R Y) (nr : Normal R r) :
    ∃ arm env, Realizes s R Y r arm env := by
  classical
  by_cases power : ∃ base e, Y = s.power base e
  · obtain ⟨base,e,rfl⟩ := power
    let left : Fin (sig.arity s.pow) := ⟨0,by rw [s.powArity]; decide⟩
    let right : Fin (sig.arity s.pow) := ⟨1,by rw [s.powArity]; decide⟩
    let ys : Fin (sig.arity s.pow) → Term sig := fun i => if i.val = 0 then base else e
    have hb : HasSort base .msg := by simpa [ys,left,s.powInput] using freeTyped (xs := ys) hy left
    have he : HasSort e .msg := by simpa [ys,right,s.powInput] using freeTyped (xs := ys) hy right
    have nb : Normal R base := normal_free_child s.pow ys ny left
    have ne : Normal R e := normal_free_child s.pow ys ny right
    obtain ⟨out,shape⟩ := DHProduct.classify s.product R s.mulSort (fun h => .free s.inv _ _ (fun _ => h))
      (fun eq => invChild s eq) e r he ne
    cases shape with
    | extend clear =>
      exact ⟨.tower,parameters _ r base e r, rfl,rfl, params (fun x => HasSort x .msg) hy hr' hb he hr', params (Normal R) ny nr nb ne nr, clear,.refl _⟩
    | cancel eq =>
      exact ⟨.cancelAll,parameters _ r base r r,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hb hr' hr',params (Normal R) ny nr nb nr nr,
        trivial,power_congr s (.refl _) eq⟩
    | cancelWith _ hu nu eq =>
      exact ⟨.cancelPositive,parameters _ r base out r,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hb hu hr',params (Normal R) ny nr nb nu nr,
        trivial,power_congr s (.refl _) eq⟩
    | cancelInside v hv nv eq =>
      exact ⟨.cancelNegative,parameters _ r base r v,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hb hr' hv,params (Normal R) ny nr nb nr nv,
        trivial,power_congr s (.refl _) eq⟩
    | cancelBoth u v hu hv nu nv eq =>
      exact ⟨.cancelMixed,parameters _ r base u v,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hb hu hv,params (Normal R) ny nr nb nu nv,
        trivial,power_congr s (.refl _) eq⟩
  · let env := parameters Y r Y Y Y
    by_cases neutral : Y = Expr.neutral.eval s env
    · exact ⟨.neutral,env,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hy hy hy,params (Normal R) ny nr ny ny ny,trivial,by rw [neutral]; exact .refl _⟩
    · exact ⟨.unchanged,env,rfl,rfl,params (fun x => HasSort x .msg) hy hr' hy hy hy,params (Normal R) ny nr ny ny ny,
        ⟨fun a b h => power ⟨a,b,h⟩,neutral⟩,.refl _⟩

theorem classify [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig)
    (Y r : Term sig) (hy : HasSort Y .msg) (hr : HasSort r .fresh) (ny : Normal R Y) (nr : Normal R r) :
    ∃ arm env, Realizes s R Y r arm env :=
  classifyMsg s R Y r hy (.widen hr .fresh_msg) ny nr

/-- The output paired with that same set of witnesses is actually reachable
from the caller's original power under the given rewrite table. -/
theorem Realizes.reduces [DecidableEq sig.ACSym] {s : Symbols sig} (T : Table s)
    {Y r : Term sig} {k : Branch} {env} (h : Realizes s (ruleRoot T.rules) Y r k env) :
    Reduces (ruleRoot T.rules) (s.power Y r) (k.pair.2.eval s env) := by
  refine Reduces.trans (.basis (power_congr s h.base (h.fresh ▸ .refl _))) (T.reaches env h.typed k)

end Tamarin.Rewriting.DHPeer
