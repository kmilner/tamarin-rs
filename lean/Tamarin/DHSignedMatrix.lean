import Tamarin.DHExponentCallerOps
import Tamarin.ACBasis
import Tamarin.StableVariants

/-! A simultaneous system of products, inverses and units on unrestricted
message inputs. For each opaque factor class, choose its sign in every input.
The resulting ordinary nonnegative homogeneous matrix describes exactly the
signed multiplicity equations, with any number of correlated observations. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis Cancellation Balance
variable {n : Nat} {sig : Signature}

inductive Expr (n : Nat) where
  | input (i : Fin n)
  | unit
  | mul (a b : Expr n)
  | inv (a : Expr n)

def Expr.term (s : Symbols sig) (env : Fin n → Term sig) : Expr n → Term sig
  | .input i => env i
  | .unit => s.product.one
  | .mul a b => s.product.mul (a.term s env) (b.term s env)
  | .inv a => s.product.inv (a.term s env)

def Expr.eval (counts : Fin n → Int) : Expr n → Int
  | .input i => counts i
  | .unit => 0
  | .mul a b => a.eval counts + b.eval counts
  | .inv a => -a.eval counts

theorem Expr.read (s : Symbols sig) (R : Root sig) (k : Class sig) (env : Fin n → Term sig)
    (c : Fin n → Int) (inputs : ∀ i, Balance.read s R k (env i) = some (c i)) (e : Expr n) :
    Balance.read s R k (e.term s env) = some (e.eval c) := by
  induction e with
  | input i => exact inputs i
  | unit => exact read_one ..
  | mul a b ha hb => simp [term,eval,ha,hb,plus]
  | inv a ha => simp [term,eval,ha,minus]

theorem Expr.sorted (s : Symbols sig) (env : Fin n → Term sig) (typed : ∀ i, HasSort (env i) .msg)
    (e : Expr n) : HasSort (e.term s env) .msg := by
  induction e with
  | input i => exact typed i
  | unit => rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
  | inv a h => rw [← s.invSort]; apply HasSort.free; intro i; simpa [s.invInput] using h
  | mul a b l r => exact s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ l) (s.mulSort ▸ r)

theorem Expr.subst_term (s : Symbols sig) (env : Fin n → Term sig) (ρ : Substitution sig) (e : Expr n) :
    ρ.apply (e.term s env) = e.term s (fun i => ρ.apply (env i)) := by
  induction e with
  | input i => rfl
  | unit => apply congrArg (Term.free s.one); funext i; exact Fin.elim0 (s.oneArity ▸ i)
  | inv a h => exact congrArg (fun t => s.product.inv t) h
  | mul a b l r => exact (congrArg (fun t => s.product.mul t _) l).trans (congrArg (s.product.mul _) r)

theorem Expr.defined (s : Symbols sig) (R : Root sig) (env : Fin n → Term sig) (e : Expr n)
    (stable : ∀ i, StableVariants.Stable R (env i)) (ρ : Substitution sig) (hn : Normalized R ρ) :
    ∀ k, ∃ z, Balance.read s R k (ρ.apply (e.term s env)) = some z := by
  intro k
  let c := fun i => (Balance.defined s R k (stable i ρ hn)).choose
  rw [e.subst_term]
  exact ⟨_,e.read s _ k _ c (fun i => (Balance.defined s R k (stable i ρ hn)).choose_spec)⟩

/-- Functional reconstruction for the narrowing driver. The same expression
may use a message input at many positions and with both signs. A stable
opaque leaf need not have a persistent head after specializing it. -/
theorem Expr.pointwise_unique [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Inventory E) (env : Fin n → Term sig) (e : Expr n) (sorted : ∀ i, HasSort (env i) .msg)
    (stable : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) {u v}
    (left : NormalForm (ruleRoot T.rules) (ρ.apply (e.term s env)) u)
    (right : NormalForm (ruleRoot T.rules) (ρ.apply (e.term s env)) v) : EquivB u v := by
  have typed := (e.sorted s env sorted).subst ρ.image ρ.sorted
  apply normal_unique inventory E.presentation (fun _ => plain_of_inverse E) _ (left.2.2 .msg typed)
    (right.2.2 .msg typed) left.2.1 right.2.1 left.1 right.1
  exact e.defined s _ env stable ρ hn

/-- The base may itself specialize to any normal message, including an older
power or the DH neutral element. Exponents share the same caller valuation.
The whole spine has a unique normal result regardless of reduction order. -/
theorem spine_pointwise_unique [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Inventory E) (powers : PowerBucket T) (unit : Normal (ruleRoot T.rules) s.product.one)
    (env : Fin n → Term sig) (sorted : ∀ i, HasSort (env i) .msg)
    (stable : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (base : Term sig) (baseSort : HasSort base .msg) (baseStable : StableVariants.Stable (ruleRoot T.rules) base)
    (exponents : List (Expr n)) (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) {u v} :
    let source := ρ.apply (exponents.foldl (fun t e => s.power t (e.term s env)) base)
    NormalForm (ruleRoot T.rules) source u → NormalForm (ruleRoot T.rules) source v → EquivB u v := by
  apply DHTower.Spine.unique powers inventory unit
  · apply HasSort.subst _ ρ.image ρ.sorted
    clear baseStable
    induction exponents generalizing base with
    | nil => exact baseSort
    | cons e _ ih => exact ih _ (DHTower.powerSorted baseSort (e.sorted s env sorted))
  · have start := DHTower.Spine.defined_normal s _ (baseStable ρ hn)
    clear baseSort baseStable
    induction exponents generalizing base with
    | nil => exact start
    | cons e _ ih =>
      apply ih
      rw [DHExponent.Caller.apply_pow]
      exact DHTower.Spine.defined_power start (e.defined s _ env stable ρ hn)

def add (a b : Vec n) : Vec n := fun i => a i + b i

def Expr.weights (negative : Fin n → Bool) : Expr n → Vec n × Vec n
  | .input i => if negative i then (fun _ => 0,spike i 1) else (spike i 1,fun _ => 0)
  | .unit => (fun _ => 0,fun _ => 0)
  | .inv a => (a.weights negative).swap
  | .mul a b => (add (a.weights negative).1 (b.weights negative).1,
    add (a.weights negative).2 (b.weights negative).2)

def signed (negative : Fin n → Bool) (x : Vec n) (i : Fin n) : Int :=
  if negative i then -(x i : Int) else (x i : Int)

theorem normal_readings (s : Symbols sig) (R : Root sig) (env : Fin n → Term sig)
    (normal : ∀ i, Normal R (env i)) : ∃ (signs : Class sig → Fin n → Bool) (mag : Class sig → Vec n), ∀ k i,
      Balance.read s R k (env i) = some (signed (signs k) (mag k) i) := by
  let c := fun k i => (Balance.defined s R k (normal i)).choose
  refine ⟨fun k i => decide (c k i < 0),fun k i => (c k i).natAbs,?_⟩
  intro k i
  rw [(Balance.defined s R k (normal i)).choose_spec]
  change some (c k i) = some (if decide (c k i < 0) then -((c k i).natAbs : Int) else ((c k i).natAbs : Int))
  cases c k i <;> simp <;> omega

/-- A finite tuple of normal messages has only finitely many nonzero
factor classes, even if a single input is an arbitrarily large product. -/
theorem finite_normal_readings [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} (E : ExtraTable T)
    (env : Fin n → Term sig) (typed : ∀ i, HasSort (env i) .msg)
    (normal : ∀ i, Normal (ruleRoot T.rules) (env i)) :
    ∃ (active : List (Class sig)) (signs : Class sig → Fin n → Bool) (mag : Class sig → Vec n),
      (∀ k i, Balance.read s (ruleRoot T.rules) k (env i) = some (signed (signs k) (mag k) i)) ∧
      ∀ k ∉ active, ∀ i, mag k i = 0 := by
  classical
  obtain ⟨signs,mag,reads⟩ := normal_readings s _ env normal
  have decomposed (i) := decompose E.presentation (fun _ => plain_of_inverse E) (typed i) (normal i)
  let pos := fun i => (decomposed i).choose
  let neg := fun i => (decomposed i).choose_spec.choose
  have canonical (i) : Canonical s _ (env i) (pos i) (neg i) := (decomposed i).choose_spec.choose_spec
  let support := fun i => bag s (pos i) ++ bag s (neg i)
  refine ⟨(List.finRange n).flatMap support,signs,mag,reads,?_⟩
  intro k absent i
  have missing : k ∉ support i := fun h => absent (List.mem_flatMap.mpr ⟨i,List.mem_finRange _,h⟩)
  have p := List.count_eq_zero.mpr (fun h => missing (List.mem_append_left _ h))
  have q := List.count_eq_zero.mpr (fun h => missing (List.mem_append_right _ h))
  have both := Option.some.inj ((reads k i).symm.trans ((canonical i).read_count k))
  rw [p,q] at both
  cases h : signs k i <;> simpa [signed,h] using both

private theorem dot_zero (x : Vec n) : dot (fun _ => 0) x = 0 := by
  simp [dot,total,List.sum_eq_zero_iff_forall_eq_nat]

private theorem dot_add_left (a b x : Vec n) :
    dot (add a b) x = dot a x + dot b x := by
  simp only [dot,add,Nat.add_mul,ACBasis.total_add]

theorem Expr.eval_weights (signs : Fin n → Bool) (x : Vec n) (e : Expr n) :
    e.eval (signed signs x) = (dot (e.weights signs).1 x : Int) - (dot (e.weights signs).2 x : Int) := by
  have single (i : Fin n) : dot (spike i 1) x = x i := by
    rw [show dot (spike i 1) x = dot x (spike i 1) by simp [dot,Nat.mul_comm], ACBasis.dot_spike,Nat.mul_one]
  induction e with
  | input i => cases h : signs i <;> simp [eval,signed,weights,h,single,dot_zero]
  | unit => simp [eval,weights,dot_zero]
  | inv a ha => simp only [eval,weights,Prod.swap,ha]; omega
  | mul a b ha hb =>
    simp only [eval,weights,dot_add_left,Int.natCast_add,ha,hb]
    omega

abbrev Constraint (n : Nat) := Expr n × Expr n

def row (signs : Fin n → Bool) (eq : Constraint n) : ACBasis.Row n :=
  let l := eq.1.weights signs
  let r := eq.2.weights signs
  .ofWeights (add l.1 r.2) (add r.1 l.2)

theorem row_iff (signs : Fin n → Bool) (eq : Constraint n) (x : Vec n) :
    (row signs eq).Holds x ↔ eq.1.eval (signed signs x) = eq.2.eval (signed signs x) := by
  rw [row,Row.ofWeights_holds,dot_add_left,dot_add_left,Expr.eval_weights,Expr.eval_weights]
  omega

/-- Any basis satisfying the ordinary AC contract suffices. A factor that has
positive multiplicity in one input can have negative multiplicity in another.
Distinct opaque factors can occupy entirely different sign regions. -/
theorem spans_iff (system : List (Constraint n)) (signs : Fin n → Bool) (x : Vec n)
    (basis : List (Vec n)) (valid : BasisCorrect (system.map (row signs)) basis) :
    Generates basis x ↔ ∀ eq ∈ system, eq.1.eval (signed signs x) = eq.2.eval (signed signs x) := by
  rw [← valid]
  constructor
  · intro h eq he; exact (row_iff signs eq x).mp (h _ (List.mem_map_of_mem he))
  · rintro h _ hr
    obtain ⟨eq,he,rfl⟩ := List.mem_map.mp hr
    exact (row_iff signs eq x).mpr (h eq he)

/-- Connect membership in the matrix span back to terms, including every
normal endpoint of a reduction under the live DH table. Both sides of each
constraint may be arbitrary signed expressions. -/
theorem normalForms_iff [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (inventory : Inventory E) (env : Fin n → Term sig) (system : List (Constraint n))
    (signs : Class sig → Fin n → Bool) (mag : Class sig → Vec n)
    (reads : ∀ k i, Balance.read s (ruleRoot T.rules) k (env i) = some (signed (signs k) (mag k) i))
    (basis : (Fin n → Bool) → List (Vec n))
    (valid : ∀ sign, BasisCorrect (system.map (row sign)) (basis sign))
    (value : Expr n → Term sig)
    (typed : ∀ i, HasSort (env i) .msg)
    (normal : ∀ eq ∈ system, ∀ e, e = eq.1 ∨ e = eq.2 →
      NormalForm (ruleRoot T.rules) (e.term s env) (value e)) :
    (∀ eq ∈ system, EquivB (value eq.1) (value eq.2)) ↔ ∀ k, Generates (basis (signs k)) (mag k) := by
  have counts (k) (eq) (he : eq ∈ system) (e) (side : e = eq.1 ∨ e = eq.2) :=
    inventory.reduces k (normal eq he e side).1 _ (e.read s _ k env _ (reads k))
  constructor
  · intro eqs k
    apply (spans_iff system _ _ _ (valid (signs k))).mpr
    intro eq he
    exact Option.some.inj ((counts k eq he _ (.inl rfl)).symm.trans
      ((Balance.equiv s _ k (eqs eq he)).trans (counts k eq he _ (.inr rfl))))
  · intro generated eq he
    have canon (e : Expr n) (side : e = eq.1 ∨ e = eq.2) := decompose E.presentation
      (fun _ => plain_of_inverse E) ((normal eq he e side).2.2 .msg (e.sorted s env typed)) (normal eq he e side).2.1
    obtain ⟨_,_,l⟩ := canon eq.1 (.inl rfl)
    obtain ⟨_,_,r⟩ := canon eq.2 (.inr rfl)
    apply l.injective r
    intro k
    rw [counts k eq he _ (.inl rfl),counts k eq he _ (.inr rfl),
      (spans_iff system _ _ _ (valid (signs k))).mp (generated k) eq he]

end Tamarin.Rewriting.DHPeer.SignedMatrix
