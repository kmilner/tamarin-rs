import TamarinCI
import Tamarin.DHPeerComplete

/-! Instantiate AC exclusion against every rule of the DH presentation.
The product theorem permits arbitrary normalized substitutions, including the
diagonal where both query variables denote the same fresh value. -/
namespace Tamarin.StableDHTests
open Rewriting Rewriting.ConstructorVariants Rewriting.StableVariants

private inductive F where
  | exp | inv | one | neutral | hash
  deriving DecidableEq

private def ar : F → Nat | .exp => 2 | .inv | .hash => 1 | _ => 0
private abbrev sig : Signature where
  FreeSym := F
  CSym := Empty
  ACSym := Unit
  Atom := Bool
  arity := ar
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort a := if a then .fresh else .pub

private abbrev T := Term sig
private def var (i : Nat) : T := .var ⟨i,.msg⟩
private def exp (a b : T) : T := .free .exp (fun i => if i.val = 0 then a else b)
private def inv (a : T) : T := .free .inv (fun _ => a)
private def one : T := .free .one Fin.elim0
private def neutral : T := .free .neutral Fin.elim0
private def mul (a b : T) : T := .ac () a b

private def rules : List (Equation sig) :=
  let x := var 1; let y := var 2; let z := var 3
  [⟨exp x one, x⟩, ⟨exp (exp x y) z, exp x (mul y z)⟩,
   ⟨exp neutral x, neutral⟩, ⟨mul x one,x⟩,
   ⟨inv (inv x), x⟩, ⟨inv one,one⟩,
   ⟨mul x (inv x),one⟩, ⟨mul (inv x) (inv y), inv (mul x y)⟩,
   ⟨mul (inv (mul x y)) y, inv x⟩,
   ⟨inv (mul (inv x) y), mul x (inv y)⟩,
   ⟨mul x (mul (inv x) y), y⟩,
   ⟨mul (inv x) (mul (inv y) z), mul (inv (mul x y)) z⟩,
   ⟨mul (inv (mul x y)) (mul y z), mul (inv x) z⟩]

private theorem apps (r) (hr : r ∈ rules) : Application r.lhs := by
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;> trivial

private def word : Head sig → UInt64
  | .free .one => 1 | .free .neutral => 2 | .free .exp => 3
  | .free .inv => 4 | .ac _ => 5 | _ => 0

private def factorRow (r : Equation sig) :=
  ((ACRepresentation.flatten () r.lhs).map (RootExclusion.required word)).toArray

private def productRows := (rules.filterMap (fun r =>
  match r.lhs with | .ac _ _ _ => some (factorRow r) | _ => none)).toArray

private theorem productInventory : Buckets rules () word productRows := by
  intro r hr hh
  refine ⟨factorRow r, ?_, ?_⟩
  · apply List.mem_toArray.mpr
    apply List.mem_filterMap.mpr
    refine ⟨r,hr,?_⟩
    cases h : r.lhs <;> rw [h] at hh <;> first | cases hh | rfl
  · intro k hk _
    obtain ⟨t,ht,h⟩ := List.mem_map.mp (List.mem_toArray.mp hk)
    exact ⟨t,ht,h⟩

private def fresh (i : Nat) : T := .var ⟨i,.fresh⟩

private theorem freshImage (i : Nat) (ρ : Substitution sig) :
    ¬Application (ρ.apply (fresh i)) := by
  apply narrow_leaf
  all_goals intro f h; cases h

private theorem freshHead (i : Nat) (ρ : Substitution sig) :
    head (ρ.apply (fresh i)) ≠ .ac () ∧ word (head (ρ.apply (fresh i))) = 0 := by
  have leaf := freshImage i ρ
  cases h : ρ.apply (fresh i) with
  | var | atom => exact ⟨(fun e => by cases e), rfl⟩
  | free | ac | comm => exact False.elim (leaf (by rw [h]; trivial))

private theorem productStable (i j : Nat) : Stable (ruleRoot rules) (mul (fresh i) (fresh j)) := by
  apply exportedStableAC_semantic rules apps () _ word productRows #[0] _ _ productInventory
    (by decide +kernel)
  · intro t ht
    simp [mul,ACRepresentation.flatten,fresh] at ht
    rcases ht with rfl|rfl <;> exact fun ρ hn => hn _
  · intro t ht ρ
    have cases : t = fresh i ∨ t = fresh j := by simpa [mul,ACRepresentation.flatten,fresh] using ht
    rcases cases with rfl|rfl
    · exact ⟨(freshHead i ρ).1, by simp [(freshHead i ρ).2]⟩
    · exact ⟨(freshHead j ρ).1, by simp [(freshHead j ρ).2]⟩

private def freeRows (f : F) := (rules.filterMap fun r =>
  match r.lhs with
  | .free g xs => if f = g then some (Array.ofFn fun i => RootExclusion.required word (xs i)) else none
  | _ => none).toArray

private theorem freeInventory (f : F) (p : Fin (ar f) → T) (rhs : T)
    (hm : (⟨.free f p, rhs⟩ : Equation sig) ∈ rules) :
    (Array.ofFn fun i => RootExclusion.required word (p i)) ∈ freeRows f := by
  apply List.mem_toArray.mpr
  exact List.mem_filterMap.mpr ⟨_,hm,by simp⟩

private theorem powerStable (i j : Nat) :
    Stable (ruleRoot rules) (exp (.atom false) (mul (fresh i) (fresh j))) := by
  unfold exp
  apply freeExcluded exportedRootExclusion_correct rules apps _ _ _ word _ _ (freeInventory .exp)
  · change Executable.excludeRoot (freeRows F.exp) #[0,5] = true
    decide +kernel
  · intro k
    split
    · exact constructors rules apps _ (by simp [operators])
    · exact productStable i j
  · intro ρ k
    split <;> rfl

example (i : Nat) : Stable (ruleRoot rules) (exp (.atom false) (fresh i)) := by
  unfold exp
  apply freeExcluded exportedRootExclusion_correct rules apps _ _ _ word _ _ (freeInventory .exp)
  · change Executable.excludeRoot (freeRows F.exp) #[0,0] = true
    decide +kernel
  · intro k
    split
    · exact constructors rules apps _ (by simp [operators])
    · exact fun ρ hn => hn _
  · intro ρ k
    split
    · rfl
    · exact (freshHead i ρ).2

private theorem apply_exp (σ : Substitution sig) (a b : T) :
    σ.apply (exp a b) = exp (σ.apply a) (σ.apply b) := by
  apply congrArg (Term.free (sig := sig) .exp)
  funext i
  change σ.apply (if _ then _ else _) = _
  split <;> rfl

private def towerBindings (i j : Nat) : Substitution sig where
  image v := if v = ⟨1,.msg⟩ then .atom false else if v = ⟨2,.msg⟩ then fresh i
    else if v = ⟨3,.msg⟩ then fresh j else .var v
  support := [⟨1,.msg⟩,⟨2,.msg⟩,⟨3,.msg⟩]
  outside := by intro v h; simp_all
  sorted := by
    intro v
    split <;> rename_i h
    · subst v; exact .widen (HasSort.atom (sig := sig) false) .pub_msg
    · split <;> rename_i h
      · subst v; exact .widen (.var _) .fresh_msg
      · split <;> rename_i h
        · subst v; exact .widen (.var _) .fresh_msg
        · exact .var _

example (i j : Nat) : Step (ruleRoot rules) (exp (exp (.atom false) (fresh i)) (fresh j))
    (exp (.atom false) (mul (fresh i) (fresh j))) := by
  apply Step.root
  let lhs := exp (exp (var 1) (var 2)) (var 3)
  let rhs := exp (var 1) (mul (var 2) (var 3))
  refine ⟨⟨lhs,rhs⟩, ?_, towerBindings i j, ?_, ?_⟩
  · simp [rules,lhs,rhs]
  · simp only [lhs,apply_exp]; rfl
  · simp only [rhs,apply_exp]; rfl

-- Presence of every required head leaves a candidate AC subgroup. Supplying 1 or inv in the subject prevents the corresponding
-- exclusion; repeating a fresh value retains normality.
#guard Executable.excludeACFactors productRows #[0]
#guard !Executable.excludeACFactors productRows #[0,1]
#guard !Executable.excludeACFactors productRows #[0,4]

example (i : Nat) :
    let q := [exp (.atom false) (mul (fresh i) (fresh i)), mul (fresh i) (fresh i), fresh i]
    let a : Variant sig := ⟨.identity,q⟩
    CompleteVariants (ruleRoot rules) q [a] ∧ a.Safe q [] ∧ a.Reconstructible (ruleRoot rules) q := by
  let q := [exp (.atom false) (mul (fresh i) (fresh i)), mul (fresh i) (fresh i), fresh i]
  have cert : ∀ t ∈ q, Representative (ruleRoot rules) t (id t) := by
    intro t ht
    simp [q] at ht
    rcases ht with rfl|rfl|rfl
    · exact stableRepresentative (powerStable i i)
    · exact stableRepresentative (productStable i i)
    · exact stableRepresentative (fun ρ hn => hn _)
  simpa [q] using tuple rules apps q id cert []

private def peerSymbols : DHPeer.Symbols sig where
  pow := .exp
  inv := .inv
  one := .one
  neutral := .neutral
  mul := ()
  powArity := rfl
  invArity := rfl
  oneArity := rfl
  neutralArity := rfl
  powInput _ := rfl
  invInput _ := rfl
  powSort := rfl
  invSort := rfl
  oneSort := rfl
  neutralSort := rfl
  mulSort := rfl

private def peerTable : DHPeer.Table peerSymbols where
  rules := rules
  actual _ i := ⟨i.val + 1, .msg⟩
  actualSort _ _ := rfl
  distinct := by intro _ i j h; apply Fin.ext; have e := congrArg Variable.id h; simpa using e
  present := by
    intro k
    cases k <;> simp only [rules, List.mem_cons, List.not_mem_nil,or_false] <;>
      first | exact Or.inl rfl | repeat' first | exact rfl | exact Or.inl rfl | right

-- The original presentation contains all seven schemas used by the decoder.
-- Instantiate every recipe with arbitrary well-sorted terms, including a
-- compound witness that itself contains inverses or exponentiation.
example (env : DHPeer.Slot → T) (typed : ∀ i, HasSort (env i) .msg) (k : DHPeer.Branch) :
    Reduces (ruleRoot rules) ((DHPeer.Expr.pow k.pair.1 DHPeer.r).eval peerSymbols env)
      (k.pair.2.eval peerSymbols env) := peerTable.reaches env typed k


private def extraTable : DHPeer.ExtraTable peerTable where
  actual _ i := ⟨i.val + 1,.msg⟩
  sorted _ _ := rfl
  distinct := by intro _ i j h; apply Fin.ext; have e := congrArg Variable.id h; simpa using e
  present := by
    intro k
    cases k <;> simp only [peerTable,rules,List.mem_cons,List.not_mem_nil,or_false] <;>
      repeat' first | exact rfl | exact Or.inl rfl | right

private theorem powerBucket : DHPeer.PowerBucket peerTable := by
  refine ⟨apps,?_⟩
  intro eq mem hd
  simp only [peerTable,rules,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first
    | exact ⟨.expOne,.inl rfl,rfl⟩
    | exact ⟨.tower,.inr (.inl rfl),rfl⟩
    | exact ⟨.neutral,.inr (.inr rfl),rfl⟩
    | cases hd

private theorem inverseBucket : DHPeer.InverseBucket extraTable := by
  refine ⟨apps,?_⟩
  intro eq mem hd
  simp only [peerTable,rules,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first
    | exact ⟨.invInv,.inl rfl,rfl⟩
    | exact ⟨.invOne,.inr (.inl rfl),rfl⟩
    | exact ⟨.pull,.inr (.inr rfl),rfl⟩
    | cases hd

example (v r : T) (hr : HasSort r .msg) (norm : Normal (ruleRoot rules) (inv (mul v r))) :
    Normal (ruleRoot rules) (inv v) := inverseBucket.shrink hr norm

example (a e : T) (ha : HasSort a .msg) (he : HasSort e .msg) :
    Normal (ruleRoot rules) (exp a e) ↔ Normal (ruleRoot rules) a ∧ Normal (ruleRoot rules) e ∧
      head a ≠ .free .exp ∧ head a ≠ .free .neutral ∧ head e ≠ .free .one := powerBucket.normal_iff ha he

private theorem multBucket : DHPeer.MulBucket extraTable := by
  refine ⟨apps,?_⟩
  intro eq mem hd
  simp only [peerTable,rules,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first
    | exact .inl ⟨.inverse,.inl rfl,rfl⟩
    | exact .inl ⟨.inverseRest,.inr (.inl rfl),rfl⟩
    | exact .inl ⟨.inside,.inr (.inr (.inl rfl)),rfl⟩
    | exact .inl ⟨.insideRest,.inr (.inr (.inr rfl)),rfl⟩
    | exact .inr ⟨.mulOne,.inl rfl,rfl⟩
    | exact .inr ⟨.join,.inr (.inl rfl),rfl⟩
    | exact .inr ⟨.joinRest,.inr (.inr rfl),rfl⟩
    | cases hd

private theorem constantsEmpty (eq : Equation sig) (mem : eq ∈ rules) :
    head eq.lhs ≠ .free .neutral ∧ head eq.lhs ≠ .free .one := by
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    constructor <;> intro h <;> cases h

private def observations (q : DHPeer.Names) : List (DHPeer.Observation sig) :=
  [.power,.context (q.symbolic .peer),.power,.context (q.symbolic .fresh)]

private theorem apart (q : DHPeer.Names) (v : Variable)
    (obs : Observed ((observations q).map (q.input peerSymbols)) v) : ¬q.witness v := by
  have distinctWitness (i : DHPeer.Slot) (x : i = .peer ∨ i = .fresh) : ¬q.witness (q.var i) := by
    rintro (hb|hp|hn)
    all_goals first | have e := q.distinct _ _ hb | have e := q.distinct _ _ hp | have e := q.distinct _ _ hn
    all_goals rcases x with rfl|rfl <;> cases e
  obtain ⟨t,ht,occ⟩ := obs
  have inside : v = q.var .peer ∨ v = q.var .fresh := by
    simp only [observations,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl
    all_goals first | exact .inl occ | exact .inr occ | skip
    all_goals
      obtain ⟨i,hi⟩ := occ
      change Term.Occurs v (if _ then _ else _) at hi
      split at hi <;> first | exact .inl hi | exact .inr hi
  rcases inside with rfl|rfl
  · exact distinctWitness _ (.inl rfl)
  · exact distinctWitness _ (.inr rfl)

-- No normality, completeness, or disjointness hypothesis: all seven answers
-- cover the joint four-slot example in the actual thirteen-rule presentation.
-- The repeated power and shared input variables use a single substitution.
example (q : DHPeer.Names) :
    let os := observations q
    let query := os.map (q.input peerSymbols)
    let answers := DHPeer.arms.map fun k => q.arm peerSymbols k os
    CompleteVariants (ruleRoot rules) query answers ∧
      ∀ a ∈ answers, a.Reconstructible (ruleRoot rules) query ∧ a.Safe query [] ∧
        ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  apply DHPeer.certified powerBucket inverseBucket multBucket (fun eq mem => (constantsEmpty eq mem).1)
    (fun eq mem => (constantsEmpty eq mem).2) q (observations q) (by simp [observations])
    [] (apart q) (by simp)
  intro t ht
  simp [observations] at ht
  rcases ht with rfl|rfl <;> exact fun ρ norm => norm _


private def names : DHPeer.Names where
  var i := ⟨match i with | .peer => 0 | .fresh => 1 | .base => 2 | .pos => 3 | .neg => 4, i.sort⟩
  distinct := by intro i j; cases i <;> cases j <;> decide
  sorted _ := rfl

private def hashed : T := .free .hash (fun _ => var 7)

private theorem hashStable : Stable (ruleRoot rules) hashed := by
  refine freeContext rules apps F.hash (fun _ => var 7) ?_ (fun _ ρ hn => hn _)
  intro hh
  obtain ⟨eq,mem,he⟩ := List.mem_map.mp hh
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> cases he

private def compound : DHPeer.Query sig where
  toNames := names
  exponent := hashed
  sortedExponent := .free _ _ (fun _ => .var _)
  independent := by rintro ⟨_,impossible⟩; cases impossible
  disjoint := by
    rintro v ⟨_,occ⟩
    obtain rfl : v = ⟨7,.msg⟩ := occ
    rintro (hb|hp|hn) <;> contradiction

private def compoundSlots : List (DHPeer.Observation sig) :=
  [.power, .context (var 7), .power, .context hashed, .context (names.symbolic .peer)]

private theorem compoundScope (v : Variable) (hv : Observed (compoundSlots.map (compound.input peerSymbols)) v) :
    ¬compound.witness v := by
  obtain ⟨t,ht,occ⟩ := hv
  have payload (h : hashed.Occurs v) : v = ⟨7,.msg⟩ := h.choose_spec
  have power (h : (compound.input peerSymbols .power).Occurs v) : v = names.var .peer ∨ v = ⟨7,.msg⟩ := by
    obtain ⟨i,hi⟩ := h
    change Term.Occurs v (if i.val = 0 then names.symbolic .peer else hashed) at hi
    split at hi
    · exact .inl hi
    · exact .inr (payload hi)
  simp only [compoundSlots,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at ht
  have either : v = names.var .peer ∨ v = ⟨7,.msg⟩ := by
    rcases ht with rfl|rfl|rfl|rfl|rfl
    · exact power occ
    · exact .inr occ
    · exact power occ
    · exact .inr (payload occ)
    · exact .inl occ
  rcases either with rfl|rfl <;> rintro (hb|hp|hn) <;> contradiction

-- One linked packet must explain both Y^hash(X) slots, X itself, hash(X)
-- and Y with one substitution. X is an unrestricted message variable.
example {rows} (run : Executable.dhPeerImages true = some rows) :
    let query := compoundSlots.map (compound.input peerSymbols)
    let answers := (DHPeer.Programs.branches rows).map fun k => compound.arm peerSymbols k compoundSlots
    CompleteVariants (ruleRoot rules) query answers ∧
      ∀ a ∈ answers, a.Reconstructible (ruleRoot rules) query ∧ a.Safe query [] ∧
        ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  have admitted : DHPeer.StableFactor peerSymbols (ruleRoot rules) compound.exponent := by
    intro ρ hn
    exact ⟨hashStable ρ hn,⟨(fun h => by cases h),(fun h => by cases h),(fun h => by cases h)⟩⟩
  apply exportedDHPeerImages_factorSemantic run powerBucket inverseBucket multBucket
    (fun eq mem => (constantsEmpty eq mem).1) (fun eq mem => (constantsEmpty eq mem).2)
    compound admitted compoundSlots (by simp [compoundSlots]) [] compoundScope (by simp)
  intro t ht
  simp [compoundSlots] at ht
  rcases ht with rfl|rfl|rfl <;> first | exact hashStable | exact fun ρ hn => hn _

-- Both occurrences of X have the same spelling at the Rust boundary.
-- A single shared X gives an empty unifier, yet the independent caller
-- and rule variables can be instantiated to opposite names.
example :
    let x : Variable := ⟨0,.msg⟩
    let subject := mul (.var x) (.atom true)
    let pattern := mul (.var x) (.atom false)
    CompleteSet [⟨subject,pattern⟩] [] ∧ ¬ACUnifierExclusion.Refuted subject pattern := by
  intro x subject pattern
  constructor
  · apply (complete_empty_iff _).mpr
    rintro ⟨σ,sol⟩
    have e : EquivB (.ac () (σ.image x) (.atom true)) (.ac () (σ.image x) (.atom false)) :=
      sol _ List.mem_cons_self
    cases (EquivB.ac_cancel_left (sig := sig) () e).head_eq
  · intro no
    let ρ := Substitution.binding x (.atom false : T) (.widen (.atom _) .pub_msg)
    let τ := Substitution.binding x (.atom true : T) (.widen (.atom _) .fresh_msg)
    apply no.incompatible ρ τ
    change EquivB (.ac () (ρ.image x) (.atom true)) (.ac () (τ.image x) (.atom false))
    simp only [ρ,τ,Substitution.binding_image_self]
    exact .ac_swap _ _ _

-- A whole-product miss can coexist with an actual reduction at a strict
-- subbag. All factors are distinct positions; the repeated name matters.
example :
    let a : T := .atom true
    let b : T := .atom false
    let pattern := mul a b
    let whole := mul pattern a
    CompleteSet [⟨whole,pattern⟩] [] ∧ ¬ Normal (ruleRoot [⟨pattern,a⟩]) whole := by
  intro a b pattern whole
  constructor
  · apply (complete_empty_iff _).mpr
    rintro ⟨σ,sol⟩
    have e := (Cancellation.flatten_equiv () (sol _ List.mem_cons_self)).length_eq
    change (Cancellation.flatten () (.ac () (.ac () a b) a)).length =
      (Cancellation.flatten () (.ac () a b)).length at e
    simp [a,b,Cancellation.flatten] at e
  · intro norm
    apply norm (mul a a)
    exact ⟨_,_,.refl _,.ac_left () a (.root ⟨_,List.mem_cons_self,.identity,rfl,rfl⟩),.refl _⟩

end Tamarin.StableDHTests
