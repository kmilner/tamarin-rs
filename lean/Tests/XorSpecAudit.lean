import TamarinCI
import Tamarin.XorFlatNormal

namespace Tamarin.XorSpecAudit
open Rewriting
open Pairing (signature PTerm PSubst)

private def x : Variable := ⟨0, .msg⟩
private def y : Variable := ⟨1, .msg⟩
private def zero : PTerm := .free (.other 0 0) Fin.elim0
private def plus (a b : PTerm) : PTerm := .ac 0 a b
private def rules : List (Equation signature) :=
  [⟨plus (.var y) zero, .var y⟩,
   ⟨plus (.var x) (.var x), zero⟩,
   ⟨plus (.var x) (plus (.var x) (.var y)), .var y⟩]
private theorem apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs := by
  intro r hr
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> trivial

private theorem zeroSorted : HasSort zero .msg := .free _ _ fun i => Fin.elim0 i
private def ρ : PSubst := Substitution.binding x zero zeroSorted

private theorem zeroNormal : Normal (ruleRoot rules) zero := by
  have normal := ConstructorVariants.constructor_normal rules apps
  rw [← Substitution.apply_identity zero]
  apply normal.2 zero _ Substitution.identity normal.1
  simp [zero, rules, plus, ConstructorVariants.operators, ConstructorVariants.ruleHeads,
    ConstructorVariants.head, headModel, Model.eval, List.ofFn_zero]
  change ¬ (Head.free (.other 0 0) : Head signature) ∈ [.ac 0, .ac 0, .ac 0]
  simp

private theorem rhoNormal : Normalized (ruleRoot rules) ρ := by
  intro v
  show Normal _ (if v = x then zero else .var v)
  split
  · exact zeroNormal
  · exact (ConstructorVariants.constructor_normal rules apps).1 _

private theorem unitResult : NormalForm (ruleRoot rules) (ρ.apply (plus (.var x) (.var y))) (.var y) := by
  change NormalForm _ (plus zero (.var y)) (.var y)
  refine ⟨.step ⟨_, _, .ac_swap .., .root ?_, .refl _⟩,
    (ConstructorVariants.constructor_normal rules apps).1 _, fun s hs => .widen (.var _) (Term.rootSort_le hs)⟩
  refine ⟨_, List.mem_cons_self .., Substitution.identity, ?_, ?_⟩ <;>
    exact (Substitution.apply_identity _).symm

-- Live Tamarin declarations return Msg or Nat. Abstract Lean signatures may
-- also have Fresh-result constructors. A syntactic disequality between their
-- outputs can disappear modulo B, without instantiating any variables.
private abbrev freshFnSig : Signature :=
  { signature with outputSort := fun _ => .fresh }
private def tagged (a b : Term freshFnSig) : Term freshFnSig :=
  .free (.other 3 1) (fun _ => .ac 0 a b)

example : let a : Term freshFnSig := .atom (0, .msg)
    let b : Term freshFnSig := .atom (1, .msg)
    HasSort (tagged a b) .fresh ∧ tagged a b ≠ tagged b a ∧ EquivB (tagged a b) (tagged b a) := by
  intro a b
  refine ⟨.free _ _ (fun _ => .ac _ _ _ (.atom _) (.atom _)), ?_,
    .free _ _ _ (fun _ => .ac_swap _ _ _)⟩
  intro e
  have pair := congrArg (fun t : Term freshFnSig => match t with
    | .free (.other _ 1) args => args 0
    | _ => a) e
  change (Term.ac 0 a b : Term freshFnSig) = .ac 0 b a at pair
  have clash : (0 : Nat) = 1 := congrArg Prod.fst (Term.atom.inj (Term.ac.inj pair).2.1)
  contradiction

-- With Msg operands, the unit instance x=zero leaves y unconstrained. The
-- raw identity value remains XOR-headed under every instantiation, while the
-- diagonal value remains zero-headed. Neither can cover the variable y.
example (answers : List (Variant signature))
    (twoValues : ∀ a ∈ answers,
      a.values = [plus (.var x) (.var y)] ∨ a.values = [zero]) :
    ¬ CompleteVariants (ruleRoot rules) [plus (.var x) (.var y)] answers := by
  intro complete
  obtain ⟨a, ha, δ, _, _, vals⟩ := complete.2 ρ rhoNormal [.var y] ⟨unitResult, trivial⟩
  rcases twoValues a ha with h | h <;> rw [h] at vals <;> cases vals.1.head_eq

-- An additional rule at zero invalidates the prescribed diagonal normal
-- value even when the active table still contains all the builtin XOR rules.
example : ¬ Normal (ruleRoot (⟨zero, .atom (1, .pub)⟩ :: rules)) zero := by
  intro hn
  exact hn _ ⟨_, _, .refl _, .root ⟨_, List.mem_cons_self .., Substitution.identity,
    (Substitution.apply_identity _).symm, rfl⟩, .refl _⟩

-- The Rust API transports only substitutions and normalizes each observed
-- term again. With two permitted results at the same ground root, even two
-- copies of one observation can require different values in the generic
-- relation. Any deterministic re-normalization yields a diagonal tuple.
private def atom (n : Nat) : PTerm := .atom (n, .msg)
private def competing : List (Equation signature) :=
  [⟨zero, atom 0⟩, ⟨zero, atom 1⟩]
private theorem compApps : ∀ r ∈ competing, ConstructorVariants.Application r.lhs := by
  intro r hr
  simp only [competing, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> trivial

private theorem atomResult (n : Nat) (h : (⟨zero, atom n⟩ : Equation signature) ∈ competing) :
    NormalForm (ruleRoot competing) (Substitution.identity.apply zero) (atom n) := by
  rw [Substitution.apply_identity]
  refine ⟨.step ⟨_, _, .refl _, .root ⟨_, h, Substitution.identity,
    (Substitution.apply_identity _).symm, rfl⟩, .refl _⟩, ?_,
    fun _ hs => .widen (.atom _) (Term.rootSort_le hs)⟩
  have hn := ConstructorVariants.constructor_normal competing compApps
  rw [← Substitution.apply_identity (atom n)]
  exact hn.2 _ (by simp [atom, ConstructorVariants.operators]) Substitution.identity hn.1

example (answers : List (Variant signature)) (same : ∀ a ∈ answers, ∃ t, a.values = [t,t]) :
    ¬ CompleteVariants (ruleRoot competing) [zero,zero] answers := by
  intro h
  have values : Aligned (fun t u => NormalForm (ruleRoot competing) (Substitution.identity.apply t) u)
      [zero,zero] [atom 0,atom 1] :=
    ⟨atomResult _ (by simp [competing]), atomResult _ (by simp [competing]), trivial⟩
  obtain ⟨a, ha, δ, _, _, matchesValues⟩ := h.2 Substitution.identity
    (ConstructorVariants.constructor_normal _ compApps).1 _ values
  obtain ⟨t, e⟩ := same a ha
  rw [e] at matchesValues
  have clash := matchesValues.1.trans matchesValues.2.1.symm
  cases clash.head_eq

private def table : FreshXor.Flat.Table signature where
  rules := rules
  f := 0
  fSort := rfl
  zero := zero
  zeroFree := ⟨_,_,rfl⟩
  zeroGround := by intro _ h; obtain ⟨i,_⟩ := h; exact Fin.elim0 i
  zeroSort := zeroSorted
  zeroAbsent := by
    simp [zero,rules,plus,ConstructorVariants.operators,ConstructorVariants.ruleHeads,
      ConstructorVariants.head,headModel,Model.eval,List.ofFn_zero]
    change ¬ (Head.free (.other 0 0) : Head signature) ∈ [.ac 0,.ac 0,.ac 0]
    simp
  apps := apps
  param := x
  paramSort := rfl
  duplicate := by simp [rules,plus]
  bucket := by
    intro r h _
    simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    · exact .inr (.inl ⟨y,rfl⟩)
    · exact .inl rfl
    · exact .inr (.inr (.inl ⟨x,y,rfl⟩))
  freeSort := by intro _; exact SortId.noConfusion
  commSort := by intro _; exact SortId.noConfusion
  acSort := by intro _; exact SortId.noConfusion
  unitRule := ⟨y,rfl,List.mem_cons_self⟩
  inventory := by
    intro r h _
    simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    · exact .inr (.inl ⟨y,rfl⟩)
    · exact .inl rfl
    · exact .inr (.inr (.inl ⟨x,y,rfl⟩))

-- A competing triple with the correct pattern and the wrong RHS is
-- invisible to a head/pattern-only inventory. It invalidates flat parity.
private def badTriple : Equation signature := ⟨plus (.var x) (plus (.var x) (.var y)), zero⟩

example (T : FreshXor.Flat.Table signature) (f : T.f = 0) (active : badTriple ∈ T.rules) : False := by
  have bad := T.inventory badTriple active (by rw [f]; rfl)
  rcases bad with dup | ⟨v,unit⟩ | ⟨u,v,triple⟩ | ⟨u,v,triple⟩
  · have h := congrArg Equation.lhs dup
    cases (Term.ac.inj h).2.2
  all_goals first
    | have h := congrArg Equation.rhs unit; cases h
    | have h := congrArg Equation.rhs triple; cases h

-- The interspersed operands have multiplicities three, two, and one.
-- Reordering the two survivors is valid. Dropping both occurrences of a
-- duplicated name indiscriminately would also drop the odd survivor.
example :
    let a : PTerm := .var ⟨2,.fresh⟩
    let b : PTerm := .var ⟨3,.fresh⟩
    let c : PTerm := .var ⟨4,.fresh⟩
    let input := table.value [a,b,c,a,b,a]
    NormalForm table.R input (plus c a) ∧ ¬ NormalForm table.R input c := by
  classical
  intro a b c input
  have ac : a ≠ c := by simp [a,c]
  have ab : a ≠ b := by simp [a,b]
  have bc : b ≠ c := by simp [b,c]
  have forms := table.normalForm_iff (a := a) (b := b) (xs := [c,a,b,a]) (ys := [c,a])
  have typed : ∀ t ∈ [a,b,c,a,b,a], HasSort t .fresh := by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> exact .var _
  have normal : ∀ t ∈ [a,b,c,a,b,a], Normal table.R t := by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (ConstructorVariants.constructor_normal rules apps).1 _
  have same : ∀ t, [a,b,c,a,b,a].count t % 2 = [c,a].count t % 2 := by
    intro t
    by_cases ha : a = t <;> by_cases hb : b = t <;> by_cases hc : c = t <;>
      simp_all [List.count_cons]
  have h := forms typed normal (by simp [Ne.symm ac]) same
  exact ⟨(h _).mpr (.refl _),fun bad => by cases ((h _).mp bad).head_eq⟩

open VariantJoin

-- Two different wide observations share one input. Its odd multiplicity
-- returns that still-open input, while its even multiplicity returns zero.
-- Repeat the first observation after the second and preserve both values.
private abbrev k : Variable := ⟨9, .fresh⟩
private abbrev kv : PTerm := .var k
private def op : Bool → PTerm
  | false => table.value [kv, kv, kv]
  | true => table.value [kv, kv, kv, kv]

private theorem admitted (i : Bool) : FreshXor.Flat.Observation table (op i) := by
  cases i
  · exact .sum k k [k] (by intro v hv; simp at hv; subst v; rfl) (.refl _)
  · exact .sum k k [k,k] (by intro v hv; simp at hv; subst v; rfl) (.refl _)

private def joined : Row signature (Key [k]) Bool :=
  ⟨fun _ => kv, fun i => if i then zero else kv⟩

private theorem op_form (ρ : PSubst) (hn : Normalized table.R ρ) (i : Bool) (t : PTerm) :
    NormalForm table.R (ρ.apply (op i)) t ↔
      EquivB t (if i then zero else ρ.image k) := by
  classical
  have sort : HasSort (ρ.image k) .fresh := ρ.sorted k
  have norm := hn k
  cases i
  · change NormalForm table.R (ρ.apply (table.value [kv,kv,kv])) t ↔ _
    rw [FreshXor.Flat.Table.subst_value]
    change NormalForm table.R (table.value [ρ.image k,ρ.image k,ρ.image k]) t ↔ _
    apply table.normalForm_iff (ys := [ρ.image k]) (xs := [ρ.image k])
    · simp_all
    · simp_all
    · simp
    · intro t; by_cases e : ρ.image k = t <;> simp [e]
  · change NormalForm table.R (ρ.apply (table.value [kv,kv,kv,kv])) t ↔ _
    rw [FreshXor.Flat.Table.subst_value]
    change NormalForm table.R (table.value [ρ.image k,ρ.image k,ρ.image k,ρ.image k]) t ↔ _
    apply table.normalForm_iff (ys := []) (xs := [ρ.image k, ρ.image k])
    · simp_all
    · simp_all
    · simp
    · intro t; by_cases e : ρ.image k = t <;> simp [e]

private theorem rows_exact : Exact table.R Subtype.val op [joined] := by
  intro ρ hn values _
  constructor
  · intro forms
    refine ⟨joined, List.mem_singleton_self _, ρ, hn, ?_, ?_⟩
    · rintro ⟨v,hv⟩; obtain rfl := List.mem_singleton.mp hv; exact .refl _
    · intro i; have eq := (op_form ρ hn i _).mp (forms i)
      cases i
      · exact eq
      · change EquivB _ (ρ.apply table.zero)
        rw [table.toTable.fixes_zero]; exact eq
  · rintro ⟨_,mem,δ,_,fits⟩
    obtain rfl := List.mem_singleton.mp mem
    have image : EquivB (ρ.image k) (δ.image k) := fits.inputs ⟨k,List.mem_singleton_self _⟩
    intro i; apply (op_form ρ hn i _).mpr
    cases i
    · exact (fits.values false).trans image.symm
    · change EquivB _ zero
      have eq : EquivB (values true) (δ.apply table.zero) := fits.values true
      rw [table.toTable.fixes_zero] at eq; exact eq

example :
    let slots : List (Sum Bool PTerm) := [.inl false, .inl true, .inl false]
    ∃ answers, CompleteVariants table.R (slots.map (packedInput op)) answers ∧
      ∀ a ∈ answers, a.Reconstructible table.R (slots.map (packedInput op)) := by
  intro slots
  have typed : ∀ r ∈ [joined], r.Sorted := by
    intro _ hm; obtain rfl := List.mem_singleton.mp hm
    rintro ⟨v,hv⟩; obtain rfl := List.mem_singleton.mp hv; exact .var _
  have normal : ∀ r ∈ [joined], r.IsNormal table.R := by
    intro _ hm; obtain rfl := List.mem_singleton.mp hm
    have vars := (ConstructorVariants.constructor_normal rules apps).1
    exact ⟨fun _ => vars k, fun i => by cases i; exact vars k; exact zeroNormal⟩
  refine ⟨_, joinedFlatXorVariants_packed table op admitted [joined] [joined] rows_exact
    (fun _ hm => hm) (fun _ => 0) (fun _ h nh => (nh h).elim) typed normal slots
    (fun i => by cases i <;> simp [slots]) ?_ id ?_⟩
  · intro v h
    obtain ⟨_,hm,hv⟩ := h
    simp only [slots,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      simpa [packedInput, op, FreshXor.Flat.Table.value, ACRepresentation.fold, Term.Occurs] using hv
  · intro t h; simp [slots] at h

end Tamarin.XorSpecAudit
