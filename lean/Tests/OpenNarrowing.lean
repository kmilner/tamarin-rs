import TamarinCI

namespace Tamarin.Rewriting.OpenNarrowingTests
open Pairing (signature PTerm PSubst Symbol)

def two {α : Type} (a b : α) (i : Fin 2) := if i = 0 then a else b

abbrev encSym : Symbol := .other 70 2
abbrev decSym : Symbol := .other 71 2
abbrev forkSym : Symbol := .other 72 0
def enc (m k : PTerm) : PTerm := .free encSym (two m k)
def dec (s k : PTerm) : PTerm := .free decSym (two s k)
def fork : PTerm := .free forkSym Fin.elim0
def atom (n : Nat) : PTerm := .atom (n, .msg)
def m : Variable := ⟨0, .msg⟩
def k : Variable := ⟨1, .msg⟩

def nonlinear : Equation signature := ⟨dec (enc (.var m) (.var k)) (.var k), .var m⟩
def left : Equation signature := ⟨fork, atom 0⟩
def right : Equation signature := ⟨fork, atom 1⟩
def table := [nonlinear, left, right]
abbrev R := ruleRoot table

theorem app_heads : ∀ r ∈ table, ConstructorVariants.Application r.lhs := by
  intro r h
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> trivial

theorem normal_atom (n : Nat) : Normal R (atom n) := by
  obtain ⟨hn, hc⟩ := ConstructorVariants.constructor_normal table app_heads
  exact hc (atom n) (by simp [atom, ConstructorVariants.operators]) Substitution.identity hn

private theorem subst_bin (s : Symbol) (hs : signature.arity s = 2) (a b : PTerm)
    (σ : PSubst) :
    σ.apply (.free s (fun i => two a b (i.cast hs))) =
      .free s (fun i => two (σ.apply a) (σ.apply b) (i.cast hs)) := by
  change @Term.free signature s _ = Term.free s _
  congr 1; funext i; by_cases h : i.cast hs = 0 <;> simp [two, h, Substitution.apply]

@[simp] theorem apply_dec (σ : PSubst) (a b : PTerm) :
    σ.apply (dec a b) = dec (σ.apply a) (σ.apply b) := subst_bin _ rfl _ _ _
@[simp] theorem apply_enc (σ : PSubst) (a b : PTerm) :
    σ.apply (enc a b) = enc (σ.apply a) (σ.apply b) := subst_bin _ rfl _ _ _

theorem fires (a b : PTerm) (ha : HasSort a .msg) (hb : HasSort b .msg) :
    R (dec (enc a b) b) a := by
  let σ := Pairing.parameters m k a b ha hb
  refine ⟨nonlinear, by simp [table], σ, ?_, ?_⟩
  · change _ = σ.apply (dec (enc (.var m) (.var k)) (.var k))
    rw [apply_dec, apply_enc]
    change dec (enc a b) b = dec (enc (σ.image m) (σ.image k)) (σ.image k)
    simp [σ, Pairing.parameters, m, k]
  · change _ = σ.image m
    simp [σ, Pairing.parameters]

-- Matching must use one shared key, but keys may be equal modulo AC.
example (a b : PTerm) (ha : HasSort a .msg) (hb : HasSort b .msg) :
    StepModulo R (dec (enc (atom 0) (.ac 0 a b)) (.ac 0 b a)) (atom 0) := by
  let crypt := enc (atom 0) (.ac 0 a b)
  refine ⟨dec crypt (.ac 0 a b), _, EquivB.free _ _ _ ?_, .root ?_, .refl _⟩
  · intro i; change EquivB (two crypt (.ac 0 b a) i) (two crypt (.ac 0 a b) i)
    by_cases h : i = 0
    · simp [two, h]; exact .refl _
    · simp [two, h]; exact EquivB.ac_swap (sig := signature) 0 b a
  · exact fires _ _ (.atom _) (.ac _ _ _ ha hb)

private theorem enc_inj_key {p q a b : PTerm} (he : EquivB (enc p a) (enc q b)) :
    EquivB a b := by simpa [two] using (Matching.free_equiv_iff _ _ _).mp he 1

-- Independent fresh variables for the two occurrences of k would admit
-- this mismatched instance. No root rewrite modulo B can fire there.
theorem same_key {p a b u : PTerm} {ys}
    (he : EquivB (dec (enc p a) b) (.free decSym ys)) (hr : R (.free decSym ys) u) :
    EquivB a b := by
  obtain ⟨r, hm, σ, h, _⟩ := hr
  simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · change _ = σ.apply (dec (enc (.var m) (.var k)) (.var k)) at h
    rw [apply_dec, apply_enc] at h
    rw [h] at he
    have ch := (Matching.free_equiv_iff _ _ _).mp he
    have hk := enc_inj_key (show EquivB (enc p a) (enc (σ.image m) (σ.image k)) from
      by simpa [two, Substitution.apply, Term.subst] using ch 0)
    exact hk.trans (show EquivB b (σ.image k) from by simpa [two, Substitution.apply, Term.subst] using ch 1).symm
  · cases congrArg ConstructorVariants.head h
  · cases congrArg ConstructorVariants.head h

theorem mismatch_normal : Normal R (dec (enc (atom 0) (atom 1)) (atom 2)) := by
  apply normal_free_no_root
  · intro i; change Normal R (two (enc (atom 0) (atom 1)) (atom 2) i)
    by_cases h : i = 0
    · simp only [two, h, ↓reduceIte]
      obtain ⟨hn, hc⟩ := ConstructorVariants.constructor_normal table app_heads
      apply (Substitution.apply_identity _ ▸ hc _ _ Substitution.identity hn)
      simp [ConstructorVariants.operators, enc, two, atom, ConstructorVariants.ruleHeads,
        table, nonlinear, left, right, ConstructorVariants.head, dec, fork, headModel,
        Model.eval, decSym, encSym, forkSym]
      change ¬(Head.free encSym : Head signature) ∈ [.free decSym, .free forkSym, .free forkSym]
      simp [encSym, decSym, forkSym]
    · simp only [two, h, ↓reduceIte]; exact normal_atom _
  · intro ys hy u hu
    have he := same_key (.free _ _ _ hy) hu
    have hk : (1 : Nat) = 2 := congrArg Prod.fst (Head.atom.inj he.head_eq)
    contradiction

example : ¬ NormalForm R (dec (enc (atom 0) (atom 1)) (atom 2)) (atom 0) := by
  intro nf
  exact nomatch (normal_reduces_equiv nf.1 mismatch_normal).head_eq

-- A normalized substitution cannot put a message constructor into a fresh
-- or node variable. The same exclusion already follows from sorting alone.
example (σ : PSubst) (v : Variable) (s : v.sort = .fresh ∨ v.sort = .node) (a b : PTerm) :
    ¬ EquivB (σ.image v) (enc a b) := by
  intro h
  have hs := Term.rootSort_le (σ.sorted v)
  rw [Term.rootSort_equiv h] at hs
  rcases s with s | s <;> rw [s] at hs <;> cases hs

-- The unrelated symbol has two incomparable normal forms in this very table.
example : ∃ u v, StepModulo R fork u ∧ Normal R u ∧
    StepModulo R fork v ∧ Normal R v ∧ ¬ EquivB u v := by
  have step (r : Equation signature) (hm : r ∈ table) (hl : r.lhs = fork) :
      StepModulo R fork r.rhs := by
    refine ⟨_, _, .refl _, .root ⟨r, hm, Substitution.identity, ?_, ?_⟩, .refl _⟩
    · simp [hl]
    · simp
  refine ⟨_, _, step left (by simp [table]) rfl, normal_atom 0,
    step right (by simp [table]) rfl, normal_atom 1, ?_⟩
  intro h
  have he : (0 : Nat) = 1 := congrArg Prod.fst (Head.atom.inj h.head_eq)
  contradiction

def p := two (enc (.var m) (.var k)) (.var k)
def x (i : Fin 2) : Variable := ⟨i.val + 10, .msg⟩

abbrev schema : OpenNarrowing.Schema signature where
  d := decSym
  p := p
  z := m
  x := x
  distinct := by intro i j h; apply Fin.ext; exact Nat.add_right_cancel (congrArg Variable.id h)
  inputSort := fun _ => .refl _
  typed := by
    intro i; change HasSort (p i) .msg
    by_cases hi : i = 0
    · simp [p, two, hi]; apply HasSort.free
      intro j; by_cases hj : j = 0 <;> simp [two, hj] <;> exact HasSort.var _
    · simp [p, two, hi]; exact .var _
  resultSort := .refl _
  pattern_mem := by
    intro i; by_cases hi : i = 0
    · simp [p, two, hi]; apply RulePattern.Free.free
      intro j; by_cases hj : j = 0 <;> simp [two, hj] <;> exact .var _
    · simp [p, two, hi]; exact .var _
  rigid := ⟨0, by trivial⟩
  outputOccurs := ⟨0, 0, rfl⟩

def noRename : VariablePermutation where
  forward := id
  backward := id
  support := []
  outside := by intros; rfl
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  sorted := fun _ => rfl

def packed : List (Option schema.Index) := [some 0, none, some 1, none]
def avoid := [x 0, x 1]

-- Both occurrences of the open application must share the very same
-- instantiation with the separately observed ciphertext and key.
theorem export_complete :
    ∃ answers, schema.decode packed (Executable.pairingVariants true) = some answers ∧
      schema.Admissible R packed avoid answers ∧
      ∀ a ∈ answers, a.Reconstructible R (packed.map schema.input) := by
  apply exportedOpenNarrowing_correct schema table p m noRename app_heads
  · exact List.mem_cons_self
  · intro r hm hh
    simp only [table, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rfl
    · cases hh
    · cases hh
  · intro i; exact (Term.subst_id (p i)).symm
  · rfl
  · intro i f hf
    change f ∈ ConstructorVariants.operators (p i) at hf
    by_cases h : i = 0
    · simp [p, two, h, enc, ConstructorVariants.operators] at hf
      subst f
      change ¬(Head.free encSym : Head signature) ∈ [.free decSym, .free forkSym, .free forkSym]
      simp [encSym, decSym, forkSym]
    · simp [p, two, h, ConstructorVariants.operators] at hf
  · simp [packed]
  · intro v ⟨i, hi⟩
    change (p i).Occurs v at hi
    have localVar : v = m ∨ v = k := by
      by_cases h : i = 0
      · simp [p, two, h] at hi
        obtain ⟨j, hj⟩ := hi
        by_cases h' : j = 0
        · exact Or.inl (by simpa [two, h', Term.Occurs] using hj)
        · exact Or.inr (by simpa [two, h', Term.Occurs] using hj)
      · exact Or.inr (by simpa [p, two, h, Term.Occurs] using hi)
    rcases localVar with rfl | rfl
    all_goals
      constructor
      · decide
      · intro ⟨j, he⟩
        have hid := congrArg Variable.id he
        change j.val + 10 = _ at hid
        simp [m, k] at hid

private theorem both : schema.Admissible R packed avoid
    [schema.identityArm packed, schema.ruleArm packed] := by
  obtain ⟨ans, reply, ok, _⟩ := export_complete
  change some [schema.identityArm packed, schema.ruleArm packed] = some ans at reply
  exact Option.some.inj reply ▸ ok

-- Neither dropping the rule arm nor dropping the identity arm is complete.
example : ¬ CompleteVariants R (packed.map schema.input) [schema.identityArm packed] := by
  intro only
  have hs := both.1.1 (schema.ruleArm packed) (by simp)
  obtain ⟨a, ha, δ, _, _, vals⟩ := only.2 _ hs.1 _ hs.2
  obtain rfl := List.mem_singleton.mp ha
  exact nomatch vals.2.1.head_eq

example : ¬ CompleteVariants R (packed.map schema.input) [schema.ruleArm packed] := by
  intro only
  have hs := both.1.1 (schema.identityArm packed) (by simp)
  obtain ⟨a, ha, δ, _, hagree, _⟩ := only.2 _ hs.1 _ hs.2
  obtain rfl := List.mem_singleton.mp ha
  have e := hagree (schema.x 0) ((schema.observed_iff packed (by simp [packed]) _).mpr ⟨0, rfl⟩)
  change EquivB (.var (x 0)) (δ.apply (schema.split.image (schema.x 0))) at e
  rw [schema.split_owned] at e
  exact nomatch e.head_eq

example : schema.Admissible R packed avoid [schema.ruleArm packed, schema.identityArm packed] := by
  apply (schema.admissible_reorder _).mp both
  intro a
  simp [or_comm]

end Tamarin.Rewriting.OpenNarrowingTests

namespace Tamarin.Rewriting.OpenNarrowingTests
open Pairing (signature PTerm Symbol)

private abbrev verifySym : Symbol := .other 73 3
private abbrev keySym : Symbol := .other 74 1
private abbrev truthSym : Symbol := .other 75 0
private def truth : PTerm := .free truthSym Fin.elim0
private def keyOf (t : PTerm) : PTerm := .free keySym (fun _ => t)
private def verifyArgs (a b : PTerm) : Fin 3 → PTerm :=
  Fin.cases (enc a b) (two a (keyOf b))
private def localKey (k : UInt64) : Variable := ⟨k.toNat, .msg⟩

-- The concrete signature rule checks both the message and the signing key;
-- the selected leaf certifies consistency but the result is the literal true.
-- The same theorem admits compound subject terms without enumerating them.
example (a b : PTerm) (ha : HasSort a .msg) (hb : HasSort b .msg) :
    let p := verifyArgs (.var (localKey 0)) (.var (localKey 1))
    let rules : List (Equation signature) := [⟨.free verifySym p, truth⟩]
    NormalForm (ruleRoot rules) (.free verifySym (verifyArgs a b)) truth := by
  dsimp only
  let subject := fun (id : UInt64) => if id = 10 then a else b
  let rows : RuleReduction.Rows := [(0,10),(1,11),(0,10),(1,11)]
  apply exportedGroundRuleReduction_semantic _ _ (verifyArgs (.var (localKey 0)) (.var (localKey 1))) _ _ 0 10 #[0,1,0,1] #[10,11,10,11] localKey subject
  · decide
  · simp
  · intro r hr; obtain rfl := List.mem_singleton.mp hr; trivial
  · intro v ⟨i, _⟩; exact Fin.elim0 i
  · exact .free _ _ (fun i => Fin.elim0 i)
  · intro f hf
    have ht : f = .free truthSym := by simpa [truth, ConstructorVariants.operators] using hf
    subst f; change ¬(Head.free truthSym : Head signature) ∈ [.free verifySym]
    simp [truthSym, verifySym]
  · have sa : RuleReduction.Skeleton localKey subject rows (.var (localKey 0)) a := by
      simpa [subject] using (RuleReduction.Skeleton.var (key := localKey) (subject := subject)
        (rows := rows) 0 10 (by decide))
    have sb : RuleReduction.Skeleton localKey subject rows (.var (localKey 1)) b := by
      simpa [subject] using (RuleReduction.Skeleton.var (key := localKey) (subject := subject)
        (rows := rows) 1 11 (by decide))
    intro i; refine Fin.cases ?_ (fun j => ?_) i
    · apply RuleReduction.Skeleton.free
      intro j; by_cases h : j = 0
      · simpa [two, h] using sa
      · simpa [two, h] using sb
    · by_cases h : j = 0
      · subst j; exact sa
      · simp [verifyArgs, two, h]; exact .free _ _ _ (fun _ => sb)
  · intro i _ j _ _ _ eq; exact UInt64.toNat.inj (congrArg Variable.id eq)
  · intro k v _; change HasSort (if v = 10 then a else b) .msg
    split <;> assumption

-- A wrong key prevents success even if the candidate selected the correct
-- message slot. Matching must validate repeated leaves across the whole rule.
example : Executable.reduceRuleSlot 0 #[0,1,0,1] #[10,11,10,12] = #[] := by decide

end Tamarin.Rewriting.OpenNarrowingTests
