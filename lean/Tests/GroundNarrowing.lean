import TamarinCI

namespace Tamarin.Rewriting.GroundNarrowing.Tests
open Pairing (PTerm PSubst signature Symbol pair)

private abbrev verifySym : Symbol := .other 0 3
private abbrev keySym : Symbol := .other 1 1
private abbrev truthSym : Symbol := .other 2 0
private def truth : PTerm := .free truthSym Fin.elim0
private def keyOf (t : PTerm) : PTerm := .free keySym (fun _ => t)
private def args {α : Type} (a b c : α) : Fin 3 → α := Fin.cases a (Fin.cases b (fun _ => c))

private theorem cases3 {P : Fin 3 → Prop} (p0 : P 0) (p1 : P 1) (p2 : P 2) (i : Fin 3) : P i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> assumption

private abbrev msg (n : Nat) : Variable := ⟨n, .msg⟩
private abbrev m := msg 0
private abbrev k := msg 1
private abbrev cipher := msg 2
private abbrev publicKey := msg 3
private abbrev c := msg 4
private abbrev observer := msg 5

private def capture : PTerm := pair (.var c) (.var c)
private theorem capSort : HasSort capture .msg := Pairing.pair_sorted (.var _) (.var _)
private def arg := args (.var cipher) capture (.var publicKey)
private def pat := args (pair (.var m) (.var k)) (.var m) (keyOf (.var k))
private def hole (v : Variable) : Option (Fin 3) :=
  if v = cipher then some 0 else if v = publicKey then some 2 else none
private def anchor : PSubst := Substitution.binding m capture capSort
private def solution : PSubst :=
  Pairing.parameters cipher publicKey (pair capture (.var k)) (keyOf (.var k))
    (Pairing.pair_sorted capSort (.var _)) (.free _ _ (fun _ => .var _))

private abbrev plan : Plan signature where
  d := verifySym
  arg := arg
  pat := pat
  rhs := truth
  typed := .free _ _ (fun i => Fin.elim0 i)
  inputTyped := cases3 (.var _) capSort (.var _)
  ground := fun _ ⟨i, _⟩ => Fin.elim0 i
  hole := hole
  anchor := anchor
  solution := solution
  image := by
    intro v; by_cases hc : v = cipher
    · subst v; change _ = (hole cipher).elim _ _
      simp [solution, Pairing.parameters, hole]
      change _ = anchor.apply (pair (.var m) (.var k))
      simp [anchor, Substitution.apply, Term.subst, Substitution.binding]
    · by_cases hp : v = publicKey
      · subst v
        simp [solution, Pairing.parameters, hole]
        rfl
      · simp [solution, Pairing.parameters, hole, hc, hp]
  holeArg := by
    intro v i hp
    by_cases hc : v = cipher
    · subst v; simp [hole] at hp; subst i; rfl
    · by_cases hk : v = publicKey
      · subst v; simp [hole] at hp; subst i; rfl
      · simp [hole, hc, hk] at hp
  position := by
    apply cases3
    · exact .inl ⟨cipher, rfl⟩
    · exact .inr ⟨m, rfl, Substitution.binding_image_self ..⟩
    · exact .inl ⟨publicKey, rfl⟩
  parameter := by
    intro v; by_cases hv : v = m
    · subst v; exact .inr ⟨1, rfl, Substitution.binding_image_self ..⟩
    · exact .inl (Substitution.binding_image_other _ _ _ _ hv)
  openAt := ⟨0, cipher, rfl, trivial⟩

private def packed : List (Option PTerm) := [none, some (.var observer), some (.var c), none]
private theorem hasApp : none ∈ packed := by simp [packed]

-- The captured message is the caller's pair(c,c), and the same rule-local
-- signing key must occur both inside the signature and under the public key.
example : plan.solution.image cipher = pair capture (.var k) ∧
    plan.solution.image publicKey = keyOf (.var k) ∧
    plan.solution.image c = .var c ∧ plan.solution.image observer = .var observer :=
  ⟨rfl, rfl, rfl, rfl⟩

private def rules : List (Equation signature) := [⟨.free verifySym pat, truth⟩]
private def Allowed (t : PTerm) := ∀ f ∈ ConstructorVariants.operators t, f ∉ ConstructorVariants.ruleHeads rules

private theorem emptyHeads {t : PTerm} (h : ConstructorVariants.operators t = []) : Allowed t := by
  intro f hf; simp [h] at hf

private theorem oneHead {t : PTerm} {op : Symbol} (h : ConstructorVariants.operators t = [.free op])
    (different : op ≠ verifySym) : Allowed t := by
  intro f hf; rw [h] at hf; obtain rfl := List.mem_singleton.mp hf
  change ¬(Head.free op : Head signature) ∈ [.free verifySym]
  exact fun hx => different (Head.free.inj (List.mem_singleton.mp hx))

private theorem inventories (v : Variable) (seen : Observed (packed.map plan.input) v)
    (localVar : plan.Local v) : False := by
  obtain ⟨t, ht, hv⟩ := seen
  have inPacked : v ∈ ((packed.map plan.input).flatMap Term.variables) :=
    List.mem_flatMap.mpr ⟨t, ht, (Term.mem_variables t v).mpr hv⟩
  obtain ⟨i, hi⟩ := localVar
  have inRule : v ∈ ((List.ofFn pat).flatMap Term.variables) :=
    List.mem_flatMap.mpr ⟨pat i, List.mem_ofFn.mpr ⟨i, rfl⟩, (Term.mem_variables _ _).mpr hi⟩
  change v ∈ [m,k,m,k] at inRule
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inRule
  rcases inRule with rfl | rfl | rfl | rfl <;> revert inPacked <;> decide

private theorem domain : plan.Domain rules packed where
  apps := by intro r hr; obtain rfl := List.mem_singleton.mp hr; trivial
  argConstructors := cases3 (emptyHeads rfl) (oneHead (op := .pair) rfl (by decide)) (emptyHeads rfl)
  patternConstructors := cases3 (oneHead (op := .pair) rfl (by decide)) (emptyHeads rfl)
    (oneHead (op := keySym) rfl (by decide))
  resultConstructors := oneHead (op := truthSym) rfl (by decide)
  observers := by
    intro t ht; change some t ∈ [none, some (.var observer), some (.var c), none] at ht
    simp at ht
    rcases ht with rfl | rfl
    · exact emptyHeads rfl
    · exact emptyHeads rfl
  containsApp := hasApp
  apart := inventories

private theorem capture_dep (i : Fin 3) (fixed : ¬ ∃ v, plan.hole v = some i)
    (v : Variable) (hv : (arg i).Occurs v) : v = c := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact False.elim (fixed ⟨cipher, rfl⟩)
  · change capture.Occurs v at hv
    simpa [capture, Pairing.occurs_pair, Term.Occurs] using hv
  · exact False.elim (fixed ⟨publicKey, rfl⟩)

private theorem separated : plan.Separated := by
  intro i fixed v hv; obtain rfl := capture_dep i fixed v hv; rfl

private theorem variants : CompleteVariants (ruleRoot rules) (packed.map plan.input)
    [plan.identityArm packed, plan.ruleArm packed] := by
  apply plan.raw_complete domain separated
  exact SpecializedRule.ground_at_head rules verifySym pat truth domain.apps (by simp [rules])
    (fun _ hr _ => List.mem_singleton.mp hr) plan.ground

-- Dropping the ground-RHS arm loses a legal capture. The shared caller
-- variable occurs twice in the signature payload and is separately observed.
example : ¬ CompleteVariants (ruleRoot rules) (packed.map plan.input) [plan.identityArm packed] := by
  intro only
  have hs := variants.1 (plan.ruleArm packed) (by simp)
  obtain ⟨a, ha, δ, _, _, vals⟩ := only.2 _ hs.1 _ hs.2
  obtain rfl := List.mem_singleton.mp ha
  exact nomatch vals.1.head_eq

-- Returning just the successful signature branch also loses the normal open application.
example : ¬ CompleteVariants (ruleRoot rules) (packed.map plan.input) [plan.ruleArm packed] := by
  intro only
  have hs := variants.1 (plan.identityArm packed) (by simp)
  obtain ⟨a, ha, δ, _, _, vals⟩ := only.2 _ hs.1 _ hs.2
  obtain rfl := List.mem_singleton.mp ha
  exact nomatch vals.1.head_eq

private def vs := (packed.map plan.input).flatMap Term.variables
private def avoid := [msg 25]
private def outputRename := FreshAnswer.freshPermutation vs avoid solution

private def noRename : VariablePermutation where
  forward := id
  backward := id
  support := []
  outside := by intros; rfl
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  sorted := fun _ => rfl

-- Check the exported mask and the fresh answer representation together. The
-- caller also reserves an unrelated name outside the packed query.
example : ∃ answers, plan.decode packed vs outputRename (Executable.groundVariant #[2,3] #[0] #[4,4] true) = some answers ∧
    plan.Admissible (ruleRoot rules) packed avoid answers ∧
    ∀ a ∈ answers, a.Reconstructible (ruleRoot rules) (packed.map plan.input) := by
  apply exportedGroundNarrowing_correct plan rules pat noRename packed domain (encode := fun v => UInt64.ofNat v.id)
  · simp [rules]
  · exact fun r hr _ => List.mem_singleton.mp hr
  · intro i; exact (Term.subst_id _).symm
  · intro v; simp [vs, Observed]
  · intro v hv w hw
    have hm : w ∈ FreshAnswer.rangeVariables vs solution :=
      List.mem_flatMap.mpr ⟨v, hv, (Term.mem_variables _ _).mpr hw⟩
    simpa only [outputRename, List.mem_append, or_comm] using FreshAnswer.renaming_avoids vs avoid solution w hm

  · simp [GroundVariantDecision.Admitted]
  · intro v i hi
    by_cases hc : v = cipher
    · subst v; decide
    · by_cases hk : v = publicKey
      · subst v; decide
      · simp [hole, hc, hk] at hi
  · intro i fixed v hv; obtain rfl := capture_dep i fixed v hv; decide

-- Capturing a hole would constrain its own solution. Repeated occurrences of
-- a fixed variable are admissible, but even one occurrence of a hole rejects.
example : Executable.groundVariant #[2,3] #[0] #[4,4,2] true = 0 := by
  apply (exportedGroundDecision_correct _ _ _ _).2.mpr
  simp [GroundVariantDecision.Admitted]

-- The caller's c and its two occurrences inside the returned signature
-- decode to one fresh variable, even with a different admissible permutation.
example (π : VariablePermutation) :
    let arm := SpecializedFresh.renameArm vs π (plan.ruleArm packed)
    arm.subst.image c = .var (π.forward c) ∧
      arm.subst.image cipher = pair (pair (.var (π.forward c)) (.var (π.forward c))) (.var (π.forward k)) ∧
      arm.subst.image observer = .var (π.forward observer) := by
  have atVar (v : Variable) (hm : v ∈ vs) :
      (SpecializedFresh.renameArm vs π (plan.ruleArm packed)).subst.image v =
        (π.subst signature).apply (solution.image v) :=
    (FreshAnswer.decode_encode_image vs solution π v).trans (ite_eq_left hm)
  constructor
  · exact atVar c (by decide)
  constructor
  · rw [atVar cipher (by decide)]
    simp [solution, Pairing.parameters, Substitution.apply, capture, Term.subst, VariablePermutation.subst]
  · exact atVar observer (by decide)

end Tamarin.Rewriting.GroundNarrowing.Tests
