import TamarinCI

namespace Tamarin.Rewriting.Tests
open Tamarin.Pairing

def a : PTerm := .atom (0, .pub)
def b : PTerm := .atom (1, .pub)
def c : PTerm := .atom (2, .pub)

-- Different arguments may rule out different equations with the same head.
#guard Executable.excludeRoot #[#[1, 0], #[0, 2]] #[2, 1]
#guard !Executable.excludeRoot #[#[1, 0], #[0, 2]] #[2, 2]
#guard !Executable.excludeRoot #[#[0, 0]] #[1, 2]
#guard !Executable.excludeRoot #[#[1]] #[2, 3]
#guard !Executable.excludeRoot #[#[]] #[]
#guard Executable.excludeRoot #[] #[]

-- In the YubiKey query [x, project(x), project(x)], one Maude variant
-- returns distinct factors at the two identical observations. Recomputing
-- the same normal result twice cannot reproduce such a tuple modulo B.
example {sig : Signature} (R : Root sig) (σ : Substitution sig) (x t anchor u v : Term sig)
    (hx : NormalForm R (σ.apply x) anchor) (hu : NormalForm R (σ.apply t) u)
    (distinct : ¬ EquivB u v) :
    ¬ (Variant.mk σ [anchor, u, v]).Reconstructible R [x, t, t] := by
  intro recover
  exact distinct (recover [anchor, u, u] ⟨hx, hu, hu, trivial⟩).2.2.1

-- Exhaustion preserves a partial result, never a false normal-form claim.
example (reduce : PTerm → Progress signature) (t : PTerm) :
    normalizeFuel reduce 0 t = .stopped .resourceLimit t := rfl

example (rank : PTerm → Nat) : ¬ Decreases (fun t => .next t) rank := by
  intro h
  exact Nat.lt_irrefl _ (h a)

example : ¬ (NormalizeResult.complete (fst (pair a b))).Correct root (fst (pair a b)) := by
  intro h
  exact h.2.1 a ⟨_, _, .refl _, .root ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩, .refl _⟩

-- Dropping a repeated component is rejected even if the substitution is valid.
example : ¬ (Variant.mk Substitution.identity [a]).Sound root [a, a] := by
  intro h
  exact h.2.2

-- B rearrangement can expose a rewrite across the original child boundaries.
def joinedRoot (t u : PTerm) : Prop := t = .ac 0 a b ∧ u = c
example : ¬ Normal joinedRoot (.ac 0 a (.ac 0 b c)) := by
  intro h
  apply h (.ac 0 c c)
  exact ⟨.ac 0 (.ac 0 a b) c, _, (EquivB.ac_assoc (sig := signature) 0 a b c).symm,
    Step.ac_left (sig := signature) (root := joinedRoot) 0 c (.root ⟨rfl, rfl⟩), .refl _⟩

-- New symbols do not need name-specific normalization/variant proofs.
def wrap (t : PTerm) : PTerm := .free (.other 42 1) (fun _ => t)
example : NormalForm root (wrap (fst (pair (.comm 7 a b) c))) (wrap (.comm 7 a b)) :=
  normalize_normalForm _

example : CompleteVariants root [wrap (.ac 13 (.var ⟨0, .msg⟩) a)]
    [referenceVariant [wrap (.ac 13 (.var ⟨0, .msg⟩) a)] Substitution.identity] := by
  apply variants_refine (answers := [Substitution.identity])
  apply constructor_variants_complete
  intro t ht
  have he := List.mem_singleton.mp ht; subst t
  exact .other 42 1 _ (fun _ => .ac 13 (.var _) (.atom _))

example : ruleRoot rules (fst (pair a b)) a :=
  (root_iff_ruleRoot (HasSort.free (sig := signature) .fst _
    (fun _ => pair_sorted (.widen (.atom _) .pub_msg) (.widen (.atom _) .pub_msg)))).mp
    ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩

-- fst(x) is already normal. Returning only its identity variant still loses
-- the solution where x becomes a pair and the first component is returned.
example (x l r : Variable) (hx : x.sort = .msg) (hl : l.sort = .msg) (hr : r.sort = .msg) :
    ¬ Rewriting.CompleteVariants root [fst (.var x)]
      [⟨Substitution.identity, [fst (.var x)]⟩] := by
  intro h
  let ρ := splitSubst x l r hx hl hr
  have hn : Rewriting.Normalized root ρ := fun v =>
    (normal_iff_rewriting _).mp (split_normalized x l r hx hl hr v)
  have image : ρ.image x = pair (.var l) (.var r) := Substitution.binding_image_self ..
  have nf : NormalForm root (ρ.apply (fst (.var x))) (.var l) := by
    have := normalize_normalForm (ρ.apply (fst (.var x)))
    change NormalForm root _ (project true (normalize (ρ.image x))) at this
    rw [image] at this
    exact this
  obtain ⟨answer, ha, δ, _, _, values⟩ := h.2 ρ hn [.var l] ⟨nf, trivial⟩
  obtain rfl := List.mem_singleton.mp ha
  exact nomatch values.1.head_eq

end Tamarin.Rewriting.Tests
