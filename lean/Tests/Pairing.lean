import TamarinCI

namespace Tamarin.Pairing.Tests
open Tamarin.Pairing

def x : Variable := ⟨0, .msg⟩
def a : PTerm := .atom (0, .pub)
def b : PTerm := .atom (1, .pub)
def query : List PTerm := [.var x, fst (.var x), fst (.var x)]

def witness : PSubst := Substitution.binding x (pair a b)
  (pair_sorted (.widen (.atom _) .pub_msg) (.widen (.atom _) .pub_msg))

theorem witness_normal : Normalized witness := by
  intro v
  change Normal (if v = x then pair a b else .var v)
  by_cases he : v = x
  · subst v; simp only [↓reduceIte]; exact .pair (.atom _) (.atom _)
  · simp only [he, ↓reduceIte]; exact .var _

/-- A mutation that drops the pair branch cannot pass semantic completeness.
The repeated projection is part of one correlated packed query. -/
theorem identity_only_incomplete : ¬ CompleteVariants query [Substitution.identity] := by
  intro h
  obtain ⟨σ, hσ, δ, _, hagree, hvalue⟩ := h.2 witness witness_normal
  have := List.mem_singleton.mp hσ; subst σ
  have hx := hagree x ⟨.var x, by simp [query], rfl⟩
  have hv := hvalue (fst (.var x)) (by simp [query])
  change pair a b = δ.image x at hx
  simp only [Substitution.apply_identity] at hv
  change a = fst (δ.image x) at hv
  rw [← hx] at hv
  cases hv

example : normalize (fst (pair (snd (pair a b)) a)) = b := rfl
example : ¬ Reduces (pair (fst (.var x)) (snd (.var x))) (.var x) := by
  intro h
  have he := reduces_normalize h
  cases he

def union (a b : PTerm) : PTerm := .ac 0 a b

/-- Constructor variants include repeated input variables under union. -/
example : CompleteVariants [.var x, union (.var x) a, pair a (union (.var x) b)]
    [Substitution.identity] := by
  apply constructor_variants_complete
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact .var _
  · exact .ac 0 (.var _) (.atom _)
  · exact .pair (.atom _) (.ac 0 (.var _) (.atom _))

/-- AC rearrangement below a projection preserves its selected normal form. -/
example : EquivB (normalize (fst (pair (union a b) b)))
    (normalize (fst (pair (union b a) b))) :=
  EquivB.ac_swap (sig := signature) 0 a b

example : ReducesModulo (fst (pair (union a b) b)) (union b a) :=
  .trans (.rewrite (.fst _ _)) (.basis (EquivB.ac_swap (sig := signature) 0 a b))

example : Normal (fst (union (.var x) a)) :=
  .fst (.ac 0 (.var _) (.atom _)) (by intro args h; cases h)

/-- Reflexivity covers nonground substitutions and shared variables across
multiple equations with a single identity answer. -/
example : CompleteSet ([⟨union (.var x) a, union (.var x) a⟩,
    ⟨union (.var x) b, union (.var x) b⟩] : Problem signature)
    [Substitution.identity] := by
  apply Reflexive.identity_complete
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

/-- The combined theory does not silently add multiset idempotence. -/
example : ¬ ReducesModulo (union a a) a := by
  intro h
  have he := reducesModulo_normalize h
  have hw := he.eval_eq (weightModel signature) (fun _ => 1)
  simp [Model.eval, weightModel, union, a, normalize] at hw

/-- Completing a reflexive problem with no answers would be unsound. -/
example : ¬ CompleteSet ([⟨union (.var x) a, union (.var x) a⟩] : Problem signature) [] := by
  rw [complete_empty_iff]
  intro h
  apply h
  refine ⟨Substitution.identity, ?_⟩
  intro e he
  have := List.mem_singleton.mp he; subst e
  exact .refl _

end Tamarin.Pairing.Tests
