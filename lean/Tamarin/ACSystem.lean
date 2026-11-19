import Tamarin.ACResidual

/-!
# Simultaneous homogeneous AC equations

The coordinates of a column are shared variable identities. A row counts the
same coordinate once per occurrence on each side. Each distinct factor class
in a substitution supplies one column for the entire system. This works for
open images and alien subterms because factors are compared modulo B.
-/
namespace Tamarin.ACSystem
open Cancellation
variable {sig : Signature}

/-- A side always denotes a term: an AC semigroup has no empty product. -/
structure Side where
  first : Variable
  rest : List Variable

def Side.vars (side : Side) := side.first :: side.rest

def Side.term (side : Side) (f : sig.ACSym) : Term sig :=
  ACRepresentation.fold f (.var side.first) (side.rest.map Term.var)

abbrev Column := Variable → Nat

def Side.weight (side : Side) (column : Column) : Nat :=
  (side.vars.map column).sum

structure Row where
  lhs : Side
  rhs : Side

def Row.equation (row : Row) (f : sig.ACSym) : Equation sig :=
  ⟨row.lhs.term f, row.rhs.term f⟩

def problem (f : sig.ACSym) (rows : List Row) : Problem sig :=
  rows.map (·.equation f)

def Balanced (rows : List Row) (column : Column) : Prop :=
  ∀ row ∈ rows, row.lhs.weight column = row.rhs.weight column

noncomputable def factorColumn (f : sig.ACSym) (σ : Substitution sig)
    (a : Class sig) : Column := by
  classical
  exact fun v => (flatten f (σ.image v)).count a

theorem flatten_side (f : sig.ACSym) (side : Side) (σ : Substitution sig) :
    flatten f (σ.apply (side.term f)) =
      side.vars.flatMap (fun v => flatten f (σ.image v)) := by
  obtain ⟨x, xs⟩ := side
  induction xs generalizing x with
  | nil => simp [Side.term, Side.vars, ACRepresentation.fold, Substitution.apply, Term.subst]
  | cons y ys ih =>
    change flatten f (.ac f (σ.image x) (σ.apply ((Side.mk y ys).term f))) = _
    rw [flatten_ac, ih]
    rfl

private theorem count_flatMap {α β} [DecidableEq β] (xs : List α) (g : α → List β) (a : β) :
    (xs.flatMap g).count a = (xs.map (fun x => (g x).count a)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.count_append, ih]

theorem row_iff (f : sig.ACSym) (row : Row) (σ : Substitution sig) :
    EquivB (σ.apply (row.lhs.term f)) (σ.apply (row.rhs.term f)) ↔
      ∀ a, row.lhs.weight (factorColumn f σ a) = row.rhs.weight (factorColumn f σ a) := by
  classical
  have hp := fun side => flatten_side f side σ
  rw [show EquivB (σ.apply (row.lhs.term f)) (σ.apply (row.rhs.term f)) ↔
    (flatten f (σ.apply (row.lhs.term f))).Perm (flatten f (σ.apply (row.rhs.term f))) from
      ⟨flatten_equiv f, equiv_of_flatten_perm f⟩, hp, hp, List.perm_iff_count]
  simp only [count_flatMap, Side.weight]
  rfl

/-- Repeated variables, repeated equations and shared variables between
rows are all interpreted by one sorted substitution. -/
theorem solves_iff (f : sig.ACSym) (rows : List Row) (σ : Substitution sig) :
    (problem f rows).Solves σ ↔ ∀ a, Balanced rows (factorColumn f σ a) := by
  constructor
  · intro sol a row hr
    exact (row_iff f row σ).mp (sol _ (List.mem_map_of_mem hr)) a
  · intro columns equation he
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp he
    exact (row_iff f row σ).mpr (fun a => columns a row hr)

def variables (rows : List Row) := rows.flatMap (fun row => row.lhs.vars ++ row.rhs.vars)

noncomputable def factors (f : sig.ACSym) (rows : List Row) (σ : Substitution sig) :=
  (variables rows).flatMap (fun v => flatten f (σ.image v))

private theorem weight_zero (side : Side) (column : Column)
    (h : ∀ v ∈ side.vars, column v = 0) : side.weight column = 0 := by
  unfold Side.weight
  generalize he : side.vars = xs at *
  clear he
  induction xs with
  | nil => rfl
  | cons v xs ih => simp [h v (by simp), ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

/-- The support can be enumerated from the input variables' images. Classes
outside this finite list give the zero vector at every observed coordinate. -/
theorem solves_iff_finite (f : sig.ACSym) (rows : List Row) (σ : Substitution sig) :
    (problem f rows).Solves σ ↔ ∀ a ∈ factors f rows σ, Balanced rows (factorColumn f σ a) := by
  classical
  rw [solves_iff]
  refine ⟨fun h a _ => h a, fun h a => ?_⟩
  by_cases present : a ∈ factors f rows σ
  · exact h a present
  · intro row hr
    have zero (v : Variable) (hv : v ∈ row.lhs.vars ++ row.rhs.vars) :
        factorColumn f σ a v = 0 :=
      List.count_eq_zero.mpr (fun hm => present <| List.mem_flatMap.mpr
        ⟨v, List.mem_flatMap.mpr ⟨row, hr, hv⟩, hm⟩)
    rw [weight_zero _ _ (fun v hv => zero v (List.mem_append_left _ hv)),
      weight_zero _ _ (fun v hv => zero v (List.mem_append_right _ hv))]

theorem side_hasSort (f : sig.ACSym) (side : Side)
    (typed : ∀ v ∈ side.vars, Subsort v.sort (sig.acSort f)) :
    HasSort (side.term f) (sig.acSort f) := by
  apply ACRepresentation.fold_hasSort
  · exact .widen (.var _) (typed _ (List.mem_cons_self ..))
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    exact .widen (.var _) (typed _ (List.mem_cons_of_mem _ hv))

theorem wellFormed (f : sig.ACSym) (rows : List Row)
    (typed : ∀ v ∈ variables rows, Subsort v.sort (sig.acSort f)) :
    (problem f rows).WellFormed := by
  intro e he
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp he
  exact ⟨⟨_, side_hasSort f _ (fun v hv => typed v <|
    List.mem_flatMap.mpr ⟨row, hr, List.mem_append_left _ hv⟩)⟩,
    ⟨_, side_hasSort f _ (fun v hv => typed v <|
    List.mem_flatMap.mpr ⟨row, hr, List.mem_append_right _ hv⟩)⟩⟩

/-- Each entry gives a nonnegative coefficient for a generator column. -/
def combination : List (Nat × Column) → Column
  | [] => fun _ => 0
  | (n, c) :: more => fun v => n * c v + combination more v

private theorem weight_linear (side : Side) (n : Nat) (a b : Column) :
    side.weight (fun v => n * a v + b v) = n * side.weight a + side.weight b := by
  unfold Side.weight
  induction side.vars with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
    omega

/-- No enumeration order or minimality requirement enters the kernel. -/
theorem balanced_combination (rows : List Row) (terms : List (Nat × Column))
    (valid : ∀ t ∈ terms, Balanced rows t.2) : Balanced rows (combination terms) := by
  induction terms with
  | nil => intro row _; rw [weight_zero, weight_zero] <;> intros <;> rfl
  | cons t ts ih =>
    obtain ⟨n,c⟩ := t
    intro row hr
    simp only [combination, weight_linear, valid (n,c) (by simp) row hr,
      ih (fun t ht => valid t (List.mem_cons_of_mem _ ht)) row hr]

/-- Multiplicities summed over all factor classes must give a positive
solution at every input coordinate. Thus ruling out all positive solutions
proves unsatisfiability, even for variables with narrower sorts. -/
theorem positive_of_solution (f : sig.ACSym) (rows : List Row) (σ : Substitution sig)
    (sol : (problem f rows).Solves σ) :
    ∃ c : Column, Balanced rows c ∧ ∀ v ∈ variables rows, 0 < c v := by
  let c := fun v => (flatten f (σ.image v)).length
  refine ⟨c, ?_, ?_⟩
  · intro row hr
    have he := flatten_equiv f (sol (row.equation f) (List.mem_map_of_mem hr))
    change (flatten f (σ.apply (row.lhs.term f))).Perm (flatten f (σ.apply (row.rhs.term f))) at he
    rw [flatten_side, flatten_side] at he
    simpa [Side.weight, List.length_flatMap, c, Function.comp_def] using he.length_eq
  · intro v _
    apply List.length_pos_iff.mpr
    intro hz
    have h := fold_flatten f (σ.image v)
    rw [hz] at h
    cases h

private def power (f : sig.ACSym) (w : Variable) : Nat → Term sig
  | 0 => .var w
  | n + 1 => .ac f (.var w) (power f w n)

private theorem power_sort (f : sig.ACSym) (w : Variable) (hw : w.sort = sig.acSort f) (n : Nat) :
    HasSort (power f w n) (sig.acSort f) := by
  have hv : HasSort (.var w : Term sig) (sig.acSort f) := hw ▸ HasSort.var w
  induction n with
  | zero => exact hv
  | succ n ih => exact .ac _ _ _ hv ih

private theorem flatten_power (f : sig.ACSym) (w : Variable) (n : Nat) :
    flatten f (power f w n) = List.replicate (n+1) (classOf (.var w)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [power, flatten_ac, ih, List.replicate_succ]; rfl

/-- With result-sort variables every positive balanced column is realizable:
use a product of that many copies of one common witness as each image. -/
theorem satisfiable_iff_positive (f : sig.ACSym) (rows : List Row)
    (sorts : ∀ v ∈ variables rows, Subsort (sig.acSort f) v.sort) :
    (problem f rows).Satisfiable ↔
      ∃ c : Column, Balanced rows c ∧ ∀ v ∈ variables rows, 0 < c v := by
  classical
  refine ⟨fun ⟨σ, hσ⟩ => positive_of_solution f rows σ hσ, ?_⟩
  rintro ⟨c, hc, pos⟩
  let w : Variable := ⟨0, sig.acSort f⟩
  let σ : Substitution sig := {
    image := fun v => if v ∈ variables rows then power f w (c v - 1) else .var v
    support := variables rows
    outside := by intro v hv; simp [hv]
    sorted := by
      intro v; split
      · next h => exact .widen (power_sort f w rfl _) (sorts v h)
      · exact .var _ }
  refine ⟨σ, (solves_iff f rows σ).mpr ?_⟩
  intro a row hr
  have count (v : Variable) (hv : v ∈ variables rows) :
      factorColumn f σ a v = if classOf (.var w : Term sig) = a then c v else 0 := by
    have hn : c v - 1 + 1 = c v := by have := pos v hv; omega
    change (flatten f (if v ∈ variables rows then power f w (c v - 1) else .var v)).count a = _
    simp only [ite_eq_left hv, flatten_power, hn, List.count_replicate, beq_iff_eq]
  have eq (side : Side) (hs : ∀ v ∈ side.vars, v ∈ variables rows) :
      side.weight (factorColumn f σ a) = if classOf (.var w : Term sig) = a then side.weight c else 0 := by
    split
    · next he =>
        apply congrArg List.sum
        exact List.map_congr_left (fun v hv => (count v (hs v hv)).trans (ite_eq_left he))
    · next he => exact weight_zero _ _ (fun v hv => (count v (hs v hv)).trans (ite_eq_right he))
  rw [eq row.lhs (fun v hv => List.mem_flatMap.mpr ⟨row, hr, List.mem_append_left _ hv⟩),
    eq row.rhs (fun v hv => List.mem_flatMap.mpr ⟨row, hr, List.mem_append_right _ hv⟩), hc row hr]

end Tamarin.ACSystem
