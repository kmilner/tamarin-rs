import Tamarin.ACBasisAnswers
import TamarinRuntime.Homogeneous

/-! Completeness of witness-bearing answers for simultaneous single-symbol
AC equations. A generator gets one shared parameter. Its instantiation is
the product of the factors whose decompositions use that generator. -/
namespace Tamarin.ACSystem
open Cancellation
variable {sig : Signature}

private theorem factor_atom (f : sig.ACSym) (t : Term sig) (ht : HasSort t (sig.acSort f))
    (a : Class sig) (ha : a ∈ flatten f t) :
    ∃ u : Term sig, HasSort u (sig.acSort f) ∧ flatten f u = [a] := by
  classical
  induction t with
  | ac g x y ix iy =>
    by_cases h : f = g
    · subst g
      have hc := Term.checkSort_complete ht
      simp only [Term.checkSort, Bool.and_eq_true] at hc
      rcases List.mem_append.mp (flatten_ac f x y ▸ ha) with hx | hy
      · exact ix (Term.checkSort_sound _ _ hc.1.2) hx
      · exact iy (Term.checkSort_sound _ _ hc.2) hy
    · simp only [flatten, ite_eq_right h, List.mem_singleton] at ha
      exact ⟨_, ht, by simp [flatten, h, ha]⟩
  | var | atom | free | comm =>
    exact ⟨_, ht, by rw [List.mem_singleton.mp ha]; rfl⟩

private theorem realize (f : sig.ACSym) (xs : List (Class sig)) (hne : xs ≠ [])
    (atom : ∀ a ∈ xs, ∃ t : Term sig, HasSort t (sig.acSort f) ∧ flatten f t = [a]) :
    ∃ t : Term sig, HasSort t (sig.acSort f) ∧ flatten f t = xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    obtain ⟨t,ht,et⟩ := atom a (by simp)
    by_cases h : xs = []
    · exact ⟨t,ht,by simpa [h] using et⟩
    · obtain ⟨u,hu,eu⟩ := ih h (fun b hb => atom b (List.mem_cons_of_mem _ hb))
      exact ⟨.ac f t u,.ac _ _ _ ht hu,by rw [flatten_ac,et,eu]; rfl⟩

private def expand {α β : Type} (xs : List α) (weight : α → Nat) (value : α → List β) :=
  xs.flatMap fun j => (List.replicate (weight j) (value j)).flatten

private theorem count_expand {α β : Type} [DecidableEq β] (xs : List α) (w : α → Nat)
    (v : α → List β) (a : β) :
    (expand xs w v).count a = (xs.map fun j => w j * (v j).count a).sum := by
  have rep (n : Nat) (ys : List β) :
      ((List.replicate n ys).flatten).count a = n * ys.count a := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
  induction xs with
  | nil => rfl
  | cons j js ih => simp only [expand, List.flatMap_cons, List.count_append, rep,
      List.map_cons, List.sum_cons] at *; rw [ih]

private theorem expand_active {α β : Type} (xs : List α) (w : α → Nat) (v : α → List β) :
    expand (xs.filter fun j => !(v j).isEmpty) w v = expand xs w v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold expand at ih ⊢
    cases h : v x <;> simp [h, ih]

private theorem parts_count {α : Type} [DecidableEq α] (ats : List α) (unique : ats.Nodup)
    (c : α → Nat) (a : α) :
    (ats.flatMap fun b => List.replicate (c b) b).count a = if a ∈ ats then c a else 0 := by
  induction ats with
  | nil => simp
  | cons b bs ih =>
    have ⟨hn,hd⟩ := List.nodup_cons.mp unique
    by_cases he : a = b
    · subst b; simp [List.count_append, ih hd, hn]
    · simp [List.count_append, List.count_replicate, ih hd, beq_iff_eq, he, Ne.symm he]

/-- Any subset of the ordered generator table obtained by filtering occurs
in the executable powerset enumeration. -/
theorem filter_mem_sublists {α : Type} (xs : List α) (q : α → Bool) :
    xs.filter q ∈ FlatMatchSearch.sublists xs := by
  induction xs with
  | nil => simp [FlatMatchSearch.sublists]
  | cons x xs ih => cases h : q x <;> simp [h, FlatMatchSearch.sublists, ih]

/-- Tables in the semantic interpretation can use arbitrary names. The
executable only knows coordinate and generator indices. -/
structure Frame (f : sig.ACSym) (rows : List Row) (n : Nat) where
  names : Fin n → Variable
  index : Variable → Option (Fin n)
  inverse : ∀ i, index (names i) = some i
  live : ∀ v ∈ variables rows, ∃ i, names i = v
  used : ∀ i, names i ∈ variables rows
  sorts : ∀ i, (names i).sort = sig.acSort f

namespace Frame
variable {f : sig.ACSym} {rows : List Row} {n : Nat} (fr : Frame f rows n)
include fr

theorem injective : Function.Injective fr.names := fun i k h => Option.some.inj
  ((fr.inverse i).symm.trans ((congrArg fr.index h).trans (fr.inverse k)))

private theorem sort_of_mem (v : Variable) (hv : v ∈ variables rows) : v.sort = sig.acSort f := by
  obtain ⟨i,rfl⟩ := fr.live v hv
  exact fr.sorts i

end Frame

private theorem expand_slots {α : Type} (js : List α) (column : α → Column) (witness : α → Variable)
    (v : Variable) (parts : Variable → List (Class sig)) :
    (slots (js.map fun j => (witness j, column j)) v).flatMap parts =
      expand js (fun j => column j v) (fun j => parts (witness j)) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [slots, expand, List.map_cons, List.flatMap_cons, List.flatMap_append] at *
    rw [ih]
    simp [List.flatMap_def]

private theorem instantiate_image {f : sig.ACSym} {rows avoid} (b : Branch f rows avoid)
    (δ : Substitution sig) (v : Variable) (hv : v ∈ variables rows) :
    flatten f (δ.apply (b.answer.image v)) = (slots b.active v).flatMap (fun w => flatten f (δ.image w)) := by
  change flatten f (δ.apply (b.image v)) = _
  rw [Branch.image, ite_eq_left hv]
  cases e : slots b.active v with
  | nil => exact False.elim (b.nonempty v hv e)
  | cons x xs =>
    exact flatten_side f ⟨x,xs⟩ δ

/-- A sorted solution factors through one covering subset, using a single
instantiating substitution even when different input variables share factors. -/
theorem factor_through_subset {n} (f : sig.ACSym) (rows : List Row) (avoid : List Variable)
    (fr : Frame f rows n) (gs : List (ACBasis.Vec n))
    (basis : ACBasis.BasisCorrect (rows.map (ACBasis.encode fr.names)) gs)
    (w : Fin gs.length → Variable) (inj : Function.Injective w)
    (typed : ∀ j, (w j).sort = sig.acSort f) (fresh : ∀ j, w j ∉ variables rows ++ avoid)
    (ρ : Substitution sig) (sol : (problem f rows).Solves ρ) :
    ∃ js ∈ FlatMatchSearch.sublists (List.finRange gs.length),
      ∃ cover : ∀ i, ∃ j ∈ js, 0 < gs.get j i,
      Substitution.InstanceOn (problem f rows).Occurs ρ
        (branchFromBasis f rows avoid fr.names fr.index fr.inverse fr.live gs basis js w
          (fun j _ => typed j) (fun j _ => fresh j) cover
          (fun v hv => (fr.sort_of_mem v hv) ▸ Subsort.refl _)).answer := by
  classical
  have dedup (xs : List (Class sig)) : ∃ ys : List (Class sig), ys.Nodup ∧ ∀ a, a ∈ ys ↔ a ∈ xs := by
    induction xs with
    | nil => exact ⟨[], by simp, fun _ => Iff.rfl⟩
    | cons x xs ih =>
      obtain ⟨ys,hd,hm⟩ := ih
      by_cases hx : x ∈ ys
      · exact ⟨ys,hd,fun a => by simp [← hm]; grind⟩
      · exact ⟨x::ys,List.nodup_cons.mpr ⟨hx,hd⟩,fun a => by simp [hm]⟩
  obtain ⟨ats,distinct,present⟩ := dedup (factors f rows ρ)
  have generates := (ACBasis.solves_iff_generates f fr.names fr.injective rows fr.live gs basis ρ).mp sol
  let co (a : Class sig) : ACBasis.Vec gs.length :=
    if ha : a ∈ ats then Classical.choose
      (generates a ((present a).mp ha))
    else fun _ => 0
  let block (j : Fin gs.length) := ats.flatMap fun a => List.replicate (co a j) a
  let all := List.finRange gs.length
  let js := all.filter fun j => !(block j).isEmpty
  have count (a : Class sig) (j) : (block j).count a = co a j := by
    dsimp only [block]; rw [parts_count _ distinct]; split
    · rfl
    · next h => simp [co,h]
  have factors_eq (i : Fin n) :
      (expand js (fun j => gs.get j i) block).Perm (flatten f (ρ.image (fr.names i))) := by
    dsimp only [js]; rw [expand_active, List.perm_iff_count]
    intro a
    rw [count_expand]
    simp only [count]
    simp only [all, List.finRange, List.map_ofFn, Function.comp_def]
    change ACBasis.mix gs.get (co a) i = factorColumn f ρ a (fr.names i)
    by_cases ha : a ∈ ats
    · dsimp only [co]; rw [dite_eq_left ha]
      exact congrFun (Classical.choose_spec (generates a ((present a).mp ha))) i
    · have zero : a ∉ flatten f (ρ.image (fr.names i)) := fun h => ha ((present a).mpr
        (List.mem_flatMap.mpr ⟨_,fr.used i,h⟩))
      simp [co,ha,ACBasis.mix,ACBasis.dot,ACBasis.total,factorColumn,List.count_eq_zero.mpr zero, List.sum_eq_zero_iff_forall_eq_nat]
  have cover (i) : ∃ j ∈ js, 0 < gs.get j i := by
    apply Classical.byContradiction
    intro h
    have zero (j) (hj : j ∈ js) : gs.get j i = 0 := by
      have hn : ¬ 0 < gs.get j i := fun hp => h ⟨j,hj,hp⟩
      omega
    have nil : expand js (fun j => gs.get j i) block = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro j hj; simp [zero j hj]
    have absurd := fold_flatten f (ρ.image (fr.names i))
    have perm := factors_eq i
    rw [nil] at perm
    rw [perm.symm.eq_nil] at absurd
    cases absurd
  refine ⟨js, filter_mem_sublists .., cover, ?_⟩
  have realized (j) (hj : j ∈ js) :
      ∃ t : Term sig, HasSort t (sig.acSort f) ∧ flatten f t = block j := by
    apply realize
    · intro h; simpa [js,h] using (List.mem_filter.mp hj).2
    · intro a ha
      obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp ha
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hm
      obtain ⟨v,hv,ht⟩ := List.mem_flatMap.mp ((present a).mp hb)
      exact factor_atom f _ ((fr.sort_of_mem v hv) ▸ ρ.sorted v) a ht
  let lookup (v : Variable) := ∃ j ∈ js, w j = v
  let image (v : Variable) : Term sig := if h : lookup v then
    Classical.choose (realized h.choose h.choose_spec.1) else .var v
  let δ : Substitution sig := {
    image := image, support := js.map w
    outside := by intro v hv; apply dite_eq_right; rintro ⟨j,hj,rfl⟩; exact hv (List.mem_map_of_mem hj)
    sorted := by
      intro v; dsimp only [image]; split
      · next h =>
        have hs : v.sort = sig.acSort f := (congrArg Variable.sort h.choose_spec.2).symm.trans (typed _)
        rw [hs]
        exact (Classical.choose_spec (realized h.choose h.choose_spec.1)).1
      · exact .var _ }
  have inst (j) (hj : j ∈ js) : flatten f (δ.image (w j)) = block j := by
    have h : lookup (w j) := ⟨j,hj,rfl⟩
    change flatten f (image _) = _
    dsimp only [image]; rw [dite_eq_left h, (Classical.choose_spec (realized h.choose h.choose_spec.1)).2, inj h.choose_spec.2]
  refine ⟨δ, fun v hv => ?_⟩
  have hv := (occurs_iff_mem f rows v).mp hv
  obtain ⟨i,rfl⟩ := fr.live v hv
  apply equiv_of_flatten_perm f
  change (flatten f _).Perm (flatten f (δ.apply _))
  rw [instantiate_image _ _ _ hv]
  change (flatten f _).Perm ((slots (js.map _) (fr.names i)).flatMap _)
  rw [expand_slots]
  apply (factors_eq i).symm.trans
  apply List.Perm.of_eq
  unfold expand
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  simp [fr.inverse, inst j hj]

/-- Reify a covering subset. Each occurrence of a generator shares its witness
across all images. The index table can be supplied independently by the caller. -/
def selectedBranch {n} {f : sig.ACSym} {rows : List Row} {avoid : List Variable}
    (fr : Frame f rows n) (gs : List (ACBasis.Vec n))
    (basis : ACBasis.BasisCorrect (rows.map (ACBasis.encode fr.names)) gs)
    (w : Fin gs.length → Variable) (typed : ∀ j, (w j).sort = sig.acSort f)
    (fresh : ∀ j, w j ∉ variables rows ++ avoid)
    (js : {l // l ∈ Homogeneous.selections gs}) : Branch f rows avoid :=
  branchFromBasis f rows avoid fr.names fr.index fr.inverse fr.live gs basis js.val w
    (fun j _ => typed j) (fun j _ => fresh j) (of_decide_eq_true (List.mem_filter.mp js.property).2)
    (fun v hv => (fr.sort_of_mem v hv) ▸ Subsort.refl _)

/-- Complete witness-bearing answers for an arbitrary finite basis. The
mathematical theorem has no bound on dimensions, coefficients or output. -/
theorem basis_answers_correct {n} {f : sig.ACSym} {rows : List Row} {avoid : List Variable}
    (fr : Frame f rows n) (gs : List (ACBasis.Vec n))
    (basis : ACBasis.BasisCorrect (rows.map (ACBasis.encode fr.names)) gs)
    (w : Fin gs.length → Variable) (inj : Function.Injective w)
    (typed : ∀ j, (w j).sort = sig.acSort f) (fresh : ∀ j, w j ∉ variables rows ++ avoid) :
    (Outcome.complete ((Homogeneous.selections gs).attach.map fun js =>
      (selectedBranch fr gs basis w typed fresh js).answer)).CorrectIn (problem f rows) avoid := by
  let make := selectedBranch fr gs basis w typed fresh
  constructor
  · constructor
    · intro σ hm; obtain ⟨js,_,rfl⟩ := List.mem_map.mp hm; exact (make js).sound
    · intro ρ hρ
      obtain ⟨js,hm,hcov,hi⟩ := factor_through_subset f rows avoid fr gs basis w inj typed fresh ρ hρ
      have hj : js ∈ Homogeneous.selections gs := List.mem_filter.mpr ⟨hm, decide_eq_true hcov⟩
      exact ⟨(make ⟨js,hj⟩).answer,List.mem_map_of_mem (List.mem_attach ..),hi⟩
  · intro σ hm; obtain ⟨js,_,rfl⟩ := List.mem_map.mp hm; exact (make js).domain
  · intro σ hm; obtain ⟨js,_,rfl⟩ := List.mem_map.mp hm; exact (make js).freshFor

end Tamarin.ACSystem
