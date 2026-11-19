import Tamarin.ACBasis

/-! Reify an active subset of balanced generator columns as an ordinary
substitution. Each column has one witness shared by all its coordinates. -/
namespace Tamarin.ACSystem
open Cancellation
variable {sig : Signature}

theorem Side.occurs_iff (s : Side) (f : sig.ACSym) (v : Variable) :
    (s.term f).Occurs v ↔ v ∈ s.vars := by
  obtain ⟨x,xs⟩ := s
  induction xs generalizing x with
  | nil => simp [Side.term, Side.vars, ACRepresentation.fold, Term.Occurs]
  | cons y ys ih =>
    change (v = x ∨ ((Side.mk y ys).term f).Occurs v) ↔ v ∈ x :: y :: ys
    rw [ih]
    simp [Side.vars]

theorem occurs_iff_mem (f : sig.ACSym) (rows : List Row) (v : Variable) :
    (problem f rows).Occurs v ↔ v ∈ variables rows := by
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_append.mpr
      (hv.imp (r.lhs.occurs_iff f v).mp (r.rhs.occurs_iff f v).mp)⟩
  · intro h
    obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp h
    exact ⟨r.equation f, List.mem_map_of_mem hr, (List.mem_append.mp hv).imp
      (r.lhs.occurs_iff f v).mpr (r.rhs.occurs_iff f v).mpr⟩

abbrev Generator := Variable × Column

def slots (active : List Generator) (v : Variable) : List Variable :=
  active.flatMap fun (w,c) => List.replicate (c v) w

structure Branch (f : sig.ACSym) (rows : List Row) (avoid : List Variable) where
  active : List Generator
  balanced : ∀ g ∈ active, Balanced rows g.2
  witnessSort : ∀ g ∈ active, g.1.sort = sig.acSort f
  fresh : ∀ g ∈ active, g.1 ∉ variables rows ++ avoid
  nonempty : ∀ v ∈ variables rows, slots active v ≠ []
  acceptsSort : ∀ v ∈ variables rows, Subsort (sig.acSort f) v.sort

namespace Branch
variable {f : sig.ACSym} {rows : List Row} {avoid : List Variable} (b : Branch f rows avoid)

def image (v : Variable) : Term sig :=
  if v ∈ variables rows then
    match slots b.active v with
    | [] => .var v
    | w :: ws => (Side.mk w ws).term f
  else .var v

private theorem slot_source (v : Variable) {w : Variable} (hw : w ∈ slots b.active v) :
    ∃ g ∈ b.active, w = g.1 := by
  obtain ⟨g,hg,hm⟩ := List.mem_flatMap.mp hw
  exact ⟨g,hg,(List.mem_replicate.mp hm).2⟩

theorem image_sort (v : Variable) : HasSort (b.image v) v.sort := by
  unfold image
  split
  · rename_i hv
    split
    · exact .var _
    · next w ws h =>
      apply HasSort.widen _ (b.acceptsSort v hv)
      apply side_hasSort
      intro u hu
      obtain ⟨g,hg,rfl⟩ := b.slot_source v (by rw [h]; exact hu)
      rw [b.witnessSort g hg]
      exact .refl _
  · exact .var _

def answer : Substitution sig where
  image := b.image
  support := variables rows
  outside := fun v hv => by simp [image, hv]
  sorted := b.image_sort

private theorem flat_slots (w : Variable) (ws : List Variable) :
    flatten (sig := sig) f ((Side.mk w ws).term f) = (w :: ws).map (fun u => classOf (.var u)) := by
  induction ws generalizing w with
  | nil => rfl
  | cons u us ih =>
    change flatten f (.ac f (.var w) ((Side.mk u us).term f)) = _
    rw [flatten_ac, ih]
    rfl

private theorem factors_image (v : Variable) (hv : v ∈ variables rows) :
    flatten f (b.answer.image v) = (slots b.active v).map (fun u => classOf (.var u)) := by
  change flatten f (b.image v) = _
  rw [image, ite_eq_left hv]
  cases he : slots b.active v with
  | nil => exact False.elim (b.nonempty v hv he)
  | cons w ws => exact flat_slots w ws

private theorem counts (gs : List Generator) (a : Class sig) (v : Variable) [DecidableEq (Class sig)] :
    ((slots gs v).map (fun u => classOf (.var u : Term sig))).count a =
      combination (gs.map fun (w,c) => (if classOf (.var w : Term sig) = a then 1 else 0, c)) v := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨w,c⟩ := g
    simp only [slots, List.flatMap_cons, List.map_append, List.map_replicate, List.count_append,
      List.count_replicate, beq_iff_eq, List.map_cons, combination] at *
    split <;> simp_all

theorem sound : (problem f rows).Solves b.answer := by
  classical
  apply (solves_iff f rows _).mpr
  intro a
  let gs := b.active.map fun (w,c) => (if classOf (.var w : Term sig) = a then 1 else 0, c)
  have hgs := balanced_combination rows gs (by
    intro t ht
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
    exact b.balanced g hg)
  intro row hr
  have weight (s : Side) (h : ∀ v ∈ s.vars, v ∈ variables rows) :
      s.weight (factorColumn f b.answer a) = s.weight (combination gs) := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro v hv
    unfold factorColumn
    rw [b.factors_image v (h v hv)]
    exact counts b.active a v
  rw [weight _ (fun v hv => List.mem_flatMap.mpr ⟨row, hr, List.mem_append_left _ hv⟩),
      weight _ (fun v hv => List.mem_flatMap.mpr ⟨row, hr, List.mem_append_right _ hv⟩)]
  exact hgs row hr

theorem domain : DomainRestricted (problem f rows) b.answer := by
  intro v hv
  exact b.answer.outside v (fun h => hv ((occurs_iff_mem f rows v).mpr h))

theorem range_fresh {v w : Variable} (hv : (problem f rows).Occurs v)
    (hw : (b.answer.image v).Occurs w) : w ∉ variables rows ++ avoid := by
  intro ha
  have mem := (occurs_iff_mem f rows v).mp hv
  change (b.image v).Occurs w at hw
  rw [image, ite_eq_left mem] at hw
  cases h : slots b.active v with
  | nil => exact b.nonempty v mem h
  | cons u us =>
    rw [h] at hw
    obtain ⟨g,hg,e⟩ := b.slot_source v (by rw [h]; exact (Side.occurs_iff ⟨u,us⟩ f w).mp hw)
    exact b.fresh g hg (e ▸ ha)

theorem freshFor : FreshFor (problem f rows) avoid b.answer :=
  fun _ hv _ hw _ ha => b.range_fresh hv hw (List.mem_append_right _ ha)

end Branch
/-- A selected numeric generator receives one caller-chosen witness, shared
throughout the substitution. The input table identifies the coordinates.
The search over numeric subsets has no access to the caller's names. -/
def branchFromBasis {n} (f : sig.ACSym) (rows : List Row) (avoid : List Variable)
    (names : Fin n → Variable) (index : Variable → Option (Fin n))
    (roundTrip : ∀ i, index (names i) = some i)
    (live : ∀ v ∈ variables rows, ∃ i, names i = v)
    (gs : List (ACBasis.Vec n)) (basis : ACBasis.BasisCorrect (rows.map (ACBasis.encode names)) gs)
    (selected : List (Fin gs.length)) (witness : Fin gs.length → Variable)
    (typed : ∀ j ∈ selected, (witness j).sort = sig.acSort f)
    (unused : ∀ j ∈ selected, witness j ∉ variables rows ++ avoid)
    (covered : ∀ i, ∃ j ∈ selected, 0 < gs.get j i)
    (accepts : ∀ v ∈ variables rows, Subsort (sig.acSort f) v.sort) : Branch f rows avoid := by
  let column (j : Fin gs.length) (v : Variable) : Nat :=
    ((index v).map (gs.get j)).getD 0
  have atName (j i) : column j (names i) = gs.get j i := by simp [column, roundTrip]
  refine { active := selected.map (fun j => (witness j, column j))
           balanced := ?_, witnessSort := ?_, fresh := ?_, nonempty := ?_, acceptsSort := accepts }
  · intro g hg
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
    have unique : Function.Injective names := fun i k h => Option.some.inj
      ((roundTrip i).symm.trans ((congrArg index h).trans (roundTrip k)))
    apply (ACBasis.encode_iff names unique rows live _).mp
    simpa only [atName] using ACBasis.mem_sol _ gs basis j
  · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg; exact typed j hj
  · intro g hg; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg; exact unused j hj
  · intro v hv empty
    obtain ⟨i,rfl⟩ := live v hv
    obtain ⟨j,hj,hp⟩ := covered i
    have mem : witness j ∈ slots (selected.map (fun j => (witness j, column j))) (names i) :=
      List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hj, List.mem_replicate.mpr
        ⟨by rw [atName]; omega, rfl⟩⟩
    rw [empty] at mem
    exact List.not_mem_nil mem

end Tamarin.ACSystem
