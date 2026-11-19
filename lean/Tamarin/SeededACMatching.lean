import Tamarin.OpenMatchAdapter
import Tamarin.CommonCancellation
import Tamarin.SortClash

/-! Directional AC matching under a partial simultaneous binding. Target
variables stay rigid, including when their names also occur in the pattern. -/
namespace Tamarin.OpenMatch
open Cancellation
variable {sig : Signature}

/-- Cancel the factors of each fully determined operand after applying the
seed. A bound variable may itself expand to several factors at this head.
The result holds for every extension of the seed on the fixed operands. -/
theorem cancel_seeded (f : sig.ACSym) (seed σ : Substitution sig)
    (pattern fixed loose subject rest : List (Term sig)) (split : pattern.Perm (fixed ++ loose))
    (agree : ∀ t ∈ fixed, ∀ v, t.Occurs v → EquivB (σ.image v) (seed.image v))
    (common missing : List (Class sig))
    (left : (fixed.flatMap fun t => flatten f (seed.apply t)).Perm (common ++ missing))
    (right : (subject.flatMap (flatten f)).Perm (common ++ rest.flatMap (flatten f)))
    (apart : ∀ k ∈ missing, k ∉ rest.flatMap (flatten f)) :
    Holds f pattern subject σ ↔ missing = [] ∧ Holds f loose rest σ := by
  let image := fun t : Term sig => flatten f (σ.apply t)
  have fixedEq (xs : List (Term sig)) (covered : ∀ t ∈ xs, t ∈ fixed) :
      (xs.flatMap image).Perm (xs.flatMap fun t => flatten f (seed.apply t)) := by
    induction xs with
    | nil => exact .nil
    | cons t ts ih =>
      exact (flatten_equiv f (t.subst_equiv σ.image seed.image (agree t (covered _ List.mem_cons_self)))).append
        (ih (fun u h => covered u (List.mem_cons_of_mem _ h)))
  have p := (split.flatMap_right image)
  rw [List.flatMap_append] at p
  have l := p.trans (((fixedEq fixed (fun _ => id)).trans left).append_right _)
  rw [List.append_assoc] at l
  rw [holds_iff,holds_iff]
  constructor
  · intro h
    have resid := (List.perm_append_left_iff _).mp (l.symm.trans (h.trans right))
    cases missing with
    | nil => exact ⟨rfl,resid⟩
    | cons k ks => exact False.elim (apart k List.mem_cons_self (resid.mem_iff.mp List.mem_cons_self))
  · rintro ⟨rfl,h⟩
    exact l.trans ((h.append_left common).trans right.symm)

/-- Interpret the linked cancellation packet on flattened seed images and rigid
subject occurrences. The interner only needs to distinguish the structural
classes actually compared on opposite sides of this call. -/
def SeededCancellationCorrect (run : Array UInt64 → Array UInt64 → Array (Array UInt64)) : Prop :=
  ∀ {s : Signature} (f : s.ACSym) (decode : UInt64 → Term s) (lhs rhs : Array UInt64)
    (fixed : List (Term s)) (seed : Substitution s),
    (fixed.flatMap fun t => flatten f (seed.apply t)).Perm (lhs.toList.map fun w => classOf (decode w)) →
    (∀ w ∈ rhs.toList, flatten f (decode w) = [classOf (decode w)]) →
    (∀ w ∈ lhs.toList, ∀ v ∈ rhs.toList, EquivB (decode w) (decode v) → w = v) →
    ∃ missing rest : List UInt64, run lhs rhs = #[missing.toArray,rest.toArray] ∧
      ∀ pattern loose, pattern.Perm (fixed ++ loose) → ∀ σ : Substitution s,
        (∀ t ∈ fixed, ∀ v, t.Occurs v → EquivB (σ.image v) (seed.image v)) →
        (Holds f pattern (rhs.toList.map decode) σ ↔
          missing = [] ∧ loose.length ≤ rest.length ∧ Holds f loose (rest.map decode) σ)

theorem seeded_correct {run} (ok : CommonCancellation.Correct run) : SeededCancellationCorrect run := by
  intro s f decode lhs rhs fixed seed layout atomic faithful
  obtain ⟨common,missing,rest,out,left,right,disjoint⟩ := ok lhs rhs
  refine ⟨missing,rest,out,?_⟩
  intro pattern loose split σ agree
  let cls := fun w => classOf (decode w)
  have live {x} (h : x ∈ rest) := right.mem_iff.mpr (List.mem_append_right common h)
  have parts (ws : List UInt64) (mem : ∀ x ∈ ws, x ∈ rhs.toList) :
      (ws.map decode).flatMap (flatten f) = ws.map cls := by
    induction ws with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.map_cons,List.flatMap_cons,atomic w (mem _ List.mem_cons_self),List.singleton_append]
      exact congrArg _ (ih (fun x hx => mem x (List.mem_cons_of_mem _ hx)))
  have l := layout.trans (left.map cls)
  rw [List.map_append] at l
  have r := right.map cls
  rw [List.map_append,← parts rest (fun _ h => live h),← parts rhs.toList (fun _ => id)] at r
  have apart (k) (hm : k ∈ missing.map cls) (hr : k ∈ (rest.map decode).flatMap (flatten f)) : False := by
    rw [parts rest (fun _ h => live h)] at hr
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp hr
    have same := faithful w (left.mem_iff.mpr (List.mem_append_right common hw)) v (live hv) (Quotient.exact eq.symm)
    exact disjoint w hw (same ▸ hv)
  rw [cancel_seeded f seed σ pattern fixed loose _ _ split agree _ _ l r apart,List.map_eq_nil_iff]
  constructor
  · rintro ⟨m,h⟩
    have width := OpenMatchAdapter.long_enough f σ loose (rest.map decode) (by
      intro t hit; obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hit; exact atomic w (live hw)) h
    exact ⟨m,by simpa using width,h⟩
  · exact fun h => ⟨h.1,h.2.2⟩

/-- A single loose variable captures the entire decoded remainder with the
same sort check used when propagating a binding across a row. An empty
remainder has no capture. -/
theorem single_capture_iff (f : sig.ACSym) (v : Variable) (rest : List (Term sig)) (σ : Substitution sig) :
    Holds f [.var v] rest σ ↔ ∃ t, ACRepresentation.decode f rest = some t ∧
      Subsort t.rootSort v.sort ∧ EquivB (σ.image v) t := by
  cases rest with
  | nil => simp [Holds,residual,ACRepresentation.decode]
  | cons a xs =>
    simp only [Holds,residual,ACRepresentation.decode,ACRepresentation.fold,Option.some.injEq,
      exists_eq_left',Matching.Matches,List.mem_singleton,forall_eq]
    constructor
    · intro h
      have sorted := Term.checkSort_sound _ _ ((SortClash.check_equiv h v.sort) ▸ Term.checkSort_complete (σ.sorted v))
      exact ⟨Term.rootSort_le sorted,h⟩
    · exact And.right

end Tamarin.OpenMatch
