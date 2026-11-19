import Tamarin.SharedOffset
import Tamarin.RigidAllocationPacket

/-! Allocate the single rigid factor in X + Y = Z + A. Either summand may
contain it, and its remaining inventory may be empty or nonempty. AC has no
unit, so these four ordinary-term substitutions are distinct cases. -/
namespace Tamarin.RigidAllocation
open Cancellation
variable {sig : Signature}

def Split (f : sig.ACSym) (a t : Term sig) :=
  EquivB t a ∨ ∃ r, HasSort r (sig.acSort f) ∧ EquivB t (.ac f a r)

private theorem split_left (f : sig.ACSym) (a u v : Term sig)
    (hu : Split f a u) (hv : HasSort v (sig.acSort f)) : Split f a (.ac f u v) := by
  right
  rcases hu with h | ⟨r, hr, h⟩
  · exact ⟨v, hv, .ac_congr _ h (.refl _)⟩
  · exact ⟨.ac f r v, .ac f _ _ hr hv, (EquivB.ac_congr f h (.refl v)).trans (.ac_assoc f _ _ _)⟩

theorem split_factor (f : sig.ACSym) (a t : Term sig) (ht : HasSort t (sig.acSort f))
    (hm : classOf a ∈ flatten f t) : Split f a t := by
  classical
  induction t with
  | ac g u v iu iv =>
    by_cases he : f = g
    · subst g
      rw [flatten_ac] at hm
      have hc := Term.checkSort_complete ht
      simp only [Term.checkSort, Bool.and_eq_true] at hc
      have hu := Term.checkSort_sound _ _ hc.1.2
      have hv := Term.checkSort_sound _ _ hc.2
      rcases List.mem_append.mp hm with h | h
      · exact split_left f a _ _ (iu hu h) hv
      · obtain h | ⟨r, hr, h⟩ := split_left f a _ _ (iv hv h) hu
        · exact Or.inl ((EquivB.ac_swap f _ _).trans h)
        · exact Or.inr ⟨r, hr, (EquivB.ac_swap f _ _).trans h⟩
    · simp only [flatten, ite_eq_right he, List.mem_singleton] at hm
      exact Or.inl (Quotient.exact hm.symm)
  | var | atom | free | comm =>
    exact Or.inl (Quotient.exact (List.mem_singleton.mp hm).symm)

theorem rotate (f : sig.ACSym) (a r v : Term sig) :
    EquivB (.ac f (.ac f a r) v) (.ac f (.ac f r v) a) :=
  (EquivB.ac_assoc f a r v).trans (.ac_swap f _ _)

structure Query (sig : Signature) where
  f : sig.ACSym
  x : Variable
  y : Variable
  z : Variable
  a : Term sig
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z
  sx : x.sort = sig.acSort f
  sy : y.sort = sig.acSort f
  sz : z.sort = sig.acSort f
  sa : HasSort a (sig.acSort f)
  outside : ∀ v, a.Occurs v → v ≠ x ∧ v ≠ y ∧ v ≠ z
  factor : ∀ ρ : Substitution sig, flatten f (ρ.apply a) = [classOf (ρ.apply a)]

namespace Query
variable (q : Query sig)

def problem : Problem sig := [⟨.ac q.f (.var q.x) (.var q.y), .ac q.f (.var q.z) q.a⟩]
theorem occurs (v : Variable) : q.problem.Occurs v ↔ v = q.x ∨ v = q.y ∨ v = q.z ∨ q.a.Occurs v := by
  simp [Problem.Occurs, problem, Term.Occurs, or_assoc]

/-- Put the rigid summand first when reasoning about a chosen orientation. -/
def owner (flip : Bool) := if flip then q.y else q.x
def other (flip : Bool) := if flip then q.x else q.y

theorem owner_other (flip) : q.owner flip ≠ q.other flip := by cases flip <;> simp [owner, other, q.xy, q.xy.symm]
theorem owner_z (flip) : q.owner flip ≠ q.z := by cases flip <;> simp [owner, q.xz, q.yz]
theorem other_z (flip) : q.other flip ≠ q.z := by cases flip <;> simp [other, q.xz, q.yz]
theorem owner_sort (flip) : (q.owner flip).sort = sig.acSort q.f := by cases flip <;> simp [owner, q.sx, q.sy]
theorem other_sort (flip) : (q.other flip).sort = sig.acSort q.f := by cases flip <;> simp [other, q.sx, q.sy]

theorem oriented (flip) (σ : Substitution sig) : q.problem.Solves σ ↔
    EquivB (.ac q.f (σ.image (q.owner flip)) (σ.image (q.other flip)))
      (.ac q.f (σ.image q.z) (σ.apply q.a)) := by
  have main : q.problem.Solves σ ↔ EquivB (.ac q.f (σ.image q.x) (σ.image q.y)) (.ac q.f (σ.image q.z) (σ.apply q.a)) :=
    ⟨fun hs => hs _ (List.mem_singleton_self _), fun h _ he => (List.mem_singleton.mp he) ▸ h⟩
  cases flip
  · exact main
  · exact main.trans ⟨fun h => (EquivB.ac_swap q.f _ _).trans h, fun h => (EquivB.ac_swap q.f _ _).trans h⟩

/-- The decomposition uses exactly one occurrence of A, even if an instance
of X or Y has several identical factors. -/
theorem decompose (ρ : Substitution sig) (solves : q.problem.Solves ρ) :
    ∃ flip : Bool, let owner := ρ.image (q.owner flip)
                   let other := ρ.image (q.other flip)
                   let a := ρ.apply q.a
                   (EquivB owner a ∧ EquivB (ρ.image q.z) other) ∨
                   ∃ r, HasSort r (sig.acSort q.f) ∧ EquivB owner (.ac q.f a r) ∧
                     EquivB (ρ.image q.z) (.ac q.f r other) := by
  have h := (q.oriented false ρ).mp solves
  have hp := flatten_equiv q.f h
  rw [flatten_ac, flatten_ac, q.factor ρ] at hp
  have hm := hp.symm.subset (List.mem_append_right _ (List.mem_singleton_self _))
  have pick : ∃ b : Bool, classOf (ρ.apply q.a) ∈ flatten q.f (ρ.image (q.owner b)) := by
    rcases List.mem_append.mp hm with hi | hi
    · exact ⟨false, hi⟩
    · exact ⟨true, hi⟩
  obtain ⟨flip, hm⟩ := pick
  refine ⟨flip, ?_⟩
  have hh := (q.oriented flip ρ).mp solves
  have ht := ρ.sorted (q.owner flip)
  rw [q.owner_sort] at ht
  obtain he | ⟨r, hr, he⟩ := split_factor _ _ _ ht hm
  · refine Or.inl ⟨he, EquivB.ac_cancel_right q.f (c := ρ.apply q.a) ?_⟩
    exact hh.symm.trans ((EquivB.ac_congr q.f he (.refl _)).trans (.ac_swap q.f _ _))
  · refine Or.inr ⟨r, hr, he, EquivB.ac_cancel_right q.f (c := ρ.apply q.a) ?_⟩
    exact hh.symm.trans ((EquivB.ac_congr q.f he (.refl _)).trans (rotate q.f _ _ _))

theorem occurs_oriented (flip : Bool) (v : Variable) :
    q.problem.Occurs v ↔ v = q.owner flip ∨ v = q.other flip ∨ v = q.z ∨ q.a.Occurs v := by
  cases flip
  · exact q.occurs v
  · rw [q.occurs]; simp only [owner, other, ↓reduceIte]; grind

theorem a_outside (flip) (v) (hv : q.a.Occurs v) :
    v ≠ q.owner flip ∧ v ≠ q.other flip ∧ v ≠ q.z := by
  have h := q.outside v hv
  cases flip <;> simp [owner, other, h.1, h.2.1, h.2.2]

structure Slots (shared : Bool) where
  u : Variable
  v : Variable
  su : u.sort = sig.acSort q.f
  sv : v.sort = sig.acSort q.f
  distinct : shared = true → u ≠ v
  outsideU : ¬ q.problem.Occurs u
  outsideV : ¬ q.problem.Occurs v

def ownerImage (shared : Bool) (u : Variable) := if shared then .ac q.f q.a (.var u) else q.a
def zImage (shared : Bool) (u v : Variable) : Term sig := if shared then .ac q.f (.var u) (.var v) else .var v

def answer (flip shared : Bool) (w : q.Slots shared) : Substitution sig where
  image t := if t = q.owner flip then q.ownerImage shared w.u else
    if t = q.other flip then .var w.v else if t = q.z then q.zImage shared w.u w.v else .var t
  support := [q.owner flip, q.other flip, q.z]
  outside := by intro t ht; simp_all
  sorted := by
    intro t; split
    · next h =>
      subst t; rw [q.owner_sort]
      cases shared
      · exact q.sa
      · exact .ac q.f _ _ q.sa (w.su ▸ HasSort.var w.u)
    · split
      · next h => subst t; rw [q.other_sort]; exact w.sv ▸ HasSort.var w.v
      · split
        · next h => subst t; rw [q.sz]; cases shared
                    · exact w.sv ▸ HasSort.var w.v
                    · exact .ac q.f _ _ (w.su ▸ HasSort.var w.u) (w.sv ▸ HasSort.var w.v)
        · exact .var _

@[simp] theorem at_owner {flip shared : Bool} (w : q.Slots shared) :
    (q.answer flip shared w).image (q.owner flip) = q.ownerImage shared w.u := by simp [answer]
@[simp] theorem at_other {flip shared : Bool} (w : q.Slots shared) :
    (q.answer flip shared w).image (q.other flip) = .var w.v := by
  simp [answer, (q.owner_other flip).symm]
@[simp] theorem at_z {flip shared : Bool} (w : q.Slots shared) :
    (q.answer flip shared w).image q.z = q.zImage shared w.u w.v := by
  simp [answer, (q.owner_z flip).symm, (q.other_z flip).symm]

theorem at_a_var (flip shared : Bool) (w : q.Slots shared) {t} (ht : q.a.Occurs t) :
    (q.answer flip shared w).image t = .var t := by
  obtain ⟨ho,hp,hz⟩ := q.a_outside flip t ht
  simp [answer, ho, hp, hz]
theorem apply_a (flip shared : Bool) (w : q.Slots shared) : (q.answer flip shared w).apply q.a = q.a :=
  (Term.subst_eq_of_agree _ Term.var q.a (fun _ => q.at_a_var flip shared w)).trans q.a.subst_id

theorem sound (flip shared : Bool) (w : q.Slots shared) : q.problem.Solves (q.answer flip shared w) := by
  apply (q.oriented flip _).mpr
  rw [at_owner, at_other, at_z, apply_a]
  cases shared
  · exact .ac_swap _ _ _
  · exact rotate _ _ _ _

def override (ρ : Substitution sig) (w : Variable) (t : Term sig) (ht : HasSort t w.sort) :
    Substitution sig where
  image v := if v = w then t else ρ.image v
  support := w :: ρ.support
  outside := by intro v h; simp_all [ρ.outside]
  sorted := by intro v; split; next h => exact h ▸ ht
               exact ρ.sorted v

private theorem covers_with (flip shared : Bool) (w : q.Slots shared) (ρ δ : Substitution sig)
    (own : EquivB (ρ.image (q.owner flip)) (δ.apply (q.ownerImage shared w.u)))
    (other : EquivB (ρ.image (q.other flip)) (δ.image w.v))
    (last : EquivB (ρ.image q.z) (δ.apply (q.zImage shared w.u w.v)))
    (ambient : ∀ v, q.a.Occurs v → δ.image v = ρ.image v) :
    Substitution.InstanceOn q.problem.Occurs ρ (q.answer flip shared w) := by
  refine ⟨δ, fun v hv => ?_⟩
  change EquivB _ (δ.apply ((q.answer flip shared w).image v))
  rcases (q.occurs_oriented flip v).mp hv with h | h | h | ha
  · rw [h, at_owner]; exact own
  · rw [h, at_other]; exact other
  · rw [h, at_z]; exact last
  · rw [q.at_a_var _ _ _ ha]; exact (ambient v ha) ▸ EquivB.refl _

def answers (slots : (flip shared : Bool) → q.Slots shared) :=
  [q.answer false false (slots false false), q.answer true false (slots true false),
   q.answer false true (slots false true), q.answer true true (slots true true)]

private theorem mem_answers (slots : (flip shared : Bool) → q.Slots shared) (f s : Bool) :
    q.answer f s (slots f s) ∈ q.answers slots := by cases f <;> cases s <;> simp [answers]

theorem complete (slots : (flip shared : Bool) → q.Slots shared) : CompleteSet q.problem (q.answers slots) := by
  constructor
  · intro σ h
    simp only [answers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact q.sound _ _ _
  · intro ρ solves
    obtain ⟨flip, alt⟩ := q.decompose ρ solves
    have otherSorted : HasSort (ρ.image (q.other flip)) (sig.acSort q.f) :=
      q.other_sort flip ▸ ρ.sorted _
    have outsideA (v : Variable) (h : ¬ q.problem.Occurs v) : ¬ q.a.Occurs v :=
      fun hv => h ((q.occurs _).mpr (Or.inr (Or.inr (Or.inr hv))))
    rcases alt with ⟨ho, hz⟩ | ⟨r, hr, ho, hz⟩
    · let w := slots flip false
      let δ := override ρ w.v (ρ.image (q.other flip)) (w.sv ▸ otherSorted)
      have dv : δ.image w.v = ρ.image (q.other flip) := by simp [δ, override]
      have da (t) (ht : q.a.Occurs t) : δ.image t = ρ.image t := by
        have ne : t ≠ w.v := fun he => outsideA _ w.outsideV (he ▸ ht)
        simp [δ, override, ne]
      refine ⟨_, q.mem_answers slots flip false, q.covers_with flip false w ρ δ ?_ ?_ ?_ da⟩
      · change EquivB _ (δ.apply q.a); rw [show δ.apply q.a = ρ.apply q.a from Term.subst_eq_of_agree _ _ _ da]
        exact ho
      · rw [dv]; exact .refl _
      · change EquivB _ (δ.image w.v); rw [dv]; exact hz
    · let w := slots flip true
      let base := override ρ w.v (ρ.image (q.other flip)) (w.sv ▸ otherSorted)
      let δ := override base w.u r (w.su ▸ hr)
      have du : δ.image w.u = r := by simp [δ, override]
      have dv : δ.image w.v = ρ.image (q.other flip) := by simp [δ, base, override, (w.distinct rfl).symm]
      have da (t) (ht : q.a.Occurs t) : δ.image t = ρ.image t := by
        have nu : t ≠ w.u := fun he => outsideA _ w.outsideU (he ▸ ht)
        have nv : t ≠ w.v := fun he => outsideA _ w.outsideV (he ▸ ht)
        simp [δ, base, override, nu, nv]
      refine ⟨_, q.mem_answers slots flip true, q.covers_with flip true w ρ δ ?_ ?_ ?_ da⟩
      · change EquivB _ (.ac q.f (δ.apply q.a) (δ.image w.u))
        rw [du, show δ.apply q.a = ρ.apply q.a from Term.subst_eq_of_agree _ _ _ da]
        exact ho
      · rw [dv]; exact .refl _
      · change EquivB _ (.ac q.f (δ.image w.u) (δ.image w.v)); rw [du, dv]; exact hz

theorem domain (flip shared) (w : q.Slots shared) : DomainRestricted q.problem (q.answer flip shared w) := by
  intro v hv
  have hn := mt (q.occurs_oriented flip v).mpr hv
  simp only [not_or] at hn
  simp [answer, hn.1, hn.2.1, hn.2.2.1]

theorem bound_range (flip shared) (w : q.Slots shared) {v t}
    (hv : v = q.owner flip ∨ v = q.other flip ∨ v = q.z)
    (ht : ((q.answer flip shared w).image v).Occurs t) :
    t = w.u ∨ t = w.v ∨ q.a.Occurs t := by
  rcases hv with rfl | rfl | rfl
  · rw [q.at_owner] at ht
    cases shared <;> simp [ownerImage, Term.Occurs] at ht <;> grind
  · rw [q.at_other] at ht
    exact Or.inr (Or.inl ht)
  · rw [q.at_z] at ht
    cases shared <;> simp [zImage, Term.Occurs] at ht <;> grind

theorem freshFor (flip shared) (w : q.Slots shared) (avoid : List Variable)
    (hu : w.u ∉ avoid) (hw : w.v ∉ avoid) : FreshFor q.problem avoid (q.answer flip shared w) := by
  intro v hv t ht outside
  by_cases ha : q.a.Occurs v
  · rw [q.at_a_var _ _ _ ha] at ht
    exact False.elim (outside (ht ▸ hv))
  · have named := (q.occurs_oriented flip v).mp hv
    have hb : v = q.owner flip ∨ v = q.other flip ∨ v = q.z := by grind
    rcases q.bound_range flip shared w hb ht with rfl | rfl | ha'
    · exact hu
    · exact hw
    · exact False.elim (outside ((q.occurs _).mpr (Or.inr (Or.inr (Or.inr ha')))))

def problemOriented (reversed : Bool) : Problem sig :=
  if reversed then [⟨.ac q.f (.var q.z) q.a, .ac q.f (.var q.x) (.var q.y)⟩] else q.problem

theorem solves_reversed (reversed : Bool) (σ : Substitution sig) :
    (q.problemOriented reversed).Solves σ ↔ q.problem.Solves σ := by
  cases reversed
  · rfl
  · change Problem.Solves [_] σ ↔ Problem.Solves [_] σ
    simp only [Problem.Solves, List.mem_singleton, forall_eq]
    exact ⟨EquivB.symm, EquivB.symm⟩

theorem occurs_reversed (reversed : Bool) (v) : (q.problemOriented reversed).Occurs v ↔ q.problem.Occurs v := by
  cases reversed
  · rfl
  · simp [problemOriented, problem, Problem.Occurs, or_comm]

theorem forall_answers (slots : (flip shared : Bool) → q.Slots shared)
    (P : Substitution sig → Prop) (h : ∀ f s, P (q.answer f s (slots f s))) :
    ∀ σ ∈ q.answers slots, P σ := by
  intro σ hm
  simp only [answers, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> exact h _ _

theorem correctIn (slots : (flip shared : Bool) → q.Slots shared) (reversed : Bool)
    (avoid : List Variable) (fresh : ∀ f s, (slots f s).u ∉ avoid ∧ (slots f s).v ∉ avoid) :
    (Outcome.complete (q.answers slots)).CorrectIn (q.problemOriented reversed) avoid := by
  have hc := q.complete slots
  constructor
  · constructor
    · exact fun σ hσ => (q.solves_reversed reversed σ).mpr (hc.sound σ hσ)
    · intro ρ hρ
      obtain ⟨σ, hσ, δ, he⟩ := hc.covers ρ ((q.solves_reversed _ _).mp hρ)
      exact ⟨σ, hσ, δ, fun v hv => he v ((q.occurs_reversed _ _).mp hv)⟩
  · apply q.forall_answers slots
    exact fun f s v hn => q.domain f s _ v (fun hv => hn ((q.occurs_reversed _ _).mpr hv))
  · apply q.forall_answers slots
    exact fun f s v hv t ht hn => q.freshFor f s _ avoid (fresh f s).1 (fresh f s).2 v
      ((q.occurs_reversed _ _).mp hv) t ht (fun ho => hn ((q.occurs_reversed _ _).mpr ho))

end Query

def decodeWord (q : Query sig) (slot : UInt64 → Variable) (w : UInt64) : Term sig :=
  if w = 0 then q.a else .var (slot w)

def decodeRow (q : Query sig) (slot : UInt64 → Variable) (row : Array UInt64) : Option (Term sig) :=
  match row.toList with
  | [a] => some (decodeWord q slot a)
  | [a,b] => some (.ac q.f (decodeWord q slot a) (decodeWord q slot b))
  | _ => none

def decodeArm (q : Query sig) (slot : UInt64 → Variable) (arm : Arm) :
    Option (List (Variable × Term sig)) := do
  let [x,y,z] := arm.toList | none
  return [(q.x, ← decodeRow q slot x), (q.y, ← decodeRow q slot y), (q.z, ← decodeRow q slot z)]

/-- The compact native encoder stores the three observed keys. With a ground
rigid factor all range variables belong exclusively to this branch. -/
def ClosedRanges (q : Query sig) (avoid : List Variable) (σ : Substitution sig) :=
  ∀ v ∈ [q.x,q.y,q.z], ∀ t, (σ.image v).Occurs t → ¬ q.problem.Occurs t ∧ t ∉ avoid

end Tamarin.RigidAllocation
