import Tamarin.RigidAllocationRefinement
import Tamarin.FiniteOccurs

/-! The rigid factor may itself depend on a summand. In X + Y = Z + A[X],
X cannot contain A[X] after any finite substitution. Both surviving answers
put A[X] into Y and share X's fresh image inside that factor and Z. -/
namespace Tamarin.DependentAllocation
open Cancellation
variable {sig : Signature}

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
  proper : FiniteOccurs.Proper x a
  onlyX : ∀ w, a.Occurs w → w = x
  factor : ∀ σ : Substitution sig, flatten f (σ.apply a) = [classOf (σ.apply a)]

namespace Query
variable (q : Query sig)

def problem : Problem sig := [⟨.ac q.f (.var q.x) (.var q.y), .ac q.f (.var q.z) q.a⟩]

theorem occurs (w) : q.problem.Occurs w ↔ w = q.x ∨ w = q.y ∨ w = q.z := by
  simp only [Problem.Occurs, problem, List.mem_singleton, exists_eq_left, Term.Occurs]
  have h := q.onlyX w
  grind

def fill (t : Term sig) : Term sig := q.a.subst (fun _ => t)

theorem apply_a (σ : Substitution sig) : σ.apply q.a = q.fill (σ.image q.x) :=
  Term.subst_eq_of_agree _ _ _ (fun w hw => congrArg σ.image (q.onlyX w hw))

theorem fill_sorted (t : Term sig) (ht : HasSort t q.x.sort) : HasSort (q.fill t) (sig.acSort q.f) := by
  let σ := Substitution.binding q.x t ht
  have h := q.sa.subst σ.image σ.sorted
  change HasSort (σ.apply q.a) _ at h
  simpa [q.apply_a, σ] using h

theorem fill_apply (σ : Substitution sig) (w : Variable) :
    σ.apply (q.fill (.var w)) = q.fill (σ.image w) := Term.subst_comp ..

private theorem decompose (σ : Substitution sig) (solves : q.problem.Solves σ) :
    let a := σ.apply q.a
    (EquivB (σ.image q.y) a ∧ EquivB (σ.image q.z) (σ.image q.x)) ∨
    ∃ r, HasSort r (sig.acSort q.f) ∧ EquivB (σ.image q.y) (.ac q.f a r) ∧
      EquivB (σ.image q.z) (.ac q.f r (σ.image q.x)) := by
  have h : EquivB (.ac q.f (σ.image q.x) (σ.image q.y)) (.ac q.f (σ.image q.z) (σ.apply q.a)) :=
    solves _ (List.mem_singleton_self _)
  have p := flatten_equiv q.f h
  rw [flatten_ac, flatten_ac, q.factor] at p
  have hm := p.mem_iff.mpr (List.mem_append_right _ (List.mem_singleton_self _))
  have inY : classOf (σ.apply q.a) ∈ flatten q.f (σ.image q.y) := by
    rcases List.mem_append.mp hm with hx | hy
    · rcases RigidAllocation.split_factor _ _ _ (q.sx ▸ σ.sorted q.x) hx with he | ⟨r, _, he⟩
      · exact False.elim (FiniteOccurs.not_equiv q.proper σ he)
      · exact False.elim (FiniteOccurs.not_equiv_ac q.proper σ q.f r he)
    · exact hy
  have hs := h.symm.trans (EquivB.ac_swap q.f _ _)
  rcases RigidAllocation.split_factor _ _ _ (q.sy ▸ σ.sorted q.y) inY with he | ⟨r, hr, he⟩
  · exact Or.inl ⟨he, EquivB.ac_cancel_right q.f ((hs.trans (.ac_congr q.f he (.refl _))).trans (.ac_swap q.f _ _))⟩
  · exact Or.inr ⟨r, hr, he, EquivB.ac_cancel_right q.f
      ((hs.trans (.ac_congr q.f he (.refl _))).trans (RigidAllocation.rotate q.f _ _ _))⟩

structure Slots (shared : Bool) where
  other : Variable
  rest : Variable
  so : other.sort = sig.acSort q.f
  sr : rest.sort = sig.acSort q.f
  distinct : shared = true → other ≠ rest

def yImage (shared : Bool) (w : q.Slots shared) : Term sig :=
  if shared then .ac q.f (q.fill (.var w.other)) (.var w.rest) else q.fill (.var w.other)

def zImage (shared : Bool) (w : q.Slots shared) : Term sig :=
  if shared then .ac q.f (.var w.rest) (.var w.other) else .var w.other

def answer (b : Bool) (w : q.Slots b) : Substitution sig where
  image v := if v = q.x then .var w.other else if v = q.y then q.yImage b w else
    if v = q.z then q.zImage b w else .var v
  support := [q.x, q.y, q.z]
  outside := by intro v hv; simp_all
  sorted := by
    intro v
    have ho : HasSort (.var (sig := sig) w.other) (sig.acSort q.f) := w.so ▸ HasSort.var w.other
    have hr : HasSort (.var (sig := sig) w.rest) (sig.acSort q.f) := w.sr ▸ HasSort.var w.rest
    have hf := q.fill_sorted _ (q.sx ▸ ho)
    split
    · next e => subst v; exact q.sx ▸ ho
    · split
      · next e => subst v; rw [q.sy]; cases b <;> first | exact hf | exact .ac q.f _ _ hf hr
      · split
        · next e => subst v; rw [q.sz]; cases b <;> first | exact ho | exact .ac q.f _ _ hr ho
        · exact .var _

@[simp] theorem at_x (b) (w : q.Slots b) : (q.answer b w).image q.x = .var w.other := by simp [answer]
@[simp] theorem at_y (b) (w : q.Slots b) : (q.answer b w).image q.y = q.yImage b w := by simp [answer, q.xy.symm]
@[simp] theorem at_z (b) (w : q.Slots b) : (q.answer b w).image q.z = q.zImage b w := by simp [answer, q.xz.symm, q.yz.symm]

theorem sound (b) (w : q.Slots b) : q.problem.Solves (q.answer b w) := by
  intro e he; obtain rfl := List.mem_singleton.mp he
  change EquivB (.ac q.f _ _) (.ac q.f _ ((q.answer b w).apply q.a))
  simp only [Term.subst, q.at_x, q.at_y, q.at_z, q.apply_a]
  cases b
  · exact .refl _
  · exact (EquivB.ac_swap q.f _ _).trans (RigidAllocation.rotate q.f _ _ _)

private theorem instance_of_images (b) (w : q.Slots b) (σ δ : Substitution sig)
    (x : δ.image w.other = σ.image q.x)
    (y : EquivB (σ.image q.y) (δ.apply (q.yImage b w)))
    (z : EquivB (σ.image q.z) (δ.apply (q.zImage b w))) :
    Substitution.InstanceOn q.problem.Occurs σ (q.answer b w) := by
  refine ⟨δ, fun v hv => ?_⟩
  change EquivB _ (δ.apply ((q.answer b w).image v))
  rcases (q.occurs _).mp hv with rfl | rfl | rfl
  · rw [q.at_x]; exact x ▸ .refl _
  · rw [q.at_y]; exact y
  · rw [q.at_z]; exact z

def answers (slots : (b : Bool) → q.Slots b) := [q.answer false (slots false), q.answer true (slots true)]

theorem complete (slots : (b : Bool) → q.Slots b) : CompleteSet q.problem (q.answers slots) := by
  constructor
  · intro σ h
    rcases List.mem_cons.mp h with rfl | h
    · exact q.sound false _
    · obtain rfl := List.mem_singleton.mp h; exact q.sound true _
  · intro σ h
    obtain ⟨hy, hz⟩ | ⟨r, hr, hy, hz⟩ := q.decompose σ h
    · let w := slots false
      let δ := Substitution.binding w.other (σ.image q.x) (w.so ▸ q.sx ▸ σ.sorted q.x)
      have hx : δ.image w.other = σ.image q.x := Substitution.binding_image_self ..
      refine ⟨_, List.mem_cons_self .., q.instance_of_images false w σ δ hx ?_ ?_⟩
      · change EquivB _ (δ.apply (q.fill (.var w.other))); rw [q.fill_apply, hx, ← q.apply_a]; exact hy
      · change EquivB _ (δ.image w.other); rw [hx]; exact hz
    · let w := slots true
      let base := Substitution.binding w.other (σ.image q.x) (w.so ▸ q.sx ▸ σ.sorted q.x)
      let δ := RigidAllocation.Query.override base w.rest r (w.sr ▸ hr)
      have hx : δ.image w.other = σ.image q.x := by simp [δ, base, RigidAllocation.Query.override, w.distinct rfl]
      have hrest : δ.image w.rest = r := by simp [δ, RigidAllocation.Query.override]
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), q.instance_of_images true w σ δ hx ?_ ?_⟩
      · change EquivB _ (.ac q.f (δ.apply (q.fill (.var w.other))) (δ.image w.rest))
        rw [q.fill_apply, hx, hrest, ← q.apply_a]; exact hy
      · change EquivB _ (.ac q.f (δ.image w.rest) (δ.image w.other)); rw [hx, hrest]; exact hz

def oriented (reverse swap : Bool) : Problem sig :=
  let l := if swap then Term.ac q.f (.var q.y) (.var q.x) else .ac q.f (.var q.x) (.var q.y)
  let r := Term.ac q.f (.var q.z) q.a
  if reverse then [⟨r,l⟩] else [⟨l,r⟩]

theorem solves_oriented (reverse swap : Bool) (σ : Substitution sig) :
    (q.oriented reverse swap).Solves σ ↔ q.problem.Solves σ := by
  cases reverse <;> cases swap <;> simp [oriented, problem, Problem.Solves,
    forall_eq, Substitution.apply, Term.subst]
  all_goals first
    | exact ⟨fun h => (EquivB.ac_swap q.f _ _).trans h, fun h => (EquivB.ac_swap q.f _ _).trans h⟩
    | exact ⟨EquivB.symm, EquivB.symm⟩
    | exact ⟨fun h => (EquivB.ac_swap q.f _ _).trans h.symm,
        fun h => h.symm.trans (.ac_swap q.f _ _)⟩

theorem occurs_oriented (reverse swap : Bool) (w) :
    (q.oriented reverse swap).Occurs w ↔ q.problem.Occurs w := by
  cases reverse <;> cases swap <;> simp [oriented, problem, Problem.Occurs, Term.Occurs,
    or_left_comm, or_assoc, or_comm]

def Closed (avoid : List Variable) (σ : Substitution sig) :=
  ∀ v, q.problem.Occurs v → ∀ k, (σ.image v).Occurs k → ¬ q.problem.Occurs k ∧ k ∉ avoid

private theorem bound_range (b : Bool) (w : q.Slots b) (v k)
    (hv : q.problem.Occurs v) (hk : ((q.answer b w).image v).Occurs k) :
    k = w.other ∨ k = w.rest := by
  have fill_occurs : (q.fill (.var w.other)).Occurs k → k = w.other :=
    fun h => ((Term.occurs_rename q.a _ k).mp h).elim (fun _ h => h.2)
  rcases (q.occurs v).mp hv with rfl | rfl | rfl
  · rw [q.at_x] at hk; exact Or.inl hk
  · rw [q.at_y] at hk
    cases b <;> simp only [yImage, ↓reduceIte, Term.Occurs] at hk
    · exact Or.inl (fill_occurs hk)
    · exact hk.imp fill_occurs id
  · rw [q.at_z] at hk
    cases b <;> simp only [zImage, ↓reduceIte, Term.Occurs] at hk
    · exact Or.inl hk
    · exact hk.symm

end Query

open RigidAllocation (Arm Live shortX shortY longX longY)

def decodeArm (q : Query sig) (slot : UInt64 → Variable) (arm : Arm) :
    Option (List (Variable × Term sig)) := do
  let [x,y,z] := arm.toList | none
  let [v] := x.toList | none
  guard (v != 0)
  let word (i : UInt64) := if i = 0 then q.fill (.var (slot v)) else .var (slot i)
  let row (r : Array UInt64) := match r.toList with
    | [a] => some (word a)
    | [a,b] => some (Term.ac q.f (word a) (word b))
    | _ => none
  return [(q.x, .var (slot v)), (q.y, ← row y), (q.z, ← row z)]

theorem packet_correct {run} (numeric : RigidAllocation.PacketCorrect run)
    (q : Query sig) (reverse swap : Bool) (avoid : List Variable)
    (d : RigidAllocation.DecoderFor q.f q.problem.Occurs avoid) :
    ∃ answers : List (Substitution sig),
      ((run reverse).toList.filterMap (fun arm => decodeArm q (d.slot arm) arm)).Perm
        (answers.map fun σ => (FreshAnswer.encode [q.x,q.y,q.z] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (q.oriented reverse swap) avoid ∧
      ∀ σ ∈ answers, q.Closed avoid σ := by
  obtain ⟨s,t,u,v,w,k,hs,ht,hu,hv,huv,hw,hk,hwk,hp⟩ := numeric reverse
  have lt : Live (shortY t) t := by simp [Live, shortY, ht]
  have lw : Live (longY w k) w := by simp [Live, longY, hw]
  have lk : Live (longY w k) k := by simp [Live, longY, hk]
  let slots : (b : Bool) → q.Slots b
    | false => ⟨d.slot _ t, d.slot _ t, d.typed _ _ lt, d.typed _ _ lt, by simp⟩
    | true => ⟨d.slot _ k, d.slot _ w, d.typed _ _ lk, d.typed _ _ lw,
        fun _ => d.distinct _ _ _ lk lw hwk.symm⟩
  have each (P : Substitution sig → Prop) (h : ∀ b, P (q.answer b (slots b))) :
      ∀ σ ∈ q.answers slots, P σ := by
    intro σ hm; rcases List.mem_cons.mp hm with rfl | hm
    · exact h false
    · obtain rfl := List.mem_singleton.mp hm; exact h true
  have closed : ∀ σ ∈ q.answers slots, q.Closed avoid σ := by
    apply each; intro b v' h t' ht'
    rcases q.bound_range b (slots b) v' t' h ht' with rfl | rfl
    · cases b; exact d.fresh _ _ lt; exact d.fresh _ _ lk
    · cases b; exact d.fresh _ _ lt; exact d.fresh _ _ lw
  refine ⟨q.answers slots, ?_, ?_, closed⟩
  · have mapped := hp.filterMap (fun arm => decodeArm q (d.slot arm) arm)
    simpa [List.filterMap_cons, guard, Query.answers, slots, shortX, shortY, longX, longY, decodeArm, FreshAnswer.encode,
      Query.yImage, Query.zImage, q.xy, q.xy.symm, q.xz.symm, q.yz.symm,
      hs, ht, hu, hv, hw, hk] using mapped
  · have hc := q.complete slots
    constructor
    · constructor
      · intro σ hm; exact (q.solves_oriented _ _ _).mpr (hc.sound _ hm)
      · intro σ h
        obtain ⟨τ, hm, δ, he⟩ := hc.covers σ ((q.solves_oriented _ _ _).mp h)
        exact ⟨τ, hm, δ, fun _ hv => he _ ((q.occurs_oriented _ _ _).mp hv)⟩
    · apply each; intro b v' hn
      have hh := mt (q.occurs _).mpr (mt (q.occurs_oriented _ _ _).mpr hn)
      simp_all [Query.answer]
    · intro σ hm v' hv' t' ht' _
      exact (closed σ hm v' ((q.occurs_oriented _ _ _).mp hv') t' ht').2

end Tamarin.DependentAllocation
