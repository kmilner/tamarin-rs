import Tamarin.RigidAllocation
import Tamarin.GroundACEquality

/-! Two-sided AC offset equations with persistent, different rigid factors.
Variables in either factor remain observed and must share their instantiator
with all occurrences in both returned images. -/
namespace Tamarin.CompoundOffset
open Cancellation
variable {sig : Signature}

/-- A fixed nonvariable head different from the AC operator remains one
factor under every substitution. Distinct fixed heads always stay distinct. -/
def Fixed (f : sig.ACSym) : Term sig → Prop
  | .var _ => False
  | .ac g _ _ => f ≠ g
  | _ => True

theorem fixed_factor (f : sig.ACSym) (t : Term sig) (ht : Fixed f t) (ρ : Substitution sig) :
    flatten f (ρ.apply t) = [classOf (ρ.apply t)] := by
  cases t with
  | var => exact False.elim ht
  | atom | free | comm => rfl
  | ac g l r => simp only [Substitution.apply, Term.subst, flatten, ite_eq_right ht]

theorem fixed_head (f : sig.ACSym) (a b : Term sig) (ha : Fixed f a) (hb : Fixed f b)
    (ne : (headModel sig).eval Head.var a ≠ (headModel sig).eval Head.var b) (ρ : Substitution sig) :
    ¬ EquivB (ρ.apply a) (ρ.apply b) := by
  intro he
  have head (t : Term sig) (ht : Fixed f t) :
      (headModel sig).eval Head.var (ρ.apply t) = (headModel sig).eval Head.var t := by
    cases t with
    | var => exact False.elim ht
    | _ => rfl
  exact ne ((head a ha).symm.trans (he.head_eq.trans (head b hb)))

structure Query (sig : Signature) where
  f : sig.ACSym
  x : Variable
  y : Variable
  a : Term sig
  b : Term sig
  xy : x ≠ y
  sx : x.sort = sig.acSort f
  sy : y.sort = sig.acSort f
  sa : HasSort a (sig.acSort f)
  sb : HasSort b (sig.acSort f)
  outside : ∀ v, a.Occurs v ∨ b.Occurs v → v ≠ x ∧ v ≠ y
  factorA : ∀ ρ : Substitution sig, flatten f (ρ.apply a) = [classOf (ρ.apply a)]
  factorB : ∀ ρ : Substitution sig, flatten f (ρ.apply b) = [classOf (ρ.apply b)]
  distinct : ∀ ρ : Substitution sig, ¬ EquivB (ρ.apply a) (ρ.apply b)

namespace Query
variable (q : Query sig)

def problem : Problem sig := [⟨.ac q.f (.var q.x) q.a, .ac q.f (.var q.y) q.b⟩]

theorem occurs (v : Variable) : q.problem.Occurs v ↔ v = q.x ∨ v = q.y ∨ q.a.Occurs v ∨ q.b.Occurs v := by
  simp [Problem.Occurs, problem, Term.Occurs, or_assoc, or_left_comm, or_comm]

private theorem exchange (f : sig.ACSym) (r a b : Term sig) :
    EquivB (.ac f (.ac f r a) b) (.ac f (.ac f r b) a) :=
  (EquivB.ac_assoc f _ _ _).trans
    ((EquivB.ac_congr f (.refl _) (.ac_swap _ _ _)).trans (EquivB.ac_assoc _ _ _ _).symm)

theorem decompose (ρ : Substitution sig) (solves : q.problem.Solves ρ) :
    (EquivB (ρ.image q.x) (ρ.apply q.b) ∧ EquivB (ρ.image q.y) (ρ.apply q.a)) ∨
    ∃ r, HasSort r (sig.acSort q.f) ∧ EquivB (ρ.image q.x) (.ac q.f r (ρ.apply q.b)) ∧
      EquivB (ρ.image q.y) (.ac q.f r (ρ.apply q.a)) := by
  have e : EquivB (.ac q.f (ρ.image q.x) (ρ.apply q.a)) (.ac q.f (ρ.image q.y) (ρ.apply q.b)) :=
    solves _ (List.mem_singleton_self _)
  have hp := flatten_equiv q.f e
  rw [flatten_ac, flatten_ac, q.factorA ρ, q.factorB ρ] at hp
  have hm := hp.symm.subset (List.mem_append_right _ (List.mem_singleton_self _))
  rcases List.mem_append.mp hm with h | h
  · rcases RigidAllocation.split_factor q.f (ρ.apply q.b) (ρ.image q.x) (q.sx ▸ ρ.sorted q.x) h with hb | ⟨r, hr, hb⟩
    · exact Or.inl ⟨hb, EquivB.ac_cancel_right q.f
        (e.symm.trans ((EquivB.ac_congr _ hb (.refl _)).trans (.ac_swap _ _ _)))⟩
    · have huv := hb.trans (.ac_swap _ _ _)
      exact Or.inr ⟨r, hr, huv, EquivB.ac_cancel_right q.f
        (e.symm.trans ((EquivB.ac_congr _ huv (.refl _)).trans (exchange _ _ _ _)))⟩
  · exact False.elim (q.distinct ρ (Quotient.exact (List.mem_singleton.mp h).symm))

def image (w : Variable) (shared : Bool) (t : Term sig) : Term sig :=
  if shared then .ac q.f (.var w) t else t

private theorem image_sorted (w : Variable) (hw : w.sort = sig.acSort q.f) (s : Bool)
    (t : Term sig) (ht : HasSort t (sig.acSort q.f)) : HasSort (q.image w s t) (sig.acSort q.f) := by
  cases s
  · exact ht
  · exact .ac q.f _ _ (hw ▸ HasSort.var w) ht

def answer (w : Variable) (hw : w.sort = sig.acSort q.f) (s : Bool) : Substitution sig where
  image v := if v = q.x then q.image w s q.b else if v = q.y then q.image w s q.a else .var v
  support := [q.x, q.y]
  outside := by intro v h; simp_all
  sorted := by
    intro v; split
    · next h => subst v; rw [q.sx]; exact q.image_sorted w hw _ _ q.sb
    · split
      · next h => subst v; rw [q.sy]; exact q.image_sorted w hw _ _ q.sa
      · exact .var _

@[simp] theorem at_x (w hw s) : (q.answer w hw s).image q.x = q.image w s q.b := by simp [answer]
@[simp] theorem at_y (w hw s) : (q.answer w hw s).image q.y = q.image w s q.a := by simp [answer, q.xy.symm]
theorem ambient (w hw s) {v} (h : q.a.Occurs v ∨ q.b.Occurs v) :
    (q.answer w hw s).image v = .var v := by
  obtain ⟨hx,hy⟩ := q.outside v h
  simp [answer, hx, hy]

theorem sound (w hw s) : q.problem.Solves (q.answer w hw s) := by
  have ea : (q.answer w hw s).apply q.a = q.a :=
    (Term.subst_eq_of_agree _ Term.var _ fun v hv => q.ambient w hw s (Or.inl hv)).trans q.a.subst_id
  have eb : (q.answer w hw s).apply q.b = q.b :=
    (Term.subst_eq_of_agree _ Term.var _ fun v hv => q.ambient w hw s (Or.inr hv)).trans q.b.subst_id
  intro e he
  obtain rfl := List.mem_singleton.mp he
  change EquivB (.ac _ ((q.answer ..).image q.x) ((q.answer ..).apply q.a))
    (.ac _ ((q.answer ..).image q.y) ((q.answer ..).apply q.b))
  rw [q.at_x, q.at_y, ea, eb]
  cases s
  · exact .ac_swap _ _ _
  · exact exchange _ _ _ _

theorem complete (w : Variable) (hw : w.sort = sig.acSort q.f) (fresh : ¬ q.problem.Occurs w) :
    CompleteSet q.problem [q.answer w hw false, q.answer w hw true] := by
  constructor
  · intro σ h; rcases List.mem_cons.mp h with rfl | h
    · exact q.sound _ _ _
    · obtain rfl := List.mem_singleton.mp h; exact q.sound _ _ _
  · intro ρ hs
    rcases q.decompose ρ hs with ⟨hb,ha⟩ | ⟨r,hr,hb,ha⟩
    · refine ⟨_, List.mem_cons_self, ρ, fun v hv => ?_⟩
      change EquivB _ (ρ.apply ((q.answer w hw false).image v))
      rcases (q.occurs v).mp hv with rfl | rfl | hv
      · exact (q.at_x ..) ▸ hb
      · rw [q.at_y]; exact ha
      · rw [q.ambient _ _ _ hv]; exact .refl _
    · let δ := RigidAllocation.Query.override ρ w r (hw ▸ hr)
      have dw : δ.image w = r := by simp [δ, RigidAllocation.Query.override]
      have dv (v : Variable) (hv : q.a.Occurs v ∨ q.b.Occurs v) : δ.image v = ρ.image v := by
        have ne : v ≠ w := fun he => fresh (he ▸ (q.occurs v).mpr (Or.inr (Or.inr hv)))
        simp [δ, RigidAllocation.Query.override, ne]
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), δ, fun v hv => ?_⟩
      change EquivB _ (δ.apply ((q.answer w hw true).image v))
      rcases (q.occurs v).mp hv with rfl | rfl | hv
      · rw [q.at_x]; change EquivB _ (.ac _ (δ.image w) (δ.apply q.b))
        rw [dw, show δ.apply q.b = ρ.apply q.b from Term.subst_eq_of_agree _ _ _ fun v h => dv v (Or.inr h)]
        exact hb
      · rw [q.at_y]; change EquivB _ (.ac _ (δ.image w) (δ.apply q.a))
        rw [dw, show δ.apply q.a = ρ.apply q.a from Term.subst_eq_of_agree _ _ _ fun v h => dv v (Or.inl h)]
        exact ha
      · rw [q.ambient _ _ _ hv]; exact (dv v hv) ▸ EquivB.refl _

end Query
end Tamarin.CompoundOffset
