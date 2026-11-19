import Tamarin.DHTowerNormal
import Tamarin.DHTowerCallerDefs
import Tamarin.DHPeerComplete

/-! Extensional replacement of a variant observation. This lets the caller
present exponent products at any level of a tower while preserving all
substitutions and all original tuple positions. -/
namespace Tamarin.Rewriting
variable {sig : Signature} {R : Root sig}

structure SameObservation (R : Root sig) (a b : Term sig) : Prop where
  observes (v) : a.Occurs v ↔ b.Occurs v
  forms (ρ : Substitution sig) : Normalized R ρ → ∀ u, NormalForm R (ρ.apply a) u ↔ NormalForm R (ρ.apply b) u

theorem SameObservation.refl (R : Root sig) (a : Term sig) : SameObservation R a a :=
  ⟨fun _ => Iff.rfl,fun _ _ _ => Iff.rfl⟩

/-- Slotwise replacement preserves the complete, reconstructible, scoped
variant family. This argument is independent of any DH-specific normalization. -/
theorem SameObservation.transport {α : Type} {before after : α → Term sig}
    {xs : List α} {answers : List (Variant sig)} (avoid : List Variable)
    (same : ∀ x ∈ xs, SameObservation R (before x) (after x))
    (complete : CompleteVariants R (xs.map before) answers)
    (arms : ∀ a ∈ answers, a.Reconstructible R (xs.map before) ∧ a.Safe (xs.map before) avoid) :
    CompleteVariants R (xs.map after) answers ∧
      ∀ a ∈ answers, a.Reconstructible R (xs.map after) ∧ a.Safe (xs.map after) avoid := by
  have names (v) : Observed (xs.map before) v ↔ Observed (xs.map after) v := by
    constructor
    · rintro ⟨t,hm,h⟩
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
      exact ⟨_,List.mem_map_of_mem hx,((same x hx).observes v).mp h⟩
    · rintro ⟨t,hm,h⟩
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
      exact ⟨_,List.mem_map_of_mem hx,((same x hx).observes v).mpr h⟩
  have forms (ρ : Substitution sig) (hn : Normalized R ρ) (vs : List (Term sig)) :
      Aligned (fun t u => NormalForm R (ρ.apply t) u) (xs.map before) vs ↔
      Aligned (fun t u => NormalForm R (ρ.apply t) u) (xs.map after) vs := by
    clear complete arms names
    induction xs generalizing vs with
    | nil => rfl
    | cons x tail ih =>
      cases vs with
      | nil => rfl
      | cons y rest =>
        exact and_congr ((same x List.mem_cons_self).forms ρ hn y)
          (ih (fun a h => same a (List.mem_cons_of_mem _ h)) rest)
  constructor
  · constructor
    · intro a h
      have ⟨n,f⟩ := complete.1 a h
      exact ⟨n,(forms a.subst n _).mp f⟩
    · intro ρ hn vs nf
      obtain ⟨a,ha,δ,nd,obs,vals⟩ := complete.2 ρ hn vs ((forms _ hn _).mpr nf)
      exact ⟨a,ha,δ,nd,fun v hv => obs v ((names v).mpr hv),vals⟩
  · intro a h
    obtain ⟨reconstruct,safe⟩ := arms a h
    exact ⟨fun vs hv => reconstruct vs ((forms _ (complete.1 a h).1 _).mpr hv),
      fun v hv => safe.domain v (fun obs => hv ((names v).mp obs)),
      fun v hv w hw => (safe.ranges v ((names v).mpr hv) w hw).imp (names w).mp id,
      fun t ht w hw => (safe.values t ht w hw).imp (names w).mp id⟩

namespace DHTower
open DHPeer Cancellation
variable {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem occurs_power (s : Symbols sig) (a b : Term sig) (v : Variable) :
    (s.power a b).Occurs v ↔ a.Occurs v ∨ b.Occurs v := by
  constructor
  · rintro ⟨i,h⟩
    change (if i.val = 0 then a else b).Occurs v at h
    split at h <;> first | exact .inl h | exact .inr h
  · rintro (h|h)
    · exact ⟨⟨0,by rw [s.powArity]; decide⟩,h⟩
    · exact ⟨⟨1,by rw [s.powArity]; decide⟩,h⟩

private theorem occurs_tower (s : Symbols sig) (b a : Term sig) (xs : List (Term sig)) (v : Variable) :
    (Spine.tower s b a xs).Occurs v ↔ b.Occurs v ∨ (ACRepresentation.fold s.mul a xs).Occurs v := by
  induction xs generalizing b a with
  | nil => exact occurs_power s b a v
  | cons c cs ih =>
    change (Spine.tower s (s.power b a) c cs).Occurs v ↔ _
    rw [ih,occurs_power]
    change _ ↔ b.Occurs v ∨ (a.Occurs v ∨ _)
    exact or_assoc

private theorem apply_fold (ρ : Substitution sig) (s : Symbols sig) (a : Term sig) (xs : List (Term sig)) :
    ρ.apply (ACRepresentation.fold s.mul a xs) = ACRepresentation.fold s.mul (ρ.apply a) (xs.map ρ.apply) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => exact congrArg (Term.ac s.mul (ρ.apply a)) (ih b)

private theorem packed_map (ρ : Substitution sig) {xs : List (Term sig)} {u} (h : packed s xs = some u) :
    packed s (xs.map ρ.apply) = some (ρ.apply u) := by
  cases xs with
  | nil => cases h
  | cons a as => cases h; exact congrArg some (apply_fold ρ s a as).symm

/-- A single uninstantiated layout comparison covers all normalized caller
assignments. The same proof transports each occurrence in a packed variant
tuple, including stable observations of every original variable. -/
theorem grouped_observation (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (q : Caller.Query sig) (e : Term sig) (groups : List (Term sig))
    (admit : ∀ r ∈ q.fs, StableFactor s (ruleRoot T.rules) r)
    (grouping : ∀ g ∈ e :: groups, ∃ part, packed s part = some g ∧ ∀ t ∈ part, t ∈ q.fs)
    (layout : (Cancellation.flatten s.mul (ACRepresentation.fold s.mul e groups)).Perm
      (Cancellation.flatten s.mul (q.added s))) :
    SameObservation (ruleRoot T.rules) (q.op s) (Spine.tower s (q.symbolic .peer) e groups) := by
  have eq := Cancellation.equiv_of_flatten_perm s.mul layout
  constructor
  · intro v; rw [occurs_tower,occurs_tower]; exact or_congr Iff.rfl (eq.occurs_iff v).symm
  · intro ρ hn u
    change NormalForm _ (ρ.apply (Spine.tower s (q.symbolic .peer) q.first q.rest)) u ↔ _
    rw [Tuple.apply_tower,Tuple.apply_tower]
    let fs := q.fs.map ρ.apply
    have hb : HasSort (ρ.image (q.var .peer)) .msg := by simpa only [q.sorted, Slot.sort] using ρ.sorted (q.var .peer)
    have facts (t) (h : t ∈ fs) : HasSort t .msg ∧ Normal (ruleRoot T.rules) t ∧ Factor s t := by
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
      exact ⟨(q.sortedFactors r hr).subst ρ.image ρ.sorted,admit r hr ρ hn⟩
    have grouped (t) (h : t ∈ ρ.apply e :: groups.map ρ.apply) :
        ∃ part, packed s part = some t ∧ ∀ t ∈ part, t ∈ fs := by
      change t ∈ (e::groups).map ρ.apply at h
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp h
      obtain ⟨part,hp,hs⟩ := grouping g hg
      refine ⟨part.map ρ.apply,packed_map ρ hp,?_⟩
      intro t ht; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ht
      exact List.mem_map_of_mem (hs x hx)
    have both := eq.subst ρ.image
    change EquivB (ρ.apply (ACRepresentation.fold s.mul e groups)) (ρ.apply (ACRepresentation.fold s.mul q.first q.rest)) at both
    rw [apply_fold,apply_fold] at both
    exact (positive_tower_iff inventory pow mul inv unit _ _ _ hb (hn _) facts u).trans
      (grouped_tower_iff inventory pow mul inv unit _ _ _ _ _ hb (hn _) facts grouped (Cancellation.flatten_equiv _ both) u).symm

/-- Repeated power observations and arbitrary stable tuple components receive
the very same answers and freshness guarantees for the caller's original tower. -/
theorem grouped_tuple {R : Root sig} {reference source : Term sig}
    (observation : SameObservation R reference source) (slots : List (Sum Unit (Term sig)))
    (answers : List (Variant sig)) (avoid : List Variable)
    (complete : CompleteVariants R (slots.map (VariantJoin.packedInput (fun _ : Unit => reference))) answers)
    (safe : ∀ a ∈ answers, a.Reconstructible R (slots.map (VariantJoin.packedInput (fun _ : Unit => reference))) ∧
      a.Safe (slots.map (VariantJoin.packedInput (fun _ : Unit => reference))) avoid ∧
      ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v) :
    let query := slots.map (VariantJoin.packedInput (fun _ : Unit => source))
    CompleteVariants R query answers ∧ ∀ a ∈ answers, a.Reconstructible R query ∧ a.Safe query avoid ∧
      ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v := by
  have same : ∀ slot ∈ slots, SameObservation R
      (VariantJoin.packedInput (fun _ : Unit => reference) slot) (VariantJoin.packedInput (fun _ : Unit => source) slot) := by
    intro slot _; cases slot with
    | inl => exact observation
    | inr => exact .refl _ _
  have ⟨hc,hr⟩ := SameObservation.transport avoid same complete (fun a h => ⟨(safe a h).1,(safe a h).2.1⟩)
  exact ⟨hc,fun a h => ⟨(hr a h).1,(hr a h).2,(safe a h).2.2⟩⟩

end DHTower
end Tamarin.Rewriting
