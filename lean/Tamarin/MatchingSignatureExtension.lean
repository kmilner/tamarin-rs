import Tamarin.SignatureExtension
import Tamarin.Matching

/-! Directional answers transfer to larger signatures with exact agreement
on pattern variables. The subject stays rigid, so observing any additional
symbol in a putative matcher's image would also observe it in the subject. -/
namespace Tamarin.SignatureExtension
variable {s x : Signature}

/-- Retract an extended term. The replacement for a foreign head has its
declared sort; its identity is irrelevant because matched images are local. -/
def restrictTerm : Term (joined s x) → Term s
  | .var v => .var v
  | .atom a => match a with | .inl b => .atom b | .inr b => .var ⟨0,x.atomSort b⟩
  | .free f as => match f with
    | .inl g => .free g fun i => restrictTerm (as i)
    | .inr g => .var ⟨0,x.outputSort g⟩
  | .comm f a b => match f with
    | .inl g => .comm g (restrictTerm a) (restrictTerm b)
    | .inr g => .var ⟨0,x.cSort g⟩
  | .ac f a b => match f with
    | .inl g => .ac g (restrictTerm a) (restrictTerm b)
    | .inr g => .var ⟨0,x.acSort g⟩

def Local : Term (joined s x) → Prop
  | .var _ => True
  | .atom a => match a with | .inl _ => True | .inr _ => False
  | .free f as => match f with | .inl _ => ∀ i, Local (as i) | .inr _ => False
  | .comm f a b => match f with | .inl _ => Local a ∧ Local b | .inr _ => False
  | .ac f a b => match f with | .inl _ => Local a ∧ Local b | .inr _ => False

theorem embedding_local (t : Term s) : Local (embed x t) := by
  induction t with
  | var | atom => trivial
  | free _ _ ih => exact ih
  | ac _ _ _ ih ik | comm _ _ _ ih ik => exact ⟨ih,ik⟩

theorem local_equiv {a b : Term (joined s x)} (h : EquivB a b) : Local a ↔ Local b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f _ _ _ ih => cases f <;> first | rfl | exact forall_congr' ih
  | ac_congr f _ _ ih ik | comm_congr f _ _ ih ik =>
    cases f <;> first | rfl | exact and_congr ih ik
  | ac_swap f | comm_swap f => cases f <;> first | rfl | exact and_comm
  | ac_assoc f => cases f <;> first | rfl | exact and_assoc

theorem restrict_embed (t : Term s) : restrictTerm (embed x t) = t := by
  induction t with
  | var | atom => rfl
  | free f args ih => exact congrArg (Term.free f) (funext ih)
  | comm f a b ih ik | ac f a b ih ik => simp [embed,restrictTerm,ih,ik]

theorem embed_restrict (t : Term (joined s x)) (inside : Local t) : embed x (restrictTerm t) = t := by
  induction t with
  | var => rfl
  | atom a => cases a <;> first | rfl | contradiction
  | free f args ih => cases f with
    | inr => contradiction
    | inl g => exact congrArg (Term.free (sig := joined s x) (.inl g)) (funext (fun i => ih i (inside i)))
  | ac f a b ih ik | comm f a b ih ik =>
    cases f with
    | inr => contradiction
    | inl g => simp [restrictTerm,embed,ih inside.1,ik inside.2]

theorem restrict_eq {a b : Term (joined s x)} (h : EquivB a b) :
    EquivB (restrictTerm a) (restrictTerm b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f _ _ _ ih => cases f <;> first | exact .refl _ | exact .free _ _ _ ih
  | ac_congr f _ _ ih ik | comm_congr f _ _ ih ik =>
    cases f <;> first | exact .refl _ | exact .ac_congr _ ih ik | exact .comm_congr _ ih ik
  | ac_swap f | comm_swap f => cases f <;> first | exact .refl _ | exact .ac_swap _ _ _ | exact .comm_swap _ _ _
  | ac_assoc f => cases f <;> first | exact .refl _ | exact .ac_assoc _ _ _ _

theorem restrict_sort {t : Term (joined s x)} {k} (h : HasSort t k) :
    HasSort (restrictTerm t) k := by
  induction h with
  | var => exact .var _
  | atom a => cases a <;> first | exact .atom _ | exact .var _
  | free f _ _ ih => cases f <;> first | exact .free _ _ ih | exact .var _
  | ac f _ _ _ _ ih ik | comm f _ _ _ _ ih ik =>
    cases f <;> first | exact .var _ | exact .ac _ _ _ ih ik | exact .comm _ _ _ ih ik
  | widen _ h ih => exact .widen ih h

def restrictSubst (ρ : Substitution (joined s x)) : Substitution s where
  image v := restrictTerm (ρ.image v)
  support := ρ.support
  outside v hv := by rw [ρ.outside v hv]; rfl
  sorted v := restrict_sort (ρ.sorted v)

theorem restrict_apply (ρ : Substitution (joined s x)) (t : Term s) :
    (restrictSubst ρ).apply t = restrictTerm (ρ.apply (embed x t)) := by
  induction t with
  | var | atom => rfl
  | free f args ih => exact congrArg (Term.free f) (funext ih)
  | ac f a b ih ik | comm f a b ih ik => simp [Substitution.apply,Term.subst,embed,restrictTerm] at *; exact ⟨ih,ik⟩

theorem local_image (ρ : Substitution (joined s x)) (t : Term s) {v} (occ : t.Occurs v)
    (inside : Local (ρ.apply (embed x t))) : Local (ρ.image v) := by
  induction t with
  | var => exact occ ▸ inside
  | atom => contradiction
  | free _ _ ih => obtain ⟨i,h⟩ := occ; exact ih i h (inside i)
  | ac _ _ _ ih ik | comm _ _ _ ih ik => exact occ.elim (fun h => ih h inside.1) (fun h => ik h inside.2)

private theorem observed (p : Problem s) (v) : Matching.Observed (query x p) v ↔ Matching.Observed p v := by
  constructor
  · rintro ⟨_,hm,occ⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
    exact ⟨e,he,(embed_occurs ..).mp occ⟩
  · rintro ⟨e,he,occ⟩
    exact ⟨_,List.mem_map_of_mem he,(embed_occurs ..).mpr occ⟩

theorem matching (x : Signature) (p : Problem s) {bindable : Variable → Prop} {as : List (Substitution s)}
    (ok : Matching.Complete p bindable as) :
    Matching.Complete (query x p) bindable (as.map (liftSubst x)) := by
  constructor
  · intro τ hτ
    obtain ⟨σ,hs,rfl⟩ := List.mem_map.mp hτ
    obtain ⟨sat,sc⟩ := ok.sound σ hs
    constructor
    · intro _ member
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp member
      simpa only [embed_apply] using embed_eq (x := x) (sat e he)
    · intro v off
      change embed x (σ.image v) = _
      rw [sc v (fun h => off ⟨(observed p v).mpr h.1,h.2⟩)]
      rfl
  · intro ρ sat sc
    have one (e) (he : e ∈ p) : EquivB (ρ.apply (embed x e.lhs)) (embed x e.rhs) :=
      sat _ (List.mem_map_of_mem he)
    have sat' : Matching.Matches p (restrictSubst ρ) := by
      intro e he
      simpa only [restrict_apply,restrict_embed] using restrict_eq (one e he)
    have sc' : Matching.Scoped p bindable (restrictSubst ρ) := by
      intro v off
      change restrictTerm (ρ.image v) = _
      rw [sc v (fun h => off ⟨(observed p v).mp h.1,h.2⟩)]
      rfl
    obtain ⟨σ,hs,agree⟩ := ok.covers _ sat' sc'
    refine ⟨_,List.mem_map_of_mem hs,?_⟩
    intro v live
    have here := (observed p v).mp live
    obtain ⟨e,he,hv⟩ := here
    have inside := local_image ρ e.lhs hv ((local_equiv (one e he)).mpr (embedding_local _))
    have eq := embed_eq (x := x) (agree v ⟨e,he,hv⟩)
    change EquivB (embed x (restrictTerm (ρ.image v))) _ at eq
    rw [embed_restrict _ inside] at eq
    exact eq

end Tamarin.SignatureExtension
