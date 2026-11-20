import Tamarin.MixedReconstruction

/-! A complete set of ordinary unifiers over a query's dictionary remains
complete after adding arbitrary free, C, AC and atom identities. Abstract
foreign-rooted values by fresh slots for their B-classes, then restore them
with a single sorted substitution shared by the entire answer. -/
namespace Tamarin.SignatureExtension
variable {s x : Signature}

/-- Disjoint additional declarations may use any arities and sort profiles. -/
abbrev joined (s x : Signature) : Signature where
  FreeSym := Sum s.FreeSym x.FreeSym
  CSym := Sum s.CSym x.CSym
  ACSym := Sum s.ACSym x.ACSym
  Atom := Sum s.Atom x.Atom
  arity := Sum.elim s.arity x.arity
  inputSort := fun f => match f with | .inl g => s.inputSort g | .inr g => x.inputSort g
  outputSort := Sum.elim s.outputSort x.outputSort
  cSort := Sum.elim s.cSort x.cSort
  acSort := Sum.elim s.acSort x.acSort
  atomSort := Sum.elim s.atomSort x.atomSort

def embed (x : Signature) : Term s → Term (joined s x)
  | .var v => .var v
  | .atom a => .atom (.inl a)
  | .free f as => .free (.inl f) fun i => embed x (as i)
  | .comm f a b => .comm (.inl f) (embed x a) (embed x b)
  | .ac f a b => .ac (.inl f) (embed x a) (embed x b)

private theorem embed_sort {t : Term s} {k} (h : HasSort t k) : HasSort (embed x t) k := by
  induction h with
  | var => exact .var _
  | atom => exact .atom _
  | free _ _ _ ih => exact .free _ _ ih
  | comm _ _ _ _ _ ih ik => exact .comm _ _ _ ih ik
  | ac _ _ _ _ _ ih ik => exact .ac _ _ _ ih ik
  | widen _ h ih => exact .widen ih h

private theorem embed_eq {a b : Term s} (h : EquivB a b) : EquivB (embed x a) (embed x b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free _ _ _ _ ih => exact .free _ _ _ ih
  | comm_congr _ _ _ ih ik => exact .comm_congr _ ih ik
  | ac_congr _ _ _ ih ik => exact .ac_congr _ ih ik
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

def liftSubst (x : Signature) (σ : Substitution s) : Substitution (joined s x) where
  image v := embed x (σ.image v)
  support := σ.support
  outside v hv := by rw [σ.outside v hv]; rfl
  sorted v := embed_sort (σ.sorted v)

private theorem embed_apply (t : Term s) (σ : Substitution s) :
    (liftSubst x σ).apply (embed x t) = embed x (σ.apply t) := by
  induction t with
  | var | atom => rfl
  | free f as ih => exact congrArg (Term.free (sig := joined s x) (.inl f)) (funext ih)
  | ac _ _ _ ih ik | comm _ _ _ ih ik => simp only [Substitution.apply,Term.subst,embed] at *; rw [ih,ik]

private theorem embed_occurs (t : Term s) (v) : (embed x t).Occurs v ↔ t.Occurs v := by
  induction t with
  | var | atom => rfl
  | free _ _ ih => exact exists_congr (fun i => ih i)
  | ac _ _ _ ih ik | comm _ _ _ ih ik => exact or_congr ih ik

def query (x : Signature) (p : Problem s) : Problem (joined s x) :=
  p.map fun e => ⟨embed x e.lhs,embed x e.rhs⟩

private theorem occurs (p : Problem s) (v) : (query x p).Occurs v ↔ p.Occurs v := by
  constructor
  · rintro ⟨_,hm,occ⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
    exact ⟨e,he,occ.imp (embed_occurs ..).mp (embed_occurs ..).mp⟩
  · rintro ⟨e,he,occ⟩
    exact ⟨_,List.mem_map_of_mem he,occ.imp (embed_occurs ..).mpr (embed_occurs ..).mpr⟩

open Cancellation MixedUnification
private noncomputable def slot (bank : List (Term (joined s x))) (t : Term (joined s x)) : Variable := by
  classical
  exact ⟨(bank.map classOf).idxOf (classOf t),t.rootSort⟩

private theorem slot_eq (bank : List (Term (joined s x))) {a b} (eq : EquivB a b) :
    slot bank a = slot bank b := by
  classical
  have cl : classOf a = classOf b := Quotient.sound eq
  simp [slot,cl,Term.rootSort_equiv eq]

private theorem equal_of_slot (bank : List (Term (joined s x))) {a b} (ha : a ∈ bank) (hb : b ∈ bank)
    (eq : slot bank a = slot bank b) : EquivB a b := by
  classical
  have ia := List.idxOf_lt_length_of_mem (List.mem_map_of_mem (f := classOf) ha)
  have ib := List.idxOf_lt_length_of_mem (List.mem_map_of_mem (f := classOf) hb)
  have same := congrArg Variable.id eq
  change (bank.map classOf).idxOf (classOf a) = (bank.map classOf).idxOf (classOf b) at same
  apply Quotient.exact (s := termSetoid _)
  have one := List.getElem?_eq_getElem ia
  have two := List.getElem?_eq_getElem ib
  rw [List.getElem_idxOf] at one two
  rw [same] at one
  exact Option.some.inj (one.symm.trans two)

private noncomputable def abstractTerm (bank : List (Term (joined s x))) : Term (joined s x) → Term s
  | t@(.var _) => .var (slot bank t)
  | t@(.atom a) => match a with | .inl c => .atom c | .inr _ => .var (slot bank t)
  | t@(.free f as) => match f with
    | .inl g => .free g fun i => abstractTerm bank (as i)
    | .inr _ => .var (slot bank t)
  | t@(.comm f a b) => match f with
    | .inl g => .comm g (abstractTerm bank a) (abstractTerm bank b)
    | .inr _ => .var (slot bank t)
  | t@(.ac f a b) => match f with
    | .inl g => .ac g (abstractTerm bank a) (abstractTerm bank b)
    | .inr _ => .var (slot bank t)

private theorem abstract_eq (bank : List (Term (joined s x))) {a b} (h : EquivB a b) :
    EquivB (abstractTerm bank a) (abstractTerm bank b) := by
  have collapsed {u v} (eq : EquivB u v) : EquivB (sig := s) (.var (slot bank u)) (.var (slot bank v)) :=
    slot_eq bank eq ▸ .refl _
  induction h with
  | refl => exact .refl _
  | trans _ _ ih ik => exact ih.trans ik
  | symm _ ih => exact ih.symm
  | free f l r h ih => cases f with
    | inl => exact .free _ _ _ ih
    | inr => exact collapsed (.free _ _ _ h)
  | ac_congr f l r ih ik => cases f with
    | inl => exact .ac_congr _ ih ik
    | inr => exact collapsed (.ac_congr _ l r)
  | comm_congr f l r ih ik => cases f with
    | inl => exact .comm_congr _ ih ik
    | inr => exact collapsed (.comm_congr _ l r)
  | comm_swap f a b => cases f with
    | inl => exact .comm_swap _ _ _
    | inr => exact collapsed (.comm_swap _ _ _)
  | ac_swap f a b => cases f with
    | inl => exact .ac_swap _ _ _
    | inr => exact collapsed (.ac_swap _ _ _)
  | ac_assoc f a b c => cases f with
    | inl => exact .ac_assoc _ _ _ _
    | inr => exact collapsed (.ac_assoc _ _ _ _)

private theorem abstract_sort (bank : List (Term (joined s x))) {t k} (h : HasSort t k) :
    HasSort (abstractTerm bank t) k := by
  induction h with
  | var => exact .var _
  | atom a => cases a with | inl => exact .atom _ | inr => exact .var _
  | free f as _ ih => cases f with | inl => exact .free _ _ ih | inr => exact .var _
  | comm f a b _ _ ih ik => cases f with | inl => exact .comm _ _ _ ih ik | inr => exact .var _
  | ac f a b _ _ ih ik => cases f with | inl => exact .ac _ _ _ ih ik | inr => exact .var _
  | widen _ h ih => exact .widen ih h

private theorem abstract_apply (bank : List (Term (joined s x))) (t : Term s) (ρ : Substitution (joined s x)) :
    abstractTerm bank (ρ.apply (embed x t)) = t.subst (fun v => abstractTerm bank (ρ.image v)) := by
  induction t with
  | var | atom => rfl
  | free f as ih => exact congrArg (Term.free f) (funext ih)
  | ac f a b ih ik => exact (congrArg (fun l => Term.ac f l _) ih).trans (congrArg (Term.ac f _) ik)
  | comm f a b ih ik => exact (congrArg (fun l => Term.comm f l _) ih).trans (congrArg (Term.comm f _) ik)

private noncomputable def restore (bank : List (Term (joined s x))) : Substitution (joined s x) := by
  classical
  let has (w : Variable) := ∃ t ∈ bank, slot bank t = w ∧ HasSort t w.sort
  exact {
    image := fun w => if h : has w then h.choose else .var w
    support := bank.map (slot bank)
    outside := fun w h => dite_eq_right (fun yes => h (List.mem_map.mpr
      ⟨yes.choose,yes.choose_spec.1,yes.choose_spec.2.1⟩))
    sorted := fun w => by
      split
      next h => exact h.choose_spec.2.2
      next => exact .var _ }

private theorem restore_slot (bank : List (Term (joined s x))) {t} (ht : t ∈ bank)
    (sort : HasSort t t.rootSort) : EquivB t ((restore bank).image (slot bank t)) := by
  classical
  unfold restore
  dsimp only
  split
  next h => exact equal_of_slot bank ht h.choose_spec.1 h.choose_spec.2.1.symm
  next no => exact (no ⟨t,ht,rfl,sort⟩).elim

private theorem restore_abstract (bank : List (Term (joined s x))) {t k} (sorted : HasSort t k)
    (all : ∀ u ∈ subterms t, u ∈ bank) : EquivB t ((restore bank).apply (embed x (abstractTerm bank t))) := by
  induction sorted with
  | var v => exact restore_slot bank (all _ (by simp [subterms])) (.var _)
  | atom a => cases a with
    | inl => exact .refl _
    | inr => exact restore_slot bank (all _ (by simp [subterms])) (.atom _)
  | free f as h ih =>
    cases f with
    | inl => exact .free _ _ _ fun i => ih i (fun u hu => all _ (List.mem_cons_of_mem _
        (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hu⟩)))
    | inr => exact restore_slot bank (all _ List.mem_cons_self) (.free _ _ h)
  | ac f a b ha hb ia ib | comm f a b ha hb ia ib =>
    cases f with
    | inr => first
      | exact restore_slot bank (all _ List.mem_cons_self) (.ac _ _ _ ha hb)
      | exact restore_slot bank (all _ List.mem_cons_self) (.comm _ _ _ ha hb)
    | inl =>
      have left := ia (fun u hu => all _ (List.mem_cons_of_mem _ (List.mem_append_left _ hu)))
      have right := ib (fun u hu => all _ (List.mem_cons_of_mem _ (List.mem_append_right _ hu)))
      first | exact .ac_congr _ left right | exact .comm_congr _ left right
  | widen _ _ ih => exact ih all

/-- Embedding every answer preserves full sorted completeness in any enlarged
signature. Concrete instances may use foreign heads even inside query AC terms. -/
theorem correctIn (x : Signature) (p : Problem s) (avoid) {as : List (Substitution s)}
    (h : (Outcome.complete as).CorrectIn p avoid) :
    (Outcome.complete (as.map (liftSubst x))).CorrectIn (query x p) avoid := by
  classical
  constructor
  · constructor
    · intro τ ht e he
      obtain ⟨σ,hs,rfl⟩ := List.mem_map.mp ht
      obtain ⟨orig,hm,rfl⟩ := List.mem_map.mp he
      simpa only [embed_apply] using embed_eq (x := x) (h.mathematical.sound _ hs orig hm)
    · intro ρ sol
      let bank := p.variables.flatMap fun v => subterms (ρ.image v)
      let img := fun v => abstractTerm bank (ρ.image v)
      let τ : Substitution s := {
        image := fun v => if v ∈ p.variables then img v else .var v
        support := p.variables
        outside := by intro v hv; simp [hv]
        sorted := by
          intro v; split
          next => exact abstract_sort _ (ρ.sorted v)
          next => exact .var _ }
      have onQ {v} (hv : p.Occurs v) : τ.image v = img v := ite_eq_left ((p.mem_variables _).mpr hv)
      have solves : p.Solves τ := by
        intro e he
        have same (t : Term s) (live : ∀ v, t.Occurs v → p.Occurs v) :
            τ.apply t = abstractTerm bank (ρ.apply (embed x t)) := by
          rw [abstract_apply]; exact Term.subst_eq_of_agree _ _ _ (fun v hv => onQ (live v hv))
        rw [same _ (fun v hv => ⟨e,he,.inl hv⟩),same _ (fun v hv => ⟨e,he,.inr hv⟩)]
        exact abstract_eq bank (sol _ (List.mem_map_of_mem he))
      obtain ⟨σ,hs,δ,agree⟩ := h.mathematical.covers τ solves
      refine ⟨_,List.mem_map_of_mem hs,(restore bank).compose (liftSubst x δ),?_⟩
      intro v hv
      have source := (occurs p v).mp hv
      have one := restore_abstract bank (ρ.sorted v) (fun u hu => List.mem_flatMap.mpr
        ⟨v,(p.mem_variables _).mpr source,hu⟩)
      have eq := agree v source
      rw [onQ source] at eq
      have two := (embed_eq (x := x) eq).subst (restore bank).image
      change EquivB _ (((restore bank).compose (liftSubst x δ)).apply (embed x (σ.image v)))
      rw [Substitution.apply_compose,embed_apply]
      exact one.trans two
  · intro τ ht v hv
    obtain ⟨σ,hs,rfl⟩ := List.mem_map.mp ht
    change embed x (σ.image v) = _
    rw [h.domain _ hs v (fun occ => hv ((occurs p v).mpr occ))]; rfl
  · intro τ ht v hv w hw fresh
    obtain ⟨σ,hs,rfl⟩ := List.mem_map.mp ht
    exact h.fresh _ hs v ((occurs p v).mp hv) w ((embed_occurs ..).mp hw)
      (fun occ => fresh ((occurs p w).mpr occ))

end Tamarin.SignatureExtension
