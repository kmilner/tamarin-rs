import Tamarin.OperatorVariantBounds
import Tamarin.DHProduct
import Tamarin.SortClash

/-! Lift a bounded path for sorted AC operands to the full term kind.
When every root redex at the operator is Msg-sorted, it lies entirely
in the maximal Msg subbag. All other factors stay in the surrounding context. -/
namespace Tamarin.Rewriting.SortedAC
open ShortVariantPaths Cancellation ConstructorVariants
variable {sig : Signature} {f : sig.ACSym} {R : Root sig}
variable [DecidableEq sig.ACSym]

noncomputable def bag (f : sig.ACSym) : Option (Term sig) → List (Class sig)
  | none => []
  | some t => flatten f t

def msg : Class sig → Bool :=
  Quotient.lift (fun t : Term sig => t.checkSort .msg) (fun _ _ e => SortClash.check_equiv e .msg)

noncomputable def selected (f : sig.ACSym) (t : Term sig) := (flatten f t).filter msg

theorem all_msg (sort : sig.acSort f = .msg) {t : Term sig} (ht : HasSort t .msg) : selected f t = flatten f t := by
  apply List.filter_eq_self.mpr
  intro k hk
  rw [DHProduct.classes] at hk
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hk
  exact Term.checkSort_complete (sort ▸ ACRepresentation.flatten_hasSort f t (sort ▸ ht) _ hu)

omit [DecidableEq sig.ACSym] in
private theorem subbag_of_selected {t u : Term sig} (eq : flatten f u = selected f t) :
    DHProduct.Subbag f u t :=
  ⟨_,by rw [eq]; exact (List.filter_append_perm msg (flatten f t)).symm⟩

private theorem normal_part {R : Root sig} {t u : Term sig} (sub : DHProduct.Subbag f u t)
    (hn : Normal R t) : Normal R u := by
  rcases sub.context with eq | ⟨_,eq⟩
  · exact (normal_equiv R eq).mp hn
  · exact (normal_ac_children f ((normal_equiv R eq).mp hn)).1

omit [DecidableEq sig.ACSym] in
private theorem pack_typed (f : sig.ACSym) (sort : sig.acSort f = .msg) (ks : List (Class sig))
    (origin : ∀ k ∈ ks, ∃ t : Term sig, flatten f t = [k] ∧ HasSort t .msg) :
    ∃ o, bag f o = ks ∧ ∀ t, o = some t → HasSort t .msg := by
  induction ks with
  | nil => exact ⟨none,rfl,by simp⟩
  | cons k ks ih =>
    obtain ⟨x,hx,tx⟩ := origin k List.mem_cons_self
    obtain ⟨o,ho,ty⟩ := ih (fun a ha => origin _ (List.mem_cons_of_mem _ ha))
    cases o with
    | none =>
      change [] = ks at ho
      subst ks
      exact ⟨some x,hx,by simpa using tx⟩
    | some y =>
      change flatten f y = ks at ho
      refine ⟨some (.ac f x y),by simp [bag,flatten_ac,hx,ho],?_⟩
      intro t ht
      cases ht
      exact sort ▸ HasSort.ac f _ _ (sort ▸ tx) (sort ▸ ty y rfl)

theorem core_exists (sort : sig.acSort f = .msg) {R : Root sig} (t : Term sig) (nt : Normal R t) :
    ∃ o, bag f o = selected f t ∧ ∀ u, o = some u → HasSort u .msg ∧ Normal R u := by
  obtain ⟨o,ho,ty⟩ := pack_typed f sort (selected f t) (by
    intro k hk
    obtain ⟨mem,tk⟩ := List.mem_filter.mp hk
    rw [DHProduct.classes] at mem
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp mem
    exact ⟨u,DHProduct.atom_factors f t u hu,Term.checkSort_sound _ _ tk⟩)
  refine ⟨o,ho,fun u e => ⟨ty u e,normal_part (subbag_of_selected (e ▸ ho)) nt⟩⟩

private def Leaves (f : sig.ACSym) (R : Root sig) (t : Term sig) :=
  ∀ u ∈ ACRepresentation.flatten f t, Normal R u

private theorem leaves_mul {R : Root sig} {a b : Term sig} (na : Leaves f R a) (nb : Leaves f R b) :
    Leaves f R (Term.ac f a b) := by
  intro u hu
  exact (List.mem_append.mp (by simpa [ACRepresentation.flatten] using hu)).elim
    (na u) (nb u)

private theorem leaves_right_of_equiv {R : Root sig} {whole core rest : Term sig} (nw : Leaves f R whole)
    (eq : EquivB whole (Term.ac f core rest)) : Leaves f R rest := by
  intro t ht
  have key : classOf t ∈ flatten f rest := by
    rw [DHProduct.classes]; exact List.mem_map_of_mem ht
  have mem := (flatten_equiv f eq).mem_iff.mpr (by
    rw [flatten_ac]
    exact List.mem_append_right _ key)
  rw [DHProduct.classes] at mem
  obtain ⟨u,hu,h⟩ := List.mem_map.mp mem
  exact (normal_equiv R (Quotient.exact h)).mp (nw u hu)

private theorem normal_with_core (sort : sig.acSort f = .msg) (redex : ∀ {p q}, head p = .ac f → R p q → HasSort p .msg) (t : Term sig)
    (leaves : Leaves f R t) (core : Option (Term sig)) (picked : bag f core = selected f t)
    (nf : ∀ u, core = some u → Normal R u) : Normal R t := by
  apply DHProduct.subgroup_normal f t leaves
  rintro p q hd ⟨tail,sub⟩ fire
  have typed := redex hd fire
  have hit := sub.filter msg
  rw [List.filter_append] at hit
  change (selected f t).Perm (selected f p ++ _) at hit
  rw [all_msg sort typed,← picked] at hit
  cases core with
  | none =>
    have emp : flatten f p = [] := (List.append_eq_nil_iff.mp hit.symm.eq_nil).1
    have never := fold_flatten f p
    simp [emp,fold] at never
  | some u =>
    exact ((DHProduct.subgroup_normal_iff f u).mp (nf u rfl)).2 p q hd ⟨_,hit⟩ fire

omit [DecidableEq sig.ACSym] in
theorem selected_mul (f : sig.ACSym) (a b : Term sig) :
    selected f (Term.ac f a b) = selected f a ++ selected f b := by
  simp [selected,flatten_ac]

/-- Lift a bounded path and its multiplicative invariant through any untouched kind-level factors. -/
theorem paths (sort : sig.acSort f = .msg) (redex : ∀ {p q}, head p = .ac f → R p q → HasSort p .msg) (P : Term sig → Term sig → Prop)
    (respect : ∀ {a b}, EquivB a b → P a b)
    (rebase : ∀ {a b c}, EquivB a b → P b c → P a c)
    (context : ∀ {a b}, P a b → ∀ r, P (Term.ac f a r) (Term.ac f b r))
    {k} (sorted : ∀ a b : Term sig, HasSort a .msg → HasSort b .msg →
      Normal R a → Normal R b →
      ∃ u, HasSort u .msg ∧ Path R k (Term.ac f a b) u ∧
        Normal R u ∧ P (Term.ac f a b) u) :
    ∀ a b : Term sig, Normal R a → Normal R b →
      ∃ u, Path R k (Term.ac f a b) u ∧ Normal R u ∧ P (Term.ac f a b) u := by
  intro a b na nb
  obtain ⟨oa,ha,pa⟩ := core_exists sort a na
  obtain ⟨ob,hb,pb⟩ := core_exists sort b nb
  have leaves := leaves_mul ((DHProduct.subgroup_normal_iff f a).mp na).1
    ((DHProduct.subgroup_normal_iff f b).mp nb).1
  cases oa with
  | none =>
    change [] = selected f a at ha
    exact ⟨_,.basis (.refl _),normal_with_core sort redex _ leaves ob (by simpa [selected_mul,← ha] using hb)
      (fun u h => (pb u h).2),respect (.refl _)⟩
  | some x =>
    change flatten f x = selected f a at ha
    obtain ⟨tx,nx⟩ := pa x rfl
    cases ob with
    | none =>
      change [] = selected f b at hb
      exact ⟨_,.basis (.refl _),normal_with_core sort redex _ leaves (some x) (by simpa [selected_mul,← hb,bag] using ha)
        (fun u h => (pa u h).2),respect (.refl _)⟩
    | some y =>
      change flatten f y = selected f b at hb
      obtain ⟨ty,ny⟩ := pb y rfl
      obtain ⟨u,tu,path,nu,pu⟩ := sorted x y tx ty nx ny
      have picked : flatten f (Term.ac f x y) = selected f (Term.ac f a b) := by
        rw [selected_mul,← ha,← hb]; exact flatten_ac ..
      rcases (subbag_of_selected picked).context with eq | ⟨rest,eq⟩
      · exact ⟨u,path.rebase eq,nu,rebase eq pu⟩
      · have nl := leaves_right_of_equiv leaves eq
        have xy : HasSort (Term.ac f x y) .msg :=
          sort ▸ HasSort.ac f _ _ (sort ▸ tx) (sort ▸ ty)
        have eqf : (selected f (Term.ac f a b)).Perm (selected f (Term.ac f x y) ++ selected f rest) := by
          simpa [selected,flatten_ac] using (flatten_equiv f eq).filter msg
        rw [all_msg sort xy,← picked] at eqf
        have emp : selected f rest = [] := by
          have h := eqf.length_eq
          simp only [List.length_append] at h
          exact List.length_eq_zero_iff.mp (by omega)
        have res := normal_with_core sort redex (Term.ac f u rest)
          (leaves_mul ((DHProduct.subgroup_normal_iff f u).mp nu).1 nl) (some u)
          (by simp [bag,selected_mul,all_msg sort tu,emp]) (fun _ h => by cases h; exact nu)
        have lifted := Path.ac f path (Path.basis (k := 0) (.refl rest))
        rw [Nat.add_zero] at lifted
        exact ⟨_,lifted.rebase eq,res,rebase eq (context pu rest)⟩

end Tamarin.Rewriting.SortedAC
