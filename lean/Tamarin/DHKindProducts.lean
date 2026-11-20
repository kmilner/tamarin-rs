import Tamarin.DHPresentation

/-! A DH product redex is always Msg-sorted, even at a kind-level position.
Thus every redex across the two operands lies inside their maximal Msg-sorted
subbag. Keep all other factors, including an isolated unit's ill-sorted
neighbors, as an unchanged AC context. -/
namespace Tamarin.Rewriting.DHPeer
open ShortVariantPaths Balance Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.ACSym]

namespace KindProduct

def msg : Class sig → Bool :=
  Quotient.lift (fun t : Term sig => t.checkSort .msg) (fun _ _ e => SortClash.check_equiv e .msg)

noncomputable def selected (s : Symbols sig) (t : Term sig) := (flatten s.mul t).filter msg

theorem all_msg {t : Term sig} (ht : HasSort t .msg) : selected s t = flatten s.mul t := by
  apply List.filter_eq_self.mpr
  intro k hk
  rw [DHProduct.classes] at hk
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hk
  exact Term.checkSort_complete (s.mulSort ▸ ACRepresentation.flatten_hasSort s.mul t (s.mulSort ▸ ht) _ hu)

omit [DecidableEq sig.ACSym] in
private theorem subbag_of_selected {t u : Term sig} (eq : flatten s.mul u = selected s t) :
    DHProduct.Subbag s.mul u t :=
  ⟨_,by rw [eq]; exact (List.filter_append_perm msg (flatten s.mul t)).symm⟩

private theorem normal_part {R : Root sig} {t u : Term sig} (sub : DHProduct.Subbag s.mul u t)
    (hn : Normal R t) : Normal R u := by
  rcases sub.context with eq | ⟨_,eq⟩
  · exact (normal_equiv R eq).mp hn
  · exact (normal_ac_children s.mul ((normal_equiv R eq).mp hn)).1

omit [DecidableEq sig.ACSym] in
private theorem pack_typed (s : Symbols sig) (ks : List (Class sig))
    (origin : ∀ k ∈ ks, ∃ t : Term sig, flatten s.mul t = [k] ∧ HasSort t .msg) :
    ∃ o, bag s o = ks ∧ ∀ t, o = some t → HasSort t .msg := by
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
      change flatten s.mul y = ks at ho
      refine ⟨some (.ac s.mul x y),by simp [bag,flatten_ac,hx,ho],?_⟩
      intro t ht
      cases ht
      exact s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ tx) (s.mulSort ▸ ty y rfl)

theorem core_exists {R : Root sig} (t : Term sig) (nt : Normal R t) :
    ∃ o, bag s o = selected s t ∧ ∀ u, o = some u → HasSort u .msg ∧ Normal R u := by
  obtain ⟨o,ho,ty⟩ := pack_typed s (selected s t) (by
    intro k hk
    obtain ⟨mem,tk⟩ := List.mem_filter.mp hk
    rw [DHProduct.classes] at mem
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp mem
    exact ⟨u,DHProduct.atom_factors s.mul t u hu,Term.checkSort_sound _ _ tk⟩)
  refine ⟨o,ho,fun u e => ⟨ty u e,normal_part (subbag_of_selected (e ▸ ho)) nt⟩⟩

private def Leaves (s : Symbols sig) (R : Root sig) (t : Term sig) :=
  ∀ u ∈ ACRepresentation.flatten s.mul t, Normal R u

private theorem leaves_mul {R : Root sig} {a b : Term sig} (na : Leaves s R a) (nb : Leaves s R b) :
    Leaves s R (s.product.mul a b) := by
  intro u hu
  exact (List.mem_append.mp (by simpa [DHProduct.Ops.mul,Symbols.product,ACRepresentation.flatten] using hu)).elim
    (na u) (nb u)

private theorem leaves_right_of_equiv {R : Root sig} {whole core rest : Term sig} (nw : Leaves s R whole)
    (eq : EquivB whole (s.product.mul core rest)) : Leaves s R rest := by
  intro t ht
  have key : classOf t ∈ flatten s.mul rest := by
    rw [DHProduct.classes]; exact List.mem_map_of_mem ht
  have mem := (flatten_equiv s.mul eq).mem_iff.mpr (by
    rw [show s.product.mul core rest = .ac s.mul core rest from rfl,flatten_ac]
    exact List.mem_append_right _ key)
  rw [DHProduct.classes] at mem
  obtain ⟨u,hu,h⟩ := List.mem_map.mp mem
  exact (normal_equiv R (Quotient.exact h)).mp (nw u hu)

private theorem normal_with_core (bucket : MulBucket E) (t : Term sig)
    (leaves : Leaves s (ruleRoot T.rules) t) (core : Option (Term sig)) (picked : bag s core = selected s t)
    (nf : ∀ u, core = some u → Normal (ruleRoot T.rules) u) : Normal (ruleRoot T.rules) t := by
  apply DHProduct.subgroup_normal s.mul t leaves
  rintro p q hd ⟨tail,sub⟩ fire
  have typed := bucket.redex_typed hd fire
  have hit := sub.filter msg
  rw [List.filter_append] at hit
  change (selected s t).Perm (selected s p ++ _) at hit
  rw [all_msg (s := s) typed,← picked] at hit
  cases core with
  | none =>
    have emp : flatten s.mul p = [] := (List.append_eq_nil_iff.mp hit.symm.eq_nil).1
    have never := fold_flatten s.mul p
    simp [emp,fold] at never
  | some u =>
    exact ((DHProduct.subgroup_normal_iff s.mul u).mp (nf u rfl)).2 p q hd ⟨_,hit⟩ fire

omit [DecidableEq sig.ACSym] in
theorem selected_mul (s : Symbols sig) (a b : Term sig) :
    selected s (s.product.mul a b) = selected s a ++ selected s b := by
  simp [selected,DHProduct.Ops.mul,Symbols.product,flatten_ac]

/-- Lift any multiplicative invariant through the untouched kind-level factors. -/
theorem paths (mul : MulBucket E) (P : Term sig → Term sig → Prop)
    (respect : ∀ {a b}, EquivB a b → P a b)
    (rebase : ∀ {a b c}, EquivB a b → P b c → P a c)
    (context : ∀ {a b}, P a b → ∀ r, P (s.product.mul a r) (s.product.mul b r))
    {k} (sorted : ∀ a b : Term sig, HasSort a .msg → HasSort b .msg →
      Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, HasSort u .msg ∧ Path (ruleRoot T.rules) k (s.product.mul a b) u ∧
        Normal (ruleRoot T.rules) u ∧ P (s.product.mul a b) u) :
    ∀ a b : Term sig, Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, Path (ruleRoot T.rules) k (s.product.mul a b) u ∧ Normal (ruleRoot T.rules) u ∧ P (s.product.mul a b) u := by
  intro a b na nb
  obtain ⟨oa,ha,pa⟩ := core_exists (s := s) a na
  obtain ⟨ob,hb,pb⟩ := core_exists (s := s) b nb
  have leaves := leaves_mul ((DHProduct.subgroup_normal_iff s.mul a).mp na).1
    ((DHProduct.subgroup_normal_iff s.mul b).mp nb).1
  cases oa with
  | none =>
    change [] = selected s a at ha
    exact ⟨_,.basis (.refl _),normal_with_core mul _ leaves ob (by simpa [selected_mul,← ha] using hb)
      (fun u h => (pb u h).2),respect (.refl _)⟩
  | some x =>
    change flatten s.mul x = selected s a at ha
    obtain ⟨tx,nx⟩ := pa x rfl
    cases ob with
    | none =>
      change [] = selected s b at hb
      exact ⟨_,.basis (.refl _),normal_with_core mul _ leaves (some x) (by simpa [selected_mul,← hb,bag] using ha)
        (fun u h => (pa u h).2),respect (.refl _)⟩
    | some y =>
      change flatten s.mul y = selected s b at hb
      obtain ⟨ty,ny⟩ := pb y rfl
      obtain ⟨u,tu,path,nu,pu⟩ := sorted x y tx ty nx ny
      have picked : flatten s.mul (s.product.mul x y) = selected s (s.product.mul a b) := by
        rw [selected_mul,← ha,← hb]; exact flatten_ac ..
      rcases (subbag_of_selected picked).context with eq | ⟨rest,eq⟩
      · exact ⟨u,path.rebase eq,nu,rebase eq pu⟩
      · have nl := leaves_right_of_equiv leaves eq
        have xy : HasSort (s.product.mul x y) .msg :=
          s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ tx) (s.mulSort ▸ ty)
        have eqf : (selected s (s.product.mul a b)).Perm (selected s (s.product.mul x y) ++ selected s rest) := by
          simpa [selected,flatten_ac] using (flatten_equiv s.mul eq).filter msg
        rw [all_msg xy,← picked] at eqf
        have emp : selected s rest = [] := by
          have h := eqf.length_eq
          simp only [List.length_append] at h
          exact List.length_eq_zero_iff.mp (by omega)
        have res := normal_with_core mul (s.product.mul u rest)
          (leaves_mul ((DHProduct.subgroup_normal_iff s.mul u).mp nu).1 nl) (some u)
          (by simp [bag,selected_mul,all_msg tu,emp]) (fun _ h => by cases h; exact nu)
        have lifted := Path.ac s.mul path (Path.basis (k := 0) (.refl rest))
        rw [Nat.add_zero] at lifted
        exact ⟨_,lifted.rebase eq,res,rebase eq (context pu rest)⟩

end KindProduct

/-- All kind-level products of two normal operands share the sorted operator's
path bound. Only the product of the two maximal sorted subbags can need work. -/
theorem kind_product_paths (inventory : Inventory E) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) :
    ∃ k, ∀ a b : Term sig, Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
      ∃ u, Path (ruleRoot T.rules) k (s.product.mul a b) u ∧ Normal (ruleRoot T.rules) u := by
  obtain ⟨k,sorted⟩ := product_paths inventory mul inv unit
  refine ⟨k,fun a b na nb => ?_⟩
  obtain ⟨u,h,hn,_⟩ := KindProduct.paths mul (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (k := k) (by
      intro x y hx hy nx ny
      obtain ⟨u,tu,hu,nu⟩ := sorted x y hx hy nx ny
      exact ⟨u,tu,hu,nu,trivial⟩) a b na nb
  exact ⟨u,h,hn⟩

end Tamarin.Rewriting.DHPeer
