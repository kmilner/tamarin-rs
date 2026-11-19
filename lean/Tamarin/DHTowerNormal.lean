import Tamarin.DHTowerCoverage
import Tamarin.DHTowerFlatten

/-! Construct a normal form of the flattened power from the active DH rules.
This discharges the existence premise when transporting arbitrary normal
results between different parenthesizations of a received-base tower. -/
namespace Tamarin.Rewriting.DHTower
open DHPeer ConstructorVariants DHProduct
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem mulType {a b : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ ha) (s.mulSort ▸ hb)
private theorem invType {a : Term sig} (ha : HasSort a .msg) : HasSort (s.product.inv a) .msg := by
  rw [← s.invSort]; apply HasSort.free; intro i; simpa [s.invInput] using ha
private theorem powType {a b : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    HasSort (s.power a b) .msg := by
  rw [← s.powSort]; apply HasSort.free; intro i; rw [s.powInput]; split <;> assumption

private theorem plus_factor (mul : MulBucket E) (inverse : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {e r : Term sig} (se : HasSort e .msg)
    (ne : Normal (ruleRoot T.rules) e) (sr : HasSort r .msg) (nr : Normal (ruleRoot T.rules) r)
    (positive : Factor s r) :
    ∃ t, Reduces (ruleRoot T.rules) (s.product.mul e r) t ∧ Normal (ruleRoot T.rules) t ∧ HasSort t .msg := by
  classical
  by_cases one : head e = .free s.one
  · obtain rfl : e = s.product.one := nullary s.oneArity one
    exact ⟨r,.step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule r sr),.refl _⟩,nr,sr⟩
  obtain ⟨t,h⟩ := classify s.product _ s.mulSort E.presentation.invCongr (fun eq => DHPeer.invChild s eq) e r se ne
  refine ⟨t,h.reduces E.presentation.roots.laws sr,?_⟩
  cases h with
  | extend clear =>
    have clean := clean_of_normal E.presentation se ne (fun eq => one eq.head_eq)
    exact ⟨cleanMul mul (clean.extend positive.single (fun eq => positive.nonUnit eq.head_eq)
      (fun _ eq => positive.nonInv eq.head_eq) clear) ne nr,mulType se sr⟩
  | cancel h => exact ⟨unit,s.oneSort ▸ HasSort.free _ _ (fun i => Fin.elim0 (s.oneArity ▸ i))⟩
  | cancelWith u su nu h => exact ⟨nu,su⟩
  | cancelInside v sv nv h => exact ⟨inverse.shrink sr ((normal_equiv _ h).mp ne), invType sv⟩
  | cancelBoth u v hu hv nu nv h =>
    exact ⟨mixedNormal mul inverse (mulType hu (invType (mulType hv sr))) sr ((normal_equiv _ h).mp ne),
      mulType hu (invType hv)⟩

/-- Normalize the old exponent plus a nonempty positive product, one
occurrence at a time. Intermediate unit exponents are legitimate. -/
private theorem accumulate (mul : MulBucket E) (inverse : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (xs : List (Term sig)) (x e : Term sig)
    (se : HasSort e .msg) (ne : Normal (ruleRoot T.rules) e)
    (facts : ∀ r ∈ x :: xs, HasSort r .msg ∧ Normal (ruleRoot T.rules) r ∧ Factor s r) :
    ∃ t, Reduces (ruleRoot T.rules) (s.product.mul e (ACRepresentation.fold s.mul x xs)) t ∧
      Normal (ruleRoot T.rules) t ∧ HasSort t .msg := by
  obtain ⟨sx,nx,px⟩ := facts x List.mem_cons_self
  induction xs generalizing x e with
  | nil => exact plus_factor mul inverse unit se ne sx nx px
  | cons y ys ih =>
    obtain ⟨u,red,nu,su⟩ := plus_factor mul inverse unit se ne sx nx px
    have fy := facts y (by simp)
    obtain ⟨t,tail,nt,st⟩ := ih y u su nu (fun r hr => facts r (List.mem_cons_of_mem x hr)) fy.1 fy.2.1 fy.2.2
    exact ⟨t,(Reduces.basis (EquivB.ac_assoc s.mul e x _).symm).trans
      ((Reduces.ac s.mul red (.basis (.refl _))).trans tail),nt,st⟩

theorem flat_exists (pow : PowerBucket T) (mul : MulBucket E) (inverse : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (Y x : Term sig) (xs : List (Term sig))
    (sy : HasSort Y .msg) (ny : Normal (ruleRoot T.rules) Y)
    (facts : ∀ r ∈ x :: xs, HasSort r .msg ∧ Normal (ruleRoot T.rules) r ∧ Factor s r) :
    ∃ t, NormalForm (ruleRoot T.rules) (s.power Y (ACRepresentation.fold s.mul x xs)) t := by
  classical
  let added := ACRepresentation.fold s.mul x xs
  have packed : packed s (x::xs) = some added := rfl
  have sa := packed_sorted (fun r h => (facts r h).1) _ packed
  have ⟨na,nonunit⟩ := packed_factors_normal mul packed (fun r h => (facts r h).2.2) (fun r h => (facts r h).2.1)
  suffices ∃ t, Reduces (ruleRoot T.rules) (s.power Y added) t ∧ Normal (ruleRoot T.rules) t ∧ HasSort t .msg by
    obtain ⟨t,h,n,st⟩ := this
    exact ⟨t,h,n,fun _ sort => .widen st (s.powSort ▸ Term.rootSort_le sort)⟩
  by_cases power : head Y = .free s.pow
  · obtain ⟨b,e,rfl⟩ := splitPower s power
    obtain ⟨sb,se⟩ := pow_types sy
    obtain ⟨nb,ne,bp,bn,_⟩ := (pow.normal_iff sb se).mp ny
    obtain ⟨v,red,nv,sv⟩ := accumulate mul inverse unit xs x e se ne facts
    let vals (i : Fin 3) := if i = 0 then b else if i = 1 then e else added
    have sorts : ∀ i, HasSort (vals i) .msg := by intro i; unfold vals; split <;> first | assumption | split <;> assumption
    have first : Reduces (ruleRoot T.rules) (s.power (s.power b e) added) (s.power b (s.product.mul e added)) := T.fire .tower vals sorts
    have second : Reduces (ruleRoot T.rules) (s.power b (s.product.mul e added)) (s.power b v) := by
      apply Reduces.free; intro i; split <;> first | exact .basis (.refl _) | exact red
    by_cases one : head v = .free s.one
    · obtain rfl : v = s.product.one := nullary s.oneArity one
      exact ⟨b,(first.trans second).trans (T.fire .expOne (fun _ => b) (fun _ => sb)),nb,sb⟩
    · exact ⟨s.power b v,first.trans second,(pow.normal_iff sb sv).mpr ⟨nb,nv,bp,bn,one⟩,powType sb sv⟩
  · by_cases neutral : head Y = .free s.neutral
    · obtain rfl : Y = s.neutralTerm := nullary s.neutralArity neutral
      exact ⟨_,T.fire .neutral (fun _ => added) (fun _ => sa),ny,sy⟩
    · exact ⟨_,.basis (.refl _),(pow.normal_iff sy sa).mpr ⟨ny,na,power,neutral,nonunit⟩,powType sy sa⟩

theorem positive_tower_iff (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (Y x : Term sig) (xs : List (Term sig)) (sy : HasSort Y .msg) (ny : Normal (ruleRoot T.rules) Y)
    (facts : ∀ r ∈ x :: xs, HasSort r .msg ∧ Normal (ruleRoot T.rules) r ∧ Factor s r) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (Spine.tower s Y x xs) out ↔
    NormalForm (ruleRoot T.rules) (s.power Y (ACRepresentation.fold s.mul x xs)) out :=
  Spine.normalForm_iff_flat pow inventory unit xs sy (facts _ List.mem_cons_self).1
    (fun t h => (facts t (List.mem_cons_of_mem _ h)).1) ny (facts _ List.mem_cons_self).2.1
    (fun t h => (facts t (List.mem_cons_of_mem _ h)).2.1) (flat_exists pow mul inv unit Y x xs sy ny facts) out

private theorem regroup_nf {R : Root sig} {a b out : Term sig} (eq : EquivB a b)
    (nf : NormalForm R a out) : NormalForm R b out :=
  ⟨(Reduces.basis eq.symm).trans nf.1,nf.2.1,fun k h => nf.2.2 k
    (Term.checkSort_sound _ _ ((SortClash.check_equiv eq k).symm ▸ Term.checkSort_complete h))⟩

/-- The adapter also accepts products within the exponent of any power.
Each actual exponent is the packed product of its own group of positive
factors. Arbitrary association, order and repeated occurrences are allowed
in the presentation of the combined product. -/
theorem grouped_tower_iff (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (Y e x : Term sig) (groups xs : List (Term sig))
    (sy : HasSort Y .msg) (ny : Normal (ruleRoot T.rules) Y)
    (facts : ∀ r ∈ x :: xs, HasSort r .msg ∧ Normal (ruleRoot T.rules) r ∧ Factor s r)
    (grouping : ∀ g ∈ e :: groups, ∃ part : List (Term sig), packed s part = some g ∧
      ∀ r ∈ part, r ∈ x :: xs)
    (layout : (Cancellation.flatten s.mul (ACRepresentation.fold s.mul e groups)).Perm
      (Cancellation.flatten s.mul (ACRepresentation.fold s.mul x xs))) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (Spine.tower s Y e groups) out ↔
      NormalForm (ruleRoot T.rules) (s.power Y (ACRepresentation.fold s.mul x xs)) out := by
  have each (g) (mem : g ∈ e :: groups) : HasSort g .msg ∧ Normal (ruleRoot T.rules) g := by
    obtain ⟨_,hp,sub⟩ := grouping g mem
    exact ⟨packed_sorted (fun r h => (facts r (sub _ h)).1) _ hp,
      (packed_factors_normal mul hp (fun r h => (facts r (sub _ h)).2.2) (fun r h => (facts r (sub _ h)).2.1)).1⟩
  have eq : EquivB (s.power Y (ACRepresentation.fold s.mul e groups))
      (s.power Y (ACRepresentation.fold s.mul x xs)) := by
    apply EquivB.free; intro i; split
    · exact .refl _
    · exact Cancellation.equiv_of_flatten_perm _ layout
  obtain ⟨v,hv⟩ := flat_exists pow mul inv unit Y x xs sy ny facts
  exact (Spine.normalForm_iff_flat pow inventory unit groups sy (each e List.mem_cons_self).1
    (fun g h => (each g (List.mem_cons_of_mem _ h)).1) ny (each e List.mem_cons_self).2
    (fun g h => (each g (List.mem_cons_of_mem _ h)).2) ⟨v,regroup_nf eq.symm hv⟩ out).trans
      ⟨regroup_nf eq,regroup_nf eq.symm⟩

end Tamarin.Rewriting.DHTower
