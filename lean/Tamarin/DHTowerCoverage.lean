import Tamarin.DHTowerReduction

/-! Term-level converse to replay of a positive DH tower exponent. A row
captures both the input image and its normalized output with the same witnesses. -/
namespace Tamarin.Rewriting.DHTower
open DHPeer ConstructorVariants Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

inductive Represents (s : Symbols sig) (R : Root sig) (ts : List (Term sig)) (added Y out : Term sig) : Prop where
  | unchanged (value : EquivB out (s.power Y added))
  | neutral (base : EquivB Y s.neutralTerm) (value : EquivB out s.neutralTerm)
  | tower (b e : Term sig) (sb : HasSort b .msg) (nb : Normal R b) (se : HasSort e .msg) (ne : Normal R e)
      (base : EquivB Y (s.power b e)) (value : EquivB out (s.power b (s.product.mul e added)))
  | cancel (mask : List Bool) (width : mask.length = ts.length) (b r : Term sig)
      (take : packed s (select mask ts) = some r) (pos neg : Option (Term sig))
      (sb : HasSort b .msg) (nb : Normal R b) (positive : Witness s R pos) (negative : Witness s R neg)
      (base : EquivB Y (s.power b (Balance.assemble s pos (append s (some r) neg))))
      (value : EquivB out (powerResult s b (append s pos (packed s (remaining mask ts))) neg))

private theorem pow_congr {a b x y : Term sig} (ea : EquivB a b) (ex : EquivB x y) :
    EquivB (s.power a x) (s.power b y) := by apply EquivB.free; intro i; split <;> assumption

theorem pow_types {a x : Term sig} (ty : HasSort (s.power a x) .msg) : HasSort a .msg ∧ HasSort x .msg := by
  have h := Term.checkSort_complete ty
  simp only [Symbols.power,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at h
  have each (i : Fin (sig.arity s.pow)) := Term.checkSort_sound _ _ (h.2 i (List.mem_finRange i))
  exact ⟨by simpa [s.powInput] using each ⟨0,by rw [s.powArity]; decide⟩,
    by simpa [s.powInput] using each ⟨1,by rw [s.powArity]; decide⟩⟩

private theorem pos_desc {v b out : Term sig} (p n : Option (Term sig))
    (shape : EquivB v (Balance.assemble s p n))
    (only : ∀ u, p = some u → head u ≠ .free s.one)
    (endpt : (v = s.product.one ∧ EquivB out b) ∨ (head v ≠ .free s.one ∧ EquivB out (s.power b v))) :
    EquivB out (powerResult s b p n) := by
  have invNotOne (u : Term sig) : head (s.product.inv u) ≠ .free s.one := by
    intro h; have e := Head.free.inj h; have ar := s.invArity; rw [e,s.oneArity] at ar; contradiction
  have powered (h : head (Balance.assemble s p n) ≠ .free s.one) :
      EquivB out (s.power b (Balance.assemble s p n)) := by
    rcases endpt with ⟨rfl,_⟩|⟨_,has⟩
    · exact False.elim (h shape.head_eq.symm)
    · exact has.trans (pow_congr (.refl _) shape)
  cases p with
  | none => cases n with
    | none =>
      rcases endpt with ⟨_,h⟩|⟨h,_⟩
      · exact h
      · exact False.elim (h shape.head_eq)
    | some n => exact powered (invNotOne n)
  | some p => cases n with
    | none => exact powered (only p rfl)
    | some n => exact powered (fun h => by cases h)

private theorem append_power {e extra : Term sig} {p n : Option (Term sig)}
    (old : EquivB e (Balance.assemble s p n)) (nonunit : head e ≠ .free s.one) :
    EquivB (Balance.assemble s (append s p (some extra)) n) (s.product.mul e extra) := by
  apply EquivB.trans _ (EquivB.ac_congr _ old.symm (.refl _))
  cases p with
  | none => cases n with
    | none => exact False.elim (nonunit old.head_eq)
    | some n => exact .ac_swap ..
  | some p => cases n with
    | none => exact .refl _
    | some n =>
      exact (EquivB.ac_assoc _ _ _ _).trans
        ((EquivB.ac_congr _ (.refl _) (.ac_swap ..)).trans (EquivB.ac_assoc _ _ _ _).symm)

/-- All normalized outputs of the received-base power with a positive product
exponent are represented by one of the emitted kinds of base image. -/
theorem classify_power (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    (ts : List (Term sig)) {added Y out : Term sig} (pack : packed s ts = some added)
    (positive : ∀ t ∈ ts, Factor s t) (normalFactors : ∀ t ∈ ts, Normal (ruleRoot T.rules) t)
    (types : ∀ t ∈ ts, HasSort t .msg) (sY : HasSort Y .msg) (nY : Normal (ruleRoot T.rules) Y)
    (nf : NormalForm (ruleRoot T.rules) (s.power Y added) out) :
    Represents s (ruleRoot T.rules) ts added Y out := by
  classical
  have sa := packed_sorted types added pack
  have ⟨na,au⟩ := packed_factors_normal mul pack positive normalFactors
  by_cases hY : head Y = .free s.pow
  · obtain ⟨b,e,rfl⟩ := splitPower s hY
    obtain ⟨sb,se⟩ := pow_types sY
    obtain ⟨nb,ne,_,_,eu⟩ := (pow.normal_iff sb se).mp nY
    obtain ⟨v,nv,vdesc⟩ := pow.tower_normal_value sb se sa nY na au unit nf
    have sp : HasSort (.ac s.mul e added) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ se) (s.mulSort ▸ sa)
    obtain ⟨m,p,n,ww,old,result,_,wp,wn⟩ := classify_product inventory ts pack positive normalFactors se ne (nv.2.2 _ sp) nv.2.1 nv.1
    let rest := packed s (remaining m ts)
    have rr : ∀ z, append s p rest = some z → head z ≠ .free s.one := by
      have part (x) (hx : x ∈ remaining m ts) : x ∈ ts := select_mem hx
      have restUnit (z) (hz : rest = some z) := (packed_factors_normal mul hz
        (fun x hx => positive x (part _ hx)) (fun x hx => normalFactors x (part _ hx))).2
      cases p with
      | none => exact restUnit
      | some p =>
        cases rest with
        | none => intro z h; cases h; exact (wp _ rfl).2.2
        | some r => intro z h; cases h; intro bad; cases bad
    have value := pos_desc (append s p rest) n result rr vdesc
    cases take : packed s (select m ts) with
    | some r =>
      apply Represents.cancel m ww b r take p n sb nb wp wn (pow_congr (.refl _) ?_) value
      simpa only [take] using old
    | none =>
      have restEq : ∃ extra, rest = some extra ∧ EquivB extra added := by
        have ht := bag_factors s (select m ts) (fun x hx => positive x (select_mem hx))
        rw [take] at ht
        have hr := bag_factors s (remaining m ts) (fun x hx => positive x (select_mem hx))
        have ha := bag_factors s ts positive
        rw [pack] at ha
        have split := (select_perm ww).map classOf
        rw [List.map_append,← ht,← hr,← ha] at split
        change (Cancellation.flatten s.mul added).Perm ([] ++ Balance.bag s rest) at split
        cases hrest : rest with
        | none =>
          rw [hrest] at split
          have h := Cancellation.fold_flatten s.mul added
          rw [List.perm_nil.mp split] at h; cases h
        | some extra =>
          exact ⟨extra,rfl,Cancellation.equiv_of_flatten_perm _ (hrest ▸ split.symm)⟩
      obtain ⟨extra,hrest,eextra⟩ := restEq
      have actual : EquivB e (Balance.assemble s p n) := by simpa only [take,append] using old
      have target := append_power (extra := extra) actual eu
      refine Represents.tower b e sb nb se ne (.refl _) (value.trans ?_)
      rw [hrest]
      have positivePower : powerResult s b (append s p (some extra)) n =
          s.power b (Balance.assemble s (append s p (some extra)) n) := by cases p <;> cases n <;> rfl
      rw [positivePower]
      exact pow_congr (.refl _) (target.trans (.ac_congr _ (.refl _) eextra))
  · by_cases hn : head Y = .free s.neutral
    · obtain rfl : Y = s.neutralTerm := nullary s.neutralArity hn
      have rule := T.fire .neutral (fun _ => added) (fun _ => sa)
      have normal : NormalForm (ruleRoot T.rules) (s.power s.neutralTerm added) s.neutralTerm :=
        ⟨rule,nY,fun _ h => .widen sY (s.powSort ▸ Term.rootSort_le h)⟩
      exact .neutral (.refl _) (inventory.peer_unique_msg pow unit sY sa au nY na nf normal)
    · exact .unchanged (normal_reduces_equiv nf.1 ((pow.normal_iff sY sa).mpr ⟨nY,na,hY,hn,au⟩)).symm

end Tamarin.Rewriting.DHTower
