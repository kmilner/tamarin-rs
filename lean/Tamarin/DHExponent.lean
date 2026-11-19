import Tamarin.DHExponentPacket
import Tamarin.DHTowerFlatten
import Tamarin.DHTowerSound

/-! Classify an unrestricted, irreducible exponent after multiplication by
one positive factor. Every observation of the exponent shares the witnesses
chosen by this classification. -/
namespace Tamarin.Rewriting.DHExponent
open DHPeer ConstructorVariants DHProduct

variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

def env (y r p n : Term sig) : Slot → Term sig
  | .peer => y
  | .fresh | .base => r
  | .pos => p
  | .neg => n

structure Realizes (s : Symbols sig) (R : Root sig) (y r : Term sig) (k : Branch)
    (v : Slot → Term sig) : Prop where
  typed : ∀ i, HasSort (v i) .msg
  normal : ∀ i, Normal R (v i)
  image : EquivB y (k.image.eval s v)
  product : NormalForm R (s.product.mul y r) (k.result.eval s v)
  oldUnit : head y = .free s.one ↔ k = .unit
  newUnit : head (k.result.eval s v) = .free s.one ↔ k = .cancelAll

theorem invNotUnit (s : Symbols sig) (t : Term sig) : head (s.product.inv t) ≠ .free s.one := by
  intro eq
  have e := Head.free.inj eq
  have h := s.invArity
  rw [e,s.oneArity] at h
  contradiction

theorem classify (mul : MulBucket E) (inverse : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {y r : Term sig}
    (sy : HasSort y .msg) (ny : Normal (ruleRoot T.rules) y)
    (sr : HasSort r .msg) (nr : Normal (ruleRoot T.rules) r) (positive : Factor s r) :
    ∃ k p n, Realizes s (ruleRoot T.rules) y r k (env y r p n) := by
  classical
  have make (k : Branch) (p n : Term sig) (sp : HasSort p .msg) (sn : HasSort n .msg)
      (np : Normal (ruleRoot T.rules) p) (nn : Normal (ruleRoot T.rules) n)
      (eq : EquivB y (k.image.eval s (env y r p n)))
      (red : Reduces (ruleRoot T.rules) (s.product.mul y r) (k.result.eval s (env y r p n)))
      (nv : Normal (ruleRoot T.rules) (k.result.eval s (env y r p n)))
      (ou : head y = .free s.one ↔ k = .unit)
      (ru : head (k.result.eval s (env y r p n)) = .free s.one ↔ k = .cancelAll) :
      Realizes s (ruleRoot T.rules) y r k (env y r p n) := by
    have typed : ∀ i, HasSort (env y r p n i) .msg := by intro i; cases i <;> assumption
    exact ⟨typed,by intro i; cases i <;> assumption,eq,⟨red,nv,
      fun _ h => .widen (k.result.sorted _ _ typed) (s.mulSort ▸ Term.rootSort_le h)⟩,ou,ru⟩
  by_cases one : head y = .free s.one
  · obtain rfl : y = s.product.one := nullary s.oneArity one
    exact ⟨.unit,r,r,make _ _ _ sr sr nr nr (.refl _)
      (.step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule r sr),.refl _⟩) nr
      ⟨fun _ => rfl,fun _ => rfl⟩ ⟨fun h => False.elim (positive.nonUnit h),by intro e; cases e⟩⟩
  obtain ⟨t,h⟩ := DHProduct.classify s.product _ s.mulSort E.presentation.invCongr
    (fun eq => DHPeer.invChild s eq) y r sy ny
  have red := h.reduces E.presentation.roots.laws sr
  cases h with
  | extend clear =>
    have clean := clean_of_normal E.presentation sy ny (fun eq => one eq.head_eq)
    exact ⟨.unchanged,r,r,make _ _ _ sr sr nr nr (.refl _) red
      (cleanMul mul (clean.extend positive.single (fun eq => positive.nonUnit eq.head_eq)
        (fun _ eq => positive.nonInv eq.head_eq) clear) ny nr) (by simp [one])
      (by constructor <;> intro e <;> cases e)⟩
  | cancel eq =>
    exact ⟨.cancelAll,r,r,make _ _ _ sr sr nr nr eq red unit (by simp [one]) ⟨fun _ => rfl,fun _ => rfl⟩⟩
  | cancelWith t su nu eq =>
    apply Exists.intro .cancelPositive
    refine ⟨t,r,make _ _ _ su sr nu nr eq red nu (by simp [one]) ⟨?_,by intro e; cases e⟩⟩
    intro hd
    obtain rfl : t = s.product.one := nullary s.oneArity hd
    have si := (Expr.inv DHPeer.r).sorted s (fun _ => r) (fun _ => sr)
    exact (ny _ ⟨_,_,eq.trans (.ac_swap ..),.root (E.presentation.unitRule _ si),.refl _⟩).elim
  | cancelInside v sv nv eq =>
    exact ⟨.cancelNegative,r,v,make _ _ _ sr sv nr nv eq red
      (inverse.shrink sr ((normal_equiv _ eq).mp ny)) (by simp [one])
      ⟨fun h => False.elim (invNotUnit s v h),by intro e; cases e⟩⟩
  | cancelBoth u v su sv nu nv eq =>
    have typed : ∀ i, HasSort (env y r u v i) .msg := by intro i; cases i <;> assumption
    exact ⟨.cancelMixed,u,v,make _ _ _ su sv nu nv eq red
      (mixedNormal mul inverse (Branch.cancelMixed.image.sorted s _ typed) sr
        ((normal_equiv _ eq).mp ny)) (by simp [one]) (by constructor <;> intro e <;> cases e)⟩


def before (s : Symbols sig) (k : Branch) (g image : Term sig) : Term sig :=
  if k = .unit then g else s.power g image

def after (s : Symbols sig) (k : Branch) (g result : Term sig) : Term sig :=
  if k = .cancelAll then g else s.power g result

private theorem powerForm (pow : PowerBucket T) {g e v : Term sig}
    (sg : HasSort g .msg) (ng : Normal (ruleRoot T.rules) g)
    (gp : head g ≠ .free s.pow) (gn : head g ≠ .free s.neutral)
    (sv : HasSort v .msg) (nv : Normal (ruleRoot T.rules) v)
    (red : Reduces (ruleRoot T.rules) e v) (c : Prop) [Decidable c]
    (unit : head v = .free s.one ↔ c) :
    NormalForm (ruleRoot T.rules) (s.power g e) (if c then g else s.power g v) := by
  have path : Reduces (ruleRoot T.rules) (s.power g e) (s.power g v) := by
    apply Reduces.free; intro i; split <;> first | exact .basis (.refl _) | exact red
  split
  · next hc =>
      obtain rfl := nullary s.oneArity (unit.mpr hc)
      exact ⟨path.trans (T.fire .expOne (fun _ => g) (fun _ => sg)), ng,
        fun _ h => .widen sg (s.powSort ▸ Term.rootSort_le h)⟩
  · next hc =>
      exact ⟨path,(pow.normal_iff sg sv).mpr ⟨ng,nv,gp,gn,fun hd => hc (unit.mp hd)⟩,
        fun _ h => .widen (DHTower.powerSorted sg sv) (s.powSort ▸ Term.rootSort_le h)⟩

theorem Realizes.beforeForm (pow : PowerBucket T) {y r k v}
    (h : Realizes s (ruleRoot T.rules) y r k v) (_sy : HasSort y .msg) (ny : Normal (ruleRoot T.rules) y)
    {g} (sg : HasSort g .msg) (ng : Normal (ruleRoot T.rules) g)
    (gp : head g ≠ .free s.pow) (gn : head g ≠ .free s.neutral) :
    NormalForm (ruleRoot T.rules) (s.power g y) (before s k g (k.image.eval s v)) :=
  powerForm pow sg ng gp gn (k.image.sorted _ _ h.typed) ((normal_equiv _ h.image).mp ny)
    (.basis h.image) _ (⟨fun eq => h.oldUnit.mp (h.image.head_eq.trans eq),fun eq => h.image.head_eq.symm.trans (h.oldUnit.mpr eq)⟩)

theorem Realizes.afterForm (pow : PowerBucket T) {y r k v}
    (h : Realizes s (ruleRoot T.rules) y r k v) (_sy : HasSort y .msg) (_sr : HasSort r .msg)
    {g} (sg : HasSort g .msg) (ng : Normal (ruleRoot T.rules) g)
    (gp : head g ≠ .free s.pow) (gn : head g ≠ .free s.neutral) :
    NormalForm (ruleRoot T.rules) (s.power g (s.product.mul y r)) (after s k g (k.result.eval s v)) :=
  powerForm pow sg ng gp gn (k.result.sorted _ _ h.typed) h.product.2.1 h.product.1 _ h.newUnit

theorem Realizes.towerForm (pow : PowerBucket T) {y r k v}
    (h : Realizes s (ruleRoot T.rules) y r k v) (sy : HasSort y .msg) (sr : HasSort r .msg)
    {g} (sg : HasSort g .msg) (ng : Normal (ruleRoot T.rules) g)
    (gp : head g ≠ .free s.pow) (gn : head g ≠ .free s.neutral) :
    NormalForm (ruleRoot T.rules) (s.power (s.power g y) r) (after s k g (k.result.eval s v)) := by
  have flat := Realizes.afterForm pow h sy sr sg ng gp gn
  have path := DHTower.Spine.flatten T (b := g) (e := y) [r] sg sy (by simpa using sr)
  exact ⟨path.trans flat.1,flat.2.1,fun _ hs => .widen (flat.2.2 _ (DHTower.powerSorted sg
    (s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ sy) (s.mulSort ▸ sr)))) (s.powSort ▸ Term.rootSort_le hs)⟩

theorem before_unique (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {y g u v} (sy : HasSort y .msg) (sg : HasSort g .msg)
    (ny : Normal (ruleRoot T.rules) y) (ng : Normal (ruleRoot T.rules) g)
    (hu : NormalForm (ruleRoot T.rules) (s.power g y) u) (hv : NormalForm (ruleRoot T.rules) (s.power g y) v) :
    EquivB u v :=
  DHTower.Spine.unique pow inv unit (DHTower.powerSorted sg sy)
    (DHTower.Spine.defined_tower s _ [] ng ny (by simp)) hu hv

theorem after_unique (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {y r g u v}
    (sy : HasSort y .msg) (sr : HasSort r .msg) (sg : HasSort g .msg)
    (ny : Normal (ruleRoot T.rules) y) (nr : Normal (ruleRoot T.rules) r) (ng : Normal (ruleRoot T.rules) g)
    (hu : NormalForm (ruleRoot T.rules) (s.power g (s.product.mul y r)) u)
    (hv : NormalForm (ruleRoot T.rules) (s.power g (s.product.mul y r)) v) : EquivB u v := by
  apply DHTower.Spine.unique pow inv unit _ (DHTower.Spine.defined_power (DHTower.Spine.defined_normal s _ ng) _) hu hv
  · exact DHTower.powerSorted sg (s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ sy) (s.mulSort ▸ sr))
  · intro k
    obtain ⟨i,hi⟩ := Balance.defined s _ k ny
    obtain ⟨j,hj⟩ := Balance.defined s _ k nr
    exact ⟨i+j,by rw [Balance.read_mul,hi,hj]; rfl⟩

theorem tower_unique (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {y r g u v}
    (sy : HasSort y .msg) (sr : HasSort r .msg) (sg : HasSort g .msg)
    (ny : Normal (ruleRoot T.rules) y) (nr : Normal (ruleRoot T.rules) r) (ng : Normal (ruleRoot T.rules) g)
    (hu : NormalForm (ruleRoot T.rules) (s.power (s.power g y) r) u)
    (hv : NormalForm (ruleRoot T.rules) (s.power (s.power g y) r) v) : EquivB u v :=
  DHTower.Spine.unique pow inv unit (DHTower.powerSorted (DHTower.powerSorted sg sy) sr)
    (DHTower.Spine.defined_tower s _ [r] ng ny (by simpa using nr)) hu hv

end Tamarin.Rewriting.DHExponent
