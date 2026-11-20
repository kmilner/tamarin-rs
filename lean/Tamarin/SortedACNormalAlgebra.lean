import Tamarin.SortedACPaths
import Tamarin.NormalAlgebra

/-! Construct an associative, commutative operation on all normal terms from an
invariant on lists of message-sorted factors. Sort-incompatible factors retain
their full multiplicities. An empty message subbag stays distinct from a
nonempty one that reduces to a unit. -/
namespace Tamarin.Rewriting.SortedAC
open Cancellation ShortVariantPaths NormalAlgebra ConstructorVariants
variable {sig : Signature} {R : Root sig} {f : sig.ACSym}

/-- The invariant may identify sorted factor lists more broadly than structural
permutation. On normal message terms it must distinguish the structural classes. -/
structure ProductInvariant (f : sig.ACSym) (R : Root sig) where
  rel : List (Class sig) → List (Class sig) → Prop
  ofPerm : ∀ {a b}, a.Perm b → rel a b
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  append : ∀ {a b c d}, rel a b → rel c d → rel (a ++ c) (b ++ d)
  distinguish : ∀ {a b}, HasSort a .msg → HasSort b .msg → Normal R a → Normal R b →
    rel (flatten f a) (flatten f b) → EquivB a b

namespace ProductInvariant
variable (I : ProductInvariant f R)

private noncomputable def other (f : sig.ACSym) (t : Term sig) := (flatten f t).filter (fun k => !msg k)

private structure Same (I : ProductInvariant f R) (a b : Term sig) : Prop where
  others : (other f a).Perm (other f b)
  empty : selected f a = [] ↔ selected f b = []
  sorted : I.rel (selected f a) (selected f b)

private theorem Same.symm {a b} (h : Same I a b) : Same I b a :=
  ⟨h.others.symm,h.empty.symm,I.symm h.sorted⟩

private theorem Same.trans {a b c} (h : Same I a b) (j : Same I b c) : Same I a c :=
  ⟨h.others.trans j.others,h.empty.trans j.empty,I.trans h.sorted j.sorted⟩

private theorem of_equiv {a b} (e : EquivB a b) : Same I a b := by
  have p := flatten_equiv f e
  have s : (selected f a).Perm (selected f b) := p.filter msg
  refine ⟨p.filter _,⟨?_,?_⟩,I.ofPerm s⟩
  · intro h; rw [h] at s; exact s.symm.eq_nil
  · intro h; rw [h] at s; exact s.eq_nil

private theorem parallel {a b c d} (h : Same I a b) (j : Same I c d) :
    Same I (.ac f a c) (.ac f b d) := by
  constructor
  · simpa only [other,flatten_ac,List.filter_append] using h.others.append j.others
  · simp only [selected_mul,List.append_eq_nil_iff,h.empty,j.empty]
  · rw [selected_mul,selected_mul]; exact I.append h.sorted j.sorted

private theorem split (t : Term sig) : (flatten f t).Perm (selected f t ++ other f t) :=
  (List.filter_append_perm msg (flatten f t)).symm

variable [DecidableEq sig.ACSym]
private theorem typed_shape (sort : sig.acSort f = .msg) {t : Term sig} (ty : HasSort t .msg) :
    other f t = [] ∧ selected f t ≠ [] := by
  have all := all_msg sort ty
  have len := (split (f := f) t).length_eq
  rw [List.length_append,all] at len
  exact ⟨List.length_eq_zero_iff.mp (by omega),fun e => by
    have h := fold_flatten f t
    simp [← all,e,fold] at h⟩

private theorem eq_normal (sort : sig.acSort f = .msg) {a b} (na : Normal R a) (nb : Normal R b)
    (h : Same I a b) : EquivB a b := by
  apply equiv_of_flatten_perm f
  refine (split a).trans ((List.Perm.append ?_ h.others).trans (split b).symm)
  obtain ⟨oa,ha,nfa⟩ := core_exists sort a na
  obtain ⟨ob,hb,nfb⟩ := core_exists sort b nb
  cases oa with
  | none => rw [h.empty.mp ha.symm,← ha]; exact .nil
  | some x =>
    obtain ⟨tx,nx⟩ := nfa x rfl
    change flatten f x = _ at ha
    cases ob with
    | none =>
      have hn := h.empty.mpr hb.symm
      exact False.elim ((typed_shape sort tx).2 ((all_msg sort tx).trans (ha.trans hn)))
    | some y =>
      obtain ⟨ty,ny⟩ := nfb y rfl
      change flatten f y = _ at hb
      rw [← ha,← hb]
      exact flatten_equiv f (I.distinguish tx ty nx ny (ha ▸ hb ▸ h.sorted))

/-- A single sorted path at this operator must preserve the invariant and reach
a normal operand. The uniform bound can also be reused for finite variants. -/
def SortedPaths (I : ProductInvariant f R) (k : Nat) : Prop :=
  ∀ a b, HasSort a .msg → HasSort b .msg → Normal R a → Normal R b →
    ∃ u, HasSort u .msg ∧ Path R k (.ac f a b) u ∧ Normal R u ∧
      I.rel (flatten f (.ac f a b)) (flatten f u)

private theorem witness (sort : sig.acSort f = .msg)
    (typed : ∀ {p q}, head p = .ac f → R p q → HasSort p .msg)
    {k} (sorted : I.SortedPaths k) (a b : Value R) :
    ∃ z : Value R, Reduces R (.ac f a.rep b.rep) z.rep ∧ Same I (.ac f a.rep b.rep) z.rep := by
  obtain ⟨u,p,nu,val⟩ := paths sort typed (Same I) (of_equiv I)
    (fun e h => (of_equiv I e).trans I h) (fun h r => parallel I h (of_equiv I (.refl r))) (k := k) (by
      intro x y tx ty nx ny
      obtain ⟨u,tu,hu,nu,keep⟩ := sorted x y tx ty nx ny
      have xy : HasSort (.ac f x y) .msg := sort ▸ HasSort.ac f _ _ (sort ▸ tx) (sort ▸ ty)
      obtain ⟨el,nl⟩ := typed_shape sort xy
      obtain ⟨er,nr⟩ := typed_shape sort tu
      exact ⟨u,tu,hu,nu,el ▸ er ▸ List.Perm.refl _,iff_of_false nl nr,
        (all_msg sort xy).symm ▸ (all_msg sort tu).symm ▸ keep⟩) a.rep b.rep a.normal b.normal
  exact ⟨value u nu,p.reduces.trans (.basis (value_rep u nu)),val.trans I (of_equiv I (value_rep u nu))⟩

noncomputable def product (sort : sig.acSort f = .msg)
    (typed : ∀ {p q}, head p = .ac f → R p q → HasSort p .msg)
    {k} (sorted : I.SortedPaths k) : Product f R where
  mul a b := (witness I sort typed sorted a b).choose
  reaches a b := (witness I sort typed sorted a b).choose_spec.1
  comm a b := by
    let w := witness I sort typed sorted
    apply Value.eq_of_rep
    apply eq_normal I sort (Value.normal _) (Value.normal _)
    exact ((w a b).choose_spec.2.symm I).trans I
      ((of_equiv I (.ac_swap f _ _)).trans I (w b a).choose_spec.2)
  assoc a b c := by
    let w := witness I sort typed sorted
    apply Value.eq_of_rep
    apply eq_normal I sort (Value.normal _) (Value.normal _)
    exact ((w _ c).choose_spec.2.symm I).trans I
      ((parallel I ((w a b).choose_spec.2.symm I) (of_equiv I (.refl c.rep))).trans I
        ((of_equiv I (.ac_assoc f _ _ _)).trans I
          ((parallel I (of_equiv I (.refl a.rep)) (w b c).choose_spec.2).trans I (w a _).choose_spec.2)))

end ProductInvariant
end Tamarin.Rewriting.SortedAC
