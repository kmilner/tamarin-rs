import Tamarin.DHChurchRosserAlgebra
import Tamarin.DHKindProducts

/-! Multiplication on normal classes at the common kind. Ill-sorted factors
persist as a multiset. The maximal Msg-sorted subbag is determined by its
signed multiplicities and by whether a sorted factor was present at all.
The latter distinction retains a unit adjacent to wholly ill-sorted factors. -/
namespace Tamarin.Rewriting.DHPeer.ChurchRosser
open KindProduct Balance Cancellation ShortVariantPaths
variable {sig : Signature} {s : Symbols sig} {R : Root sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.ACSym]

private noncomputable def bad (s : Symbols sig) (t : Term sig) :=
  (flatten s.mul t).filter (fun c => !msg c)

private noncomputable def weight (s : Symbols sig) (R : Root sig) (k : Class sig) : Class sig → Int :=
  Quotient.lift (fun t => (read s R k t).getD 0) (fun _ _ h => congrArg (fun p => p.getD 0) (equiv s R k h))

private noncomputable def count (s : Symbols sig) (R : Root sig) (k : Class sig) (t : Term sig) :=
  ((selected s t).map (weight s R k)).sum

private structure Same (s : Symbols sig) (R : Root sig) (a b : Term sig) : Prop where
  inert : (bad s a).Perm (bad s b)
  empty : selected s a = [] ↔ selected s b = []
  signed : ∀ k, count s R k a = count s R k b

omit [DecidableEq sig.ACSym] in
private theorem Same.symm {a b} (h : Same s R a b) : Same s R b a :=
  ⟨h.inert.symm,h.empty.symm,fun k => (h.signed k).symm⟩

omit [DecidableEq sig.ACSym] in
private theorem Same.trans {a b c} (h : Same s R a b) (i : Same s R b c) : Same s R a c :=
  ⟨h.inert.trans i.inert,h.empty.trans i.empty,fun k => (h.signed k).trans (i.signed k)⟩

omit [DecidableEq sig.ACSym] in
private theorem of_equiv {a b : Term sig} (h : EquivB a b) : Same s R a b := by
  have p := flatten_equiv s.mul h
  have good : (selected s a).Perm (selected s b) := p.filter msg
  refine ⟨p.filter _,⟨?_,?_⟩,fun k => ?_⟩
  · intro e; rw [e] at good; exact good.symm.eq_nil
  · intro e; rw [e] at good; exact good.eq_nil
  have eqSum {xs ys : List Int} (hp : xs.Perm ys) : xs.sum = ys.sum := by
    induction hp with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp [Int.add_left_comm]
    | trans _ _ l r => exact l.trans r
  exact eqSum (good.map _)

omit [DecidableEq sig.ACSym] in
private theorem congr_mul {a b c d} (h : Same s R a b) (i : Same s R c d) :
    Same s R (s.product.mul a c) (s.product.mul b d) := by
  have bad_mul x y : bad s (s.product.mul x y) = bad s x ++ bad s y := by
    simp [bad,DHProduct.Ops.mul,Symbols.product,flatten_ac]
  constructor
  · simp only [bad_mul]; exact h.inert.append i.inert
  · simp only [selected_mul,List.append_eq_nil_iff,h.empty,i.empty]
  · intro k
    simp only [count,selected_mul,List.map_append,List.sum_append_int]
    change count s R k a + count s R k c = count s R k b + count s R k d
    rw [h.signed,i.signed]

omit [DecidableEq sig.ACSym] in
private theorem split_bag (t : Term sig) : (flatten s.mul t).Perm (selected s t ++ bad s t) :=
  (List.filter_append_perm msg (flatten s.mul t)).symm

private theorem typed_shape {t : Term sig} (ty : HasSort t .msg) :
    bad s t = [] ∧ selected s t ≠ [] := by
  have all := all_msg (s := s) ty
  have split := (split_bag (s := s) t).length_eq
  rw [List.length_append,all] at split
  exact ⟨List.length_eq_zero_iff.mp (by omega),fun e => by
    have h := fold_flatten s.mul t
    simp [← all,e,fold] at h⟩

private theorem raw_count (k : Class sig) (t : Term sig) (nt : Normal R t) :
    ((flatten s.mul t).map (weight s R k)).sum = (read s R k t).getD 0 := by
  induction t with
  | ac f a b ih ik =>
    by_cases h : s.mul = f
    · subst f
      obtain ⟨na,nb⟩ := normal_ac_children _ nt
      obtain ⟨x,hx⟩ := defined s R k na
      obtain ⟨y,hy⟩ := defined s R k nb
      have rd := read_mul s R k a b
      change read s R k (.ac s.mul a b) = _ at rd
      simp [flatten_ac,ih na,ik nb,rd,hx,hy,plus]
    · simp [flatten,h,weight,classOf] <;> rfl
  | _ => simp [flatten,weight,classOf] <;> rfl

private theorem typed_read {t : Term sig} (ty : HasSort t .msg) (nt : Normal R t) (k) :
    read s R k t = some (count s R k t) := by
  obtain ⟨n,eq⟩ := defined s R k nt
  simp only [count,all_msg ty,raw_count k t nt,eq]; rfl

include E in
private theorem eq_normal {a b} (na : Normal (ruleRoot T.rules) a) (nb : Normal (ruleRoot T.rules) b)
    (h : Same s (ruleRoot T.rules) a b) : EquivB a b := by
  apply equiv_of_flatten_perm s.mul
  refine (split_bag a).trans ((List.Perm.append ?_ h.inert).trans (split_bag b).symm)
  obtain ⟨oa,ha,nfa⟩ := core_exists (s := s) a na
  obtain ⟨ob,hb,nfb⟩ := core_exists (s := s) b nb
  cases oa with
  | none => rw [h.empty.mp ha.symm,← ha]; exact .nil
  | some x =>
    obtain ⟨tx,nx⟩ := nfa x rfl
    change flatten s.mul x = _ at ha
    cases ob with
    | none =>
      have hn := h.empty.mpr hb.symm
      exact False.elim ((typed_shape (s := s) tx).2 ((all_msg tx).trans (ha.trans hn)))
    | some y =>
      obtain ⟨ty,ny⟩ := nfb y rfl
      change flatten s.mul y = _ at hb
      obtain ⟨_,_,cx⟩ := decompose E.presentation (fun _ => plain_of_inverse E) tx nx
      obtain ⟨_,_,cy⟩ := decompose E.presentation (fun _ => plain_of_inverse E) ty ny
      have e := cx.injective cy (fun k => by
        rw [typed_read tx nx,typed_read ty ny]
        simpa only [count,all_msg tx,all_msg ty,ha,hb] using congrArg some (h.signed k))
      rw [← ha,← hb]
      exact flatten_equiv s.mul e

private theorem witness (tab : ProtectedTable E) (a b : Value (ruleRoot T.rules)) :
    ∃ z : Value (ruleRoot T.rules), Reduces (ruleRoot T.rules) (s.product.mul a.rep b.rep) z.rep ∧
      Same s (ruleRoot T.rules) (s.product.mul a.rep b.rep) z.rep := by
  obtain ⟨k,go⟩ := product_paths tab.inventory tab.product tab.inverse tab.unit
  obtain ⟨u,p,nu,val⟩ := KindProduct.paths tab.product (Same s (ruleRoot T.rules)) of_equiv
    (fun e h => (of_equiv e).trans h) (fun h r => congr_mul h (of_equiv (.refl r))) (k := k) (by
      intro x y tx ty nx ny
      obtain ⟨u,tu,path,nu⟩ := go x y tx ty nx ny
      refine ⟨u,tu,path,nu,?_⟩
      have xy : HasSort (s.product.mul x y) .msg := s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ tx) (s.mulSort ▸ ty)
      obtain ⟨el,nl⟩ := typed_shape (s := s) xy
      obtain ⟨er,nr⟩ := typed_shape (s := s) tu
      refine ⟨el ▸ er ▸ List.Perm.refl _,iff_of_false nl nr,fun j => ?_⟩
      have readXY : read s (ruleRoot T.rules) j (s.product.mul x y) = some (count s (ruleRoot T.rules) j (s.product.mul x y)) := by
        simp [read_mul,typed_read tx nx,typed_read ty ny,count,selected_mul,plus]
      exact Option.some.inj ((tab.inventory.reduces j path.reduces _ readXY).symm.trans (typed_read tu nu j))
    ) a.rep b.rep a.normal b.normal
  exact ⟨value u nu,p.reduces.trans (.basis (value_rep u nu)),val.trans (of_equiv (value_rep u nu))⟩

/-- Multiplication of any two normal kind-level values is reachable and forms
an associative commutative operation on their structural equivalence classes. -/
noncomputable def protectedProduct (tab : ProtectedTable E) : Product s (ruleRoot T.rules) where
  mul a b := (witness tab a b).choose
  reaches a b := (witness tab a b).choose_spec.1
  comm a b := by
    apply Value.eq_of_rep
    apply eq_normal (E := E) (Value.normal _) (Value.normal _)
    exact (witness tab a b).choose_spec.2.symm.trans ((of_equiv (.ac_swap s.mul _ _)).trans (witness tab b a).choose_spec.2)
  assoc a b c := by
    apply Value.eq_of_rep
    apply eq_normal (E := E) (Value.normal _) (Value.normal _)
    exact (witness tab _ c).choose_spec.2.symm.trans ((congr_mul (witness tab a b).choose_spec.2.symm (of_equiv (.refl c.rep))).trans
      ((of_equiv (.ac_assoc s.mul _ _ _)).trans ((congr_mul (of_equiv (.refl a.rep)) (witness tab b c).choose_spec.2).trans
        (witness tab a _).choose_spec.2)))

/-- Specialize the operation to a table containing exactly the DH rules. -/
noncomputable def kindProduct (tab : ExactTable E) : Product s (ruleRoot T.rules) :=
  protectedProduct tab.protectedTable

end Tamarin.Rewriting.DHPeer.ChurchRosser
