import Tamarin.VariantComposition
import Tamarin.HereditaryConvergence

/-! A changing operand can expose an entire product at the cancellation
symbol. Its contribution is the bag of its normal form, counted modulo two.
This handles both a rewrite below an operand and its cancellation before
the rewrite, irrespective of the number of newly exposed factors. -/
namespace Tamarin.Rewriting.BinaryXor.Splicing
open Cancellation ConstructorVariants
variable {s : Signature} (T : Table s)
noncomputable section
open Classical

private def Domain (t : Term s) := ∀ k ∈ T.bag t, Hereditary T.R (rep k)

private theorem parts (a b : Term s) : Domain T (.ac T.f a b) ↔ Domain T a ∧ Domain T b := by
  simp [Domain,FreshXor.Flat.Table.bag,flatten_ac,List.mem_append,or_imp,forall_and]

private theorem alien {a : Term s} (h : head a ≠ .ac T.f) : T.bag a = [classOf a] := by
  cases a with
  | ac f a b =>
    have ne : T.f ≠ f := fun e => h (e ▸ rfl)
    simp [FreshXor.Flat.Table.bag,flatten,ne]
  | _ => rfl

private theorem reprEq (a : Term s) : EquivB a (rep (classOf a)) :=
  Quotient.exact (rep_key _).symm

private theorem domain_of {a : Term s} (h : Hereditary T.R a) : Domain T a := by
  have leaf {t : Term s} (ht : Hereditary T.R t) (ne : head t ≠ .ac T.f) : Domain T t := by
    intro k hk
    rw [alien T ne] at hk
    obtain rfl := List.mem_singleton.mp hk
    exact ht.follow (.reduces (.basis (reprEq t)))
  induction a with
  | var | atom | free | comm => exact leaf h (by intro e; cases e)
  | ac f a b ih ik =>
    by_cases e : f = T.f
    · subst f
      exact (parts T ..).mpr ⟨ih (h.follow (.child (.ac_left ..))),ik (h.follow (.child (.ac_right ..)))⟩
    · exact leaf h (fun e' => e (Head.ac.inj e'))

private theorem hereditary_of_alien {a : Term s} (h : Domain T a) (ne : head a ≠ .ac T.f) :
    Hereditary T.R a :=
  (h _ (alien T ne ▸ List.mem_cons_self)).follow (.reduces (.basis (reprEq a).symm))

private def label (k : Class s) : List (Class s) :=
  if h : Settles T.R (rep k) then T.bag h.choose else [k]

private def labels (a : Term s) := (T.bag a).flatMap (label T)

private theorem labels_ac (a b : Term s) : labels T (.ac T.f a b) = labels T a ++ labels T b := by
  simp [labels,FreshXor.Flat.Table.bag,flatten_ac]

private theorem bag_ac (a b : Term s) : T.bag (.ac T.f a b) = T.bag a ++ T.bag b :=
  flatten_ac ..

private theorem label_perm {a n : Term s} (hn : Good T n) (h : Converges T.R a n) :
    (label T (classOf a)).Perm (T.bag n) := by
  have onRep := h.follow (.basis (reprEq a))
  have settled : Settles T.R (rep (classOf a)) := ⟨n,hn.2,hn.1,onRep⟩
  unfold label
  rw [dite_eq_left settled]
  exact flatten_equiv T.f (Converges.agree settled.choose_spec.2.2 onRep settled.choose_spec.1)

private def Same (xs ys : List (Class s)) :=
  ∀ k, k ≠ T.zeroClass → xs.count k % 2 = ys.count k % 2

private theorem same_append {a b c d : List (Class s)} (l : Same T a c) (r : Same T b d) :
    Same T (a ++ b) (c ++ d) := by
  intro k ne
  have left := l k ne
  have right := r k ne
  simp only [List.count_append]
  omega

private theorem same_perm {a b : List (Class s)} (p : a.Perm b) : Same T a b :=
  fun k _ => congrArg (· % 2) (p.count_eq k)

private theorem same_trans {a b c : List (Class s)} (p : Same T a b) (q : Same T b c) : Same T a c :=
  fun k ne => (p k ne).trans (q k ne)

private theorem normalize {t : Term s} (h : Domain T t) :
    ∃ n, Reduces T.R t n ∧ Good T n ∧ Same T (labels T t) (T.bag n) := by
  have leaf {a : Term s} (ha : Domain T a) (ne : head a ≠ .ac T.f) :
      ∃ n, Reduces T.R a n ∧ Good T n ∧ Same T (labels T a) (T.bag n) := by
    obtain ⟨n,hn,ty,c⟩ := (hereditary_of_alien T ha ne).settles
    refine ⟨n,c _ (.basis (.refl _)),⟨ty,hn⟩,?_⟩
    simpa [labels,alien T ne] using same_perm T (label_perm T ⟨ty,hn⟩ c)
  induction t with
  | var | atom | free | comm => exact leaf h (by intro e; cases e)
  | ac f a b ih ik =>
    by_cases e : f = T.f
    · subst f
      obtain ⟨ha,hb⟩ := (parts T ..).mp h
      obtain ⟨l,rl,gl,pl⟩ := ih ha
      obtain ⟨r,rr,gr,pr⟩ := ik hb
      have ty : HasSort (.ac T.f l r) .msg :=
        T.fSort ▸ HasSort.ac T.f _ _ (T.fSort ▸ gl.1) (T.fSort ▸ gr.1)
      obtain ⟨n,nf⟩ := normal_exists T ty T.fSort
        (normalFactors_ac T (fun _ => fact_of_mem T gl) (fun _ => fact_of_mem T gr))
      have parity := (T.reduces_kept nf.1 ((T.pure_ac ..).mpr ⟨pure_good T gl,pure_good T gr⟩)).2
      refine ⟨n,(Reduces.ac T.f rl rr).trans nf.1,⟨nf.2.2 _ ty,nf.2.1⟩,?_⟩
      apply same_trans T _ parity
      rw [labels_ac,bag_ac]
      exact same_append T pl pr
    · exact leaf h (fun e' => e (Head.ac.inj e'))

private def Preserves (a b : Term s) := Domain T b ∧ Same T (labels T a) (labels T b)

private theorem basis {a b : Term s} (h : Domain T a) (e : EquivB a b) : Preserves T a b := by
  have p := flatten_equiv T.f e
  exact ⟨fun k hk => h k (p.mem_iff.mpr hk),same_perm T (p.flatMap_right (label T))⟩

private theorem through {a b c : Term s} (p : Preserves T a b) (q : Preserves T b c) : Preserves T a c :=
  ⟨q.1,same_trans T p.2 q.2⟩

private theorem parallel {a b c d : Term s} (p : Preserves T a c) (q : Preserves T b d) :
    Preserves T (.ac T.f a b) (.ac T.f c d) := by
  refine ⟨(parts T ..).mpr ⟨p.1,q.1⟩,?_⟩
  rw [labels_ac,labels_ac]
  exact same_append T p.2 q.2

private theorem on_alien {a b : Term s} (h : Domain T a) (ne : head a ≠ .ac T.f)
    (red : Reduces T.R a b) : Preserves T a b := by
  have her := hereditary_of_alien T h ne
  have db := domain_of T (her.follow (.reduces red))
  obtain ⟨n,rn,gn,pn⟩ := normalize T db
  obtain ⟨w,hw,tw,cw⟩ := her.settles
  have e := normal_reduces_equiv (cw _ (red.trans rn)) gn.2
  have pa : Same T (labels T a) (T.bag w) := by
    simpa [labels,alien T ne] using same_perm T (label_perm T ⟨tw,hw⟩ cw)
  have equiv := same_perm T (flatten_equiv T.f e)
  exact ⟨db,fun k nk => (pa k nk).trans ((equiv k nk).symm.trans (pn k nk).symm)⟩

private theorem zero_labels : Same T (labels T T.zero) [T.zeroClass] := by
  rw [labels,T.bag_zero,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [← T.bag_zero]
  exact same_perm T (label_perm T ⟨T.zeroSort,T.toTable.zero_normal⟩ (Converges.normal T.toTable.zero_normal))

private theorem on_root (hz : Hereditary T.R T.zero) {a b : Term s} (h : Domain T a)
    (he : head a = .ac T.f) (step : T.R a b) : Preserves T a b := by
  have z k (ne : k ≠ T.zeroClass) : (labels T T.zero).count k % 2 = 0 := by
    simpa [Ne.symm ne] using zero_labels T k ne
  rcases T.root_cases he step with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩|⟨a,b,rfl,rfl⟩|⟨a,b,rfl,rfl⟩
  all_goals constructor
  · exact domain_of T hz
  · intro k ne; have := z k ne; simp only [labels_ac,List.count_append]; omega
  · exact ((parts T ..).mp h).1
  · intro k ne; have := z k ne; simp only [labels_ac,List.count_append]; omega
  · exact ((parts T ..).mp ((parts T ..).mp h).2).2
  · intro k _; simp only [labels_ac,List.count_append]; omega
  · exact ((parts T ..).mp h).2
  · intro k _; simp only [labels_ac,List.count_append]; omega

private theorem on_step (hz : Hereditary T.R T.zero) {a b : Term s} (st : Step T.R a b)
    (h : Domain T a) : Preserves T a b := by
  induction st with
  | @root a b r =>
    by_cases he : head a = .ac T.f
    · exact on_root T hz h he r
    · exact on_alien T h he (.step ⟨_,_,.refl _,.root r,.refl _⟩)
  | @ac_left g a b c st ih =>
    by_cases e : g = T.f
    · subst g
      obtain ⟨ha,hc⟩ := (parts T ..).mp h
      exact parallel T (ih ha) (basis T hc (.refl _))
    · exact on_alien T h (fun e' => e (Head.ac.inj e')) (.step ⟨_,_,.refl _,.ac_left g c st,.refl _⟩)
  | @ac_right g c a b st ih =>
    by_cases e : g = T.f
    · subst g
      obtain ⟨hc,ha⟩ := (parts T ..).mp h
      exact parallel T (basis T hc (.refl _)) (ih ha)
    · exact on_alien T h (fun e' => e (Head.ac.inj e')) (.step ⟨_,_,.refl _,.ac_right g c st,.refl _⟩)
  | free => exact on_alien T h (by intro e; cases e) (.step ⟨_,_,.refl _,.free _ _ _ ‹_›,.refl _⟩)
  | comm_left => exact on_alien T h (by intro e; cases e) (.step ⟨_,_,.refl _,.comm_left _ _ ‹_›,.refl _⟩)
  | comm_right => exact on_alien T h (by intro e; cases e) (.step ⟨_,_,.refl _,.comm_right _ _ ‹_›,.refl _⟩)

private theorem preserves (hz : Hereditary T.R T.zero) {a b : Term s} (red : Reduces T.R a b)
    (h : Domain T a) : Preserves T a b := by
  induction red with
  | basis e => exact basis T h e
  | trans _ _ ih ik => exact through T (ih h) (ik (ih h).1)
  | step st =>
    obtain ⟨x,y,e,s,d⟩ := st
    have first := basis T h e
    have next := on_step T hz s first.1
    exact through T first (through T next (basis T next.1 d))
  | ac f l r ih ik =>
    by_cases he : f = T.f
    · subst f
      obtain ⟨hl,hr⟩ := (parts T ..).mp h
      exact parallel T (ih hl) (ik hr)
    · exact on_alien T h (fun e => he (Head.ac.inj e)) (.ac _ l r)
  | free f xs ys rs _ => exact on_alien T h (by intro e; cases e) (.free f xs ys rs)
  | comm f l r _ _ => exact on_alien T h (by intro e; cases e) (.comm f l r)

private theorem settles (hz : Hereditary T.R T.zero) {a : Term s} (h : Domain T a) : Settles T.R a := by
  obtain ⟨n,_,gn,pn⟩ := normalize T h
  refine ⟨n,gn.2,gn.1,?_⟩
  intro b red
  obtain ⟨db,pb⟩ := preserves T hz red h
  obtain ⟨v,rv,gv,pv⟩ := normalize T db
  exact rv.trans (.basis (normal_eq T gv gn (fun k ne =>
    ((pb k ne).trans (pv k ne)).symm.trans (pn k ne))))

private theorem child_domain {a b : Term s} (h : Domain T a) (child : Immediate a b) : Domain T b := by
  by_cases e : head a = .ac T.f
  · cases child with
    | ac_left => cases e; exact ((parts T ..).mp h).1
    | ac_right => cases e; exact ((parts T ..).mp h).2
    | _ => contradiction
  · exact domain_of T ((hereditary_of_alien T h e).follow (.child child))

/-- Hereditary convergence is closed under the cancellation operation. An
opaque operand may rewrite to a product of arbitrary width, including after
its duplicate has already been erased along another reduction path. -/
theorem hereditary_ac (hz : Hereditary T.R T.zero) {a b : Term s}
    (ha : Hereditary T.R a) (hb : Hereditary T.R b) : Hereditary T.R (.ac T.f a b) :=
  Hereditary.of_invariant (Domain T) (fun _ => settles T hz)
    (fun _ _ dom red => (preserves T hz red dom).1) (fun _ _ => child_domain T)
    ((parts T ..).mpr ⟨domain_of T ha,domain_of T hb⟩)

end
end Tamarin.Rewriting.BinaryXor.Splicing
