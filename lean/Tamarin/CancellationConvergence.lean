import Tamarin.VariantComposition
import Tamarin.LocalConvergence

/-! Local convergence for cancellation with changing operands. A factor may
rewrite internally while another copy cancels. Count factors by the normal
value they converge to, so both orders of reduction have the same parity. -/
namespace Tamarin.Rewriting
variable {s : Signature} {R : Root s}

namespace BinaryXor
open Cancellation ConstructorVariants
variable (T : Table s)
noncomputable section
open Classical

/-- An opaque factor stays indivisible at the chosen AC symbol on every path
and all its descendants can reach the same typed normal value. -/
def Factor (k : Class s) (n : Term s) :=
  Good T n ∧ Converges T.R (rep k) n ∧
    ∀ u, Reduces T.R (rep k) u → T.bag u = [classOf u]

private def label (k : Class s) := if h : ∃ n, Factor T k n then classOf h.choose else k

private theorem factor_label {k : Class s} {n : Term s} (h : Factor T k n) : label T k = classOf n := by
  unfold label
  rw [dite_eq_left (show ∃ m, Factor T k m from ⟨n,h⟩)]
  exact Quotient.sound (Converges.agree (Exists.choose_spec (show ∃ m, Factor T k m from ⟨n,h⟩)).2.1
    h.2.1 (Exists.choose_spec (show ∃ m, Factor T k m from ⟨n,h⟩)).1.2)

private theorem to_rep (a : Term s) : EquivB a (rep (classOf a)) := Quotient.exact (rep_key _).symm

private theorem factor_of {a n : Term s} (gn : Good T n) (h : Converges T.R a n)
    (shape : ∀ b, Reduces T.R a b → T.bag b = [classOf b]) : Factor T (classOf a) n := by
  have e := Reduces.basis (root := T.R) (to_rep a)
  exact ⟨gn,h.follow e,fun b r => shape b (e.trans r)⟩

private theorem factor_follow {a b n : Term s} (h : Factor T (classOf a) n) (red : Reduces T.R a b) :
    Factor T (classOf b) n := by
  have r := (Reduces.basis (to_rep a).symm).trans red
  exact factor_of T h.1 (h.2.1.follow r) (fun _ next => h.2.2 _ (r.trans next))

/-- Recognized sums allow each opaque factor to have its own reduction
strategy. Other active heads can be present anywhere in the signature. -/
def ConvergentFactors (t : Term s) := ∀ k ∈ T.bag t, ∃ n, Factor T k n

private theorem alien {a : Term s} (h : head a ≠ .ac T.f) : T.bag a = [classOf a] := by
  cases a with
  | ac f a b =>
    have ne : T.f ≠ f := fun e => h (e ▸ rfl)
    simp [FreshXor.Flat.Table.bag,flatten,ne]
  | _ => rfl

private theorem single_transport {a b : Term s} (h : T.bag a = [classOf a]) (e : EquivB a b) :
    T.bag b = [classOf b] := by
  have perm := (flatten_equiv T.f e).symm
  change (T.bag b).Perm (T.bag a) at perm
  rw [h,show classOf a = classOf b from Quotient.sound e] at perm
  exact List.perm_singleton.mp perm

theorem convergentFactors_normal {a : Term s} (g : Good T a) : ConvergentFactors T a := by
  intro k hk
  have fact := fact_of_mem T g hk
  refine ⟨rep k,fact.1,Converges.normal fact.1.2,?_⟩
  intro u r
  apply single_transport T _ (normal_reduces_equiv r fact.1.2)
  rw [rep_key]
  exact fact.2

theorem convergentFactors_free (f : s.FreeSym) (inert : ∀ xs u, ¬T.R (.free f xs) u) {xs ns}
    (children : ∀ i, Converges T.R (xs i) (ns i)) (gn : Good T (.free f ns)) :
    ConvergentFactors T (.free f xs) := by
  intro k hk
  obtain rfl := List.mem_singleton.mp hk
  exact ⟨_,factor_of T gn (Converges.free f inert children) (fun _ r => by
    obtain ⟨_,rfl,_⟩ := StableVariants.reduces_free_view f inert r
    rfl)⟩

theorem convergentFactors_ac (a b : Term s) : ConvergentFactors T (.ac T.f a b) ↔
    ConvergentFactors T a ∧ ConvergentFactors T b := by
  simp [ConvergentFactors,FreshXor.Flat.Table.bag,flatten_ac,List.mem_append,or_imp,forall_and]

private def labels (a : Term s) := (T.bag a).map (label T)
private theorem labels_ac (a b : Term s) : labels T (.ac T.f a b) = labels T a ++ labels T b := by
  simp [labels,FreshXor.Flat.Table.bag,flatten_ac]

private theorem normal_labels {t : Term s} (g : Good T t) : labels T t = T.bag t := by
  apply List.map_congr_left (g := id) _ |>.trans (List.map_id _)
  intro k hk
  obtain ⟨n,hn⟩ := convergentFactors_normal T g k hk
  have normal := (fact_of_mem T g hk).1.2
  exact (factor_label T hn).trans ((Quotient.sound (normal_reduces_equiv (hn.2.1 _ (.basis (.refl _))) normal)).symm.trans (rep_key k))

private def Preserves (a b : Term s) := ConvergentFactors T b ∧
  ∀ k, k ≠ T.zeroClass → (labels T a).count k % 2 = (labels T b).count k % 2

private theorem on_basis {a b : Term s} (h : ConvergentFactors T a) (e : EquivB a b) : Preserves T a b :=
  ⟨fun k hk => h k ((flatten_equiv T.f e).mem_iff.mpr hk),
    fun k _ => congrArg (· % 2) (((flatten_equiv T.f e).map (label T)).count_eq k)⟩

private theorem through {a b c : Term s} (p : Preserves T a b) (q : Preserves T b c) : Preserves T a c :=
  ⟨q.1,fun k ne => (p.2 k ne).trans (q.2 k ne)⟩

private theorem parallel {a b c d : Term s} (p : Preserves T a c) (q : Preserves T b d) :
    Preserves T (.ac T.f a b) (.ac T.f c d) := by
  refine ⟨(convergentFactors_ac ..).mpr ⟨p.1,q.1⟩,?_⟩
  intro k ne
  have l := p.2 k ne
  have r := q.2 k ne
  rw [labels_ac,labels_ac,List.count_append,List.count_append]
  omega

private theorem on_alien {a b : Term s} (h : ConvergentFactors T a) (shape : head a ≠ .ac T.f)
    (red : Reduces T.R a b) : Preserves T a b := by
  have ha := alien T shape
  obtain ⟨n,hn⟩ := h (classOf a) (ha ▸ List.mem_cons_self)
  have hb := hn.2.2 b ((Reduces.basis (to_rep a).symm).trans red)
  have next := factor_follow T hn red
  constructor
  · intro k hk; rw [hb] at hk; obtain rfl := List.mem_singleton.mp hk; exact ⟨n,next⟩
  · intro k _; simp [labels,ha,hb,factor_label T hn,factor_label T next]

private theorem on_root {a b : Term s} (h : ConvergentFactors T a) (he : head a = .ac T.f)
    (step : T.R a b) : Preserves T a b := by
  have gz : Good T T.zero := ⟨T.zeroSort,T.toTable.zero_normal⟩
  have z := (normal_labels T gz).trans T.bag_zero
  rcases T.root_cases he step with ⟨a,rfl,rfl⟩|⟨a,rfl,rfl⟩|⟨a,b,rfl,rfl⟩|⟨a,b,rfl,rfl⟩
  all_goals constructor
  · exact convergentFactors_normal T gz
  · intro k ne; simp [labels_ac,z,Ne.symm ne]; omega
  · exact ((convergentFactors_ac ..).mp h).1
  · intro k ne; simp [labels_ac,z,Ne.symm ne]
  · exact ((convergentFactors_ac ..).mp ((convergentFactors_ac ..).mp h).2).2
  · intro k _; simp only [labels_ac,List.count_append]; omega
  · exact ((convergentFactors_ac ..).mp h).2
  · intro k _; simp only [labels_ac,List.count_append]; omega

private theorem on_step {a b : Term s} (st : Step T.R a b) (h : ConvergentFactors T a) : Preserves T a b := by
  by_cases he : head a = .ac T.f
  · induction st with
    | root r => exact on_root T h he r
    | @ac_left g a b c child ih =>
      obtain rfl := Head.ac.inj he
      obtain ⟨l,r⟩ := (convergentFactors_ac ..).mp h
      by_cases childHead : head a = .ac T.f
      · exact parallel T (ih l childHead) (on_basis T r (.refl _))
      · exact parallel T (on_alien T l childHead (.step ⟨_,_,.refl _,child,.refl _⟩)) (on_basis T r (.refl _))
    | @ac_right g c a b child ih =>
      obtain rfl := Head.ac.inj he
      obtain ⟨l,r⟩ := (convergentFactors_ac ..).mp h
      by_cases childHead : head a = .ac T.f
      · exact parallel T (on_basis T l (.refl _)) (ih r childHead)
      · exact parallel T (on_basis T l (.refl _)) (on_alien T r childHead (.step ⟨_,_,.refl _,child,.refl _⟩))
    | free | comm_left | comm_right => contradiction
  · exact on_alien T h he (.step ⟨_,_,.refl _,st,.refl _⟩)

private theorem preserves {a b : Term s} (red : Reduces T.R a b) (h : ConvergentFactors T a) : Preserves T a b := by
  induction red with
  | basis e => exact on_basis T h e
  | trans _ _ ih ik => exact through T (ih h) (ik (ih h).1)
  | step st =>
    obtain ⟨x,y,e,s,d⟩ := st
    have first := on_basis T h e
    have next := on_step T s first.1
    exact through T first (through T next (on_basis T next.1 d))
  | ac f l r ih ik =>
    by_cases he : f = T.f
    · subst f
      obtain ⟨hl,hr⟩ := (convergentFactors_ac ..).mp h
      exact parallel T (ih hl) (ik hr)
    · exact on_alien T h (fun e => he (Head.ac.inj e)) (.ac _ l r)
  | free f xs ys rs _ => exact on_alien T h (by intro e; cases e) (.free f xs ys rs)
  | comm f l r _ _ => exact on_alien T h (by intro e; cases e) (.comm f l r)

private theorem reaches_good (a : Term s) (h : ConvergentFactors T a) :
    ∃ n, Reduces T.R a n ∧ Good T n := by
  have leaf {a : Term s} (dom : ConvergentFactors T a) (ne : head a ≠ .ac T.f) :
      ∃ n, Reduces T.R a n ∧ Good T n := by
    obtain ⟨n,hn⟩ := dom (classOf a) (alien T ne ▸ List.mem_cons_self)
    exact ⟨n,hn.2.1 _ (.basis (to_rep a).symm),hn.1⟩
  induction a with
  | var | atom | free | comm => exact leaf h (by intro e; cases e)
  | ac f a b ih ik =>
    by_cases e : f = T.f
    · subst f
      obtain ⟨ha,hb⟩ := (convergentFactors_ac ..).mp h
      obtain ⟨l,rl,gl⟩ := ih ha
      obtain ⟨r,rr,gr⟩ := ik hb
      have ty := HasSort.ac T.f _ _ (T.fSort ▸ gl.1) (T.fSort ▸ gr.1)
      obtain ⟨n,nf⟩ := normal_exists T (t := .ac T.f l r) (T.fSort ▸ ty) T.fSort
        (normalFactors_ac T (fun _ => fact_of_mem T gl) (fun _ => fact_of_mem T gr))
      exact ⟨n,(Reduces.ac T.f rl rr).trans nf.1,nf.2.2 _ (T.fSort ▸ ty),nf.2.1⟩
    · exact leaf h (fun eq => e (Head.ac.inj eq))

theorem convergentFactors_settle {a : Term s} (h : ConvergentFactors T a) :
    ∃ n, Good T n ∧ Converges T.R a n := by
  obtain ⟨n,rn,gn⟩ := reaches_good T a h
  have ref := preserves T rn h
  refine ⟨n,gn,?_⟩
  intro u ru
  have curr := preserves T ru h
  obtain ⟨v,rv,gv⟩ := reaches_good T u curr.1
  have last := preserves T rv curr.1
  apply rv.trans (Reduces.basis (normal_eq T gv gn ?_))
  intro k ne
  rw [← normal_labels T gv,← normal_labels T gn]
  exact ((curr.2 k ne).trans (last.2 k ne)).symm.trans (ref.2 k ne)

/-- The native fragment after a normalized caller assignment. An otherwise
unknown head is admissible as a normal leaf. A changing free application
must have an inert head and message argument slots. -/
inductive Fragment : Term s → Prop where
  | leaf {t} : Good T t → Fragment t
  | free (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads T.rules)
      (slots : ∀ i, s.inputSort f i = .msg) (out : Subsort (s.outputSort f) .msg)
      (xs : Fin (s.arity f) → Term s) (children : ∀ i, Fragment (xs i)) :
      Fragment (.free f xs)
  | ac {a b} : Fragment a → Fragment b → Fragment (.ac T.f a b)

/-- Each admitted expression has a typed normal form reachable from every
reduct. In particular, erasing a redex before reducing it cannot introduce
another observable answer. -/
theorem Fragment.settles {t : Term s} (h : Fragment T t) :
    ConvergentFactors T t ∧ ∃ n, Good T n ∧ NormalForm T.R t n ∧ Converges T.R t n := by
  induction h with
  | leaf g =>
    exact ⟨convergentFactors_normal T g,_,g,⟨.basis (.refl _),g.2,fun _ x => x⟩,Converges.normal g.2⟩
  | free f absent slots out xs _ ih =>
    let ns := fun i => (ih i).2.choose
    have props := fun i => (ih i).2.choose_spec
    have inert args u : ¬T.R (.free f args) u := by
      rintro ⟨r,hr,σ,eq,_⟩
      apply absent
      have he := (congrArg head eq).trans (instance_head r (T.apps r hr) σ)
      change head (.free f args) ∈ ruleHeads T.rules
      rw [he]; exact List.mem_map_of_mem hr
    have nf := free_normalForm T.rules T.apps f absent xs ns (fun i => (props i).2.1)
    have gn : Good T (.free f ns) := ⟨(HasSort.free f ns (fun i => slots i ▸ (props i).1.1)).widen out,nf.2.1⟩
    have child := fun i => (props i).2.2
    exact ⟨convergentFactors_free T f inert child gn,_,gn,nf,Converges.free f inert child⟩
  | ac _ _ l r =>
    have dom := (convergentFactors_ac ..).mpr ⟨l.1,r.1⟩
    obtain ⟨n,gn,conv⟩ := convergentFactors_settle T dom
    exact ⟨dom,n,gn,⟨conv _ (.basis (.refl _)),gn.2,fun _ hs => .widen gn.1 (T.fSort ▸ Term.rootSort_le hs)⟩,conv⟩

/-- Staging on changing operands computes exactly the full normal-form
relation. This statement is quantified over caller instances, including
ones where the two operands have shared or coincident images. -/
theorem staged_fragment {a b u : Term s} (left : Fragment T a) (right : Fragment T b) :
    NormalForm T.R (.ac T.f a b) u ↔
      ∃ l r, NormalForm T.R a l ∧ NormalForm T.R b r ∧ NormalForm T.R (.ac T.f l r) u := by
  obtain ⟨l,gl,nl,_⟩ := (left.settles T).2
  obtain ⟨r,gr,nr,_⟩ := (right.settles T).2
  obtain ⟨n,gn,_,conv⟩ := ((Fragment.ac left right).settles T).2
  constructor
  · intro nf
    have eq := normal_reduces_equiv (conv _ nf.1) nf.2.1
    have reach := conv _ (.ac T.f nl.1 nr.1)
    exact ⟨l,r,nl,nr,⟨reach.trans (.basis eq.symm),nf.2.1,fun _ hs =>
      .widen (sort_equiv eq.symm gn.1) (T.fSort ▸ Term.rootSort_le hs)⟩⟩
  · rintro ⟨l',r',hl,hr,form⟩
    have red := (Reduces.ac T.f hl.1 hr.1).trans form.1
    have eq := normal_reduces_equiv (conv _ red) form.2.1
    exact ⟨red,form.2.1,fun _ hs => .widen (sort_equiv eq.symm gn.1) (T.fSort ▸ Term.rootSort_le hs)⟩

/-- Admission before the caller's assignment. Stable leaves can mention any
declared symbols and can instantiate to products of arbitrary width. -/
inductive Admitted : Term s → Prop where
  | stable {t} : HasSort t .msg → StableVariants.Stable T.R t → Admitted t
  | free (f : s.FreeSym) (absent : Head.free f ∉ ruleHeads T.rules)
      (slots : ∀ i, s.inputSort f i = .msg) (out : Subsort (s.outputSort f) .msg)
      (xs : Fin (s.arity f) → Term s) (children : ∀ i, Admitted (xs i)) :
      Admitted (.free f xs)
  | ac {a b} : Admitted a → Admitted b → Admitted (.ac T.f a b)

theorem Admitted.instance_fragment {t : Term s} (h : Admitted T t) (ρ : Substitution s)
    (hn : Normalized T.R ρ) : Fragment T (ρ.apply t) := by
  induction h with
  | stable typed stable => exact .leaf ⟨typed.subst ρ.image ρ.sorted,stable ρ hn⟩
  | free f ha hi ho xs _ ih => exact .free f ha hi ho _ ih
  | ac _ _ l r => exact .ac l r

theorem Admitted.unique {t u v : Term s} (h : Admitted T t) (ρ : Substitution s)
    (hn : Normalized T.R ρ) (nu : NormalForm T.R (ρ.apply t) u)
    (nv : NormalForm T.R (ρ.apply t) v) : EquivB u v := by
  obtain ⟨_,_,_,conv⟩ := ((h.instance_fragment T ρ hn).settles T).2
  exact (normal_reduces_equiv (conv _ nu.1) nu.2.1).trans
    (normal_reduces_equiv (conv _ nv.1) nv.2.1).symm

end
end BinaryXor
end Tamarin.Rewriting
