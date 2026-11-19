import Tamarin.VariantJoinPacked
import Tamarin.BinaryXorNormal

/-! In a staged operation the join keys are the children's normal values.
The public answer exposes the caller images and final values only. -/
namespace Tamarin.Rewriting.VariantJoin
variable {s : Signature} {I K A : Type}

def Row.transpose (r : Row s K I) : Row s I K := ⟨r.value,r.input⟩

theorem denotes_transpose {R : Root s} (r : Row s K I) (x : K → Term s) (m : I → Term s) :
    Denotes R r.transpose m x ↔ Denotes R r x m := by
  constructor <;> rintro ⟨δ,n,h⟩ <;> exact ⟨δ,n,h.values,h.inputs⟩

def Row.hideOperands (r : Row s I (Sum K A)) : Row s K A :=
  ⟨fun k => r.value (.inl k),fun a => r.value (.inr a)⟩

/-- A parent with active rules needs a staging law: every normal form must
be obtainable after normalizing the operands. This can hold locally even
when other rules in the signature have nonunique or divergent results.
The joined relation on the right is supplied by exact_join on the transposed
child rows and the parent rows. -/
theorem exact_hideOperands {rules : List (Equation s)} (keys : List Variable) (query : A → Term s)
    (typed : ∀ a, HasSort (query a) (query a).rootSort)
    (scope : ∀ a v, (query a).Occurs v → v ∈ keys)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (rows : List (Row s I (Sum (Key keys) A)))
    (sorted : ∀ r ∈ rows, r.hideOperands.Sorted)
    (normal : ∀ r ∈ rows, r.IsNormal (ruleRoot rules))
    (staged : ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → ∀ y, (∀ a, Normal (ruleRoot rules) (y a)) →
      ((∀ a, NormalForm (ruleRoot rules) (ρ.apply (query a)) (y a)) ↔
       ∃ m, (∀ i, Normal (ruleRoot rules) (m i)) ∧ ∃ r ∈ rows,
         Denotes (ruleRoot rules) r m (Sum.elim (fun k => ρ.image k.val) y))) :
    Exact (ruleRoot rules) Subtype.val query (rows.map Row.hideOperands) := by
  intro ρ hn y ny
  constructor
  · intro forms
    obtain ⟨_,_,r,mem,δ,nd,fit⟩ := (staged ρ hn y ny).mp forms
    exact ⟨_,List.mem_map_of_mem mem,δ,nd,fun k => fit.values (.inl k),fun a => fit.values (.inr a)⟩
  · rintro ⟨q,mem,δ,_,fit⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
    let σ := r.hideOperands.project (sorted r hr)
    have nr := normal r hr
    have ns := r.hideOperands.project_normal (sorted r hr) vars
      ⟨fun k => nr.2 (.inl k),fun a => nr.2 (.inr a)⟩
    have joint : Denotes (ruleRoot rules) r r.input (Sum.elim (fun k : Key keys => σ.image k.val) r.hideOperands.value) := by
      refine ⟨.identity,vars,?_,?_⟩
      · intro i; rw [Substitution.apply_identity]; exact .refl _
      · intro j; rw [Substitution.apply_identity]; cases j with
        | inl k => change EquivB (σ.image k.val) _; rw [show σ.image k.val = _ from r.hideOperands.project_key _ k]; exact .refl _
        | inr a => exact .refl _
    have forms := (staged σ ns r.hideOperands.value (fun a => nr.2 (.inr a))).mpr ⟨r.input,nr.1,r,hr,joint⟩
    -- A later substitution can introduce a redex in a hidden intermediate.
    -- Lift the witnessed reduction itself; only the final value must stay normal.
    intro a
    apply form_of_instance hn (typed a) (σ := σ) (δ := δ) _ (forms a) (fit.values a) (ny a)
    intro v hv
    let k : Key keys := ⟨v,scope a v hv⟩
    change EquivB (ρ.image k.val) (δ.apply (σ.image k.val))
    rw [show σ.image k.val = _ from r.hideOperands.project_key _ k]
    exact fit.inputs k

/-- Form the staged relation by ordinary unification of each pair. Local
families may use any generation algorithm. The completeness obligation for
the operation concerns their denotations, independently of witness names,
CSU enumeration, hidden columns, ordering, and deletion of duplicate rows. -/
theorem exact_staged {rules : List (Equation s)} (keys : List Variable) (query : A → Term s)
    (typed : ∀ a, HasSort (query a) (query a).rootSort)
    (scope : ∀ a v, (query a).Occurs v → v ∈ keys)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (children : List (Row s (Key keys) I)) (parents : List (Row s I A))
    (localLaw : ∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → ∀ y,
      (∀ a, Normal (ruleRoot rules) (y a)) →
      ((∀ a, NormalForm (ruleRoot rules) (ρ.apply (query a)) (y a)) ↔
       ∃ m, (∀ i, Normal (ruleRoot rules) (m i)) ∧
       (∃ c ∈ children, Denotes (ruleRoot rules) c (fun k => ρ.image k.val) m) ∧
       ∃ p ∈ parents, Denotes (ruleRoot rules) p m y))
    (slots : List I) (allSlots : ∀ i, i ∈ slots) (anchors : List (Term s))
    (sols : Row s (Key keys) I → Row s I A → List (Substitution s))
    (apart : ∀ c ∈ children, ∀ p ∈ parents, ∀ v, c.transpose.Uses v → ¬p.Uses v)
    (track : ∀ c ∈ children, ∀ p ∈ parents, ∀ v, c.transpose.Uses v ∨ p.Uses v →
      (problem c.transpose p slots anchors).Occurs v)
    (solved : ∀ c ∈ children, ∀ p ∈ parents, CompleteSet (problem c.transpose p slots anchors) (sols c p))
    (rows : List (Row s I (Sum (Key keys) A)))
    (members : ∀ r, r ∈ rows ↔ ∃ c ∈ children, ∃ p ∈ parents, ∃ μ ∈ sols c p,
      r = join c.transpose p μ ∧ r.IsNormal (ruleRoot rules))
    (sorted : ∀ r ∈ rows, r.hideOperands.Sorted) :
    Exact (ruleRoot rules) Subtype.val query (rows.map Row.hideOperands) := by
  apply exact_hideOperands keys query typed scope vars rows sorted
  · intro r hr
    obtain ⟨_,_,_,_,_,_,_,hn⟩ := (members r).mp hr
    exact hn
  intro ρ hn y ny
  rw [localLaw ρ hn y ny]
  have both c hc p hp m nm := exact_join vars c.transpose p (apart c hc p hp) slots allSlots
    anchors (track c hc p hp) (sols c p) (solved c hc p hp) m (fun k => ρ.image k.val) y
    nm (fun k => hn k.val) ny
  constructor
  · rintro ⟨m,nm,⟨c,hc,dc⟩,p,hp,dp⟩
    obtain ⟨μ,hm,n,fit⟩ := (both c hc p hp m nm).mp ⟨(denotes_transpose c _ _).mpr dc,dp⟩
    exact ⟨m,nm,_,(members _).mpr ⟨c,hc,p,hp,μ,hm,rfl,n⟩,fit⟩
  · rintro ⟨m,nm,r,hr,d⟩
    obtain ⟨c,hc,p,hp,μ,hm,rfl,n⟩ := (members _).mp hr
    obtain ⟨dc,dp⟩ := (both c hc p hp m nm).mpr ⟨μ,hm,n,d⟩
    exact ⟨m,nm,⟨c,hc,(denotes_transpose c _ _).mp dc⟩,p,hp,dp⟩

/-- Appending a stable caller operand to the prefix observation must reuse
the same witness substitution for both. This tracks aliases across the split. -/
theorem denotes_append {R : Root s} {keys : List Variable} (r : Row s (Key keys) I)
    (sorted : r.Sorted) (t : Term s) (scope : ∀ v, t.Occurs v → v ∈ keys)
    (ρ : Substitution s) (m : I → Term s) :
    Denotes R ⟨r.input,Sum.elim r.value (fun _ : Unit => (r.project sorted).apply t)⟩
      (fun k => ρ.image k.val) (Sum.elim m (fun _ => ρ.apply t)) ↔
    Denotes R r (fun k => ρ.image k.val) m := by
  constructor
  · rintro ⟨δ,n,h⟩; exact ⟨δ,n,h.inputs,fun i => h.values (.inl i)⟩
  · rintro ⟨δ,n,h⟩
    refine ⟨δ,n,h.inputs,?_⟩
    intro j
    cases j with
    | inl i => exact h.values i
    | inr _ =>
      change EquivB (ρ.apply t) (δ.apply ((r.project sorted).apply t))
      rw [←Substitution.apply_compose]
      apply Term.subst_equiv
      intro v hv
      let k : Key keys := ⟨v,scope v hv⟩
      change EquivB (ρ.image k.val) (δ.apply ((r.project sorted).image k.val))
      rw [r.project_key sorted k]
      exact h.inputs k

end Tamarin.Rewriting.VariantJoin

namespace Tamarin.Rewriting.BinaryXor
open Cancellation
variable {s : Signature} (T : Table s)
noncomputable section
open Classical

/-- All opaque factors of a stable leaf have normal representatives, even
when the leaf instantiates to a sum. This invariant composes at any width. -/
def NormalFactors (t : Term s) := ∀ k ∈ T.bag t, Fact T k

theorem normalFactors_ac {a b : Term s} (l : NormalFactors T a) (r : NormalFactors T b) :
    NormalFactors T (.ac T.f a b) := by
  intro k hk
  rw [FreshXor.Flat.Table.bag,flatten_ac] at hk
  exact (List.mem_append.mp hk).elim (l k) (r k)

private theorem distinct {α : Type} [DecidableEq α] (as : List α) : as.eraseDups.Nodup := by
  cases as with
  | nil => simp
  | cons x as =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp [List.mem_eraseDups],distinct _⟩
termination_by as.length
decreasing_by have := List.length_filter_le (fun (v : α) => !v == x) as; simp; omega

theorem normal_exists {t : Term s} (typed : HasSort t .msg) (root : t.rootSort = .msg)
    (facts : NormalFactors T t) : ∃ u, NormalForm T.R t u := by
  let xs := T.bag t
  let keep := xs.eraseDups.filter fun k => decide (k ≠ T.zeroClass ∧ xs.count k % 2 = 1)
  have nd : keep.Nodup := (distinct xs).filter _
  have mem k : k ∈ keep ↔ k ≠ T.zeroClass ∧ xs.count k % 2 = 1 := by
    simp only [keep,List.mem_filter,List.mem_eraseDups,decide_eq_true_eq]
    refine ⟨And.right,fun h => ⟨List.count_pos_iff.mp ?_,h⟩⟩
    omega
  refine ⟨_,(parity_normalForm T typed root facts nd (fun h => ((mem _).mp h).1 rfl) (ys := keep) ?_ _).mpr (.refl _)⟩
  intro k ne
  by_cases h : k ∈ keep
  · rw [nd.count_of_mem h]; exact (mem k |>.mp h).2
  · rw [List.count_eq_zero.mpr h]
    have odd : xs.count k % 2 ≠ 1 := fun o => h ((mem k).mpr ⟨ne,o⟩)
    change xs.count k % 2 = 0 % 2
    omega

/-- Splitting a flattened cancellation application into two subproducts and
normalizing them first preserves *all* normal forms, including ones reached
by a cancellation crossing the chosen split. -/
theorem staged_ac {a b u : Term s} (ta : HasSort a .msg) (tb : HasSort b .msg)
    (fa : NormalFactors T a) (fb : NormalFactors T b)
    (ea : ∃ v, NormalForm T.R a v) (eb : ∃ v, NormalForm T.R b v) :
    NormalForm T.R (.ac T.f a b) u ↔ ∃ l r, NormalForm T.R a l ∧ NormalForm T.R b r ∧ NormalForm T.R (.ac T.f l r) u := by
  have ty (x y : Term s) (hx : HasSort x .msg) (hy : HasSort y .msg) : HasSort (.ac T.f x y) .msg :=
    T.fSort ▸ HasSort.ac T.f _ _ (T.fSort ▸ hx) (T.fSort ▸ hy)
  have back {l r v} (nl : NormalForm T.R a l) (nr : NormalForm T.R b r) (n : NormalForm T.R (.ac T.f l r) v) :
      NormalForm T.R (.ac T.f a b) v :=
    ⟨(Reduces.ac T.f nl.1 nr.1).trans n.1,n.2.1,fun _ h =>
      .widen (n.2.2 _ (ty _ _ (nl.2.2 _ ta) (nr.2.2 _ tb))) (T.fSort ▸ Term.rootSort_le h)⟩
  constructor
  · intro n
    obtain ⟨l,nl⟩ := ea
    obtain ⟨r,nr⟩ := eb
    have gl : Good T l := ⟨nl.2.2 _ ta,nl.2.1⟩
    have gr : Good T r := ⟨nr.2.2 _ tb,nr.2.1⟩
    obtain ⟨v,nv⟩ := normal_exists T (ty _ _ gl.1 gr.1) T.fSort
      (normalFactors_ac T (fun _ => fact_of_mem T gl) (fun _ => fact_of_mem T gr))
    have pure : T.PureFrom (fun _ => True) (.ac T.f a b) :=
      fun k hk => .inr ⟨rep k,trivial,(normalFactors_ac T fa fb k hk).1.2,rep_key k⟩
    have eq := unique_of_pure T (ty _ _ ta tb) pure n (back nl nr nv)
    exact ⟨l,r,nl,nr,nv.1.trans (.basis eq.symm),n.2.1,fun _ hs => .widen (n.2.2 _ (ty _ _ ta tb)) (T.fSort ▸ Term.rootSort_le hs)⟩
  · rintro ⟨l,r,nl,nr,n⟩; exact back nl nr n

/-- Relational specification of the left-to-right fold. Each stage observes
the prior prefix and the next operand under a single caller substitution. -/
def scanForms (first : Term s) (rest : List (Term s)) : Term s → Prop :=
  rest.foldl (fun prior b v => ∃ l r, prior l ∧ NormalForm T.R b r ∧
    NormalForm T.R (.ac T.f l r) v) (NormalForm T.R first)

theorem scanForms_iff (first : Term s) (rest : List (Term s)) (initial : Good T first)
    (factors : ∀ t ∈ rest, Good T t) (v : Term s) :
    scanForms T first rest v ↔ NormalForm T.R (rest.foldl (.ac T.f) first) v := by
  have self {a : Term s} (g : Good T a) : NormalForm T.R a a :=
    ⟨.basis (.refl _),g.2,fun _ h => h⟩
  have inv (bs : List (Term s)) (good : ∀ t ∈ bs, Good T t) :
      let p := bs.foldl (.ac T.f) first
      HasSort p .msg ∧ NormalFactors T p ∧ (∃ n, NormalForm T.R p n) ∧
        ∀ n, scanForms T first bs n ↔ NormalForm T.R p n := by
    obtain ⟨rev,rfl⟩ : ∃ rev : List (Term s), bs = rev.reverse := ⟨bs.reverse,(List.reverse_reverse _).symm⟩
    induction rev with
    | nil => exact ⟨initial.1,fun _ => fact_of_mem T initial,⟨first,self initial⟩,fun _ => Iff.rfl⟩
    | cons b bs ih =>
      rw [List.reverse_cons] at good ⊢
      obtain ⟨typed,facts,existsNF,prior⟩ := ih (fun t ht => good t (List.mem_append_left _ ht))
      have gb := good b (List.mem_append_right _ List.mem_cons_self)
      have both := normalFactors_ac T facts (fun _ => fact_of_mem T gb)
      have ty := HasSort.ac T.f _ _ (T.fSort ▸ typed) (T.fSort ▸ gb.1)
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
      refine ⟨T.fSort ▸ ty,both,normal_exists T (T.fSort ▸ ty) T.fSort both,?_⟩
      intro n
      rw [staged_ac T typed gb.1 facts (fun _ => fact_of_mem T gb) existsNF ⟨b,self gb⟩]
      simp only [scanForms,List.foldl_append,List.foldl_cons,List.foldl_nil]
      exact exists_congr fun l => exists_congr fun r => and_congr_left fun _ => prior l
  exact (inv rest factors).2.2.2 v

end
end Tamarin.Rewriting.BinaryXor
