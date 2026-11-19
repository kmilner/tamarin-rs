import Tamarin.ContextualReduction
import Tamarin.ConstructorReduction

/-! A commutative or AC constructor with no equations at its own head
can normalize its original operands independently. In particular, a child
may reduce to an arbitrary product at the same AC head. -/
namespace Tamarin.Rewriting.InertProduct
open ConstructorVariants ACSubproductReduction
variable {s : Signature} {R : Root s}

/-- One step changes one original operand, up to structural equations. -/
def Independent (R : Root s) (op : Term s → Term s → Term s) : Prop :=
  ∀ a b t, StepModulo R (op a b) t →
    (∃ a', StepModulo R a a' ∧ EquivB (op a' b) t) ∨
    (∃ b', StepModulo R b b' ∧ EquivB (op a b') t)

theorem reduces_view {op : Term s → Term s → Term s} (indep : Independent R op)
    {a b t} (red : Reduces R (op a b) t) :
    ∃ x y, Reduces R a x ∧ Reduces R b y ∧ EquivB (op x y) t := by
  let P t := ∃ x y, Reduces R a x ∧ Reduces R b y ∧ EquivB (op x y) t
  apply RootNarrowing.reduction_invariant P _ _ red ⟨a,b,.basis (.refl _),.basis (.refl _),.refl _⟩
  · rintro _ _ ⟨x,y,hx,hy,eq⟩ e
    exact ⟨x,y,hx,hy,eq.trans e⟩
  · rintro _ _ ⟨x,y,hx,hy,eq⟩ ⟨p,q,l,st,r⟩
    rcases indep x y _ ⟨p,q,eq.trans l,st,r⟩ with ⟨x',step,out⟩|⟨y',step,out⟩
    · exact ⟨x',y,hx.trans (.step step),hy,out⟩
    · exact ⟨x,y',hx,hy.trans (.step step),out⟩

private theorem root_absent (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    {h : Head s} (absent : h ∉ ruleHeads rules) {p q : Term s} (hp : head p = h) :
    ¬ruleRoot rules p q := by
  rintro ⟨r,hr,σ,rfl,_⟩
  exact absent (((instance_head r (apps r hr) σ).symm.trans hp) ▸ List.mem_map_of_mem hr)

theorem comm_independent (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.CSym) (absent : Head.comm f ∉ ruleHeads rules) :
    Independent (ruleRoot rules) (.comm f) := by
  intro a b t st
  rcases (ContextualReduction.comm_iff ..).mp st with ⟨_,_,l,hit,_⟩|inside
  · exact (root_absent rules apps absent l.head_eq.symm hit).elim
  · exact inside

/-- Add one sibling to an existing occurrence context. Both the selected
factor and its replacement will be grouped with precisely this remainder. -/
private def sibling (f : s.ACSym) (k : Option (Term s)) (b : Term s) : Option (Term s) :=
  some (plug f k b)

private theorem plug_sibling (f : s.ACSym) (k : Option (Term s)) (p b : Term s) :
    EquivB (.ac f (plug f k p) b) (plug f (sibling f k b) p) := by
  cases k with
  | none => exact .refl _
  | some u => exact (EquivB.ac_assoc f p u b).trans (.ac_congr f (.refl _) (.ac_swap ..))

private theorem factor_context [DecidableEq s.ACSym] (f : s.ACSym) (a : Term s) {p}
    (mem : p ∈ ACRepresentation.flatten f a) : ∃ k, EquivB a (plug f k p) := by
  induction a with
  | ac g a b ia ib =>
    by_cases same : f = g
    · subst g
      simp [ACRepresentation.flatten] at mem
      rcases mem with ha|hb
      · obtain ⟨k,eq⟩ := ia ha
        exact ⟨_,(EquivB.ac_congr f eq (.refl _)).trans (plug_sibling f k p b)⟩
      · obtain ⟨k,eq⟩ := ib hb
        exact ⟨_,(EquivB.ac_swap ..).trans ((EquivB.ac_congr f eq (.refl _)).trans (plug_sibling f k p a))⟩
    · simp only [ACRepresentation.flatten,ite_eq_right same,List.mem_singleton] at mem
      exact ⟨none,mem ▸ .refl _⟩
  | _ =>
    simp only [ACRepresentation.flatten,List.mem_singleton] at mem
    exact ⟨none,mem ▸ .refl _⟩

private theorem replace_left [DecidableEq s.ACSym] (f : s.ACSym) {a b p q t : Term s}
    (mem : p ∈ ACRepresentation.flatten f a) (k : Option (Term s))
    (step : StepModulo R p q) (l : EquivB (.ac f a b) (plug f k p))
    (r : EquivB (plug f k q) t) :
    ∃ v, StepModulo R a v ∧ EquivB (.ac f v b) t := by
  obtain ⟨ka,ea⟩ := factor_context f _ mem
  have before := (EquivB.ac_congr f ea (.refl b)).trans (plug_sibling f ka p b)
  obtain ⟨x,y,ll,st,rr⟩ := lift_step f ka step
  exact ⟨_,⟨x,y,ea.trans ll,st,rr⟩,(plug_sibling f ka q b).trans ((same_context f before l (.refl _) q).trans r)⟩

theorem ac_independent [DecidableEq s.ACSym] (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (absent : Head.ac f ∉ ruleHeads rules) :
    Independent (ruleRoot rules) (.ac f) := by
  intro a b t st
  rcases (all_steps_iff f _ _).mp st with ⟨_,_,_,hp,hit,_,_⟩|⟨p,hm,q,k,step,l,r⟩
  · exact (root_absent rules apps absent hp hit).elim
  · simp [ACRepresentation.flatten] at hm
    rcases hm with ha|hb
    · exact .inl (replace_left f ha k step l r)
    · obtain ⟨y,sy,eq⟩ := replace_left f hb k step ((EquivB.ac_swap ..).trans l) r
      exact .inr ⟨y,sy,(EquivB.ac_swap ..).trans eq⟩

/-- A child occupying a wider slot either cannot change, or its declared
sort agrees with the slot. This recovers every sort of the original child
from the sort of the whole normal form. -/
def Slot (R : Root s) (k : SortId) (a : Term s) := Normal R a ∨ a.rootSort = k

private theorem child_sorts {a x : Term s} {k : SortId} (slot : Slot R k a)
    (red : Reduces R a x) (st : HasSort x k) : ∀ j, HasSort a j → HasSort x j := by
  intro j hs
  rcases slot with hn|e
  · exact Term.checkSort_sound _ _ ((SortClash.check_equiv (normal_reduces_equiv red hn) j) ▸
      Term.checkSort_complete hs)
  · exact .widen st (e ▸ Term.rootSort_le hs)

/-- The full normal-form relation factors: normalization in each child is
sufficient, and every possible endpoint is represented. -/
theorem ac_forms [DecidableEq s.ACSym] (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (absent : Head.ac f ∉ ruleHeads rules)
    (a b u : Term s) (ta : HasSort a (s.acSort f)) (tb : HasSort b (s.acSort f))
    (sa : Slot (ruleRoot rules) (s.acSort f) a) (sb : Slot (ruleRoot rules) (s.acSort f) b) :
    NormalForm (ruleRoot rules) (.ac f a b) u ↔ ∃ x y,
      NormalForm (ruleRoot rules) a x ∧ NormalForm (ruleRoot rules) b y ∧ EquivB (.ac f x y) u := by
  constructor
  · intro nf
    obtain ⟨x,y,rx,ry,e⟩ := reduces_view (ac_independent rules apps f absent) nf.1
    have norms := normal_ac_children f ((normal_equiv _ e).mpr nf.2.1)
    have typed := Term.checkSort_complete (nf.2.2 _ (HasSort.ac f _ _ ta tb))
    rw [←SortClash.check_equiv e] at typed
    simp only [Term.checkSort,Bool.and_eq_true] at typed
    exact ⟨x,y,⟨rx,norms.1,child_sorts sa rx (Term.checkSort_sound _ _ typed.1.2)⟩,
      ⟨ry,norms.2,child_sorts sb ry (Term.checkSort_sound _ _ typed.2)⟩,e⟩
  · rintro ⟨x,y,hx,hy,e⟩
    refine ⟨(.ac f hx.1 hy.1 : Reduces _ _ _).trans (.basis e),
      (normal_equiv _ e).mp (constructor_node_normal rules apps _ absent ⟨hx.2.1,hy.2.1⟩),?_⟩
    intro k hs
    apply Term.checkSort_sound
    rw [←SortClash.check_equiv e]
    exact Term.checkSort_complete (.widen (.ac f _ _ (hx.2.2 _ ta) (hy.2.2 _ tb)) (Term.rootSort_le hs))

theorem comm_forms (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.CSym) (absent : Head.comm f ∉ ruleHeads rules) (a b u : Term s)
    (ta : HasSort a (s.cSort f)) (tb : HasSort b (s.cSort f))
    (sa : Slot (ruleRoot rules) (s.cSort f) a) (sb : Slot (ruleRoot rules) (s.cSort f) b) :
    NormalForm (ruleRoot rules) (.comm f a b) u ↔ ∃ x y,
      NormalForm (ruleRoot rules) a x ∧ NormalForm (ruleRoot rules) b y ∧ EquivB (.comm f x y) u := by
  constructor
  · intro nf
    obtain ⟨x,y,rx,ry,e⟩ := reduces_view (comm_independent rules apps f absent) nf.1
    have norms := normal_comm_children f ((normal_equiv _ e).mpr nf.2.1)
    have typed := Term.checkSort_complete (nf.2.2 _ (HasSort.comm f _ _ ta tb))
    rw [←SortClash.check_equiv e] at typed
    simp only [Term.checkSort,Bool.and_eq_true] at typed
    exact ⟨x,y,⟨rx,norms.1,child_sorts sa rx (Term.checkSort_sound _ _ typed.1.2)⟩,
      ⟨ry,norms.2,child_sorts sb ry (Term.checkSort_sound _ _ typed.2)⟩,e⟩
  · rintro ⟨x,y,hx,hy,e⟩
    refine ⟨(.comm f hx.1 hy.1 : Reduces _ _ _).trans (.basis e),
      (normal_equiv _ e).mp (constructor_node_normal rules apps _ absent ⟨hx.2.1,hy.2.1⟩),?_⟩
    intro k hs
    apply Term.checkSort_sound
    rw [←SortClash.check_equiv e]
    exact Term.checkSort_complete (.widen (.comm f _ _ (hx.2.2 _ ta) (hy.2.2 _ tb)) (Term.rootSort_le hs))

private theorem move_output {a b c : Term s} (nf : NormalForm R a b) (e : EquivB b c) :
    NormalForm R a c :=
  ⟨nf.1.trans (.basis e),(normal_equiv _ e).mp nf.2.1,fun k hs => Term.checkSort_sound _ _
    ((SortClash.check_equiv e k) ▸ Term.checkSort_complete (nf.2.2 _ hs))⟩

/-- Array-level contract: every normal form of a nonempty product is
precisely the fold of a positionally aligned list of child normal forms,
up to arbitrary reassociation, flattening and permutation. -/
theorem fold_forms [DecidableEq s.ACSym] (rules : List (Equation s))
    (apps : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (absent : Head.ac f ∉ ruleHeads rules)
    (a : Term s) (as : List (Term s)) (u : Term s)
    (domains : ∀ t ∈ a :: as, HasSort t (s.acSort f) ∧ Slot (ruleRoot rules) (s.acSort f) t) :
    NormalForm (ruleRoot rules) (ACRepresentation.fold f a as) u ↔
      ∃ x xs, NormalForm (ruleRoot rules) a x ∧ Aligned (NormalForm (ruleRoot rules)) as xs ∧
        EquivB (ACRepresentation.fold f x xs) u := by
  induction as generalizing a u with
  | nil =>
    constructor
    · intro nf; exact ⟨u,[],nf,trivial,.refl _⟩
    · rintro ⟨x,(_|_),nx,ok,eq⟩
      · exact move_output nx eq
      · exact ok.elim
  | cons b bs ih =>
    have left := domains a (by simp)
    have rest (t) (ht : t ∈ b :: bs) := domains t (List.mem_cons_of_mem _ ht)
    have tb := ACRepresentation.fold_hasSort f b bs (rest b (by simp)).1
      (fun t ht => (rest t (List.mem_cons_of_mem _ ht)).1)
    have sb : Slot (ruleRoot rules) (s.acSort f) (ACRepresentation.fold f b bs) := by
      cases bs with
      | nil => exact (rest b (by simp)).2
      | cons _ _ => exact .inr rfl
    rw [ACRepresentation.fold,ac_forms rules apps f absent _ _ _ left.1 tb left.2 sb]
    constructor
    · rintro ⟨x,r,nx,nr,eq⟩
      obtain ⟨y,ys,ny,nys,er⟩ := (ih b r rest).mp nr
      exact ⟨x,y::ys,nx,⟨ny,nys⟩,(EquivB.ac_congr f (.refl _) er).trans eq⟩
    · rintro ⟨x,(_|⟨y,ys⟩),nx,ok,eq⟩
      · exact ok.elim
      · exact ⟨x,_,nx,(ih b _ rest).mpr ⟨y,ys,ok.1,ok.2,.refl _⟩,eq⟩

end Tamarin.Rewriting.InertProduct
