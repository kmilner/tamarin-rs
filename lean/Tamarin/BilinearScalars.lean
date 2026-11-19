import Tamarin.BilinearRoots

/-! Project reductions of point actions and bilinear maps on normalized
operands to a single scalar product under the shared group rules. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer
variable {sig : Signature} {s : Symbols sig} {T : Table s} {β : Operators sig}

/-- A positional binary call either rewrites at the parent or in exactly
one operand. This applies to both the point-action and DH power symbols. -/
theorem Operators.steps (β : Operators sig) {R : Root sig} {a p out : Term sig}
    (st : StepModulo R (β.point a p) out) :
    ContextualReduction.AtRoot R (β.point a p) out ∨
      (∃ b, StepModulo R a b ∧ EquivB (β.point b p) out) ∨
      (∃ q, StepModulo R p q ∧ EquivB (β.point a q) out) := by
  rcases (ContextualReduction.free_iff ..).mp st with h|⟨i,t,hit,align⟩
  · exact .inl h
  have ar := β.arity
  by_cases hi : i.val = 0
  · refine .inr (.inl ⟨t,by simpa [hi] using hit,EquivB.trans ?_ align⟩)
    apply EquivB.free; intro j
    have he : j = i ↔ j.val = 0 := ⟨fun e => e ▸ hi, fun e => Fin.ext (e.trans hi.symm)⟩
    simp only [he]; change EquivB (if _ then _ else _) (if _ then _ else (if _ then _ else _))
    split <;> simp_all [EquivB.refl]
  · refine .inr (.inr ⟨t,by simpa [hi] using hit,EquivB.trans ?_ align⟩)
    apply EquivB.free; intro j
    have he : j = i ↔ j.val ≠ 0 := ⟨fun e => e ▸ hi,fun h => Fin.ext (by have := i.isLt; have := j.isLt; omega)⟩
    simp only [he]; change EquivB (if _ then _ else _) (if _ then _ else (if _ then _ else _))
    split <;> simp_all [EquivB.refl]

private def powerOp (β : Operators sig) (s : Symbols sig) : Operators sig :=
  { β with pmult := s.pow, arity := s.powArity, inputs := s.powInput, pointSort := s.powSort }

private theorem rootStep {R : Root sig} {a b : Term sig} (hit : R a b) : StepModulo R a b :=
  ⟨_,_,.refl _,.root hit,.refl _⟩

private theorem step_rebase {R : Root sig} {a b c d : Term sig} (l : EquivB a b) (st : StepModulo R b c)
    (r : EquivB c d) : StepModulo R a d := by
  obtain ⟨x,y,e,h,f⟩ := st
  exact ⟨x,y,l.trans e,h,f.trans r⟩

/-- Force one of the possible first steps before reaching any normal output. -/
private theorem tail {R : Root sig} {a out : Term sig} (A : Term sig → Prop)
    (someStep : ∃ b, StepModulo R a b)
    (next : ∀ b, StepModulo R a b → ∃ x, A x ∧ EquivB x b) (r : Reduces R a out) (nn : Normal R out) :
    ∃ x, A x ∧ Reduces R x out := by
  let P (u : Term sig) := EquivB a u ∨ ∃ x, A x ∧ Reduces R x u
  have e : P out := RootNarrowing.reduction_invariant P (fun h e => by
    rcases h with h|⟨x,hx,r⟩
    · exact .inl (h.trans e)
    · exact .inr ⟨x,hx,r.trans (.basis e)⟩) (fun h st => by
    rcases h with h|⟨x,hx,r⟩
    · obtain ⟨x,hx,ex⟩ := next _ (step_rebase h st (.refl _))
      exact .inr ⟨x,hx,.basis ex⟩
    · exact .inr ⟨x,hx,r.trans (.step st)⟩) r (.inl (.refl _))
  rcases e with e|h
  · obtain ⟨b,st⟩ := someStep; exact ((normal_equiv _ e).mpr nn b st).elim
  · exact h

private theorem typed_equiv {a b : Term sig} (e : EquivB a b) {k} (h : HasSort a k) : HasSort b k :=
  Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h)

private theorem nested_steps (I : Inventory s β T.rules) {a b p out : Term sig}
    (na : Normal (ruleRoot T.rules) a) (np : Normal (ruleRoot T.rules) (β.point b p))
    (nonunit : head a ≠ .free s.one) (st : StepModulo (ruleRoot T.rules) (β.point a (β.point b p)) out) :
    EquivB (β.point (s.product.mul a b) p) out := by
  rcases β.steps st with ⟨t,u,e,h,v⟩|⟨x,h,_⟩|⟨x,h,_⟩
  · cases I.point_root e h with
    | one one => exact (nonunit one).elim
    | nested point result =>
      obtain ⟨l,r⟩ := β.point_equiv point
      exact (β.point_congr (.ac_congr _ (.refl _) l) r).trans (result.symm.trans v)
  · exact (na x h).elim
  · exact (np x h).elim

/-- For a fixed normal plain point, all changes are changes of its scalar
until a unit scalar exposes the point itself. -/
private theorem fixed_point (I : Inventory s β T.rules) {a p out : Term sig}
    (np : Normal (ruleRoot T.rules) p) (plain : head p ≠ .free β.pmult)
    (red : Reduces (ruleRoot T.rules) (β.point a p) out) :
    (∃ b, Reduces (ruleRoot T.rules) a b ∧ EquivB (β.point b p) out) ∨
    (Reduces (ruleRoot T.rules) a s.product.one ∧ EquivB p out) := by
  let P (t : Term sig) := (∃ b, Reduces (ruleRoot T.rules) a b ∧ EquivB (β.point b p) t) ∨
    (Reduces (ruleRoot T.rules) a s.product.one ∧ EquivB p t)
  apply RootNarrowing.reduction_invariant P _ _ red (.inl ⟨a,.basis (.refl _),.refl _⟩)
  · rintro _ _ (⟨b,r,e⟩|⟨r,e⟩) f
    · exact .inl ⟨b,r,e.trans f⟩
    · exact .inr ⟨r,e.trans f⟩
  · rintro _ _ (⟨b,r,e⟩|⟨r,e⟩) st
    · rcases β.steps (step_rebase e st (.refl _)) with ⟨u,v,pre,h,post⟩|⟨c,h,v⟩|⟨c,h,v⟩
      · cases I.point_root pre h with
        | one unit v =>
          obtain rfl : b = s.product.one := nullary s.oneArity unit
          exact .inr ⟨r,v.symm.trans post⟩
        | nested h => exact (plain h.head_eq).elim
      · exact .inl ⟨c,r.trans (.step h),v⟩
      · exact (np c h).elim
    · exact ((normal_equiv _ e).mp np _ st).elim

private theorem mul_sorted {a b : Term sig} (l : HasSort a .msg) (r : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ l) (s.mulSort ▸ r)

private theorem one_sorted (s : Symbols sig) : HasSort s.product.one .msg := by
  rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)

/-- Both the nonunit and the folded unit rows use the very same normalized
scalar product and concrete scalar inputs. -/
def Fold (s : Symbols sig) (op : Term sig → Term sig) (plain m out : Term sig) : Prop :=
  (m = s.product.one ∧ EquivB out plain) ∨ (head m ≠ .free s.one ∧ EquivB out (op m))

theorem Inventory.point_lift (I : Inventory s β T.rules) {a b p out : Term sig}
    (sa : HasSort a .msg) (sb : HasSort b .msg) (sp : HasSort p .msg)
    (na : Normal (ruleRoot T.rules) a) (np : Normal (ruleRoot T.rules) (β.point b p))
    (nonunit : head a ≠ .free s.one) (one : Normal (ruleRoot T.rules) s.product.one) :
    NormalForm (ruleRoot T.rules) (β.point a (β.point b p)) out ↔
      ∃ m, NormalForm (ruleRoot T.rules) (s.product.mul a b) m ∧ Fold s (fun x => β.point x p) p m out := by
  obtain ⟨_,npoint,_,plain⟩ := (I.point_normal_iff sb sp).mp np
  have fire := rootStep (I.nested sa sb sp)
  have start := β.point_sorted sa (β.point_sorted sb sp)
  constructor
  · intro form
    obtain ⟨_,rfl,r⟩ := tail (· = β.point (s.product.mul a b) p) ⟨_,fire⟩
      (fun _ st => ⟨_,rfl,nested_steps I na np nonunit st⟩) form.1 form.2.1
    have make {x} (rx : Reduces _ (s.product.mul a b) x) (nx : Normal (ruleRoot T.rules) x) (sx : HasSort x .msg) :
        NormalForm (ruleRoot T.rules) (s.product.mul a b) x := ⟨rx,nx,fun _ h => .widen sx (s.mulSort ▸ Term.rootSort_le h)⟩
    rcases fixed_point I npoint plain r with ⟨m,rm,eq⟩|⟨rm,eq⟩
    · have sm := (β.point_types (typed_equiv eq.symm (form.2.2 _ start))).1
      obtain ⟨nm,_,nu,_⟩ := (I.point_normal_iff sm sp).mp ((normal_equiv _ eq).mpr form.2.1)
      exact ⟨m,make rm nm sm,.inr ⟨nu,eq.symm⟩⟩
    · exact ⟨_,make rm one (one_sorted s),.inl ⟨rfl,eq.symm⟩⟩
  · rintro ⟨m,nf,d⟩
    have sm := nf.2.2 _ (mul_sorted sa sb)
    have reduced : Reduces (ruleRoot T.rules) (β.point a (β.point b p)) (β.point m p) :=
      (Reduces.step fire).trans (by apply Reduces.free; intro i; split <;> first | exact nf.1 | exact .basis (.refl _))
    rcases d with ⟨rfl,eq⟩|⟨nu,eq⟩
    · exact ⟨(reduced.trans (.step (rootStep (I.one sp)))).trans (.basis eq.symm),
        (normal_equiv _ eq).mpr npoint,fun _ h => .widen (typed_equiv eq.symm sp) (β.pointSort ▸ Term.rootSort_le h)⟩
    · exact ⟨reduced.trans (.basis eq.symm),(normal_equiv _ eq).mpr ((I.point_normal_iff sm sp).mpr ⟨nf.2.1,npoint,nu,plain⟩),
        fun _ h => .widen (typed_equiv eq.symm (β.point_sorted sm sp)) (β.pointSort ▸ Term.rootSort_le h)⟩

/-- The unit rule overlaps the point nesting rule when its other operand
is an action. Both orders preserve the same point even when the scalar or
underlying point contains arbitrary additional constructors. -/
theorem Inventory.point_one [DecidableEq sig.ACSym] {E : ExtraTable T} (I : Inventory s β T.rules)
    (group : Balance.Inventory E) {p out : Term sig} (sp : HasSort p .msg)
    (np : Normal (ruleRoot T.rules) p) (one : Normal (ruleRoot T.rules) s.product.one) :
    NormalForm (ruleRoot T.rules) (β.point s.product.one p) out ↔ EquivB out p := by
  have start := β.point_sorted (one_sorted s) sp
  constructor
  · intro form
    let P (u : Term sig) := u = p ∨ ∃ b q, p = β.point b q ∧ u = β.point (s.product.mul s.product.one b) q
    obtain ⟨u,branch,red⟩ := tail P ⟨_,rootStep (I.one sp)⟩ (fun t st => by
      rcases β.steps st with ⟨x,y,e,r,v⟩|⟨x,h,_⟩|⟨x,h,_⟩
      · cases I.point_root e r with
        | one _ res => exact ⟨p,.inl rfl,res.symm.trans v⟩
        | nested eq res =>
          obtain ⟨b,q,hp⟩ := β.split eq.head_eq
          obtain ⟨l,r⟩ := β.point_equiv (hp ▸ eq)
          exact ⟨_,.inr ⟨b,q,hp,rfl⟩,(β.point_congr (.ac_congr _ (.refl _) l) r).trans (res.symm.trans v)⟩
      · exact (one x h).elim
      · exact (np x h).elim) form.1 form.2.1
    rcases branch with rfl|⟨b,q,rfl,rfl⟩
    · exact (normal_reduces_equiv red np).symm
    · obtain ⟨sb,sq⟩ := β.point_types sp
      obtain ⟨nb,nq,bu,plain⟩ := (I.point_normal_iff sb sq).mp np
      have toB : Reduces (ruleRoot T.rules) (s.product.mul s.product.one b) b :=
        .step ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule b sb),.refl _⟩
      have domain := Staging.signed_mul (fun k => Balance.defined s _ k one) (fun k => Balance.defined s _ k nb)
      have unique {v} (r : Reduces (ruleRoot T.rules) (s.product.mul s.product.one b) v)
          (nv : Normal (ruleRoot T.rules) v) (sv : HasSort v .msg) : EquivB v b :=
        Balance.normal_unique group E.presentation (fun _ => Balance.plain_of_inverse E) domain sv sb nv nb r toB
      rcases fixed_point I nq plain red with ⟨m,rm,eq⟩|⟨rm,eq⟩
      · have sm := (β.point_types (typed_equiv eq.symm (form.2.2 _ start))).1
        have nm := ((I.point_normal_iff sm sq).mp ((normal_equiv _ eq).mpr form.2.1)).1
        exact eq.symm.trans (β.point_congr (unique rm nm sm) (.refl _))
      · exact (bu (unique rm one (one_sorted s)).head_eq.symm).elim
  · intro e
    exact ⟨(Reduces.step (rootStep (I.one sp))).trans (.basis e.symm),(normal_equiv _ e).mpr np,
      fun _ h => .widen (typed_equiv e.symm sp) (β.pointSort ▸ Term.rootSort_le h)⟩

private theorem pow_congr {b c e f : Term sig} (h : EquivB b c) (k : EquivB e f) :
    EquivB (s.power b e) (s.power c f) := by apply EquivB.free; intro i; split <;> assumption

private theorem pow_red {R : Root sig} {b c e f : Term sig} (h : Reduces R b c) (k : Reduces R e f) :
    Reduces R (s.power b e) (s.power c f) := by apply Reduces.free; intro i; split <;> assumption

private theorem map_left_steps (I : Inventory s β T.rules) {a p q out : Term sig}
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) q)
    (plain : head q ≠ .free β.pmult) (st : StepModulo (ruleRoot T.rules) (β.map (β.point a p) q) out) :
    EquivB (s.power (β.map p q) a) out := by
  rcases (ContextualReduction.comm_iff ..).mp st with ⟨t,u,e,h,v⟩|⟨x,h,_⟩|⟨x,h,_⟩
  · cases I.map_root e h with
    | left point result =>
      obtain ⟨l,r⟩ := β.point_equiv point
      exact (pow_congr (.comm_congr _ r (.refl _)) l).trans (result.symm.trans v)
    | right point => exact (plain point.head_eq).elim
  · exact (lhs x h).elim
  · exact (rhs x h).elim

private theorem map_left_fire (I : Inventory s β T.rules) {a p q : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg) (sq : HasSort q .msg) :
    StepModulo (ruleRoot T.rules) (β.map (β.point a p) q) (s.power (β.map p q) a) :=
  ⟨_,_,.comm_swap ..,.root (I.extract sq sa sp),pow_congr (.comm_swap ..) (.refl _)⟩

/-- When only one operand is a point action, both commutative orientations
give exactly the same normal power. -/
theorem Inventory.map_single (I : Inventory s β T.rules) (pow : PowerBucket T) {a p q out : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg) (sq : HasSort q .msg)
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) q)
    (plain : head q ≠ .free β.pmult) :
    NormalForm (ruleRoot T.rules) (β.map (β.point a p) q) out ↔ EquivB out (s.power (β.map p q) a) := by
  obtain ⟨na,np,nu,nop⟩ := (I.point_normal_iff sa sp).mp lhs
  have baseN := (I.map_normal_iff sp sq).mpr ⟨np,rhs,nop,plain⟩
  have normal := (pow.normal_iff (β.map_sorted sp sq) sa).mpr ⟨baseN,na,(by intro e; cases e),(by intro e; cases e),nu⟩
  have fire := map_left_fire I sa sp sq
  constructor
  · intro form
    obtain ⟨_,rfl,r⟩ := tail (· = s.power (β.map p q) a) ⟨_,fire⟩
      (fun _ st => ⟨_,rfl,map_left_steps I lhs rhs plain st⟩) form.1 form.2.1
    exact (normal_reduces_equiv r normal).symm
  · intro eq
    exact ⟨(Reduces.step fire).trans (.basis eq.symm),(normal_equiv _ eq).mpr normal,
      fun _ h => .widen (typed_equiv eq.symm (DHTower.powerSorted (β.map_sorted sp sq) sa)) (β.mapSort ▸ Term.rootSort_le h)⟩

/-- Modulo the free-power context, the second extraction is forced before
either the unit, tower, or neutral power rule can fire. -/
private theorem middle (I : Inventory s β T.rules) (pow : PowerBucket T) {a b p q out : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg) (sq : HasSort q .msg)
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) q)
    (plain : head q ≠ .free β.pmult) (nb : Normal (ruleRoot T.rules) b) (bu : head b ≠ .free s.one)
    (red : Reduces (ruleRoot T.rules) (s.power (β.map (β.point a p) q) b) out) (nn : Normal (ruleRoot T.rules) out) :
    Reduces (ruleRoot T.rules) (s.power (s.power (β.map p q) a) b) out := by
  have inner := map_left_fire I sa sp sq
  have someStep : ∃ t, StepModulo (ruleRoot T.rules) (s.power (β.map (β.point a p) q) b) t := by
    apply Classical.byContradiction; intro none
    have hn : Normal (ruleRoot T.rules) (s.power (β.map (β.point a p) q) b) := fun t ht => none ⟨t,ht⟩
    let i : Fin (sig.arity s.pow) := ⟨0,by have := s.powArity; omega⟩
    have child : Normal (ruleRoot T.rules) (β.map (β.point a p) q) := by
      simpa [i] using normal_free_child s.pow _ hn i
    exact child _ inner
  obtain ⟨_,rfl,rest⟩ := tail (· = s.power (s.power (β.map p q) a) b) someStep (fun z st => by
    refine ⟨_,rfl,?_⟩
    rcases (powerOp β s).steps st with ⟨t,u,e,h,v⟩|⟨x,h,e⟩|⟨x,h,e⟩
    · cases pow.root _ _ e h with
      | one bad => exact (bu bad).elim
      | neutral bad => cases bad
      | tower base => cases base.head_eq
    · exact (pow_congr (map_left_steps I lhs rhs plain h) (.refl _)).trans e
    · exact (nb x h).elim) red nn
  exact rest

private theorem map_double_steps (I : Inventory s β T.rules) {a b p q out : Term sig}
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) (β.point b q))
    (st : StepModulo (ruleRoot T.rules) (β.map (β.point a p) (β.point b q)) out) :
    EquivB (s.power (β.map (β.point a p) q) b) out ∨ EquivB (s.power (β.map (β.point b q) p) a) out := by
  rcases (ContextualReduction.comm_iff ..).mp st with ⟨t,u,e,h,v⟩|⟨x,h,_⟩|⟨x,h,_⟩
  · cases I.map_root e h with
    | left point result =>
      obtain ⟨l,r⟩ := β.point_equiv point
      exact .inr ((pow_congr ((EquivB.comm_swap ..).trans (.comm_congr _ r (.refl _))) l).trans (result.symm.trans v))
    | right point result =>
      obtain ⟨l,r⟩ := β.point_equiv point
      exact .inl ((pow_congr (.comm_congr _ (.refl _) r) l).trans (result.symm.trans v))
  · exact (lhs x h).elim
  · exact (rhs x h).elim

private theorem tower_project (I : Inventory s β T.rules) (pow : PowerBucket T)
    {a b p q out : Term sig} (sa : HasSort a .msg) (sb : HasSort b .msg) (sp : HasSort p .msg) (sq : HasSort q .msg)
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) (β.point b q))
    (unit : Normal (ruleRoot T.rules) s.product.one) (so : HasSort out .msg) (no : Normal (ruleRoot T.rules) out)
    (red : Reduces (ruleRoot T.rules) (s.power (β.map (β.point a p) q) b) out) :
    ∃ m, NormalForm (ruleRoot T.rules) (s.product.mul a b) m ∧ Fold s (s.power (β.map p q)) (β.map p q) m out := by
  obtain ⟨na,np,au,hp⟩ := (I.point_normal_iff sa sp).mp lhs
  obtain ⟨nb,nq,bu,hq⟩ := (I.point_normal_iff sb sq).mp rhs
  have tower := middle I pow sa sp sq lhs nq hq nb bu red no
  have nm := (I.map_normal_iff sp sq).mpr ⟨np,nq,hp,hq⟩
  have base := β.map_sorted sp sq
  have first := (pow.normal_iff base sa).mpr ⟨nm,na,(by intro e; cases e),(by intro e; cases e),au⟩
  exact pow.tower_normal_value base sa sb first nb bu unit ⟨tower,no,fun _ h => .widen so (s.powSort ▸ Term.rootSort_le h)⟩

/-- Extracting the left or the right scalar first gives precisely the
same normal-output relation. A folded unit removes the exponent entirely. -/
theorem Inventory.map_lift (I : Inventory s β T.rules) (pow : PowerBucket T) {a b p q out : Term sig}
    (sa : HasSort a .msg) (sb : HasSort b .msg) (sp : HasSort p .msg) (sq : HasSort q .msg)
    (lhs : Normal (ruleRoot T.rules) (β.point a p)) (rhs : Normal (ruleRoot T.rules) (β.point b q))
    (unit : Normal (ruleRoot T.rules) s.product.one) :
    NormalForm (ruleRoot T.rules) (β.map (β.point a p) (β.point b q)) out ↔
      ∃ m, NormalForm (ruleRoot T.rules) (s.product.mul a b) m ∧ Fold s (s.power (β.map p q)) (β.map p q) m out := by
  have step := rootStep (I.extract (β.point_sorted sa sp) sb sq)
  constructor
  · intro form
    have so := form.2.2 _ (β.map_sorted (β.point_sorted sa sp) (β.point_sorted sb sq))
    obtain ⟨x,which,red⟩ := tail (fun x => x = s.power (β.map (β.point a p) q) b ∨ x = s.power (β.map (β.point b q) p) a)
      ⟨_,step⟩ (fun z st => by
        rcases map_double_steps I lhs rhs st with left|right
        · exact ⟨_,.inl rfl,left⟩
        · exact ⟨_,.inr rfl,right⟩) form.1 form.2.1
    rcases which with rfl|rfl
    · exact tower_project I pow sa sb sp sq lhs rhs unit so form.2.1 red
    · obtain ⟨m,nf,view⟩ := tower_project I pow sb sa sq sp rhs lhs unit so form.2.1 red
      refine ⟨m,⟨(Reduces.basis (.ac_swap ..)).trans nf.1,nf.2.1,fun k h => nf.2.2 k (typed_equiv (.ac_swap ..) h)⟩,?_⟩
      rcases view with ⟨rfl,e⟩|⟨nu,e⟩
      · exact .inl ⟨rfl,e.trans (.comm_swap ..)⟩
      · exact .inr ⟨nu,e.trans (pow_congr (.comm_swap ..) (.refl _))⟩
  · rintro ⟨m,nf,view⟩
    let base := β.map p q
    have typedBase := β.map_sorted sp sq
    obtain ⟨_,np,_,hp⟩ := (I.point_normal_iff sa sp).mp lhs
    obtain ⟨_,nq,_,hq⟩ := (I.point_normal_iff sb sq).mp rhs
    have normalBase := (I.map_normal_iff sp sq).mpr ⟨np,nq,hp,hq⟩
    have toTower := (Reduces.step step).trans (pow_red (Reduces.step (map_left_fire I sa sp sq)) (.basis (.refl _)))
    let vals (i : Fin 3) := if i = 0 then base else if i = 1 then a else b
    have typed (i) : HasSort (vals i) .msg := by unfold vals; split <;> first | assumption | split <;> assumption
    have collapse : Reduces (ruleRoot T.rules) (s.power (s.power base a) b) (s.power base (s.product.mul a b)) :=
      T.fire .tower vals typed
    have r := (toTower.trans collapse).trans (pow_red (.basis (.refl _)) nf.1)
    rcases view with ⟨rfl,eq⟩|⟨nu,eq⟩
    · exact ⟨(r.trans (T.fire .expOne (fun _ => base) (fun _ => typedBase))).trans (.basis eq.symm),
        (normal_equiv _ eq).mpr normalBase,fun _ h => .widen (typed_equiv eq.symm typedBase) (β.mapSort ▸ Term.rootSort_le h)⟩
    · have sm := nf.2.2 _ (mul_sorted sa sb)
      have nm := (pow.normal_iff typedBase sm).mpr ⟨normalBase,nf.2.1,(by intro h; cases h),(by intro h; cases h),nu⟩
      exact ⟨r.trans (.basis eq.symm),(normal_equiv _ eq).mpr nm,fun _ h =>
        .widen (typed_equiv eq.symm (DHTower.powerSorted typedBase sm)) (β.mapSort ▸ Term.rootSort_le h)⟩

/-- Total shape split for two independently normalized messages at the
point-action head. The nested branch delegates only a scalar product. -/
inductive PointResult (s : Symbols sig) (β : Operators sig) (R : Root sig) (a p out : Term sig) : Prop where
  | unit (scalar : a = s.product.one) (value : EquivB out p)
  | plain (scalar : head a ≠ .free s.one) (base : head p ≠ .free β.pmult) (value : EquivB out (β.point a p))
  | nested {b q m} (scalar : head a ≠ .free s.one) (point : p = β.point b q)
      (product : NormalForm R (s.product.mul a b) m) (value : Fold s (fun v => β.point v q) q m out)

/-- The source syntax has one commutative extraction schema. The four
input shapes account for both orientations and their overlap. -/
inductive MapResult (s : Symbols sig) (β : Operators sig) (R : Root sig) (p q out : Term sig) : Prop where
  | plain (left : head p ≠ .free β.pmult) (right : head q ≠ .free β.pmult) (value : EquivB out (β.map p q))
  | left {a w} (point : p = β.point a w) (plain : head q ≠ .free β.pmult) (value : EquivB out (s.power (β.map w q) a))
  | right {b w} (point : q = β.point b w) (plain : head p ≠ .free β.pmult) (value : EquivB out (s.power (β.map p w) b))
  | both {a b v w m} (left : p = β.point a v) (right : q = β.point b w)
      (product : NormalForm R (s.product.mul a b) m) (value : Fold s (s.power (β.map v w)) (β.map v w) m out)

private theorem already {R : Root sig} {a out : Term sig} (n : Normal R a) :
    NormalForm R a out ↔ EquivB out a :=
  ⟨fun f => (normal_reduces_equiv f.1 n).symm,fun e => ⟨.basis e.symm,(normal_equiv _ e).mpr n,fun _ => typed_equiv e.symm⟩⟩

private theorem basis_input {R : Root sig} {a b out : Term sig} (e : EquivB a b) (nf : NormalForm R a out) :
    NormalForm R b out := ⟨(Reduces.basis e.symm).trans nf.1,nf.2.1,fun _ h => nf.2.2 _ (typed_equiv e.symm h)⟩

theorem Inventory.point_results [DecidableEq sig.ACSym] {E : ExtraTable T} (I : Inventory s β T.rules)
    (group : Balance.Inventory E) (unit : Normal (ruleRoot T.rules) s.product.one) {a p out : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg) (na : Normal (ruleRoot T.rules) a) (np : Normal (ruleRoot T.rules) p) :
    NormalForm (ruleRoot T.rules) (β.point a p) out ↔ PointResult s β (ruleRoot T.rules) a p out := by
  constructor
  · intro nf
    by_cases u : head a = .free s.one
    · obtain rfl : a = s.product.one := nullary s.oneArity u
      exact .unit rfl ((I.point_one group sp np unit).mp nf)
    by_cases point : head p = .free β.pmult
    · obtain ⟨b,q,rfl⟩ := β.split point
      obtain ⟨sb,sq⟩ := β.point_types sp
      obtain ⟨m,prod,value⟩ := (I.point_lift sa sb sq na np u unit).mp nf
      exact .nested u rfl prod value
    · exact .plain u point ((already ((I.point_normal_iff sa sp).mpr ⟨na,np,u,point⟩)).mp nf)
  · intro result
    cases result with
    | unit e value => subst a; exact (I.point_one group sp np unit).mpr value
    | plain u point value => exact (already ((I.point_normal_iff sa sp).mpr ⟨na,np,u,point⟩)).mpr value
    | nested u e prod value =>
      subst p; obtain ⟨sb,sq⟩ := β.point_types sp
      exact (I.point_lift sa sb sq na np u unit).mpr ⟨_,prod,value⟩

private theorem map_right (I : Inventory s β T.rules) (pow : PowerBucket T) {p b q out : Term sig}
    (sp : HasSort p .msg) (sb : HasSort b .msg) (sq : HasSort q .msg)
    (np : Normal (ruleRoot T.rules) p) (rhs : Normal (ruleRoot T.rules) (β.point b q)) (plain : head p ≠ .free β.pmult) :
    NormalForm (ruleRoot T.rules) (β.map p (β.point b q)) out ↔ EquivB out (s.power (β.map p q) b) :=
  ⟨fun nf => ((I.map_single pow sb sq sp rhs np plain).mp (basis_input (.comm_swap ..) nf)).trans
    (pow_congr (.comm_swap ..) (.refl _)),
   fun e => basis_input (.comm_swap ..) ((I.map_single pow sb sq sp rhs np plain).mpr
    (e.trans (pow_congr (.comm_swap ..) (.refl _))))⟩

theorem Inventory.map_results (I : Inventory s β T.rules) (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one) {p q out : Term sig}
    (sp : HasSort p .msg) (sq : HasSort q .msg) (np : Normal (ruleRoot T.rules) p) (nq : Normal (ruleRoot T.rules) q) :
    NormalForm (ruleRoot T.rules) (β.map p q) out ↔ MapResult s β (ruleRoot T.rules) p q out := by
  constructor
  · intro nf
    by_cases l : head p = .free β.pmult
    · obtain ⟨a,v,rfl⟩ := β.split l
      obtain ⟨sa,sv⟩ := β.point_types sp
      by_cases r : head q = .free β.pmult
      · obtain ⟨b,w,rfl⟩ := β.split r
        obtain ⟨sb,sw⟩ := β.point_types sq
        obtain ⟨m,prod,value⟩ := (I.map_lift pow sa sb sv sw np nq unit).mp nf
        exact .both rfl rfl prod value
      · exact .left rfl r ((I.map_single pow sa sv sq np nq r).mp nf)
    · by_cases r : head q = .free β.pmult
      · obtain ⟨b,w,rfl⟩ := β.split r
        obtain ⟨sb,sw⟩ := β.point_types sq
        exact .right rfl l ((map_right I pow sp sb sw np nq l).mp nf)
      · exact .plain l r ((already ((I.map_normal_iff sp sq).mpr ⟨np,nq,l,r⟩)).mp nf)
  · intro result
    cases result with
    | plain l r v => exact (already ((I.map_normal_iff sp sq).mpr ⟨np,nq,l,r⟩)).mpr v
    | left e r v => subst p; obtain ⟨sa,sw⟩ := β.point_types sp; exact (I.map_single pow sa sw sq np nq r).mpr v
    | right e l v => subst q; obtain ⟨sb,sw⟩ := β.point_types sq; exact (map_right I pow sp sb sw np nq l).mpr v
    | both l r prod v =>
      subst p; subst q; obtain ⟨sa,sv⟩ := β.point_types sp; obtain ⟨sb,sw⟩ := β.point_types sq
      exact (I.map_lift pow sa sb sv sw np nq unit).mpr ⟨_,prod,v⟩

end Tamarin.Rewriting.Bilinear
