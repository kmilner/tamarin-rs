import Tamarin.BilinearScalars

/-! Child-first scalar evaluation for a bilinear point action. A point
which was a variable in the query may itself be a normalized action. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T} {β : Operators sig}

private theorem point_red {R : Root sig} {a b p : Term sig} (r : Reduces R a b) :
    Reduces R (β.point a p) (β.point b p) := by
  apply Reduces.free; intro i; split <;> first | exact r | exact .basis (.refl _)

private theorem typed_b {a b : Term sig} (e : EquivB a b) {k} (h : HasSort a k) : HasSort b k :=
  Term.checkSort_sound _ _ ((SortClash.check_equiv e k) ▸ Term.checkSort_complete h)

private theorem mul_typed {a b : Term sig} (l : HasSort a .msg) (r : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ l) (s.mulSort ▸ r)

private theorem at_root {R : Root sig} {a b : Term sig} (h : R a b) : StepModulo R a b :=
  ⟨_,_,.refl _,.root h,.refl _⟩

/-- Extracting the inner point before any changes to the outer scalar
retains every normal endpoint, including the competing outer unit step. -/
theorem Inventory.extract_first (I : Inventory s β T.rules) (E : ExtraTable T) {a b p out : Term sig}
    (sa : HasSort a .msg) (sb : HasSort b .msg) (sp : HasSort p .msg)
    (np : Normal (ruleRoot T.rules) (β.point b p)) :
    NormalForm (ruleRoot T.rules) (β.point a (β.point b p)) out ↔
      NormalForm (ruleRoot T.rules) (β.point (s.product.mul a b) p) out := by
  have fire := at_root (I.nested sa sb sp)
  have sourceType := β.point_sorted sa (β.point_sorted sb sp)
  have targetType := β.point_sorted (mul_typed (s := s) sa sb) sp
  constructor
  · intro nf
    let P (u : Term sig) := (∃ t, Reduces (ruleRoot T.rules) a t ∧ EquivB (β.point t (β.point b p)) u) ∨
      Reduces (ruleRoot T.rules) (β.point (s.product.mul a b) p) u
    have ready {t} (r : Reduces (ruleRoot T.rules) a t) :
        Reduces (ruleRoot T.rules) (β.point (s.product.mul a b) p) (β.point (s.product.mul t b) p) :=
      point_red (.ac _ r (.basis (.refl _)))
    have endState : P out := RootNarrowing.reduction_invariant P (fun h e => by
      rcases h with ⟨t,r,f⟩|r
      · exact .inl ⟨t,r,f.trans e⟩
      · exact .inr (r.trans (.basis e))) (fun h st => by
      rcases h with ⟨t,r,eq⟩|r
      · obtain ⟨x,y,pre,raw,post⟩ := st
        rcases β.steps ⟨x,y,eq.trans pre,raw,post⟩ with ⟨u,v,e,hh,f⟩|⟨c,hit,v⟩|⟨c,hit,v⟩
        · cases I.point_root e hh with
          | one unit align =>
            obtain rfl : t = s.product.one := nullary s.oneArity unit
            have ustep : StepModulo (ruleRoot T.rules) (s.product.mul s.product.one b) b :=
              ⟨_,_,.ac_swap ..,.root (E.presentation.unitRule b sb),.refl _⟩
            exact .inr (((ready r).trans (point_red (.step ustep))).trans (.basis (align.symm.trans f)))
          | nested eq result =>
            obtain ⟨l,k⟩ := β.point_equiv eq
            exact .inr ((ready r).trans (.basis ((β.point_congr (.ac_congr _ (.refl _) l) k).trans (result.symm.trans f))))
        · exact .inl ⟨c,r.trans (.step hit),v⟩
        · exact (np c hit).elim
      · exact .inr (r.trans (.step st))) nf.1 (.inl ⟨a,.basis (.refl _),.refl _⟩)
    rcases endState with ⟨t,_,eq⟩|red
    · have tt := (β.point_types (typed_b eq.symm (nf.2.2 _ sourceType))).1
      exact ((normal_equiv _ eq).mpr nf.2.1 _ (at_root (I.nested tt sb sp))).elim
    · exact ⟨red,nf.2.1,fun _ h => .widen (nf.2.2 _ sourceType) (β.pointSort ▸ Term.rootSort_le h)⟩
  · intro nf
    exact ⟨(Reduces.step fire).trans nf.1,nf.2.1,
      fun _ h => .widen (nf.2.2 _ targetType) (β.pointSort ▸ Term.rootSort_le h)⟩

/-- A scalar may be reduced inside an action on a plain point whenever its
typed normal endpoints are preserved by that reduction. -/
private theorem plain_stage (I : Inventory s β T.rules) {a v p out : Term sig}
    (sa : HasSort a .msg) (sv : HasSort v .msg) (sp : HasSort p .msg)
    (np : Normal (ruleRoot T.rules) p) (plain : head p ≠ .free β.pmult)
    (unit : Normal (ruleRoot T.rules) s.product.one) (r : Reduces (ruleRoot T.rules) a v)
    (preserve : ∀ m, HasSort m .msg → Normal (ruleRoot T.rules) m →
      Reduces (ruleRoot T.rules) a m → Reduces (ruleRoot T.rules) v m) :
    NormalForm (ruleRoot T.rules) (β.point a p) out ↔ NormalForm (ruleRoot T.rules) (β.point v p) out := by
  have sourceType := β.point_sorted sa sp
  have targetType := β.point_sorted sv sp
  constructor
  · intro nf
    refine ⟨?_,nf.2.1,fun _ h => .widen (nf.2.2 _ sourceType) (β.pointSort ▸ Term.rootSort_le h)⟩
    rcases fixed_point I np plain nf.1 with ⟨m,rm,eq⟩|⟨rm,eq⟩
    · have tm := (β.point_types (typed_b eq.symm (nf.2.2 _ sourceType))).1
      have nm := ((I.point_normal_iff tm sp).mp ((normal_equiv _ eq).mpr nf.2.1)).1
      exact (point_red (preserve m tm nm rm)).trans (.basis eq)
    · have typed : HasSort s.product.one .msg := by
        rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
      exact ((point_red (preserve _ typed unit rm)).trans (.step (at_root (I.one sp)))).trans (.basis eq)
  · intro nf
    exact ⟨(point_red r).trans nf.1,nf.2.1,fun _ h => .widen (nf.2.2 _ targetType) (β.pointSort ▸ Term.rootSort_le h)⟩

/-- Normalizing a signed scalar first preserves every possible point action
result on a normalized point, for any normalized substitution of the query. -/
theorem Inventory.point_scalar_stage [DecidableEq sig.ACSym] (I : Inventory s β T.rules)
    (group : Balance.Inventory E) {a v p out : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg) (np : Normal (ruleRoot T.rules) p)
    (unit : Normal (ruleRoot T.rules) s.product.one) (domain : Staging.Signed s (ruleRoot T.rules) a)
    (nf : NormalForm (ruleRoot T.rules) a v) :
    NormalForm (ruleRoot T.rules) (β.point a p) out ↔ NormalForm (ruleRoot T.rules) (β.point v p) out := by
  have sv := nf.2.2 _ sa
  by_cases nested : head p = .free β.pmult
  · obtain ⟨b,q,rfl⟩ := β.split nested
    obtain ⟨sb,sq⟩ := β.point_types sp
    obtain ⟨nb,nq,_,plain⟩ := (I.point_normal_iff sb sq).mp np
    rw [I.extract_first E sa sb sq np,I.extract_first E sv sb sq np]
    apply plain_stage I (mul_typed sa sb) (mul_typed sv sb) sq nq plain unit (.ac _ nf.1 (.basis (.refl _)))
    intro m sm nm rm
    have stable : NormalForm (ruleRoot T.rules) b b := ⟨.basis (.refl _),nb,fun _ h => h⟩
    exact ((Staging.mul_stage group sa sb domain (fun k => Balance.defined s _ k nb) nf stable).mp
      ⟨rm,nm,fun _ h => .widen sm (s.mulSort ▸ Term.rootSort_le h)⟩).1
  · apply plain_stage I sa sv sp np nested unit nf.1
    intro m sm nm rm
    exact .basis (Balance.normal_unique group E.presentation (fun _ => Balance.plain_of_inverse E) domain
      sv sm nf.2.1 nm nf.1 rm)

/-- A signed argument which exposes a point action is already normal:
the whole point is an opaque factor for the signed product. -/
theorem signed_point_normal (β : Operators sig) {R : Root sig} {t : Term sig}
    (domain : Staging.Signed s R t) (point : head t = .free β.pmult) : Normal R t := by
  obtain ⟨z,h⟩ := domain (classOf s.product.one)
  have different {f : sig.FreeSym} (arity : sig.arity f ≠ 2) : head t ≠ .free f := by
    intro same
    have eq := Head.free.inj (point.symm.trans same)
    exact arity (eq ▸ β.arity)
  rw [Balance.read_alien s _ _ _ (by rw [point]; intro h; cases h)
    (different (by rw [s.invArity]; decide)) (different (by rw [s.oneArity]; decide))] at h
  apply Classical.byContradiction
  intro nn
  simp [Balance.alien,nn] at h

/-- A signed point argument may be normalized before any scalar or action
step. Encountering a nested point already fixes that argument, while unit
elimination can expose it before it has finished normalizing. -/
theorem Inventory.point_argument_stage [DecidableEq sig.ACSym] (I : Inventory s β T.rules)
    (group : Balance.Inventory E) {a p q out : Term sig}
    (sa : HasSort a .msg) (sp : HasSort p .msg)
    (domain : Staging.Signed s (ruleRoot T.rules) p) (nf : NormalForm (ruleRoot T.rules) p q) :
    NormalForm (ruleRoot T.rules) (β.point a p) out ↔ NormalForm (ruleRoot T.rules) (β.point a q) out := by
  have sq := nf.2.2 _ sp
  have sourceType := β.point_sorted sa sp
  have targetType := β.point_sorted sa sq
  have same {t} (rt : Reduces (ruleRoot T.rules) p t) (nt : Normal (ruleRoot T.rules) t) : EquivB q t :=
    Balance.normal_unique group E.presentation (fun _ => Balance.plain_of_inverse E) domain
      sq (group.reduces_sorted sp (domain _) rt) nf.2.1 nt nf.1 rt
  constructor
  · intro form
    let P (u : Term sig) :=
      (∃ a' t, Reduces (ruleRoot T.rules) a a' ∧ Reduces (ruleRoot T.rules) p t ∧ EquivB (β.point a' t) u) ∨
      (Reduces (ruleRoot T.rules) a s.product.one ∧ Reduces (ruleRoot T.rules) p u) ∨
      Reduces (ruleRoot T.rules) (β.point a q) u
    have endpoints : P out := RootNarrowing.reduction_invariant P (fun h eq => by
      rcases h with ⟨a',t,ra,rt,f⟩|⟨ru,rt⟩|r
      · exact .inl ⟨a',t,ra,rt,f.trans eq⟩
      · exact .inr (.inl ⟨ru,rt.trans (.basis eq)⟩)
      · exact .inr (.inr (r.trans (.basis eq)))) (fun h st => by
      rcases h with ⟨a',t,ra,rt,e⟩|⟨ru,rt⟩|r
      · obtain ⟨x,y,pre,raw,post⟩ := st
        rcases β.steps ⟨x,y,e.trans pre,raw,post⟩ with ⟨u,v,align,hit,after⟩|⟨b,step,eq⟩|⟨b,step,eq⟩
        · cases I.point_root align hit with
          | one unit result =>
            obtain rfl : a' = s.product.one := nullary s.oneArity unit
            exact .inr (.inl ⟨ra,rt.trans (.basis (result.symm.trans after))⟩)
          | nested point _ =>
            have defined : Staging.Signed s (ruleRoot T.rules) t :=
              fun k => let ⟨z,rd⟩ := domain k; ⟨z,group.reduces k rt z rd⟩
            have eq := same rt (signed_point_normal β defined point.head_eq)
            exact .inr (.inr ((point_red ra).trans (.step
              ⟨u,v,(β.point_congr (.refl _) eq).trans align,.root hit,after⟩)))
        · exact .inl ⟨b,t,ra.trans (.step step),rt,eq⟩
        · exact .inl ⟨a',b,ra,rt.trans (.step step),eq⟩
      · exact .inr (.inl ⟨ru,rt.trans (.step st)⟩)
      · exact .inr (.inr (r.trans (.step st)))) form.1 (.inl ⟨a,p,.basis (.refl _),.basis (.refl _),.refl _⟩)
    refine ⟨?_,form.2.1,fun _ h => .widen (form.2.2 _ sourceType) (β.pointSort ▸ Term.rootSort_le h)⟩
    rcases endpoints with ⟨a',t,ra,rt,eq⟩|⟨ru,rt⟩|r
    · obtain ⟨ta,tt⟩ := β.point_types (typed_b eq.symm (form.2.2 _ sourceType))
      obtain ⟨_,nt,_,_⟩ := (I.point_normal_iff ta tt).mp ((normal_equiv _ eq).mpr form.2.1)
      exact (point_red ra).trans (.basis ((β.point_congr (.refl _) (same rt nt)).trans eq))
    · exact ((point_red ru).trans (.step (at_root (I.one sq)))).trans (.basis (same rt form.2.1))
    · exact r
  · intro form
    have replay : Reduces (ruleRoot T.rules) (β.point a p) (β.point a q) := by
      apply Reduces.free; intro i; split <;> first | exact .basis (.refl _) | exact nf.1
    exact ⟨replay.trans form.1,form.2.1,fun _ h => .widen (form.2.2 _ targetType) (β.pointSort ▸ Term.rootSort_le h)⟩

end Tamarin.Rewriting.Bilinear
