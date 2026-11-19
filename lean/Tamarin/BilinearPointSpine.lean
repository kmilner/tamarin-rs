import Tamarin.BilinearPointStaging

/-! An arbitrarily nested sequence of point actions has one underlying
plain point and one signed scalar multiplicity at every factor class. -/
namespace Tamarin.Rewriting.Bilinear.PointSpine
open ConstructorVariants DHPeer Cancellation
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {T : Table s} {E : ExtraTable T}
variable {R : Root sig} {k : Class sig} {p : Term sig}

def spine (β : Operators sig) (x : Term sig) (es : List (Term sig)) : Term sig :=
  es.foldl (fun p a => β.point a p) x

inductive Trace (s : Symbols sig) (β : Operators sig) (R : Root sig) (k : Class sig) (p : Term sig) : Term sig → Int → Prop where
  | bare {t} (shape : EquivB p t) (norm : Normal R p) (plain : head p ≠ .free β.pmult) : Trace s β R k p t 0
  | action {a q t i j} (shape : EquivB (β.point a q) t) (inner : Trace s β R k p q i)
      (typed : HasSort a .msg) (signed : Staging.Signed s R a) (count : Balance.read s R k a = some j) :
      Trace s β R k p t (i+j)
  | delayed {v t z} (value : Trace s β R k p v z) (normal : Normal R v) (typed : HasSort t .msg)
      (signed : Staging.Signed s R t) (settles : ∀ {u}, Reduces R t u → Normal R u → EquivB v u) :
      Trace s β R k p t z

private theorem type_b {t u : Term sig} (eq : EquivB t u) (ty : HasSort t .msg) : HasSort u .msg :=
  Term.checkSort_sound _ _ ((SortClash.check_equiv eq _) ▸ Term.checkSort_complete ty)

theorem Trace.rebase {t u z} (h : Trace s β R k p t z) (eq : EquivB t u) : Trace s β R k p u z := by
  cases h with
  | bare e n hp => exact .bare (e.trans eq) n hp
  | action e h ty rd cnt => exact .action (e.trans eq) h ty rd cnt

  | delayed h n ty d fixed =>
    exact .delayed h n (type_b eq ty)
      (fun k => let ⟨z,r⟩ := d k; ⟨z,(Balance.equiv s R k eq).symm.trans r⟩)
      (fun r nt => fixed ((Reduces.basis eq).trans r) nt)

theorem Trace.typed {t z} (h : Trace s β R k p t z) (sp : HasSort p .msg) : HasSort t .msg := by
  induction h with
  | bare eq => exact type_b eq sp
  | action eq h st _ _ ih => exact type_b eq (β.point_sorted st ih)
  | delayed _ _ st => exact st

private theorem Trace.split_action {t z a q} (h : Trace s β R k p t z) (eq : EquivB t (β.point a q)) :
    ∃ i j, Trace s β R k p q i ∧ HasSort a .msg ∧ Staging.Signed s R a ∧ Balance.read s R k a = some j ∧ z = i+j := by
  induction h with
  | bare e _ plain => exact (plain (e.trans eq).head_eq).elim
  | action e h ty rd cnt _ =>
    obtain ⟨l,r⟩ := β.point_equiv (e.trans eq)
    exact ⟨_,_,h.rebase r,type_b l ty,
      fun k => let ⟨z,h⟩ := rd k; ⟨z,(Balance.equiv s R k l).symm.trans h⟩,
      (Balance.equiv s R k l).symm.trans cnt,rfl⟩

  | delayed _ _ _ rd settles ih =>
    have e := settles (.basis (.refl _)) (signed_point_normal β rd eq.head_eq)
    exact ih (e.trans eq)

theorem Trace.parts {t z a q} (h : Trace s β R k p t z) (eq : EquivB t (β.point a q)) :
    ∃ i j, Trace s β R k p q i ∧ Balance.read s R k a = some j ∧ z = i+j := by
  obtain ⟨i,j,h,_,_,r,e⟩ := h.split_action eq; exact ⟨i,j,h,r,e⟩

theorem Trace.unscaled {t z} (h : Trace s β R k p t z) (nt : Normal R t) (plain : head t ≠ .free β.pmult) :
    EquivB t p ∧ z = 0 := by
  induction h with
  | bare e => exact ⟨e.symm,rfl⟩
  | action e => exact (plain e.head_eq.symm).elim

  | delayed _ nv _ _ settles ih =>
    have f := settles (.basis (.refl _)) nt
    obtain ⟨e,z⟩ := ih nv (fun h => plain (f.head_eq.symm.trans h))
    exact ⟨f.symm.trans e,z⟩

theorem Trace.step (I : Inventory s β T.rules) (g : Balance.Inventory E) {t u z}
    (h : Trace s β (ruleRoot T.rules) k p t z) (st : StepModulo (ruleRoot T.rules) t u) :
    Trace s β (ruleRoot T.rules) k p u z := by
  induction h generalizing u with
  | bare e n _ => exact ((normal_equiv _ e).mp n _ st).elim
  | @action a q t i j e h ty rd cnt ih =>
    obtain ⟨x,y,l,raw,r⟩ := st
    rcases β.steps ⟨x,y,e.trans l,raw,r⟩ with ⟨u,v,before,hit,after⟩|⟨b,st,res⟩|⟨b,st,res⟩
    · cases I.point_root before hit with
      | one unit result =>
        obtain rfl : a = s.product.one := nullary s.oneArity unit
        rw [Balance.read_one] at cnt; obtain rfl := Option.some.inj cnt
        simpa using h.rebase (result.symm.trans after)
      | @nested b q' eq result =>
        obtain ⟨m,n,base,sb,db,count,rfl⟩ := h.split_action eq
        have product : Balance.read s (ruleRoot T.rules) k (s.product.mul a b) = some (j+n) := by
          rw [Balance.read_mul,cnt,count]; rfl
        have sorted := s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ ty) (s.mulSort ▸ sb)
        have next := Trace.action (result.symm.trans after) base sorted (Staging.signed_mul rd db) product
        simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using next
    · exact .action res h (g.reduces_sorted ty (rd _) (.step st))
        (fun k => let ⟨z,h⟩ := rd k; ⟨z,g.reduces k (.step st) z h⟩) (g.reduces k (.step st) j cnt)
    · exact .action res (ih st) ty rd cnt

  | delayed h n ty rd fixed _ =>
    exact .delayed h n (g.reduces_sorted ty (rd _) (.step st))
      (fun k => let ⟨z,r⟩ := rd k; ⟨z,g.reduces k (.step st) z r⟩)
      (fun r nt => fixed ((Reduces.step st).trans r) nt)

private theorem Trace.fold {b : Term sig} (base : ∃ z, Trace s β R k p b z) (es : List (Term sig))
    (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s R e) :
    ∃ z, Trace s β R k p (spine β b es) z := by
  induction es generalizing b with
  | nil => exact base
  | cons e rest ih =>
    obtain ⟨i,h⟩ := base
    obtain ⟨j,r⟩ := rd e List.mem_cons_self k
    exact ih ⟨i+j,.action (.refl _) h (se _ List.mem_cons_self) (rd _ List.mem_cons_self) r⟩
      (fun t mem => se t (List.mem_cons_of_mem _ mem)) (fun t mem => rd t (List.mem_cons_of_mem _ mem))

theorem view (I : Inventory s β T.rules) {x : Term sig} (sx : HasSort x .msg) (nx : Normal (ruleRoot T.rules) x)
    (es : List (Term sig)) (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e) :
    ∃ p, HasSort p .msg ∧ Normal (ruleRoot T.rules) p ∧ head p ≠ .free β.pmult ∧
      ∀ k, ∃ z, Trace s β (ruleRoot T.rules) k p (spine β x es) z := by
  by_cases point : head x = .free β.pmult
  · obtain ⟨a,p,rfl⟩ := β.split point
    obtain ⟨sa,sp⟩ := β.point_types sx
    obtain ⟨na,np,_,hp⟩ := (I.point_normal_iff sa sp).mp nx
    refine ⟨p,sp,np,hp,fun k => ?_⟩
    obtain ⟨j,h⟩ := Balance.defined s _ k na
    exact Trace.fold ⟨0+j,.action (.refl _) (.bare (.refl _) np hp) sa (fun k => Balance.defined s _ k na) h⟩ es se rd
  · exact ⟨x,sx,nx,point,fun _ => Trace.fold ⟨0,.bare (.refl _) nx point⟩ es se rd⟩


/-- A signed expression used as the underlying point may expose an action
after reduction. Every normal result of that expression gives the same
point view, even when an outer action or map has already started reducing. -/
theorem signed_view [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (g : Balance.Inventory E) {x : Term sig}
    (sx : HasSort x .msg) (dx : Staging.Signed s (ruleRoot T.rules) x) (es : List (Term sig))
    (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e) :
    ∃ p, HasSort p .msg ∧ Normal (ruleRoot T.rules) p ∧ head p ≠ .free β.pmult ∧
      ∀ k, ∃ z, Trace s β (ruleRoot T.rules) k p (spine β x es) z := by
  obtain ⟨v,red,nv,sv⟩ := g.normal_exists sx (dx _)
  obtain ⟨p,sp,np,hp,cases⟩ := view I sv nv [] (by simp) (by simp)
  refine ⟨p,sp,np,hp,fun k => ?_⟩
  obtain ⟨z,h⟩ := cases k
  apply Trace.fold (b := x) _ es se rd
  exact ⟨z,.delayed (v := v) h nv sx dx (fun r n =>
    Balance.normal_unique g E.presentation (fun _ => Balance.plain_of_inverse E) dx sv
      (g.reduces_sorted sx (dx _) r) nv n red r)⟩

private inductive Form (s : Symbols sig) (β : Operators sig) : Term sig → Term sig → Term sig → Prop where
  | plain {p : Term sig} : Form s β p s.product.one p
  | acted {a p : Term sig} (nonunit : head a ≠ .free s.one) : Form s β (β.point a p) a p

private theorem unit_typed (s : Symbols sig) : HasSort s.product.one .msg := by
  rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)

private theorem normal_view (I : Inventory s β T.rules) (unit : Normal (ruleRoot T.rules) s.product.one)
    {t : Term sig} (st : HasSort t .msg) (nt : Normal (ruleRoot T.rules) t) :
    ∃ a q, HasSort a .msg ∧ Normal (ruleRoot T.rules) a ∧ Form s β t a q ∧
      ∀ k p z, Trace s β (ruleRoot T.rules) k p t z → EquivB q p ∧ Balance.read s (ruleRoot T.rules) k a = some z := by
  by_cases scaled : head t = .free β.pmult
  · obtain ⟨a,q,rfl⟩ := β.split scaled
    obtain ⟨sa,sq⟩ := β.point_types st
    obtain ⟨na,nq,au,plain⟩ := (I.point_normal_iff sa sq).mp nt
    refine ⟨a,q,sa,na,.acted au,fun k p z h => ?_⟩
    obtain ⟨i,j,base,cnt,rfl⟩ := h.parts (.refl _)
    obtain ⟨e,rfl⟩ := base.unscaled nq plain
    exact ⟨e,by simpa using cnt⟩
  · refine ⟨s.product.one,t,unit_typed s,unit,.plain,fun k p z h => ?_⟩
    obtain ⟨eq,rfl⟩ := h.unscaled nt scaled
    exact ⟨eq,Balance.read_one ..⟩

private theorem Trace.path (I : Inventory s β T.rules) (g : Balance.Inventory E) {a t z}
    (h : Trace s β (ruleRoot T.rules) k p a z) (red : Reduces (ruleRoot T.rules) a t) :
    Trace s β (ruleRoot T.rules) k p t z :=
  RootNarrowing.reduction_invariant _ Trace.rebase (Trace.step I g) red h

/-- Normal traces with the same underlying point and all the same signed
counts have equivalent value, whether or not the scalar folds to one. -/
theorem unique [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (g : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {t x y p : Term sig} (st : HasSort t .msg)
    (initial : ∀ k, ∃ z, Trace s β (ruleRoot T.rules) k p t z)
    (l : NormalForm (ruleRoot T.rules) t x) (r : NormalForm (ruleRoot T.rules) t y) : EquivB x y := by
  obtain ⟨a,q,sa,na,fx,left⟩ := normal_view I unit (l.2.2 _ st) l.2.1
  obtain ⟨b,v,sb,nb,fy,right⟩ := normal_view I unit (r.2.2 _ st) r.2.1
  have same (k) : EquivB q v ∧ Balance.read s (ruleRoot T.rules) k a = Balance.read s (ruleRoot T.rules) k b := by
    obtain ⟨z,tr⟩ := initial k
    obtain ⟨eq,za⟩ := left k p z (tr.path I g l.1)
    obtain ⟨f,zb⟩ := right k p z (tr.path I g r.1)
    exact ⟨eq.trans f.symm,za.trans zb.symm⟩
  obtain ⟨_,_,ca⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) sa na
  obtain ⟨_,_,cb⟩ := Balance.decompose E.presentation (fun _ => Balance.plain_of_inverse E) sb nb
  have scalars := ca.injective cb (fun k => (same k).2)
  have points := (same (classOf p)).1
  cases fx with
  | plain => cases fy with
    | plain => exact points
    | acted hb => exact (hb scalars.head_eq.symm).elim
  | acted ha => cases fy with
    | plain => exact (ha scalars.head_eq).elim
    | acted _ => exact β.point_congr scalars points

theorem point_exists [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (g : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {a p : Term sig} (sa : HasSort a .msg) (sp : HasSort p .msg)
    (na : Normal (ruleRoot T.rules) a) (np : Normal (ruleRoot T.rules) p) :
    ∃ v, NormalForm (ruleRoot T.rules) (β.point a p) v := by
  by_cases one : head a = .free s.one
  · obtain rfl : a = s.product.one := nullary s.oneArity one
    exact ⟨p,(I.point_one g sp np unit).mpr (.refl _)⟩
  by_cases nested : head p = .free β.pmult
  · obtain ⟨b,q,rfl⟩ := β.split nested
    obtain ⟨sb,sq⟩ := β.point_types sp
    have nb := ((I.point_normal_iff sb sq).mp np).1
    have domain := Staging.signed_mul (fun k => Balance.defined s _ k na) (fun k => Balance.defined s _ k nb)
    have typeP := s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ sa) (s.mulSort ▸ sb)
    obtain ⟨m,r,n,sm⟩ := g.normal_exists typeP (domain _)
    have prod : NormalForm (ruleRoot T.rules) (s.product.mul a b) m :=
      ⟨r,n,fun _ h => .widen sm (s.mulSort ▸ Term.rootSort_le h)⟩
    have lift := fun out => (I.point_lift (out := out) sa sb sq na np one unit).mpr
    by_cases cancel : head m = .free s.one
    · exact ⟨q,lift _ ⟨m,prod,.inl ⟨nullary s.oneArity cancel,.refl _⟩⟩⟩
    · exact ⟨β.point m q,lift _ ⟨m,prod,.inr ⟨cancel,.refl _⟩⟩⟩
  · exact ⟨_,.basis (.refl _),(I.point_normal_iff sa sp).mpr ⟨na,np,one,nested⟩,fun _ h => h⟩

/-- A point-spine child can be normalized before applying the next signed
scalar, even when two adjacent actions could have merged earlier. -/
theorem stage_signed [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (g : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {a x v p out : Term sig}
    (sa : HasSort a .msg) (da : Staging.Signed s (ruleRoot T.rules) a)
    (sx : HasSort x .msg) (dx : Staging.Signed s (ruleRoot T.rules) x) (es : List (Term sig))
    (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e)
    (scalar : NormalForm (ruleRoot T.rules) a v) (point : NormalForm (ruleRoot T.rules) (spine β x es) p) :
    NormalForm (ruleRoot T.rules) (β.point a (spine β x es)) out ↔ NormalForm (ruleRoot T.rules) (β.point v p) out := by
  obtain ⟨base,sb,_,_,init⟩ := signed_view I g sx dx es se rd
  obtain ⟨_,tr⟩ := init (classOf base)
  have st := tr.typed sb
  have sv := scalar.2.2 _ sa
  have sp := point.2.2 _ st
  have source := β.point_sorted sa st
  have dest := β.point_sorted sv sp
  have red : Reduces (ruleRoot T.rules) (β.point a (spine β x es)) (β.point v p) := by
    apply Reduces.free; intro i; split <;> first | exact point.1 | exact scalar.1
  have replay {v} (nf : NormalForm (ruleRoot T.rules) (β.point _ p) v) :
      NormalForm (ruleRoot T.rules) (β.point a (spine β x es)) v :=
    ⟨red.trans nf.1,nf.2.1,fun _ h => .widen (nf.2.2 _ dest) (β.pointSort ▸ Term.rootSort_le h)⟩
  constructor
  · intro nf
    obtain ⟨b,nb⟩ := point_exists I g unit sv sp scalar.2.1 point.2.1
    have eq := unique I g unit source (p := base) (fun k => by
      obtain ⟨i,h⟩ := init k
      obtain ⟨j,c⟩ := da k
      exact ⟨i+j,.action (.refl _) h sa da c⟩) (replay nb) nf
    exact ⟨nb.1.trans (.basis eq),nf.2.1,fun _ h => .widen (nf.2.2 _ source) (β.pointSort ▸ Term.rootSort_le h)⟩
  · exact replay

/-- A stable normal point is also an admissible signed base. -/
theorem stage [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (g : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {a x v p out : Term sig}
    (sa : HasSort a .msg) (da : Staging.Signed s (ruleRoot T.rules) a)
    (sx : HasSort x .msg) (nx : Normal (ruleRoot T.rules) x) (es : List (Term sig))
    (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e)
    (scalar : NormalForm (ruleRoot T.rules) a v) (point : NormalForm (ruleRoot T.rules) (spine β x es) p) :
    NormalForm (ruleRoot T.rules) (β.point a (spine β x es)) out ↔ NormalForm (ruleRoot T.rules) (β.point v p) out :=
  stage_signed I g unit sa da sx (fun k => Balance.defined s _ k nx) es se rd scalar point

end Tamarin.Rewriting.Bilinear.PointSpine
