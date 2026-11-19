import Tamarin.BilinearPointSpine

/-! A power spine can race with extraction of either scalar from its
bilinear-map base. Track the plain underlying pairing and the total signed
multiplicity of each scalar factor through every one of these reductions. -/
namespace Tamarin.Rewriting.Bilinear.PowerSpine
open DHPeer ConstructorVariants Cancellation DHTower
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {T : Table s} {E : ExtraTable T}
variable {R : Root sig} {k : Class sig} {p q : Term sig}

private inductive Track (s : Symbols sig) (β : Operators sig) (R : Root sig) (k : Class sig) (p q : Term sig) :
    Term sig → Int → Prop where
  | map {x y t i j} (shape : EquivB (β.map x y) t)
      (l : PointSpine.Trace s β R k p x i) (r : PointSpine.Trace s β R k q y j) :
      Track s β R k p q t (i+j)
  | power {b e t i j} (shape : EquivB (s.power b e) t) (base : Track s β R k p q b i)
      (exp : Balance.read s R k e = some j) : Track s β R k p q t (i+j)

private theorem Track.rebase {u v z} (h : Track s β R k p q u z) (eq : EquivB u v) : Track s β R k p q v z := by
  cases h with
  | map e l r => exact .map (e.trans eq) l r
  | power e b r => exact .power (e.trans eq) b r

private def powerOp (β : Operators sig) (s : Symbols sig) : Operators sig :=
  { β with pmult := s.pow, arity := s.powArity, inputs := s.powInput, pointSort := s.powSort }

private theorem Track.parts {u b e z} (h : Track s β R k p q u z) (eq : EquivB u (s.power b e)) :
    ∃ i j, Track s β R k p q b i ∧ Balance.read s R k e = some j ∧ z = i+j := by
  cases h with
  | map a => cases (a.trans eq).head_eq
  | power a h r =>
    obtain ⟨l,v⟩ := (powerOp β s).point_equiv (a.trans eq)
    exact ⟨_,_,h.rebase l,(Balance.equiv s R k v).symm.trans r,rfl⟩

private theorem change_source {u v w : Term sig} (eq : EquivB u v) (st : StepModulo R v w) : StepModulo R u w := by
  obtain ⟨a,b,l,h,r⟩ := st; exact ⟨a,b,eq.trans l,h,r⟩

private theorem Track.step (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    {u v : Term sig} {z : Int} (h : Track s β (ruleRoot T.rules) k p q u z)
    (st : StepModulo (ruleRoot T.rules) u v) : Track s β (ruleRoot T.rules) k p q v z := by
  induction h generalizing v with
  | @map x y t i j shape l r =>
    rcases (ContextualReduction.comm_iff ..).mp (change_source shape st) with
      ⟨_,_,before,hit,after⟩|⟨_,st,out⟩|⟨_,st,out⟩
    · cases I.map_root before hit with
      | left take dst =>
        obtain ⟨a,d,tr,read,rfl⟩ := l.parts take
        have more := Track.power (dst.symm.trans after) (Track.map (.refl _) tr r) read
        simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using more
      | right take dst =>
        obtain ⟨a,d,tr,read,rfl⟩ := r.parts take
        have more := Track.power (dst.symm.trans after) (Track.map (.refl _) l tr) read
        simpa [Int.add_assoc] using more
    · exact .map out (l.step I group st) r
    · exact .map out l (r.step I group st)
  | @power b e t i j shape base count ih =>
    rcases (powerOp β s).steps (change_source shape st) with ⟨_,_,before,hit,after⟩|⟨v,st,out⟩|⟨v,st,out⟩
    · cases pow.root _ _ before hit with
      | one he dst =>
        obtain rfl : e = s.product.one := nullary s.oneArity he
        rw [Balance.read_one] at count
        obtain rfl := Option.some.inj count
        simpa using base.rebase (dst.symm.trans after)
      | neutral he =>
        cases base with
        | map form => cases form.head_eq.trans he
        | power form =>
          have eq := Head.free.inj (form.head_eq.trans he)
          have ar := s.powArity; rw [eq,s.neutralArity] at ar; contradiction
      | tower tower dst =>
        obtain ⟨a,m,old,exp,rfl⟩ := base.parts tower
        have prod := show Balance.read s (ruleRoot T.rules) k (s.product.mul _ e) = some (m+j) by
          rw [Balance.read_mul,exp,count]; rfl
        simpa [Int.add_assoc] using Track.power (dst.symm.trans after) old prod
    · exact .power out (ih st) count
    · exact .power out base (group.reduces k (.step st) j count)

private theorem Track.normal_read (I : Inventory s β T.rules) (sp : HasSort p .msg) (sq : HasSort q .msg) {t z}
    (h : Track s β (ruleRoot T.rules) k p q t z) (nt : Normal (ruleRoot T.rules) t) :
    Spine.read s (ruleRoot T.rules) k t = some (classOf (β.map p q),z) := by
  induction h with
  | map shape l r =>
    have norm := (normal_equiv _ shape).mpr nt
    obtain ⟨nx,ny,plainX,plainY⟩ := (I.map_normal_iff (l.typed sp) (r.typed sq)).mp norm
    obtain ⟨hl,rfl⟩ := l.unscaled nx plainX
    obtain ⟨hr,rfl⟩ := r.unscaled ny plainY
    rw [← Spine.equiv s _ k shape,Spine.read_plain s _ k (by intro e; cases e) norm,
      show classOf _ = classOf (β.map p q) from Quotient.sound (.comm_congr _ hl hr)]
    rfl
  | @power b e t i j shape base exp ih =>
    have norm := (normal_equiv _ shape).mpr nt
    let zero : Fin (sig.arity s.pow) := ⟨0,by have := s.powArity; omega⟩
    have nb : Normal (ruleRoot T.rules) b := by simpa [zero] using normal_free_child _ _ norm zero
    rw [← Spine.equiv s _ k shape]
    apply Spine.read_extend (ih nb) _ exp
    intro clash; cases (Quotient.exact clash : EquivB _ _).head_eq

/-- Every class is read from the same underlying plain point. This point may
be reached via any number of bilinear actions. -/
def PointView (s : Symbols sig) (β : Operators sig) (R : Root sig) (t : Term sig) : Prop :=
  ∃ p, HasSort p .msg ∧ Normal R p ∧ head p ≠ .free β.pmult ∧
    ∀ k, ∃ z, PointSpine.Trace s β R k p t z

private theorem normal_view (I : Inventory s β T.rules) {x : Term sig}
    (sx : HasSort x .msg) (nx : Normal (ruleRoot T.rules) x) : PointView s β (ruleRoot T.rules) x :=
  PointSpine.view I sx nx [] (by simp) (by simp)

private theorem Track.fold {b : Term sig} (base : ∃ z, Track s β R k p q b z) (exps : List (Term sig))
    (rd : ∀ e ∈ exps, Staging.Signed s R e) : ∃ z, Track s β R k p q (exps.foldl s.power b) z := by
  induction exps generalizing b with
  | nil => exact base
  | cons e rest ih =>
    obtain ⟨i,bi⟩ := base
    obtain ⟨j,rj⟩ := rd e List.mem_cons_self k
    exact ih ⟨i+j,.power (.refl _) bi rj⟩ (fun e he => rd e (List.mem_cons_of_mem _ he))

private theorem fold_type {b : Term sig} (sb : HasSort b .msg) (exps : List (Term sig))
    (se : ∀ e ∈ exps, HasSort e .msg) : HasSort (exps.foldl s.power b) .msg := by
  induction exps generalizing b with
  | nil => exact sb
  | cons e rest ih => exact ih (powerSorted sb (se _ List.mem_cons_self)) (fun e he => se e (List.mem_cons_of_mem _ he))

private theorem fold_root {b : Term sig} (sb : b.rootSort = .msg) (exps : List (Term sig)) :
    (exps.foldl s.power b).rootSort = .msg := by
  induction exps generalizing b with
  | nil => exact sb
  | cons e rest ih => exact ih s.powSort

/-- Powers of a pairing have a unique normal result for any finite signed
exponent spine. Either operand of the map may first extract or reduce any
number of signed point actions. -/
theorem unique_viewed (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (vx : PointView s β (ruleRoot T.rules) x) (vy : PointView s β (ruleRoot T.rules) y)
    (exps : List (Term sig)) (se : ∀ e ∈ exps, HasSort e .msg) (rd : ∀ e ∈ exps, Staging.Signed s (ruleRoot T.rules) e)
    {u v} (nu : NormalForm (ruleRoot T.rules) (exps.foldl s.power (β.map x y)) u)
    (nv : NormalForm (ruleRoot T.rules) (exps.foldl s.power (β.map x y)) v) : EquivB u v := by
  obtain ⟨p,sp,np,hp,vl⟩ := vx
  obtain ⟨q,sq,nq,hq,vr⟩ := vy
  have t := fold_type (s := s) (β.map_sorted sx sy) exps se
  apply Spine.injective pow unit (nu.2.2 _ t) (nv.2.2 _ t) nu.2.1 nv.2.1 _ E
  intro k
  obtain ⟨i,li⟩ := vl k
  obtain ⟨j,rj⟩ := vr k
  obtain ⟨z,track⟩ := Track.fold ⟨i+j,Track.map (.refl _) li rj⟩ exps rd
  have endpoint {o} (form : NormalForm (ruleRoot T.rules) (exps.foldl s.power (β.map x y)) o) :=
    (RootNarrowing.reduction_invariant (fun b => Track s β (ruleRoot T.rules) k p q b z)
      (fun h e => h.rebase e) (fun h e => h.step I pow group e) form.1 track).normal_read I sp sq form.2.1
  exact (endpoint nu).trans (endpoint nv).symm

/-- Powers of a pairing have a unique normal result for any finite signed
exponent spine. Each normalized operand of the map can be an arbitrary
message, including an existing point action. -/
theorem unique (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (nx : Normal (ruleRoot T.rules) x) (ny : Normal (ruleRoot T.rules) y)
    (exps : List (Term sig)) (se : ∀ e ∈ exps, HasSort e .msg) (rd : ∀ e ∈ exps, Staging.Signed s (ruleRoot T.rules) e)
    {u v} (nu : NormalForm (ruleRoot T.rules) (exps.foldl s.power (β.map x y)) u)
    (nv : NormalForm (ruleRoot T.rules) (exps.foldl s.power (β.map x y)) v) : EquivB u v :=
  unique_viewed I pow group unit sx sy (normal_view I sx nx) (normal_view I sy ny) exps se rd nu nv

private theorem signed_form (group : Balance.Inventory E) {e : Term sig} (se : HasSort e .msg)
    (rd : Staging.Signed s (ruleRoot T.rules) e) : ∃ z, NormalForm (ruleRoot T.rules) e z := by
  by_cases n : Normal (ruleRoot T.rules) e
  · exact ⟨_,.basis (.refl _),n,fun _ h => h⟩
  have root : e.rootSort = .msg := by
    by_cases h : head e = .ac s.mul
    · cases e <;> cases h; exact s.mulSort
    by_cases h' : head e = .free s.inv
    · cases e <;> cases h'; exact s.invSort
    by_cases h'' : head e = .free s.one
    · cases e <;> cases h''; exact s.oneSort
    obtain ⟨z,hz⟩ := rd (classOf s.product.one)
    simp [Balance.read_alien s _ _ _ h h' h'',Balance.alien,n] at hz
  obtain ⟨o,red,nt,ty⟩ := group.normal_exists se (rd _)
  exact ⟨o,red,nt,fun _ h => .widen ty (root ▸ Term.rootSort_le h)⟩

/-- A map with normal arguments reaches a normal value. The two-action
case computes a single actual normal scalar product, including the unit. -/
theorem map_exists (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (nx : Normal (ruleRoot T.rules) x) (ny : Normal (ruleRoot T.rules) y) :
    ∃ b, NormalForm (ruleRoot T.rules) (β.map x y) b := by
  suffices ∃ b, MapResult s β (ruleRoot T.rules) x y b by
    obtain ⟨b,view⟩ := this
    exact ⟨b,(I.map_results pow unit sx sy nx ny).mpr view⟩
  by_cases l : head x = .free β.pmult
  · obtain ⟨a,p,rfl⟩ := β.split l
    by_cases r : head y = .free β.pmult
    · obtain ⟨b,q,rfl⟩ := β.split r
      obtain ⟨sa,sp⟩ := β.point_types sx
      obtain ⟨sb,sq⟩ := β.point_types sy
      have ds := Staging.signed_mul (fun k => Balance.defined s _ k ((I.point_normal_iff sa sp).mp nx).1)
        (fun k => Balance.defined s _ k ((I.point_normal_iff sb sq).mp ny).1)
      have ts : HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ sa) (s.mulSort ▸ sb)
      obtain ⟨m,nf⟩ := signed_form group ts ds
      by_cases u : head m = .free s.one
      · exact ⟨_,.both rfl rfl nf (.inl ⟨nullary s.oneArity u,.refl _⟩)⟩
      · exact ⟨_,.both rfl rfl nf (.inr ⟨u,.refl _⟩)⟩
    · exact ⟨_,.left rfl r (.refl _)⟩
  · by_cases r : head y = .free β.pmult
    · obtain ⟨b,q,rfl⟩ := β.split r
      exact ⟨_,.right rfl l (.refl _)⟩
    · exact ⟨_,.plain l r (.refl _)⟩

/-- The map may extract from either point spine before its operands finish
reducing. Normalizing both operands first preserves the entire normal-form
relation, with one arbitrary normalization choice for each operand. -/
theorem map_stage_viewed (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y a b out : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg)
    (vx : PointView s β (ruleRoot T.rules) x) (vy : PointView s β (ruleRoot T.rules) y)
    (l : NormalForm (ruleRoot T.rules) x a) (r : NormalForm (ruleRoot T.rules) y b) :
    NormalForm (ruleRoot T.rules) (β.map x y) out ↔ NormalForm (ruleRoot T.rules) (β.map a b) out := by
  have sa := l.2.2 _ sx
  have sb := r.2.2 _ sy
  have replay {u} (nf : NormalForm (ruleRoot T.rules) (β.map a b) u) :
      NormalForm (ruleRoot T.rules) (β.map x y) u :=
    ⟨(Reduces.comm _ l.1 r.1).trans nf.1,nf.2.1,fun _ h =>
      .widen (nf.2.2 _ (β.map_sorted sa sb)) (β.mapSort ▸ Term.rootSort_le h)⟩
  refine ⟨fun nf => ?_,replay⟩
  obtain ⟨v,both⟩ := map_exists I pow group unit sa sb l.2.1 r.2.1
  have eq := unique_viewed I pow group unit sx sy vx vy [] (by simp) (by simp) (replay both) nf
  exact ⟨both.1.trans (.basis eq),nf.2.1,fun k h =>
    Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete (both.2.2 k h))⟩

private theorem power_red {a b c d : Term sig} (l : Reduces R a b) (r : Reduces R c d) :
    Reduces R (s.power a c) (s.power b d) := by apply Reduces.free; intro i; split <;> assumption

private theorem fold_normal (group : Balance.Inventory E) (pow : PowerBucket T) {b : Term sig}
    (sb : HasSort b .msg) (nb : Normal (ruleRoot T.rules) b) (es : List (Term sig))
    (typed : ∀ e ∈ es, HasSort e .msg) (normal : ∀ e ∈ es, Normal (ruleRoot T.rules) e) :
    ∃ v, NormalForm (ruleRoot T.rules) (es.foldl s.power b) v := by
  cases es with
  | nil => exact ⟨_,.basis (.refl _),nb,fun _ h => h⟩
  | cons e es =>
    obtain ⟨u,nf⟩ := Staging.power_exists group pow sb (typed e List.mem_cons_self) nb (normal e List.mem_cons_self)
    have path := nf.1
    have sn := nf.2.2 _ (powerSorted sb (typed e List.mem_cons_self))
    have no := nf.2.1
    have run {src z : Term sig} (r : Reduces (ruleRoot T.rules) src z)
        (sz : HasSort z .msg) (nz : Normal (ruleRoot T.rules) z) (rest : List (Term sig))
        (ty : ∀ t ∈ rest, HasSort t .msg) (nn : ∀ t ∈ rest, Normal (ruleRoot T.rules) t) :
        ∃ v, Reduces (ruleRoot T.rules) (rest.foldl s.power src) v ∧
          Normal (ruleRoot T.rules) v ∧ HasSort v .msg := by
      induction rest generalizing src z with
      | nil => exact ⟨_,r,nz,sz⟩
      | cons t ts ih =>
        obtain ⟨u,f⟩ := Staging.power_exists group pow sz (ty t List.mem_cons_self) nz (nn t List.mem_cons_self)
        exact ih ((power_red r (.basis (.refl t))).trans f.1) (f.2.2 _ (powerSorted sz (ty t List.mem_cons_self))) f.2.1
          (fun e h => ty e (List.mem_cons_of_mem _ h)) (fun e h => nn e (List.mem_cons_of_mem _ h))
    obtain ⟨v,r,n,t⟩ := run path sn no es (fun x h => typed x (List.mem_cons_of_mem _ h)) (fun x h => normal x (List.mem_cons_of_mem _ h))
    exact ⟨v,r,n,fun _ h => .widen t (fold_root (s := s) (b := s.power b e) s.powSort es ▸ Term.rootSort_le h)⟩

private theorem fold_red (es : List (Term sig)) (val : Term sig → Term sig)
    (exp : ∀ e ∈ es, Reduces R e (val e)) {a b : Term sig} (base : Reduces R a b) :
    Reduces R (es.foldl s.power a) ((es.map val).foldl s.power b) := by
  induction es generalizing a b with
  | nil => exact base
  | cons e rest ih => exact ih (fun e h => exp e (List.mem_cons_of_mem _ h)) (power_red base (exp e List.mem_cons_self))

/-- Normalizing the bilinear map and any signed exponents first preserves
every normal result of the original power spine. This includes a pairing
that becomes a power and an exponent that becomes one. -/
theorem stage_viewed (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y b : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (vx : PointView s β (ruleRoot T.rules) x) (vy : PointView s β (ruleRoot T.rules) y)
    (es : List (Term sig)) (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e)
    (val : Term sig → Term sig) (forms : ∀ e ∈ es, NormalForm (ruleRoot T.rules) e (val e))
    (base : NormalForm (ruleRoot T.rules) (β.map x y) b) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (es.foldl s.power (β.map x y)) out ↔
      NormalForm (ruleRoot T.rules) ((es.map val).foldl s.power b) out := by
  have ty : ∀ e ∈ es.map val, HasSort e .msg := by
    rintro e he; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    exact (forms t ht).2.2 _ (se t ht)
  have nn : ∀ e ∈ es.map val, Normal (ruleRoot T.rules) e := by
    rintro e he; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he; exact (forms t ht).2.1
  have sb := base.2.2 _ (β.map_sorted sx sy)
  have ts := fold_type (s := s) sb (es.map val) ty
  have original := fold_root (s := s) (b := β.map x y) β.mapSort es
  have pre := fold_red (s := s) es val (fun e h => (forms e h).1) base.1
  have replay {v} (nf : NormalForm (ruleRoot T.rules) ((es.map val).foldl s.power b) v) :
      NormalForm (ruleRoot T.rules) (es.foldl s.power (β.map x y)) v :=
    ⟨pre.trans nf.1,nf.2.1,fun _ h => .widen (nf.2.2 _ ts) (original ▸ Term.rootSort_le h)⟩
  constructor
  · intro nf
    obtain ⟨v,hv⟩ := fold_normal group pow sb base.2.1 (es.map val) ty nn
    have eq := unique_viewed I pow group unit sx sy vx vy es se rd (replay hv) nf
    exact ⟨hv.1.trans (.basis eq),nf.2.1,fun k h =>
      Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete (hv.2.2 _ h))⟩
  · exact replay

/-- Normalizing the bilinear map and any signed exponents first preserves
every normal result of the original power spine. This includes a pairing
that becomes a power and an exponent that becomes one. -/
theorem stage (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y b : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (nx : Normal (ruleRoot T.rules) x) (ny : Normal (ruleRoot T.rules) y)
    (es : List (Term sig)) (se : ∀ e ∈ es, HasSort e .msg) (rd : ∀ e ∈ es, Staging.Signed s (ruleRoot T.rules) e)
    (val : Term sig → Term sig) (forms : ∀ e ∈ es, NormalForm (ruleRoot T.rules) e (val e))
    (base : NormalForm (ruleRoot T.rules) (β.map x y) b) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (es.foldl s.power (β.map x y)) out ↔
      NormalForm (ruleRoot T.rules) ((es.map val).foldl s.power b) out :=
  stage_viewed I pow group unit sx sy (normal_view I sx nx) (normal_view I sy ny) es se rd val forms base out

/-- One child-first evaluation step for the common pairing-power operation.
All intermediate normal forms exist for the specified grammar. -/
theorem power_map (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y e : Term sig}
    (sx : HasSort x .msg) (sy : HasSort y .msg) (se : HasSort e .msg)
    (nx : Normal (ruleRoot T.rules) x) (ny : Normal (ruleRoot T.rules) y)
    (rd : Staging.Signed s (ruleRoot T.rules) e) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (s.power (β.map x y) e) out ↔
      ∃ b k, NormalForm (ruleRoot T.rules) (β.map x y) b ∧ NormalForm (ruleRoot T.rules) e k ∧
        NormalForm (ruleRoot T.rules) (s.power b k) out := by
  have same {b k} (bn : NormalForm (ruleRoot T.rules) (β.map x y) b) (en : NormalForm (ruleRoot T.rules) e k) :=
    stage I pow group unit sx sy nx ny [e] (by simpa using se) (by simpa using rd) (fun _ => k)
      (by simpa using en) bn out
  constructor
  · intro nf
    obtain ⟨b,bn⟩ := map_exists I pow group unit sx sy nx ny
    obtain ⟨k,en⟩ := signed_form group se rd
    exact ⟨b,k,bn,en,(same bn en).mp nf⟩
  · rintro ⟨_,_,bn,en,nf⟩; exact (same bn en).mpr nf

/-- At a normalized caller substitution, the stable arguments of the map
and every signed exponent use the very same valuation. In particular the
two point inputs can coincide or contain shared caller variables. -/
theorem caller_power_map {m : Nat} (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {x y : Term sig} (sx : HasSort x .msg) (sy : HasSort y .msg)
    (nx : StableVariants.Stable (ruleRoot T.rules) x) (ny : StableVariants.Stable (ruleRoot T.rules) y)
    (env : Fin m → Term sig) (se : ∀ i, HasSort (env i) .msg) (ne : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (e : SignedMatrix.Expr m) (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) (out : Term sig) :
    NormalForm (ruleRoot T.rules) (ρ.apply (s.power (β.map x y) (e.term s env))) out ↔
      ∃ b k, NormalForm (ruleRoot T.rules) (ρ.apply (β.map x y)) b ∧ NormalForm (ruleRoot T.rules) (ρ.apply (e.term s env)) k ∧
        NormalForm (ruleRoot T.rules) (s.power b k) out := by
  rw [DHExponent.Caller.apply_pow]
  exact power_map I pow group unit (sx.subst ρ.image ρ.sorted) (sy.subst ρ.image ρ.sorted)
    ((e.sorted s env se).subst ρ.image ρ.sorted) (nx ρ hn) (ny ρ hn) (e.defined s _ env ne ρ hn) out

end Tamarin.Rewriting.Bilinear.PowerSpine
