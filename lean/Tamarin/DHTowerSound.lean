import Tamarin.DHTowerCoverage
import Tamarin.DHPeerSymbolic

/-! Normality of symbolic base images and predicted values, independently of
instruction order or variable naming. All products below admit arbitrary
length and repeated positive factors. -/
namespace Tamarin.Rewriting.DHTower
open DHPeer ConstructorVariants Cancellation
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

structure Positive (s : Symbols sig) (R : Root sig) (t : Term sig) : Prop where
  typed : HasSort t .msg
  normal : Normal R t
  noUnit : classOf s.product.one ∉ Cancellation.flatten s.mul t
  noInv : ∀ u, classOf (s.product.inv u) ∉ Cancellation.flatten s.mul t

abbrev Pos (s : Symbols sig) (R : Root sig) (x : Option (Term sig)) :=
  ∀ t, x = some t → Positive s R t

private theorem absent {t u : Term sig} (h : ¬EquivB t u) : classOf u ∉ [classOf t] :=
  fun mem => h (Quotient.exact (List.mem_singleton.mp mem)).symm

theorem Positive.factor {t : Term sig} {R : Root sig} (typed : HasSort t .msg)
    (nt : Normal R t) (p : Factor s t) : Positive s R t where
  typed := typed
  normal := nt
  noUnit := p.single ▸ absent (fun e => p.nonUnit e.head_eq)
  noInv _ := p.single ▸ absent (fun e => p.nonInv e.head_eq)

theorem Positive.packed (mul : MulBucket E) {ts : List (Term sig)} (typed : ∀ t ∈ ts, HasSort t .msg)
    (normal : ∀ t ∈ ts, Normal (ruleRoot T.rules) t) (factor : ∀ t ∈ ts, Factor s t) :
    Pos s (ruleRoot T.rules) (packed s ts) := by
  intro t h
  have hh := bag_factors s ts factor
  rw [h] at hh
  change Cancellation.flatten s.mul t = _ at hh
  apply Positive.mk (packed_sorted typed t h) (packed_factors_normal mul h factor normal).1
  · intro mem
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp (hh ▸ mem)
    exact (factor _ ha).nonUnit (Quotient.exact eq).head_eq
  · intro u mem
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp (hh ▸ mem)
    exact (factor _ ha).nonInv (Quotient.exact eq).head_eq

theorem Positive.mul (bucket : MulBucket E) {p q : Term sig}
    (hp : Positive s (ruleRoot T.rules) p) (hq : Positive s (ruleRoot T.rules) q) :
    Positive s (ruleRoot T.rules) (s.product.mul p q) := by
  let ps := Cancellation.flatten s.mul p ++ Cancellation.flatten s.mul q
  have f : Cancellation.flatten s.mul (s.product.mul p q) = ps := Cancellation.flatten_ac ..
  have unit : classOf s.product.one ∉ ps := fun h => (List.mem_append.mp h).elim hp.noUnit hq.noUnit
  have inv (v) : classOf (s.product.inv v) ∉ ps := fun h => (List.mem_append.mp h).elim (hp.noInv v) (hq.noInv v)
  have clean : DHProduct.Clean s.product ps :=
    ⟨unit,fun n _ _ perm => inv n (perm.mem_iff.mpr List.mem_cons_self),fun n hn => False.elim (inv n hn)⟩
  exact ⟨s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ hp.typed) (s.mulSort ▸ hq.typed),
    cleanMul bucket (f ▸ clean) hp.normal hq.normal,f ▸ unit,fun v => f ▸ inv v⟩

theorem Positive.append (bucket : MulBucket E) {p q} (hp : Pos s (ruleRoot T.rules) p)
    (hq : Pos s (ruleRoot T.rules) q) : Pos s (ruleRoot T.rules) (DHTower.append s p q) := by
  cases p with
  | none => cases q <;> exact hq
  | some p => cases q with
    | none => exact hp
    | some q => intro t h; cases h; exact (hp _ rfl).mul bucket (hq _ rfl)

private theorem invNotOne (s : Symbols sig) (t : Term sig) : head (s.product.inv t) ≠ .free s.one := by
  intro eq; have ar := s.invArity; rw [Head.free.inj eq,s.oneArity] at ar; contradiction

private theorem invTyped {t : Term sig} (h : HasSort t .msg) : HasSort (s.product.inv t) .msg := by
  rw [← s.invSort]; apply HasSort.free; intro i; simpa [s.invInput] using h

private theorem mixed_clean {p n : Term sig} (hp : Positive s (ruleRoot T.rules) p)
    (hn : Positive s (ruleRoot T.rules) n)
    (apart : ∀ k ∈ Cancellation.flatten s.mul n, k ∉ Cancellation.flatten s.mul p) :
    DHProduct.Clean s.product (Cancellation.flatten s.mul (s.product.mul p (s.product.inv n))) := by
  classical
  let ps := Cancellation.flatten s.mul p
  let key (a : Term sig) := classOf (s.product.inv a)
  change DHProduct.Clean s.product (Cancellation.flatten s.mul (.ac s.mul p (s.product.inv n)))
  rw [Cancellation.flatten_ac]
  change DHProduct.Clean s.product (ps ++ [key n])
  constructor
  · intro h
    rcases List.mem_append.mp h with h|h
    · exact hp.noUnit h
    · exact invNotOne s n (Quotient.exact (List.mem_singleton.mp h)).head_eq.symm
  · intro x y rest perm
    let isNeg (v : Class sig) := decide (∃ a, v = key a)
    have hit (a) : isNeg (key a) = true := decide_eq_true ⟨a,rfl⟩
    have clear : ps.countP isNeg = 0 := List.countP_eq_zero.mpr (by
      intro v hv test
      obtain ⟨a,rfl⟩ := of_decide_eq_true test
      exact hp.noInv a hv)
    have num := perm.countP_eq isNeg
    change (ps ++ [key n]).countP isNeg = (key x :: key y :: rest).countP isNeg at num
    simp [List.countP_append,clear,hit] at num
  · intro x hx k hk h
    obtain eq := List.mem_singleton.mp ((List.mem_append.mp hx).resolve_left (hp.noInv x))
    have arg : EquivB x n :=
      (Matching.free_equiv_iff ..).mp (Quotient.exact eq) ⟨0,by rw [s.invArity]; decide⟩
    have mem := (Cancellation.flatten_equiv s.mul arg).mem_iff.mp hk
    rcases List.mem_append.mp h with h|h
    · exact apart k mem h
    · obtain rfl := List.mem_singleton.mp h
      exact hn.noInv n mem

theorem assembled_normal (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {p n}
    (hp : Pos s (ruleRoot T.rules) p) (hn : Pos s (ruleRoot T.rules) n)
    (apart : ∀ k ∈ Balance.bag s n, k ∉ Balance.bag s p) :
    HasSort (Balance.assemble s p n) .msg ∧ Normal (ruleRoot T.rules) (Balance.assemble s p n) ∧
    (head (Balance.assemble s p n) = .free s.one → p = none ∧ n = none) := by
  have neg {t : Term sig} (h : Positive s (ruleRoot T.rules) t) :=
    inv.normal_positive h.normal h.noUnit h.noInv
  cases p with
  | none => cases n with
    | none =>
      exact ⟨by rw [← s.oneSort]; apply HasSort.free; exact fun i => Fin.elim0 (s.oneArity ▸ i),unit,by simp⟩
    | some n =>
      exact ⟨invTyped (hn _ rfl).typed,neg (hn _ rfl),fun e => False.elim (invNotOne s n e)⟩
  | some p => cases n with
    | none =>
      refine ⟨(hp _ rfl).typed,(hp _ rfl).normal,fun h => ?_⟩
      obtain rfl : p = s.product.one := nullary s.oneArity h
      exact False.elim ((hp _ rfl).noUnit List.mem_cons_self)
    | some n =>
      exact ⟨s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ (hp _ rfl).typed)
        (s.mulSort ▸ invTyped (hn _ rfl).typed),cleanMul mul (mixed_clean (hp _ rfl) (hn _ rfl) apart)
        (hp _ rfl).normal (neg (hn _ rfl)),fun e => by cases e⟩

/-- A tower image and its reported value are normal at the uninstantiated
row. Witness names need only be apart from the factor classes on the opposite
side of each signed product. -/
theorem symbolic_cancel (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {b r : Term sig} {p n rest : Option (Term sig)}
    (sb : HasSort b .msg) (nb : Normal (ruleRoot T.rules) b)
    (noPow : head b ≠ .free s.pow) (noNeutral : head b ≠ .free s.neutral)
    (sr : Positive s (ruleRoot T.rules) r) (sp : Pos s (ruleRoot T.rules) p)
    (sn : Pos s (ruleRoot T.rules) n) (st : Pos s (ruleRoot T.rules) rest)
    (baseApart : ∀ k ∈ Balance.bag s (DHTower.append s (some r) n), k ∉ Balance.bag s p)
    (valueApart : ∀ k ∈ Balance.bag s n, k ∉ Balance.bag s (DHTower.append s p rest)) :
    Normal (ruleRoot T.rules) (s.power b (Balance.assemble s p (DHTower.append s (some r) n))) ∧
    Normal (ruleRoot T.rules) (powerResult s b (DHTower.append s p rest) n) := by
  have rs : Pos s (ruleRoot T.rules) (some r) := by intro t h; cases h; exact sr
  have ⟨ib,inorm,iu⟩ := assembled_normal mul inv unit sp (Positive.append mul rs sn) baseApart
  have ⟨vb,vnorm,vu⟩ := assembled_normal mul inv unit (Positive.append mul sp st) sn valueApart
  constructor
  · apply (pow.normal_iff sb ib).mpr
    refine ⟨nb,inorm,noPow,noNeutral,fun h => ?_⟩
    have impossible := (iu h).2
    cases n <;> cases impossible
  · generalize DHTower.append s p rest = q at *
    cases q with
    | none => cases n with
      | none => exact nb
      | some n => exact (pow.normal_iff sb vb).mpr ⟨nb,vnorm,noPow,noNeutral,fun h => by cases (vu h).2⟩
    | some q => cases n <;>
        exact (pow.normal_iff sb vb).mpr ⟨nb,vnorm,noPow,noNeutral,fun h => by cases (vu h).1⟩

/-- The Rust adapter allocates separate Msg names for these optional parameters. -/
def parameter (sig : Signature) (enabled : Bool) (v : Variable) : Option (Term sig) :=
  if enabled then some (.var v) else none

private theorem bag_parameter {use : Bool} {v : Variable} {k} (h : k ∈ Balance.bag s (parameter sig use v)) :
    k = classOf (.var v) := by cases use <;> simp_all [parameter,Balance.bag,Cancellation.flatten]

private theorem variablePositive (pow : PowerBucket T) (v : Variable) (typed : HasSort (.var v : Term sig) .msg) :
    Positive s (ruleRoot T.rules) (.var v) :=
  .factor typed ((constructor_normal _ pow.1).1 _) (by constructor <;> intro h <;> cases h)

private theorem optionalPositive (pow : PowerBucket T) (use : Bool) (v : Variable)
    (tv : HasSort (.var v : Term sig) .msg) : Pos s (ruleRoot T.rules) (parameter sig use v) := by
  cases use with
  | false => simp [Pos,parameter]
  | true => intro t h; cases h; exact variablePositive pow _ tv

theorem powerSorted {a e : Term sig} (ha : HasSort a .msg) (he : HasSort e .msg) :
    HasSort (s.power a e) .msg := by
  rw [← s.powSort]; apply HasSort.free; intro i; rw [s.powInput]; split <;> assumption

theorem signedSorted {p n} (hp : sorted p) (hn : sorted n) :
    HasSort (Balance.assemble s p n) .msg := by
  cases p with
  | none => cases n with
    | none => rw [← s.oneSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.oneArity ▸ i)
    | some n => exact invTyped (hn n rfl)
  | some p => cases n with
    | none => exact hp p rfl
    | some n => exact s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ hp p rfl) (s.mulSort ▸ invTyped (hn n rfl))

private theorem resultSorted {b : Term sig} (hb : HasSort b .msg) (p n : Option (Term sig))
    (hp : sorted p) (hn : sorted n) : HasSort (powerResult s b p n) .msg := by
  cases p <;> cases n
  · exact hb
  all_goals exact powerSorted hb (signedSorted hp hn)

/-- Every nonempty occurrence mask produces a genuine symbolic variant for
fresh positive and negative witnesses. Actual exponent occurrences may share
variables and need not designate distinct factors. -/
theorem fresh_cancel (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (ts : List (Term sig)) (m : List Bool)
    (b p n : Variable) (useP useN : Bool) (sb : HasSort (.var b : Term sig) .msg)
    (sp : HasSort (.var p : Term sig) .msg) (sn : HasSort (.var n : Term sig) .msg)
    (pn : p ≠ n) (apart : ∀ t ∈ ts, ¬EquivB t (.var p) ∧ ¬EquivB t (.var n))
    (types : ∀ t ∈ ts, HasSort t .msg) (normal : ∀ t ∈ ts, Normal (ruleRoot T.rules) t)
    (factor : ∀ t ∈ ts, Factor s t) (width : m.length = ts.length) {added r}
    (pack : packed s ts = some added) (take : packed s (select m ts) = some r) :
    let ps := parameter sig useP p
    let ns := parameter sig useN n
    let base := s.power (.var b) (Balance.assemble s ps (DHTower.append s (some r) ns))
    let out := powerResult s (.var b) (DHTower.append s ps (packed s (remaining m ts))) ns
    Normal (ruleRoot T.rules) base ∧ NormalForm (ruleRoot T.rules) (s.power base added) out := by
  let ps := parameter sig useP p
  let ns := parameter sig useN n
  let rest := packed s (remaining m ts)
  have pr := optionalPositive pow useP p sp
  have nr := optionalPositive pow useN n sn
  have inTake {t : Term sig} (h : t ∈ select m ts) := select_mem h
  have inRest {t : Term sig} (h : t ∈ remaining m ts) := select_mem h
  have subset {as : List (Term sig)} (sub : ∀ t ∈ as, t ∈ ts) :=
    Positive.packed mul (fun t h => types t (sub t h)) (fun t h => normal t (sub t h))
      (fun t h => factor t (sub t h))
  have sr := subset (fun _ => inTake) r take
  have left : Pos s (ruleRoot T.rules) rest := subset (fun _ => inRest)
  have diff : classOf (.var p : Term sig) ≠ classOf (.var n) := fun e => pn (Head.var.inj (Quotient.exact e).head_eq)
  have used := bag_factors s (select m ts) (fun _ h => factor _ (inTake h))
  rw [take] at used
  have leftBag : Balance.bag s rest = _ := bag_factors s (remaining m ts) (fun _ h => factor _ (inRest h))
  have baseApart (k) (h : k ∈ Balance.bag s (DHTower.append s (some r) ns)) (other : k ∈ Balance.bag s ps) : False := by
    have key := bag_parameter other
    rw [bag_append,used] at h
    rcases List.mem_append.mp h with x|x
    · obtain ⟨t,inc,e⟩ := List.mem_map.mp x
      exact (apart t (inTake inc)).1 (Quotient.exact (e.trans key))
    · exact diff (key.symm.trans (bag_parameter x))
  have valueApart (k) (h : k ∈ Balance.bag s ns) (other : k ∈ Balance.bag s (DHTower.append s ps rest)) : False := by
    have key := bag_parameter h
    rw [bag_append,leftBag] at other
    rcases List.mem_append.mp other with x|x
    · exact diff ((bag_parameter x).symm.trans key)
    · obtain ⟨t,inc,e⟩ := List.mem_map.mp x
      exact (apart t (inRest inc)).2 (Quotient.exact (e.trans key))
  obtain ⟨nb,nv⟩ := symbolic_cancel pow mul inv unit sb (constructor_normal _ pow.1 |>.1 _) (by intro e; cases e)
    (by intro e; cases e) sr pr nr left baseApart valueApart
  have path := replay_mask E ts m ps ns pack width take factor types (fun u h => (pr u h).typed)
    (fun u h => (nr u h).typed) sb
  have os := resultSorted (s := s) sb (DHTower.append s ps rest) ns
    (fun u h => (Positive.append mul pr left u h).typed) (fun u h => (nr u h).typed)
  exact ⟨nb,path,nv,fun _ h => .widen os (s.powSort ▸ Term.rootSort_le h)⟩

/-- A base image and its uniquely reconstructible symbolic output are both
irreducible for the selected substitution. -/
def SoundImage (s : Symbols sig) (R : Root sig) (added image value : Term sig) : Prop :=
  Normal R image ∧ NormalForm R (s.power image added) value

/-- The three rows that do not consume a negative factor. Their input and
output are normal even when some exponent occurrences are repeated. -/
theorem fresh_prefix (pow : PowerBucket T) (mul : MulBucket E)
    (neutral : Normal (ruleRoot T.rules) s.neutralTerm)
    (ts : List (Term sig)) {added} (pack : packed s ts = some added)
    (typed : ∀ t ∈ ts, HasSort t .msg) (normal : ∀ t ∈ ts, Normal (ruleRoot T.rules) t)
    (factor : ∀ t ∈ ts, Factor s t) (Y b p : Variable)
    (sy : HasSort (.var Y : Term sig) .msg) (sb : HasSort (.var b : Term sig) .msg)
    (sp : HasSort (.var p : Term sig) .msg) :
    let Sound := SoundImage s (ruleRoot T.rules) added
    Sound (.var Y) (s.power (.var Y) added) ∧ Sound s.neutralTerm s.neutralTerm ∧
      Sound (s.power (.var b) (.var p)) (s.power (.var b) (s.product.mul (.var p) added)) := by
  have a := Positive.packed mul typed normal factor added pack
  have sa := a.typed
  have au := (packed_factors_normal mul pack factor normal).2
  have vars := (constructor_normal _ pow.1).1
  have varPower (q : Variable) (sq : HasSort (.var q : Term sig) .msg) (e : Term sig)
      (ht : HasSort e .msg) (hn : Normal (ruleRoot T.rules) e) (unitless : head e ≠ .free s.one) :
      Normal (ruleRoot T.rules) (s.power (.var q) e) :=
    (pow.normal_iff sq ht).mpr ⟨vars _,⟨hn,⟨(fun h => nomatch h),⟨(fun h => nomatch h),unitless⟩⟩⟩⟩
  have prod := (variablePositive pow p sp).mul mul a
  have nsort : HasSort s.neutralTerm .msg := by
    rw [← s.neutralSort]; apply HasSort.free; intro i; exact Fin.elim0 (s.neutralArity ▸ i)
  let env (i : Fin 3) : Term sig := if i = 0 then .var b else if i = 1 then .var p else added
  have st : ∀ i, HasSort (env i) .msg := by intro i; unfold env; split <;> first | assumption | split <;> assumption
  exact ⟨⟨vars _,.basis (.refl _),varPower Y sy _ sa a.normal au,fun _ h => h⟩,
    ⟨neutral,T.fire .neutral (fun _ => added) (fun _ => sa),neutral,fun _ h => .widen nsort (s.powSort ▸ Term.rootSort_le h)⟩,
    varPower b sb _ sp (vars _) (by intro h; cases h),T.fire .tower env st,
    varPower b sb _ prod.typed prod.normal (by intro h; cases h),
    fun _ h => .widen (powerSorted sb prod.typed) (s.powSort ▸ Term.rootSort_le h)⟩

end Tamarin.Rewriting.DHTower
