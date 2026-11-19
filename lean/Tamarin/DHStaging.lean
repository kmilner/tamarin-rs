import Tamarin.DHGroupExistence
import Tamarin.DHSignedMatrix
import Tamarin.VariantPresentation

/-! Child-first staging for signed exponent expressions and powers. The source
may reduce in any order, including tower flattening before either operand
normalizes. A normal base may be a previous power or the neutral element. -/
namespace Tamarin.Rewriting.DHPeer.Staging
open ConstructorVariants Cancellation DHTower
variable {m : Nat} {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

def Signed (s : Symbols sig) (R : Root sig) (t : Term sig) :=
  ∀ k, ∃ z, Balance.read s R k t = some z

private theorem mul_sorted {a b : Term sig} (l : HasSort a .msg) (r : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ l) (s.mulSort ▸ r)

private theorem inv_sorted {t : Term sig} (typed : HasSort t .msg) :
    HasSort (s.product.inv t) .msg := by
  rw [← s.invSort]; apply HasSort.free; intro i; simpa only [s.invInput] using typed

theorem signed_mul {R : Root sig} {x y : Term sig} (l : Signed s R x) (r : Signed s R y) :
    Signed s R (s.product.mul x y) := by
  intro k
  obtain ⟨i,hi⟩ := l k
  obtain ⟨j,hj⟩ := r k
  exact ⟨i+j,by rw [Balance.read_mul,hi,hj]; rfl⟩

theorem signed_inv {R : Root sig} {x : Term sig} (h : Signed s R x) :
    Signed s R (s.product.inv x) := by
  intro k
  obtain ⟨i,hi⟩ := h k
  exact ⟨-i,by rw [Balance.read_inv,hi]; rfl⟩

private theorem pow_red {R : Root sig} {a x b y : Term sig} (l : Reduces R a b) (r : Reduces R x y) :
    Reduces R (s.power a x) (s.power b y) := by
  apply Reduces.free; intro i; split <;> assumption

private def triple (x y z : Term sig) (i : Fin 3) := if i = 0 then x else if i = 1 then y else z

private theorem typed3 {x y z : Term sig} (hx : HasSort x .msg) (hy : HasSort y .msg)
    (hz : HasSort z .msg) : ∀ i, HasSort (triple x y z i) .msg := by
  intro i; unfold triple; split <;> first | assumption | split <;> assumption

/-- Two arbitrary normal message arguments give a reachable normal power.
When the base is a previous power, its old and new signed exponents can
cancel to the unit, recovering the original base. -/
theorem power_exists (table : Balance.Inventory E) (pow : PowerBucket T) {base e : Term sig}
    (sb : HasSort base .msg) (se : HasSort e .msg)
    (nb : Normal (ruleRoot T.rules) base) (ne : Normal (ruleRoot T.rules) e) :
    ∃ v, NormalForm (ruleRoot T.rules) (s.power base e) v := by
  suffices ∃ v, Reduces (ruleRoot T.rules) (s.power base e) v ∧
      Normal (ruleRoot T.rules) v ∧ HasSort v .msg by
    obtain ⟨v,r,n,h⟩ := this
    exact ⟨v,r,n,fun _ hs => .widen h (s.powSort ▸ Term.rootSort_le hs)⟩
  by_cases unit : head e = .free s.one
  · obtain rfl : e = s.product.one := nullary s.oneArity unit
    exact ⟨base,T.fire .expOne (fun _ => base) (fun _ => sb),nb,sb⟩
  by_cases neutral : head base = .free s.neutral
  · obtain rfl : base = s.neutralTerm := nullary s.neutralArity neutral
    exact ⟨_,T.fire .neutral (fun _ => e) (fun _ => se),nb,sb⟩
  by_cases previous : head base = .free s.pow
  · obtain ⟨b,p,rfl⟩ := splitPower s previous
    obtain ⟨tb,tp⟩ := pow_types sb
    obtain ⟨normalB,normalP,plain,nonneutral,_⟩ := (pow.normal_iff tb tp).mp nb
    have signed := signed_mul (fun k => Balance.defined s _ k normalP) (fun k => Balance.defined s _ k ne)
    obtain ⟨n,red,nn,tn⟩ := table.normal_exists (mul_sorted tp se) (signed _)
    have tower : Reduces (ruleRoot T.rules) (s.power (s.power b p) e) (s.power b (s.product.mul p e)) :=
      T.fire .tower _ (typed3 tb tp se)
    have result := tower.trans (pow_red (.basis (.refl b)) red)
    by_cases cancel : head n = .free s.one
    · obtain rfl : n = s.product.one := nullary s.oneArity cancel
      exact ⟨b,result.trans (T.fire .expOne (fun _ => b) (fun _ => tb)),normalB,tb⟩
    · exact ⟨s.power b n,result,(pow.normal_iff tb tn).mpr ⟨normalB,nn,plain,nonneutral,cancel⟩,
        powerSorted tb tn⟩
  · exact ⟨_,.basis (.refl _),(pow.normal_iff sb se).mpr ⟨nb,ne,previous,neutral,unit⟩,powerSorted sb se⟩

private theorem stage {R : Root sig} {source staged out : Term sig} (red : Reduces R source staged)
    (ss : HasSort source .msg) (ts : HasSort staged .msg)
    (ms : source.rootSort = .msg) (mt : staged.rootSort = .msg)
    (unique : ∀ u v, NormalForm R source u → NormalForm R source v → EquivB u v)
    (existsNF : ∃ n, NormalForm R staged n) : NormalForm R source out ↔ NormalForm R staged out := by
  have replay {u} (nf : NormalForm R staged u) : NormalForm R source u :=
    ⟨red.trans nf.1,nf.2.1,fun _ hs => .widen (nf.2.2 _ ts) (ms ▸ Term.rootSort_le hs)⟩
  constructor
  · intro nf
    obtain ⟨n,nn⟩ := existsNF
    exact ⟨nn.1.trans (.basis (unique n out (replay nn) nf)),nf.2.1,
      fun _ hs => .widen (nf.2.2 _ ss) (mt ▸ Term.rootSort_le hs)⟩
  · exact replay

/-- Reducing any signed children first preserves every normal result. The
replacement may already be a compound normalized product and may share
variables with other operands. -/
theorem signed_stage [DecidableEq sig.ACSym] (table : Balance.Inventory E)
    {source staged out : Term sig} (sourceSort : HasSort source .msg) (stagedSort : HasSort staged .msg)
    (ms : source.rootSort = .msg) (mt : staged.rootSort = .msg)
    (domain : Signed s (ruleRoot T.rules) source) (red : Reduces (ruleRoot T.rules) source staged) :
    NormalForm (ruleRoot T.rules) source out ↔ NormalForm (ruleRoot T.rules) staged out := by
  apply stage red sourceSort stagedSort ms mt
  · intro u v nu nv
    exact Balance.normal_unique table E.presentation (fun _ => Balance.plain_of_inverse E) domain
      (nu.2.2 _ sourceSort) (nv.2.2 _ sourceSort) nu.2.1 nv.2.1 nu.1 nv.1
  · obtain ⟨j,hj⟩ := domain (classOf s.product.one)
    obtain ⟨n,r,hn,sn⟩ := table.normal_exists stagedSort ⟨j,table.reduces _ red j hj⟩
    exact ⟨n,r,hn,fun _ h => .widen sn (mt ▸ Term.rootSort_le h)⟩

/-- A binary stage can consume entire normalized products on either side,
including products obtained by normalizing a previous stage. -/
theorem mul_stage [DecidableEq sig.ACSym] (table : Balance.Inventory E) {a b x y out : Term sig}
    (sa : HasSort a .msg) (sb : HasSort b .msg)
    (da : Signed s (ruleRoot T.rules) a) (db : Signed s (ruleRoot T.rules) b)
    (l : NormalForm (ruleRoot T.rules) a x) (r : NormalForm (ruleRoot T.rules) b y) :
    NormalForm (ruleRoot T.rules) (s.product.mul a b) out ↔
      NormalForm (ruleRoot T.rules) (s.product.mul x y) out :=
  signed_stage table (mul_sorted sa sb) (mul_sorted (l.2.2 _ sa) (r.2.2 _ sb)) s.mulSort s.mulSort
    (signed_mul da db) (.ac _ l.1 r.1)

theorem inv_stage [DecidableEq sig.ACSym] (table : Balance.Inventory E) {a x out : Term sig}
    (sa : HasSort a .msg) (da : Signed s (ruleRoot T.rules) a)
    (r : NormalForm (ruleRoot T.rules) a x) :
    NormalForm (ruleRoot T.rules) (s.product.inv a) out ↔ NormalForm (ruleRoot T.rules) (s.product.inv x) out :=
  signed_stage table (inv_sorted sa) (inv_sorted (r.2.2 _ sa)) s.invSort s.invSort
    (signed_inv da) (by apply Reduces.free; intro i; exact r.1)

/-- Normalizing the changing base and exponent before applying the power
operation is exact. The base can be any signed power spine with defined
readings, and the exponent any term with defined signed balances. -/
theorem power_stage [DecidableEq sig.ACSym] (table : Balance.Inventory E) (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one) {base e b n out : Term sig}
    (sb : HasSort base .msg) (se : HasSort e .msg)
    (baseDomain : Spine.Defined s (ruleRoot T.rules) base) (expDomain : Signed s (ruleRoot T.rules) e)
    (left : NormalForm (ruleRoot T.rules) base b) (right : NormalForm (ruleRoot T.rules) e n) :
    NormalForm (ruleRoot T.rules) (s.power base e) out ↔ NormalForm (ruleRoot T.rules) (s.power b n) out := by
  have tb := left.2.2 _ sb
  have tn := right.2.2 _ se
  exact stage (pow_red left.1 right.1) (powerSorted sb se) (powerSorted tb tn) s.powSort s.powSort
    (fun _ _ => Spine.unique pow table unit (powerSorted sb se) (Spine.defined_power baseDomain expDomain))
    (power_exists table pow tb tn left.2.1 right.2.1)

/-- The signed expression grammar supplies both a defined reading and a
normal form. Repeated inputs use the same caller substitution throughout. -/
theorem signed_admitted (table : Balance.Inventory E) (env : Fin m → Term sig)
    (typed : ∀ i, HasSort (env i) .msg) (stable : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) (e : SignedMatrix.Expr m) :
    let t := ρ.apply (e.term s env)
    HasSort t .msg ∧ Signed s (ruleRoot T.rules) t ∧ ∃ n, NormalForm (ruleRoot T.rules) t n := by
  have ht := (e.sorted s env typed).subst ρ.image ρ.sorted
  have domain := e.defined s _ env stable ρ hn
  refine ⟨ht,domain,?_⟩
  obtain ⟨v,r,n,hv⟩ := table.normal_exists ht (domain _)
  by_cases msg : (ρ.apply (e.term s env)).rootSort = .msg
  · exact ⟨v,r,n,fun _ hs => .widen hv (msg ▸ Term.rootSort_le hs)⟩
  · cases e with
    | input i => exact ⟨_,.basis (.refl _),stable i ρ hn,fun _ h => h⟩
    | unit => exact (msg s.oneSort).elim
    | mul => exact (msg s.mulSort).elim
    | inv => exact (msg s.invSort).elim

/-- All finite base spines, including an empty spine, have a normal form
at every normalized caller instance. The base itself may specialize to a
previous power, a neutral element, or a message of a narrower sort. -/
theorem spine_admitted (table : Balance.Inventory E) (pow : PowerBucket T)
    (env : Fin m → Term sig) (typed : ∀ i, HasSort (env i) .msg)
    (stable : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (base : Term sig) (sb : HasSort base .msg) (nb : StableVariants.Stable (ruleRoot T.rules) base)
    (xs : List (SignedMatrix.Expr m)) (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) :
    let t := ρ.apply (xs.foldl (fun b e => s.power b (e.term s env)) base)
    HasSort t .msg ∧ Spine.Defined s (ruleRoot T.rules) t ∧ ∃ n, NormalForm (ruleRoot T.rules) t n := by
  have hs : HasSort (ρ.apply base) .msg := sb.subst ρ.image ρ.sorted
  have dom := Spine.defined_normal s _ (nb ρ hn)
  have nf : ∃ n, NormalForm (ruleRoot T.rules) (ρ.apply base) n :=
    ⟨_,.basis (.refl _),nb ρ hn,fun _ h => h⟩
  clear nb sb
  induction xs generalizing base with
  | nil => exact ⟨hs,dom,nf⟩
  | cons e rest ih =>
    obtain ⟨se,de,v,vnf⟩ := signed_admitted table env typed stable ρ hn e
    obtain ⟨u,unf⟩ := nf
    have su := unf.2.2 _ hs
    have sv := vnf.2.2 _ se
    obtain ⟨n,pnf⟩ := power_exists table pow su sv unf.2.1 vnf.2.1
    apply ih
    all_goals rw [DHExponent.Caller.apply_pow]
    · exact powerSorted hs se
    · exact Spine.defined_power dom de
    · exact ⟨n,(pow_red unf.1 vnf.1).trans pnf.1,pnf.2.1,fun _ h =>
        .widen (pnf.2.2 _ (powerSorted su sv)) (s.powSort ▸ Term.rootSort_le h)⟩

/-- The caller's exact spine grammar discharges the semantic hypotheses of
child-first power staging, including existence of both intermediate values. -/
theorem spine_stage [DecidableEq sig.ACSym] (table : Balance.Inventory E) (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one) (env : Fin m → Term sig)
    (typed : ∀ i, HasSort (env i) .msg) (stable : ∀ i, StableVariants.Stable (ruleRoot T.rules) (env i))
    (base : Term sig) (sb : HasSort base .msg) (nb : StableVariants.Stable (ruleRoot T.rules) base)
    (xs : List (SignedMatrix.Expr m)) (e : SignedMatrix.Expr m)
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) (out : Term sig) :
    let b := xs.foldl (fun b x => s.power b (x.term s env)) base
    NormalForm (ruleRoot T.rules) (ρ.apply (s.power b (e.term s env))) out ↔
      ∃ x y, NormalForm (ruleRoot T.rules) (ρ.apply b) x ∧
        NormalForm (ruleRoot T.rules) (ρ.apply (e.term s env)) y ∧ NormalForm (ruleRoot T.rules) (s.power x y) out := by
  dsimp only
  rw [DHExponent.Caller.apply_pow]
  obtain ⟨hs,dom,u,unf⟩ := spine_admitted table pow env typed stable base sb nb xs ρ hn
  obtain ⟨he,de,v,vnf⟩ := signed_admitted table env typed stable ρ hn e
  constructor
  · intro result
    exact ⟨u,v,unf,vnf,(power_stage table pow unit hs he dom de unf vnf).mp result⟩
  · rintro ⟨_,_,l,r,result⟩
    exact (power_stage table pow unit hs he dom de l r).mpr result

end Tamarin.Rewriting.DHPeer.Staging
