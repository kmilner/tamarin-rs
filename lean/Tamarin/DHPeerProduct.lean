import Tamarin.DHPeerInverse
import Tamarin.DHBase

namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants DHProduct
variable {sig : Signature} {s : Symbols sig}

private def triple (u v w : Term sig) (i : Fin 3) := if i = 0 then u else if i = 1 then v else w

private theorem typed3 {u v w : Term sig} (hu : HasSort u .msg) (hv : HasSort v .msg) (hw : HasSort w .msg) :
    ∀ i, HasSort (triple u v w i) .msg := by
  intro i; unfold triple; split <;> first | assumption | split <;> assumption

/-- Syntactic operations and the six simplifying multiplication rules needed
to extract signed-factor conditions directly from the original presentation. -/
theorem ExtraTable.presentation {T : Table s} (E : ExtraTable T) : Presentation s.product (ruleRoot T.rules) where
  multSort := s.mulSort
  invFactor _ := rfl
  unitFactor := rfl
  invCongr eq := .free _ _ _ (fun _ => eq)
  invChild _ h := by
    let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
    have ht := Term.checkSort_complete h
    simp only [Symbols.product,Term.checkSort,Bool.and_eq_true,List.all_eq_true] at ht
    exact s.invInput i ▸ Term.checkSort_sound _ _ (ht.2 i (List.mem_finRange i))
  invLarger t := by
    change _ < (List.ofFn (fun _ : Fin (sig.arity s.inv) => FiniteOccurs.nodes t)).sum + 1
    have ar := s.invArity
    generalize sig.arity s.inv = m at ar ⊢
    have h : m = 1 := by assumption
    subst m
    simp [List.ofFn_succ]
  unitRule _ hx := E.fireRoot .mulOne _ (typed3 hx hx hx)
  joinRule _ _ hx hy := E.fireRoot .join _ (typed3 hx hy hx)
  roots := {
    direct := fun _ hx => T.fireRoot .inverse _ (typed3 hx hx hx)
    extra := fun _ _ hx hy => T.fireRoot .inverseRest _ (typed3 hx hy hy)
    inside := fun _ _ hx hy => T.fireRoot .inside _ (typed3 hx hy hy)
    both := fun _ _ _ hx hy hz => T.fireRoot .insideRest _ (typed3 hx hy hz)
  }

/-- Multiplication has seven left-hand sides, four from the basic
cancellation table and three supplementary equations. -/
def MulBucket {T : Table s} (E : ExtraTable T) : Prop :=
  (∀ eq ∈ T.rules, Application eq.lhs) ∧ ∀ eq ∈ T.rules, head eq.lhs = .ac s.mul →
    (∃ k : Rule, (k = .inverse ∨ k = .inverseRest ∨ k = .inside ∨ k = .insideRest) ∧
      eq = k.instantiate s (fun i => .var (T.actual k i))) ∨
    (∃ k : ExtraRule, (k = .mulOne ∨ k = .join ∨ k = .joinRest) ∧
      eq = k.instantiate s (fun i => .var (E.actual k i)))

theorem MulBucket.inventory {T : Table s} {E : ExtraTable T} (bucket : MulBucket E) :
    ∀ p q, head p = .ac s.product.mult → ruleRoot T.rules p q → MulPattern s.product p := by
  rintro _ _ hd ⟨eq,mem,σ,rfl,rfl⟩
  have here := (instance_head eq (bucket.1 eq mem) σ).symm.trans hd
  rcases bucket.2 eq mem here with ⟨k,tag,rfl⟩ | ⟨k,tag,rfl⟩
  · simp only [Rule.instantiate,Expr.subst_eval]
    rcases tag with rfl|rfl|rfl|rfl
    · exact .cancel _
    · exact .cancelRest _ _
    · exact .inside _ _
    · exact .insideRest _ _ _
  · simp only [ExtraRule.instantiate,Expr.subst_eval]
    rcases tag with rfl|rfl|rfl
    · exact .unit _
    · exact .inverses _ _
    · exact .inversesRest _ _ _

theorem cleanMul {T : Table s} {E : ExtraTable T} (bucket : MulBucket E) {u v : Term sig}
    (c : Clean s.product (Cancellation.flatten s.mul (s.product.mul u v)))
    (nu : Normal (ruleRoot T.rules) u) (nv : Normal (ruleRoot T.rules) v) :
    Normal (ruleRoot T.rules) (s.product.mul u v) := by
  classical
  apply c.normal E.presentation.unitFactor E.presentation.invFactor _ bucket.inventory
  intro z hz
  change z ∈ ACRepresentation.flatten s.mul (.ac s.mul u v) at hz
  rcases List.mem_append.mp (by simpa [ACRepresentation.flatten] using hz) with h|h
  · exact ((subgroup_normal_iff s.mul u).mp nu).1 _ h
  · exact ((subgroup_normal_iff s.mul v).mp nv).1 _ h

/-- Normality of the mixed positive/negative cancellation residual. Both
components may be arbitrary nonempty products with repeated factors. -/
theorem mixedNormal {T : Table s} {E : ExtraTable T} (mult : MulBucket E) (inv : InverseBucket E)
    {u v r : Term sig} (typed : HasSort (s.product.mul u (s.product.inv (s.product.mul v r))) .msg)
    (hr : HasSort r .msg) (norm : Normal (ruleRoot T.rules) (s.product.mul u (s.product.inv (s.product.mul v r)))) :
    Normal (ruleRoot T.rules) (s.product.mul u (s.product.inv v)) := by
  classical
  have c := clean_of_normal E.presentation typed norm (fun h => by cases h.head_eq)
  have children := normal_ac_children _ norm
  exact cleanMul mult (cleanShrink E.presentation.invLarger c) children.1 (inv.shrink hr children.2)


private theorem mulTyped (s : Symbols sig) {u v : Term sig} (hu : HasSort u .msg) (hv : HasSort v .msg) :
    HasSort (s.product.mul u v) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ hu) (s.mulSort ▸ hv)

private theorem invNotOne (s : Symbols sig) (t : Term sig) : head (s.product.inv t) ≠ .free s.one := by
  intro eq; have e := Head.free.inj eq; have h := s.invArity; rw [e,s.oneArity] at h; contradiction

/-- Normality of every concretely classified value follows from the exact
buckets for powers, inverses and products. No uniqueness or confluence
assumption is needed, including for mixed cancellations. -/
theorem classifiedNormalFactor [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E) {Y r k env}
    (h : Realizes s (ruleRoot T.rules) Y r k env) (factor : Factor s r) :
    Normal (ruleRoot T.rules) (k.pair.2.eval s env) := by
  have original := (normal_equiv _ h.base).mp (h.peer ▸ h.normal .peer)
  have fr : Factor s (env .fresh) := h.fresh ▸ factor
  have unit := fr.nonUnit
  have atom := fr.single
  have nonInv (n) : ¬EquivB (env .fresh) (s.product.inv n) := fun eq => fr.nonInv eq.head_eq
  let base := env .base
  have rebuild {p v : Term sig} (hp : HasSort p .msg) (hv : HasSort v .msg)
      (ny : Normal (ruleRoot T.rules) (s.power base p)) (nv : Normal (ruleRoot T.rules) v)
      (unit : head v ≠ .free s.one) : Normal (ruleRoot T.rules) (s.power base v) := by
    obtain ⟨nb,_,noPow,noNeutral,_⟩ := (pow.normal_iff (h.typed .base) hp).mp ny
    exact (pow.normal_iff (h.typed .base) hv).mpr ⟨nb,nv,noPow,noNeutral,unit⟩
  cases k with
  | unchanged =>
    apply (pow.normal_iff (h.typed .peer) (h.typed .fresh)).mpr
    refine ⟨h.normal .peer,h.normal .fresh,?_,?_,unit⟩
    · intro hd; obtain ⟨a,b,eq⟩ := splitPower s hd; exact h.guard.1 a b eq
    · intro hd; exact h.guard.2 (nullary s.neutralArity hd)
  | neutral => exact original
  | cancelAll => exact h.normal .base
  | tower =>
    have np := (pow.normal_iff (h.typed .base) (h.typed .pos)).mp original
    have c := clean_of_normal E.presentation (h.typed .pos) (h.normal .pos) (fun e => np.2.2.2.2 e.head_eq)
    have plus := c.extend atom (fun e => unit e.head_eq) nonInv h.guard
    exact rebuild (h.typed .pos) (mulTyped s (h.typed .pos) (h.typed .fresh)) original
      (cleanMul mul plus (h.normal .pos) (h.normal .fresh)) (fun e => by cases e)
  | cancelPositive =>
    have hp := (Expr.mul p (.inv DHPeer.r)).sorted s env h.typed
    have np := ((pow.normal_iff (h.typed .base) hp).mp original).2.1
    refine rebuild hp (h.typed .pos) original (h.normal .pos) ?_
    intro hd
    have eq := nullary s.oneArity hd
    have red := E.presentation.unitRule (s.product.inv (env .fresh)) ((Expr.inv DHPeer.r).sorted s env h.typed)
    exact np _ ⟨_,_,(EquivB.ac_congr _ (eq ▸ EquivB.refl _) (.refl _)).trans (.ac_swap ..),.root red,.refl _⟩
  | cancelMixed =>
    have hp := (Expr.mul p (.inv (.mul n DHPeer.r))).sorted s env h.typed
    have np := ((pow.normal_iff (h.typed .base) hp).mp original).2.1
    exact rebuild hp ((Expr.mul p (.inv n)).sorted s env h.typed) original (mixedNormal mul inv hp (h.typed .fresh) np) (fun eq => by cases eq)
  | cancelNegative =>
    have hp := (Expr.inv (.mul n DHPeer.r)).sorted s env h.typed
    have np := ((pow.normal_iff (h.typed .base) hp).mp original).2.1
    exact rebuild hp ((Expr.inv n).sorted s env h.typed) original (inv.shrink (h.typed .fresh) np) (invNotOne s _)

theorem classifiedNormal [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E) {Y r k env}
    (h : Realizes s (ruleRoot T.rules) Y r k env) (hr : HasSort r .fresh) :
    Normal (ruleRoot T.rules) (k.pair.2.eval s env) :=
  classifiedNormalFactor pow mul inv h (.of_fresh s hr)

end Tamarin.Rewriting.DHPeer
