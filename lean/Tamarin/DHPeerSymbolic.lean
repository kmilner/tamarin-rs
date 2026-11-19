import Tamarin.DHPeerProduct
import Tamarin.DHPeerTuple

/-! Normality of the symbolic DH peer branches follows from the actual
power, inverse, and multiplication buckets and the distinct witness names. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants Cancellation DHProduct
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private structure Positive (s : Symbols sig) (t : Term sig) : Prop where
  unit : classOf s.product.one ∉ Cancellation.flatten s.mul t
  inverse : ∀ n, classOf (s.product.inv n) ∉ Cancellation.flatten s.mul t

private theorem positive_factor {t : Term sig} (h : Factor s t) : Positive s t where
  unit mem := by
    rw [h.single] at mem
    have eq : EquivB s.product.one t := Quotient.exact (List.mem_singleton.mp mem)
    exact h.nonUnit eq.head_eq.symm
  inverse n mem := by
    rw [h.single] at mem
    have eq : EquivB (s.product.inv n) t := Quotient.exact (List.mem_singleton.mp mem)
    exact h.nonInv eq.head_eq.symm

private theorem positive_mul {a b : Term sig} (ha : Positive s a) (hb : Positive s b) : Positive s (.ac s.mul a b) where
  unit := by simpa [Cancellation.flatten_ac] using And.intro ha.unit hb.unit
  inverse n := by simpa [Cancellation.flatten_ac] using And.intro (ha.inverse n) (hb.inverse n)

private theorem notVar {f : sig.FreeSym} {args : Fin (sig.arity f) → Term sig} {v} :
    classOf (.free f args) ≠ classOf (.var v) := by
  intro eq; cases (Quotient.exact eq).head_eq

private theorem pureClean {t : Term sig} (h : Positive s t) :
    Clean s.product (Cancellation.flatten s.mul t) where
  noUnit := h.unit
  oneInverse n _ _ perm := h.inverse n (perm.mem_iff.mpr List.mem_cons_self)
  disjoint n mem := False.elim (h.inverse n mem)

private theorem positiveInv {t : Term sig} (bucket : InverseBucket E) (positive : Positive s t)
    (nt : Normal (ruleRoot T.rules) t) : Normal (ruleRoot T.rules) (s.product.inv t) := by
  apply normal_free_no_root (fun _ => nt)
  rintro ys hy out ⟨eq,mem,σ,hp,_⟩
  have here : head eq.lhs = .free s.inv :=
    (instance_head eq (bucket.1 eq mem) σ).symm.trans (congrArg head hp).symm
  obtain ⟨k,hk,rfl⟩ := bucket.2 eq mem here
  let env (i : Fin 3) := σ.apply (.var (E.actual k i))
  have key : EquivB (s.product.inv t) (k.equation.1.eval s env) := by
    have align : EquivB (s.product.inv t) (.free s.inv ys) := .free _ _ _ hy
    rw [hp] at align
    simpa [ExtraRule.instantiate, Expr.subst_eval,env] using align
  let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  rcases hk with rfl|rfl|rfl
  · have arg : EquivB t (s.product.inv (env 0)) := (Matching.free_equiv_iff ..).mp key i
    exact positive.inverse _ ((Cancellation.flatten_equiv s.mul arg).mem_iff.mpr (List.mem_singleton_self _))
  · have arg : EquivB t s.product.one := (Matching.free_equiv_iff ..).mp key i
    exact positive.unit ((Cancellation.flatten_equiv s.mul arg).mem_iff.mpr (List.mem_singleton_self _))
  · have arg : EquivB t (.ac s.mul (s.product.inv (env 0)) (env 1)) := (Matching.free_equiv_iff ..).mp key i
    apply positive.inverse (env 0) ((Cancellation.flatten_equiv s.mul arg).mem_iff.mpr ?_)
    rw [Cancellation.flatten_ac]
    exact List.mem_append_left _ (List.mem_singleton_self _)

/-- Any irreducible product without units or inverse factors remains normal
under a single outer inversion in the active DH inventory. -/
theorem InverseBucket.normal_positive (bucket : InverseBucket E) {t : Term sig}
    (nt : Normal (ruleRoot T.rules) t) (noUnit : classOf s.product.one ∉ Cancellation.flatten s.mul t)
    (noInv : ∀ u, classOf (s.product.inv u) ∉ Cancellation.flatten s.mul t) :
    Normal (ruleRoot T.rules) (s.product.inv t) :=
  positiveInv bucket ⟨noUnit,noInv⟩ nt

private theorem unary {u v : Term sig} (e : EquivB (s.product.inv u) (s.product.inv v)) : EquivB u v :=
  (Matching.free_equiv_iff ..).mp e ⟨0,by rw [s.invArity]; decide⟩

private theorem mixedClean {v : Variable} {t : Term sig} (positive : Positive s t)
    (apart : classOf (.var v : Term sig) ∉ Cancellation.flatten s.mul t) :
    Clean s.product [classOf (.var v),classOf (s.product.inv t)] := by
  constructor
  · intro h
    rcases List.mem_cons.mp h with h|h
    · exact notVar h
    · have eq := Head.free.inj (Quotient.exact (List.mem_singleton.mp h)).head_eq
      have one := s.oneArity
      rw [eq] at one
      have := s.invArity
      omega
  · intro n m rest perm
    have len := perm.length_eq
    simp at len
    have hv := perm.mem_iff.mp List.mem_cons_self
    simp [len] at hv
    rcases hv with h|h <;> exact notVar h.symm
  · intro n hinv k hk matched
    rcases List.mem_cons.mp hinv with h|h
    · exact notVar h
    · have eq := unary (Quotient.exact (List.mem_singleton.mp h))
      have mem := (Cancellation.flatten_equiv s.mul eq).mem_iff.mp hk
      rcases List.mem_cons.mp matched with e|e
      · exact apart (e ▸ mem)
      · exact positive.inverse t ((List.mem_singleton.mp e) ▸ mem)

private theorem varClass (q : Names) {i j : Slot}
    (same : classOf (q.symbolic (sig := sig) i) = classOf (q.symbolic j)) : i = j :=
  q.distinct i j (Head.var.inj (Quotient.exact same).head_eq)

/-- Empty root buckets establish normality of the actual unit and neutral
constants using the same live-table inventory as the power rules. -/
theorem normalConstant (rules : List (Equation sig)) (apps : ∀ eq ∈ rules, Application eq.lhs)
    (f : sig.FreeSym) (nullary : sig.arity f = 0)
    (empty : ∀ eq ∈ rules, head eq.lhs ≠ .free f) :
    Normal (ruleRoot rules) (.free f fun i => Fin.elim0 (nullary ▸ i)) := by
  apply normal_free_no_root (fun i => Fin.elim0 (nullary ▸ i))
  rintro ys _ out ⟨eq,mem,σ,align,_⟩
  exact empty eq mem ((instance_head eq (apps eq mem) σ).symm.trans (congrArg head align).symm)

/-- Both terms in each template are normal under the full live rule table.
Only the three witnesses need distinct names disjoint from the query variables.
The neutral constructor is admitted when its active root bucket is empty. -/
theorem symbolicNormalFactor [DecidableEq sig.ACSym] (power : PowerBucket T) (inverse : InverseBucket E)
    (mult : MulBucket E) (neutral : Normal (ruleRoot T.rules) s.neutralTerm)
    (q : Names) (t : Term sig) (ht : HasSort t .msg) (nt : Normal (ruleRoot T.rules) t)
    (factor : Factor s t) (apart : ¬EquivB (q.symbolic .pos) t) (k : Branch) :
    let env i := if i = .fresh then t else q.symbolic i
    Normal (ruleRoot T.rules) (k.pair.1.eval s env) ∧ Normal (ruleRoot T.rules) (k.pair.2.eval s env) := by
  let env (i : Slot) := if i = .fresh then t else q.symbolic i
  let N (e : Expr Slot) := Normal (ruleRoot T.rules) (e.eval s env)
  let unitless (e : Expr Slot) := head (e.eval s env) ≠ .free s.one
  have sorted (i : Slot) : HasSort (env i) .msg := by unfold env; split <;> first | exact ht | exact q.typed _
  have norm (i : Slot) : N (.var i) := by
    change Normal _ (if _ then t else q.symbolic i)
    split <;> first | exact nt | exact (constructor_normal _ power.1).1 _
  have leaf (i : Slot) : Factor s (env i) := by
    unfold env; split
    · exact factor
    · exact (by constructor <;> intro e <;> cases e)
  have pos (i : Slot) := positive_factor (leaf i)
  have pairPos (i j : Slot) := positive_mul (pos i) (pos j)
  have pureN (i j : Slot) : N (.mul (.var i) (.var j)) :=
    cleanMul mult (pureClean (pairPos i j)) (norm i) (norm j)
  have negN (i : Slot) : N (.inv (.var i)) := positiveInv inverse (pos i) (norm i)
  have bothN : N (.inv (.mul n r)) := positiveInv inverse (pairPos .neg .fresh) (pureN _ _)
  have mixed (e : Expr Slot) (positive : Positive s (e.eval s env))
      (disjoint : classOf (q.symbolic .pos) ∉ Cancellation.flatten s.mul (e.eval s env))
      (hn : N (.inv e)) : N (.mul p (.inv e)) := by
    apply cleanMul mult _ (norm .pos) hn
    change Clean s.product (Cancellation.flatten s.mul (.ac s.mul _ _))
    rw [Cancellation.flatten_ac]; exact mixedClean positive disjoint
  have apartN : classOf (q.symbolic .pos) ∉ Cancellation.flatten s.mul (env .neg) :=
    fun mem => by have eq := varClass q (i := .pos) (j := .neg) (List.mem_singleton.mp mem); cases eq
  have apartR : classOf (q.symbolic .pos) ∉ Cancellation.flatten s.mul (env .fresh) := by
    change _ ∉ Cancellation.flatten s.mul t
    rw [factor.single]; exact fun mem => apart (Quotient.exact (List.mem_singleton.mp mem))
  have bothApart : classOf (q.symbolic .pos) ∉ Cancellation.flatten s.mul ((Expr.mul n r).eval s env) := by
    change _ ∉ Cancellation.flatten s.mul (.ac s.mul _ _)
    rw [Cancellation.flatten_ac]
    exact fun mem => (List.mem_append.mp mem).elim apartN apartR
  have invOne (e : Expr Slot) : unitless (.inv e) := by
    intro h
    have eq := Head.free.inj h
    have ar := s.invArity
    rw [eq] at ar
    have := s.oneArity
    omega
  have powN (i : Slot) (other : i ≠ .fresh) (e : Expr Slot) (hn : N e) (h : unitless e) : N (.pow (.var i) e) := by
    apply (power.normal_iff (sorted i) (e.sorted s _ sorted)).mpr
    have base : env i = q.symbolic i := ite_eq_right other
    refine ⟨norm i,hn,?_,?_,h⟩ <;> rw [base] <;> intro bad <;> cases bad
  cases k with
  | unchanged => exact ⟨norm _,powN _ (by decide) r (norm _) (leaf _).nonUnit⟩
  | neutral => exact ⟨neutral,neutral⟩
  | tower => exact ⟨powN _ (by decide) p (norm _) (leaf _).nonUnit,
      powN _ (by decide) (.mul p r) (pureN _ _) (fun h => by cases h)⟩
  | cancelPositive => exact ⟨powN _ (by decide) (.mul p (.inv r))
      (mixed r (pos _) apartR (negN _)) (fun h => by cases h),
      powN _ (by decide) p (norm _) (leaf _).nonUnit⟩
  | cancelAll => exact ⟨powN _ (by decide) (.inv r) (negN _) (invOne _),norm _⟩
  | cancelMixed => exact ⟨powN _ (by decide) (.mul p (.inv (.mul n r)))
      (mixed (.mul n r) (pairPos _ _) bothApart bothN) (fun h => by cases h),
      powN _ (by decide) (.mul p (.inv n)) (mixed n (pos _) apartN (negN _)) (fun h => by cases h)⟩
  | cancelNegative => exact ⟨powN _ (by decide) (.inv (.mul n r)) bothN (invOne _),
      powN _ (by decide) (.inv n) (negN _) (invOne _)⟩

theorem symbolicNormal [DecidableEq sig.ACSym] (power : PowerBucket T) (inverse : InverseBucket E)
    (mult : MulBucket E) (neutral : Normal (ruleRoot T.rules) s.neutralTerm) (q : Names) (k : Branch) :
    Normal (ruleRoot T.rules) (k.pair.1.eval s q.symbolic) ∧
    Normal (ruleRoot T.rules) (k.pair.2.eval s q.symbolic) := by
  have eq : (fun i => if i = .fresh then q.symbolic (sig := sig) .fresh else q.symbolic i) = q.symbolic := by
    funext i; split <;> simp_all
  have h := symbolicNormalFactor power inverse mult neutral q (q.symbolic .fresh) (q.typed _)
    ((constructor_normal _ power.1).1 _) (by constructor <;> intro e <;> cases e)
    (fun e => by have eq := varClass q (i := .pos) (j := .fresh) (Quotient.sound e); cases eq) k
  simpa only [eq] using h

end Tamarin.Rewriting.DHPeer
