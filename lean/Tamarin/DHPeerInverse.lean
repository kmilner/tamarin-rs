import Tamarin.DHPeerClassification
import Tamarin.RootNormalForms
import Tamarin.DHProductNormal

/-! Removing one factor from a normalized negative product cannot expose a
new inverse redex. The inversion bucket contains the exact three active
rules at that head. Rules with other heads enter only through normality of
the original term and the product-unit rule. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig}

/-- The remaining six equations of the thirteen-rule DH presentation. -/
inductive ExtraRule where
  | mulOne | invInv | invOne | join | pull | joinRest
  deriving DecidableEq

def ExtraRule.equation : ExtraRule → Expr (Fin 3) × Expr (Fin 3)
  | .mulOne => (.mul (.var 0) .one, .var 0)
  | .invInv => (.inv (.inv (.var 0)), .var 0)
  | .invOne => (.inv .one, .one)
  | .join => (.mul (.inv (.var 0)) (.inv (.var 1)), .inv (.mul (.var 0) (.var 1)))
  | .pull => (.inv (.mul (.inv (.var 0)) (.var 1)), .mul (.var 0) (.inv (.var 1)))
  | .joinRest => (.mul (.inv (.var 0)) (.mul (.inv (.var 1)) (.var 2)),
      .mul (.inv (.mul (.var 0) (.var 1))) (.var 2))

def ExtraRule.instantiate (r : ExtraRule) (s : Symbols sig) (env : Fin 3 → Term sig) : Equation sig :=
  ⟨r.equation.1.eval s env, r.equation.2.eval s env⟩

structure ExtraTable (T : Table s) where
  actual : ExtraRule → Fin 3 → Variable
  sorted : ∀ r i, (actual r i).sort = .msg
  distinct : ∀ r i j, actual r i = actual r j → i = j
  present : ∀ r : ExtraRule, r.instantiate s (fun i => .var (actual r i)) ∈ T.rules

theorem ExtraTable.fireRoot {T : Table s} (E : ExtraTable T) (r : ExtraRule)
    (values : Fin 3 → Term sig) (typed : ∀ i, HasSort (values i) .msg) :
    ruleRoot T.rules (r.instantiate s values).lhs (r.instantiate s values).rhs :=
  fireSchema _ _ _ (E.sorted r) (E.distinct r) (E.present r) values typed

def InverseBucket {T : Table s} (E : ExtraTable T) : Prop :=
  (∀ eq ∈ T.rules, Application eq.lhs) ∧
  ∀ eq ∈ T.rules, head eq.lhs = .free s.inv →
    ∃ k : ExtraRule, (k = .invInv ∨ k = .invOne ∨ k = .pull) ∧
      eq = k.instantiate s (fun i => .var (E.actual k i))

private theorem unary {a b : Term sig} (h : EquivB (s.product.inv a) (s.product.inv b)) : EquivB a b :=
  (Matching.free_equiv_iff ..).mp h ⟨0,by rw [s.invArity]; decide⟩

private theorem congrInv {a b : Term sig} (h : EquivB a b) : EquivB (s.product.inv a) (s.product.inv b) :=
  .free _ _ _ (fun _ => h)

private def args (a b : Term sig) (i : Fin 3) := if i = 0 then a else b

private theorem argsSorted {a b : Term sig} (ha : HasSort a .msg) (hb : HasSort b .msg) :
    ∀ i, HasSort (args a b i) .msg := by intro i; unfold args; split <;> assumption

theorem InverseBucket.shrink {T : Table s} {E : ExtraTable T} (bucket : InverseBucket E) {v r : Term sig}
    (typed : HasSort r .msg) (normal : Normal (ruleRoot T.rules) (s.product.inv (s.product.mul v r))) :
    Normal (ruleRoot T.rules) (s.product.inv v) := by
  let idx : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  have productN : Normal (ruleRoot T.rules) (s.product.mul v r) := normal_free_child s.inv _ normal idx
  have nv := (normal_ac_children _ productN).1
  apply normal_free_no_root (fun _ => nv)
  rintro ys hy out ⟨eq,mem,σ,hp,_⟩
  have atInv : head eq.lhs = .free s.inv := (instance_head eq (bucket.1 eq mem) σ).symm.trans
    (congrArg head hp).symm
  obtain ⟨k,hk,rfl⟩ := bucket.2 eq mem atInv
  let env (i : Fin 3) := σ.apply (.var (E.actual k i))
  have sort (i : Fin 3) : HasSort (env i) .msg := E.sorted k i ▸ σ.sorted _
  have key : EquivB (s.product.inv v) (k.equation.1.eval s env) := by
    have e : EquivB (s.product.inv v) (.free s.inv ys) := .free _ _ _ hy
    rw [hp] at e
    simpa [ExtraRule.instantiate, Expr.subst_eval, env] using e
  have pull (x y : Term sig) (hx : HasSort x .msg) (hy : HasSort y .msg)
      (eq : EquivB (s.product.mul v r) (s.product.mul (s.product.inv x) y)) : False :=
    normal _ ⟨_,_,congrInv eq,.root (E.fireRoot .pull _ (argsSorted hx hy)),.refl _⟩
  rcases hk with rfl | rfl | rfl
  · exact pull (env 0) r (sort 0) typed (.ac_congr _ (unary key) (.refl _))
  · have swap := (EquivB.ac_congr s.mul (unary key) (.refl r)).trans (.ac_swap ..)
    exact productN _ ⟨_,_,swap,.root (E.fireRoot .mulOne _ (argsSorted typed typed)),.refl _⟩
  · have both : HasSort (s.product.mul (env 1) r) .msg :=
      s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ sort 1) (s.mulSort ▸ typed)
    exact pull (env 0) _ (sort 0) both ((EquivB.ac_congr _ (unary key) (.refl _)).trans (.ac_assoc ..))

/-- The single shared inverse factor loses one occurrence. No collision can
appear with the positive factors of the old normal product. -/
theorem cleanShrink [DecidableEq sig.ACSym] {u v r : Term sig}
    (larger : ∀ a, FiniteOccurs.nodes a < FiniteOccurs.nodes (s.product.inv a))
    (old : DHProduct.Clean s.product
      (Cancellation.flatten s.mul (s.product.mul u (s.product.inv (s.product.mul v r))))) :
    DHProduct.Clean s.product (Cancellation.flatten s.mul (s.product.mul u (s.product.inv v))) := by
  classical
  let xs := Cancellation.flatten s.mul u
  let neg (t : Term sig) := Cancellation.classOf (s.product.inv t)
  let oldNeg := s.product.mul v r
  change DHProduct.Clean s.product (Cancellation.flatten s.mul (.ac s.mul u _)) at old ⊢
  simp only [Cancellation.flatten_ac] at old ⊢
  change DHProduct.Clean s.product (xs ++ [neg oldNeg]) at old
  change DHProduct.Clean s.product (xs ++ [neg v])
  have noInv (n : Term sig) : neg n ∉ xs := by
    intro occupied
    have perm := (List.perm_cons_erase occupied).append_right [neg oldNeg]
    apply old.oneInverse n oldNeg (xs.erase (neg n))
    exact perm.trans ((List.perm_append_comm (l₁ := xs.erase (neg n)) (l₂ := [neg oldNeg])).cons _)
  have one : Cancellation.classOf s.product.one ≠ neg v := by
    intro h
    have eq := Head.free.inj (Quotient.exact h).head_eq
    have ar := s.oneArity
    rw [eq,s.invArity] at ar
    contradiction
  constructor
  · intro unit
    rcases List.mem_append.mp unit with h | h
    · exact old.noUnit (List.mem_append_left _ h)
    · exact one (List.mem_singleton.mp h)
  · intro n m rest perm
    have p := (List.perm_append_comm (l₁ := [neg v]) (l₂ := xs)).trans perm
    change (neg v :: xs).Perm (neg n :: neg m :: rest) at p
    have eq : neg n = neg v := (List.mem_cons.mp (p.mem_iff.mpr List.mem_cons_self)).resolve_right (noInv n)
    rw [eq] at p
    exact noInv m (p.cons_inv.mem_iff.mpr List.mem_cons_self)
  · intro n present k inside live
    have eq : neg n = neg v := List.mem_singleton.mp ((List.mem_append.mp present).resolve_left (noInv n))
    have inV := (Cancellation.flatten_equiv s.mul (unary (Quotient.exact eq))).mem_iff.mp inside
    have inBoth : k ∈ Cancellation.flatten s.mul oldNeg := by simp [oldNeg,DHProduct.Ops.mul,Cancellation.flatten_ac,inV,Symbols.product]
    rcases List.mem_append.mp live with hx | added
    · exact old.disjoint oldNeg (by simp [neg]) k inBoth (List.mem_append_left _ hx)
    · obtain rfl := List.mem_singleton.mp added
      rw [DHProduct.classes] at inV
      obtain ⟨z,hz,he⟩ := List.mem_map.mp inV
      have := FiniteOccurs.nodes_equiv (Quotient.exact he)
      have := DHProduct.factor_nodes s.mul v z hz
      have := larger v
      omega

end Tamarin.Rewriting.DHPeer
