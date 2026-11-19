import Tamarin.ContextualReduction
import Tamarin.DHPeerPlain
import Tamarin.DHPeerSymbolic

/-! Recognition of irreducible signed products and inverses after inspecting
the concrete factors of a DH term. Multiplication can rewrite any subbag,
and inversion can pull out an inverse anywhere in its argument's product.
Opaque factors may use other active rules, so their normality is separate. -/
namespace Tamarin.Rewriting.DHPeer.GroupNormal
open ConstructorVariants Cancellation DHProduct
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- The flattened array contains no unit and at most one inverse occurrence.
If one inverse occurs, none of its argument's flattened factors also occurs
in the outer product. Enumeration and membership are modulo B. -/
def ProductGuard (s : Symbols sig) (xs : List (Class sig)) : Prop :=
  classOf s.product.one ∉ xs ∧
    ((∀ n, classOf (s.product.inv n) ∉ xs) ∨
      ∃ n rest, xs.Perm (classOf (s.product.inv n) :: rest) ∧
        (∀ m, classOf (s.product.inv m) ∉ rest) ∧
        ∀ k ∈ flatten s.mul n, k ∉ xs)

/-- Filtering a canonical array for zero, one or multiple inverse entries
implements the signed-product criterion. Repeated equal inverses count as
two separate occurrences. -/
theorem productGuard_iff (xs : List (Class sig)) : ProductGuard s xs ↔ Clean s.product xs := by
  classical
  constructor
  · rintro ⟨unit,h⟩
    refine ⟨unit,?_,?_⟩
    · intro u v tail two
      rcases h with noInv|⟨n,rest,one,noRest,_⟩
      · exact noInv u (two.mem_iff.mpr List.mem_cons_self)
      · have eu := (List.mem_cons.mp ((one.symm.trans two).mem_iff.mpr List.mem_cons_self)).resolve_right (noRest u)
        rw [eu] at two
        exact noRest v ((one.symm.trans two).cons_inv.mem_iff.mpr List.mem_cons_self)
    · intro u existsU k factor
      rcases h with noInv|⟨n,rest,one,noRest,apart⟩
      · exact (noInv u existsU).elim
      · have en := (List.mem_cons.mp (one.mem_iff.mp existsU)).resolve_right (noRest u)
        let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
        have eq : EquivB u n := (Matching.free_equiv_iff ..).mp (Quotient.exact en) i
        exact apart k ((flatten_equiv s.mul eq).mem_iff.mp factor)
  · intro h
    refine ⟨h.noUnit,?_⟩
    by_cases existsInv : ∃ n, classOf (s.product.inv n) ∈ xs
    · obtain ⟨n,mem⟩ := existsInv
      have p := List.perm_cons_erase mem
      exact .inr ⟨n,_,p,fun m hm => h.oneInverse n m _ (p.trans ((List.perm_cons_erase hm).cons _)),h.disjoint n mem⟩
    · exact .inl (fun n hn => existsInv ⟨n,hn⟩)

/-- The root guard alone excludes every multiplication subbag, regardless
of reducible redexes at other heads inside the operands. -/
theorem product_root_iff [DecidableEq sig.ACSym] (bucket : MulBucket E) (x y : Term sig)
    (typed : HasSort (s.product.mul x y) .msg) :
    ProductGuard s (flatten s.mul (s.product.mul x y)) ↔
      ∀ p q, head p = .ac s.mul → Subbag s.mul p (s.product.mul x y) → ¬ruleRoot T.rules p q := by
  rw [productGuard_iff]
  constructor
  · rintro c p q hd ⟨rest,sub⟩ hit
    exact (bucket.inventory p q hd hit).conflict E.presentation.unitFactor E.presentation.invFactor (c.part sub)
  · intro clear
    apply clean_of_blocked E.presentation typed (fun _ _ sub out => clear _ out rfl sub)
    intro e; cases e.head_eq

/-- Multiplication is normal exactly when its opaque operands are normal
and the guard succeeds. Thus any failed guard proves reducibility even
before visiting children. -/
theorem product_iff [DecidableEq sig.ACSym] (bucket : MulBucket E) (x y : Term sig)
    (typed : HasSort (s.product.mul x y) .msg) :
    Normal (ruleRoot T.rules) (s.product.mul x y) ↔
      ProductGuard s (flatten s.mul (s.product.mul x y)) ∧
      ∀ t ∈ ACRepresentation.flatten s.mul (s.product.mul x y), Normal (ruleRoot T.rules) t := by
  rw [product_root_iff bucket x y typed,subgroup_normal_iff s.mul]
  exact and_comm

/-- For a unary inverse the direct argument must differ from the unit, and
neither a single inverse nor a product containing an inverse is allowed. -/
def InverseGuard [DecidableEq sig.ACSym] (s : Symbols sig) (t : Term sig) : Prop :=
  ¬EquivB t s.product.one ∧ ∀ x ∈ ACRepresentation.flatten s.mul t, head x ≠ .free s.inv

private def pairArgs (x y : Term sig) (i : Fin 3) := if i = 0 then x else y

private theorem pairArgs_typed {x y : Term sig} (hx : HasSort x .msg) (hy : HasSort y .msg) :
    ∀ i, HasSort (pairArgs x y i) .msg := by intro i; unfold pairArgs; split <;> assumption

/-- The three inverse rules fire precisely when the guard fails. In the
pull rule the inverse can be selected from anywhere in the AC argument.
This statement is about the outer inverse even when its child is reducible. -/
theorem inverse_root_iff [DecidableEq sig.ACSym] (bucket : InverseBucket E) (t : Term sig)
    (typed : HasSort t .msg) : InverseGuard s t ↔
      ∀ out, ¬ContextualReduction.AtRoot (ruleRoot T.rules) (s.product.inv t) out := by
  let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  constructor
  · rintro ⟨unit,invs⟩ _ ⟨_,_,align,⟨eq,mem,σ,rfl,rfl⟩,_⟩
    have hd := (instance_head eq (bucket.1 eq mem) σ).symm.trans align.head_eq.symm
    obtain ⟨k,hk,rfl⟩ := bucket.2 _ mem hd
    let env (j : Fin 3) := σ.apply (.var (E.actual k j))
    have key : EquivB (s.product.inv t) (k.equation.1.eval s env) := by
      simpa only [ExtraRule.instantiate,Expr.subst_eval] using align
    have block {u} (hm : classOf (s.product.inv u) ∈ flatten s.mul t) : False := by
      rw [DHProduct.classes] at hm
      obtain ⟨a,ha,e⟩ := List.mem_map.mp hm
      exact invs a ha (Quotient.exact e).head_eq
    rcases hk with rfl|rfl|rfl
    · have arg : EquivB t (s.product.inv (env 0)) := (Matching.free_equiv_iff ..).mp key i
      exact block ((flatten_equiv s.mul arg).mem_iff.mpr List.mem_cons_self)
    · exact unit ((Matching.free_equiv_iff ..).mp key i)
    · have arg : EquivB t (.ac s.mul (s.product.inv (env 0)) (env 1)) :=
        (Matching.free_equiv_iff ..).mp key i
      apply block (u := env 0) ((flatten_equiv s.mul arg).mem_iff.mpr ?_)
      rw [flatten_ac]
      exact List.mem_append_left _ List.mem_cons_self
  · intro clear
    have fire {p out} (arg : EquivB t p) (st : ruleRoot T.rules (s.product.inv p) out) : False :=
      clear out ⟨_,out,E.presentation.invCongr arg,st,.refl _⟩
    refine ⟨fun e => fire e (E.fireRoot .invOne _ (pairArgs_typed typed typed)),?_⟩
    intro a ha hd
    obtain ⟨u,rfl⟩ := Balance.splitInv s hd
    have su := E.presentation.invChild u (s.mulSort ▸ ACRepresentation.flatten_hasSort s.mul t
      (s.mulSort ▸ typed) _ ha)
    have mem : classOf (s.product.inv u) ∈ flatten s.mul t := by
      rw [DHProduct.classes]; exact List.mem_map_of_mem ha
    have sub : Subbag s.mul (s.product.inv u) t := by
      classical
      exact ⟨_,List.perm_cons_erase mem⟩
    rcases sub.context with single|⟨rest,rearranged⟩
    · exact fire single (E.fireRoot .invInv _ (pairArgs_typed su su))
    · have sorted := SortClash.check_equiv rearranged .msg ▸ Term.checkSort_complete typed
      simp only [Term.checkSort,Bool.and_eq_true] at sorted
      have restType := s.mulSort ▸ Term.checkSort_sound _ _ sorted.2
      exact fire rearranged (E.fireRoot .pull _ (pairArgs_typed su restType))

theorem inverse_iff [DecidableEq sig.ACSym] (bucket : InverseBucket E) (t : Term sig)
    (typed : HasSort (s.product.inv t) .msg) :
    Normal (ruleRoot T.rules) (s.product.inv t) ↔ InverseGuard s t ∧ Normal (ruleRoot T.rules) t := by
  let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
  rw [inverse_root_iff bucket t (E.presentation.invChild t typed)]
  constructor
  · intro hn
    exact ⟨fun out ⟨p,q,pre,fire,post⟩ => hn out ⟨p,q,pre,.root fire,post⟩,
      normal_free_child s.inv _ hn i⟩
  · rintro ⟨root,child⟩
    apply normal_free_no_root (fun _ => child)
    intro ys eq out fire
    exact root out ⟨_,_,.free _ _ _ eq,fire,.refl _⟩

/-- The exact DH signature gives a nullary unit and an empty unit-headed
rule bucket. There are no arguments left for the caller to check. -/
theorem unit_normal (apps : ∀ eq ∈ T.rules, Application eq.lhs)
    (none : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one) : Normal (ruleRoot T.rules) s.product.one :=
  normalConstant _ apps _ s.oneArity none

end Tamarin.Rewriting.DHPeer.GroupNormal
