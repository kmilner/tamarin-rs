import Tamarin.DHProductUnique
import Tamarin.NarrowingFrontier

/-! Signed group reductions strictly decrease the number of nodes when
every opaque operand is irreducible in the live theory. -/
namespace Tamarin.Rewriting.DHPeer.Balance
open ConstructorVariants Cancellation FiniteOccurs
variable {α : Type} {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem inv_size (s : Symbols sig) (x : Term sig) : nodes (s.product.inv x) = nodes x + 1 := by
  change (List.ofFn (fun _ : Fin (sig.arity s.inv) => nodes x)).sum + 1 = _
  have one := s.invArity
  generalize sig.arity s.inv = m at one ⊢
  subst m; simp [List.ofFn_succ]

private theorem mul_size (s : Symbols sig) (x y : Term sig) :
    nodes (s.product.mul x y) = nodes x + nodes y + 1 := rfl

private theorem one_size (s : Symbols sig) : nodes s.product.one = 1 := by
  change (List.ofFn (fun i => nodes (Fin.elim0 (s.oneArity ▸ i) : Term sig))).sum + 1 = 1
  have empty {α : Type} {n} (h : n = 0) (f : Fin n → α) : List.ofFn f = [] := by subst n; simp
  rw [empty s.oneArity]; rfl

private def weight : Expr α → (α → Nat) → Nat
  | .var i, w => w i
  | .one, _ | .neutral, _ => 1
  | .inv a, w => weight a w + 1
  | .mul a b, w | .pow a b, w => weight a w + weight b w + 1

private theorem group_weight (s : Symbols sig) (e : Expr α) (env : α → Term sig) :
    nodes (e.eval s env) = weight e (fun i => nodes (env i)) := by
  induction e with
  | var => rfl
  | one => exact one_size s
  | neutral =>
    change (List.ofFn (fun i => nodes (Fin.elim0 (s.neutralArity ▸ i) : Term sig))).sum + 1 = 1
    have empty {α : Type} {n} (h : n = 0) (f : Fin n → α) : List.ofFn f = [] := by subst n; simp
    rw [empty s.neutralArity]; rfl
  | mul a b l r =>
    exact (mul_size s _ _).trans (by simp [weight,l,r])
  | inv a h => exact (inv_size s _).trans (by simp [weight,h])
  | pow a b l r =>
    change (List.ofFn (fun i : Fin (sig.arity s.pow) => nodes (if i.val = 0 then a.eval s env else b.eval s env))).sum + 1 = _
    have two := s.powArity
    generalize sig.arity s.pow = m at two ⊢
    subst m
    simp [List.ofFn_succ,weight,l,r]

private theorem standard_size (s : Symbols sig) (r : Rule) (env : Fin 3 → Term sig)
    (h : r = .inverse ∨ r = .inverseRest ∨ r = .inside ∨ r = .insideRest) :
    nodes (r.equation.2.eval s env) < nodes (r.equation.1.eval s env) := by
  rw [group_weight,group_weight]
  rcases h with rfl|rfl|rfl|rfl <;> simp [Rule.equation,weight] <;> omega

private theorem extra_size (s : Symbols sig) (r : ExtraRule) (env : Fin 3 → Term sig) :
    nodes (r.equation.2.eval s env) < nodes (r.equation.1.eval s env) := by
  rw [group_weight,group_weight]
  cases r <;> simp [ExtraRule.equation,weight] <;> omega

private def Measured (s : Symbols sig) (R : Root sig) (t : Term sig) :=
  ∃ z, read s R (classOf s.product.one) t = some z

private theorem root_decreases (table : Inventory E) {a b : Term sig} (root : ruleRoot T.rules a b)
    (meas : Measured s (ruleRoot T.rules) a) : nodes b < nodes a ∧ HasSort b .msg := by
  by_cases hd : head a = .ac s.mul ∨ head a = .free s.inv ∨ head a = .free s.one
  · obtain ⟨eq,mem,ρ,rfl,rfl⟩ := root
    rw [instance_head eq (table.1 eq mem) ρ] at hd
    rcases table.2 _ mem hd with ⟨r,tag,rfl⟩|⟨r,rfl⟩
    · let env j := ρ.apply (.var (T.actual r j))
      simp only [Rule.instantiate,Expr.subst_eval]
      exact ⟨standard_size s r env tag,r.equation.2.sorted s env (fun i => T.actualSort r i ▸ ρ.sorted _)⟩
    · let env j := ρ.apply (.var (E.actual r j))
      simp only [ExtraRule.instantiate,Expr.subst_eval]
      exact ⟨extra_size s r env,r.equation.2.sorted s env (fun i => E.sorted r i ▸ ρ.sorted _)⟩
  · obtain ⟨z,h⟩ := meas
    have nn : ¬Normal (ruleRoot T.rules) a := fun n => n _ ⟨_,_,.refl _,.root root,.refl _⟩
    simp [read_alien s _ _ _ (fun e => hd (.inl e)) (fun e => hd (.inr (.inl e)))
      (fun e => hd (.inr (.inr e))),alien,nn] at h

private theorem inv_sorted (s : Symbols sig) {t : Term sig} (typed : HasSort t .msg) :
    HasSort (s.product.inv t) .msg := by
  rw [← s.invSort]; apply HasSort.free; intro i; simpa only [s.invInput] using typed

private theorem mul_sorted (s : Symbols sig) {a b : Term sig} (l : HasSort a .msg) (r : HasSort b .msg) :
    HasSort (s.product.mul a b) .msg := s.mulSort ▸ HasSort.ac _ _ _ (s.mulSort ▸ l) (s.mulSort ▸ r)

private theorem step_decreases (table : Inventory E) {a b : Term sig} (step : Step (ruleRoot T.rules) a b)
    (meas : Measured s (ruleRoot T.rules) a) (typed : HasSort a .msg) : nodes b < nodes a ∧ HasSort b .msg := by
  have alienStep {p q : Term sig} (st : Step (ruleRoot T.rules) p q) (m : Measured s (ruleRoot T.rules) p)
      (hm : head p ≠ .ac s.mul) (hi : head p ≠ .free s.inv) (ho : head p ≠ .free s.one) : False := by
    obtain ⟨z,hz⟩ := m
    have nn : ¬Normal (ruleRoot T.rules) p := fun n => n q ⟨_,_,.refl _,st,.refl _⟩
    simp [read_alien s _ _ _ hm hi ho,alien,nn] at hz
  induction step with
  | root root => exact root_decreases table root meas
  | @free f xs i u st ih =>
    by_cases inv : f = s.inv
    · subst f
      have all (j : Fin (sig.arity s.inv)) : j = i := Fin.ext (by have := s.invArity; omega)
      have ex : (Term.free s.inv xs) = s.product.inv (xs i) := congrArg (Term.free s.inv) (funext fun j => congrArg xs (all j))
      have ey : (Term.free s.inv fun j => if j = i then u else xs j) = s.product.inv u := by
        apply congrArg (Term.free s.inv); funext j; simp [all j]
      rw [ex] at meas typed ⊢
      rw [ey,inv_size,inv_size]
      obtain ⟨z,h⟩ := meas
      rw [read_inv] at h
      cases hm : read s (ruleRoot T.rules) (classOf s.product.one) (xs i) with
      | none => simp [hm,minus] at h
      | some val =>
        obtain ⟨sm,su⟩ := ih ⟨val,hm⟩ (E.presentation.invChild _ typed)
        exact ⟨by omega,inv_sorted s su⟩
    · by_cases one : f = s.one
      · subst f; exact Fin.elim0 (s.oneArity ▸ i)
      · exact (alienStep (.free f xs i st) meas (by intro e; cases e)
          (fun e => inv (Head.free.inj e)) (fun e => one (Head.free.inj e))).elim
  | @ac_left f a b c st ih | @ac_right f c a b st ih =>
    by_cases mul : f = s.mul
    · subst f
      have ok := Term.checkSort_complete typed
      simp only [Term.checkSort,Bool.and_eq_true,s.mulSort] at ok
      obtain ⟨z,h⟩ := meas
      simp only [read,ite_true] at h
      cases hm : read s (ruleRoot T.rules) (classOf s.product.one) a with
      | none => cases hc : read s (ruleRoot T.rules) (classOf s.product.one) c <;> simp [hc,hm,plus] at h
      | some v =>
        have result := ih ⟨v,hm⟩ (Term.checkSort_sound _ _ (by first | exact ok.1.2 | exact ok.2))
        constructor
        · simp only [show ∀ l r : Term sig, nodes (.ac s.mul l r) = nodes l + nodes r + 1 from fun _ _ => rfl]
          have := result.1
          omega
        · first | exact mul_sorted s result.2 (Term.checkSort_sound _ _ ok.2)
                | exact mul_sorted s (Term.checkSort_sound _ _ ok.1.2) result.2
    · apply False.elim
      apply alienStep (by first | exact Step.ac_left f c st | exact Step.ac_right f c st) meas
      · exact fun e => mul (Head.ac.inj e)
      all_goals intro e; cases e
  | comm_left f c st _ | comm_right f c st _ =>
    apply False.elim
    apply alienStep (by first | exact Step.comm_left f c st | exact Step.comm_right f c st) meas
    all_goals intro e; cases e

private theorem transport {t u : Term sig} (e : EquivB t u) (ht : HasSort t .msg) : HasSort u .msg :=
  Term.checkSort_sound _ _ (SortClash.check_equiv e _ ▸ Term.checkSort_complete ht)

/-- Signed reductions preserve message sorting at every intermediate state,
including opaque factors exposed by intermediate simplifications. -/
theorem Inventory.reduces_sorted (table : Inventory E) {t u : Term sig}
    (typed : HasSort t .msg) (reads : ∃ z, read s (ruleRoot T.rules) (classOf s.product.one) t = some z)
    (red : Reduces (ruleRoot T.rules) t u) : HasSort u .msg := by
  obtain ⟨z,hz⟩ := reads
  let P (a : Term sig) := HasSort a .msg ∧ read s (ruleRoot T.rules) (classOf s.product.one) a = some z
  exact (RootNarrowing.reduction_invariant P (fun h eq =>
    ⟨transport eq h.1,(equiv s _ _ eq).symm.trans h.2⟩) (fun h st => by
      obtain ⟨a,c,pre,raw,post⟩ := st
      obtain ⟨_,sc⟩ := step_decreases table raw ⟨z,(equiv s _ _ pre).symm.trans h.2⟩ (transport pre h.1)
      exact ⟨transport post sc,table.reduces _ (.step ⟨a,c,pre,raw,post⟩) z h.2⟩) red ⟨typed,hz⟩).1

/-- Existence for an arbitrary signed term. One defined reading already
ensures that every encountered opaque operand is normal. No positivity,
linearity, or restriction on rules at other heads is required. -/
theorem Inventory.normal_exists (table : Inventory E) {t : Term sig}
    (typed : HasSort t .msg) (reads : ∃ z, read s (ruleRoot T.rules) (classOf s.product.one) t = some z) :
    ∃ n, Reduces (ruleRoot T.rules) t n ∧ Normal (ruleRoot T.rules) n ∧ HasSort n .msg := by
  induction h : nodes t using Nat.strongRecOn generalizing t with
  | ind k ih =>
    by_cases hn : Normal (ruleRoot T.rules) t
    · exact ⟨t,.basis (.refl _),hn,typed⟩
    · obtain ⟨b,hit⟩ : ∃ b, StepModulo (ruleRoot T.rules) t b :=
        Classical.byContradiction fun nope => hn fun b step => nope ⟨b,step⟩
      obtain ⟨a,c,pre,st,post⟩ := hit
      obtain ⟨z,hz⟩ := reads
      have atA : Measured s (ruleRoot T.rules) a := ⟨z,(equiv s _ _ pre).symm.trans hz⟩
      have ⟨smaller,sc⟩ := step_decreases table st atA (transport pre typed)
      have short : nodes b < k := by rw [← h,nodes_equiv pre,← nodes_equiv post]; exact smaller
      have edge : Reduces (ruleRoot T.rules) t b := .step ⟨_,_,pre,st,post⟩
      obtain ⟨n,red,norm,sn⟩ := ih (nodes b) short (transport post sc) ⟨z,table.reduces _ edge z hz⟩ rfl
      exact ⟨n,edge.trans red,norm,sn⟩

end Tamarin.Rewriting.DHPeer.Balance
