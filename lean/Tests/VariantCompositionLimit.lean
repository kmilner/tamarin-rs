import Tamarin.OperatorVariantBounds

/-! f(s(X)) -> g(X) and g(X) -> f(X) each have bounded variants in
isolation. Together they consume arbitrarily long prefixes in an input
to f. No finite covering family can represent all the normalized values. -/
namespace Tamarin.VariantCompositionLimit
open Rewriting MaudeOperations ShortVariantPaths FiniteOccurs

private inductive Op | f | g | s deriving DecidableEq
private abbrev S : Signature where
  FreeSym := Op
  CSym := Empty
  ACSym := Empty
  Atom := Unit
  arity := fun _ => 1
  inputSort := fun _ _ => .msg
  outputSort := fun _ => .msg
  cSort := Empty.elim
  acSort := Empty.elim
  atomSort := fun _ => .msg

private abbrev app (op : Op) (t : Term S) : Term S := .free op (fun _ => t)
private def x : Variable := ⟨0,.msg⟩
private abbrev z : Term S := .atom ()
private def rules : Problem S := [⟨app .f (app .s (.var x)),app .g (.var x)⟩,⟨app .g (.var x),app .f (.var x)⟩]
private def copies : Nat → Term S | 0 => z | n+1 => app .s (copies n)
private theorem typed (n : Nat) : HasSort (copies n) .msg := by
  induction n with
  | zero => exact HasSort.atom (sig := S) ()
  | succ _ ih => exact .free _ _ (fun _ => ih)

private theorem basis_eq {a b : Term S} (h : EquivB a b) : a = b := by
  induction h with
  | refl => rfl
  | symm _ h => exact h.symm
  | trans _ _ l r => exact l.trans r
  | free op xs ys _ hs => exact congrArg (Term.free op) (funext hs)
  | comm_congr f | ac_congr f | comm_swap f | ac_swap f | ac_assoc f => exact nomatch f

private theorem clean (n : Nat) : Normal (ruleRoot rules) (copies n) := by
  induction n with
  | zero =>
    intro _ ⟨_,_,eq,one,_⟩
    cases basis_eq eq
    cases one with
    | root h => obtain ⟨r,hr,σ,e,_⟩ := h; simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
                rcases hr with rfl | rfl <;> cases e
  | succ n ih =>
    apply normal_free_no_root (fun _ => ih)
    rintro ys _ _ ⟨r,hr,σ,e,_⟩
    simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> cases e

private theorem end_normal : Normal (ruleRoot rules) (app .f z) := by
  apply normal_free_no_root (fun _ => clean 0)
  rintro ys eq _ ⟨r,hr,σ,src,_⟩
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · have h := congrFun (eq_of_heq (Term.free.inj src).2) 0
    have l := basis_eq (eq 0)
    exact nomatch l.trans h
  · cases src

private theorem consumes (n : Nat) : Reduces (ruleRoot rules) (app .f (copies n)) (app .f z) := by
  induction n with
  | zero => exact .basis (.refl _)
  | succ n ih =>
    let σ : Substitution S := .binding x (copies n) (typed n)
    have first : ruleRoot rules (app .f (copies (n+1))) (app .g (copies n)) := by
      exact ⟨_,List.mem_cons_self,σ,by rfl,by rfl⟩
    have second : ruleRoot rules (app .g (copies n)) (app .f (copies n)) := by
      exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,σ,by rfl,by rfl⟩
    exact (Reduces.step ⟨_,_,.refl _,.root first,.refl _⟩).trans
      ((Reduces.step ⟨_,_,.refl _,.root second,.refl _⟩).trans ih)

private theorem size_app (op : Op) (t : Term S) : nodes (app op t) = nodes t + 1 := by
  change (List.ofFn (fun _ : Fin 1 => nodes t)).sum + 1 = _
  simp [List.ofFn_succ]

private theorem slow_step {a b : Term S} (st : Step (ruleRoot rules) a b) : nodes a ≤ nodes b + 1 := by
  induction st with
  | root h =>
    obtain ⟨r,hr,σ,rfl,rfl⟩ := h
    simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change nodes (app .f (app .s (σ.image x))) ≤ nodes (app .g (σ.image x)) + 1
      simp [size_app]
    · change nodes (app .g (σ.image x)) ≤ nodes (app .f (σ.image x)) + 1
      simp [size_app]
  | free op xs i st ih =>
    have unique (j : Fin (S.arity op)) : j = i := Subsingleton.elim _ _
    change (List.ofFn (fun j => nodes (xs j))).sum + 1 ≤
      (List.ofFn (fun j => nodes (if j = i then _ else xs j))).sum + 1 + 1
    simp [List.ofFn_succ,unique] at *
    omega
  | ac_left f | ac_right f | comm_left f | comm_right f => exact nomatch f

private theorem needs {k a b} (p : Path (ruleRoot rules) k a b) : nodes a ≤ nodes b + k := by
  induction p with
  | basis h => rw [nodes_equiv h]; omega
  | step h _ ih =>
    obtain ⟨_,_,l,st,r⟩ := h
    rw [nodes_equiv l]
    have := slow_step st
    rw [nodes_equiv r] at this
    omega

example : ¬ FiniteVariantProperty (ruleRoot rules) := by
  intro finite
  obtain ⟨k,all⟩ := bounded_paths_of_finite_variants finite (app .f (.var x))
  let σ : Substitution S := .binding x (copies (k+1)) (typed _)
  have vars := (ConstructorVariants.constructor_normal rules (by
    intro r hr; simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl <;> trivial)).1
  have normalized : Normalized (ruleRoot rules) σ := by
    intro v
    change Normal _ (if v = x then copies (k+1) else .var v)
    by_cases e : v = x
    · simp [e,clean]
    · simp only [e,ite_false]
      exact vars v
  have path := all σ normalized (app .f z) ⟨consumes _,end_normal,fun sort h => .widen (.free _ _ (fun _ => HasSort.atom (sig := S) ())) (Term.rootSort_le h)⟩
  have lower := needs path
  change nodes (app .f (copies (k+1))) ≤ nodes (app .f z) + k at lower
  have size (n : Nat) : nodes (copies n) = nodes z + n := by
    induction n with
    | zero => rfl
    | succ n ih => change nodes (app .s (copies n)) = _; rw [size_app,ih]; omega
  simp only [size_app,size] at lower
  omega

end Tamarin.VariantCompositionLimit
