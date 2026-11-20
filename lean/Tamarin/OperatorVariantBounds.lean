import Tamarin.ShortVariantPaths
import Tamarin.FiniteOccurs

/-! A criterion for the whole variant command with one local normalization
bound per operator. Operands can be kind-level terms. The bounds count rewrites
after the operands have been normalized and may select any available path. -/
namespace Tamarin.ShortVariantPaths
open Rewriting MaudeOperations
variable {s : Signature} {R : Root s} {rs : Problem s}

theorem Path.weaken {a b : Term s} {k m} (p : Path R k a b) (le : k ≤ m) : Path R m a b := by
  induction p generalizing m with
  | basis e => exact .basis e
  | step h _ ih => cases m with
    | zero => omega
    | succ m => exact .step h (ih (by omega))

theorem Path.append {a b c : Term s} {k m} (p : Path R k a b) (q : Path R m b c) : Path R (k+m) a c := by
  induction p with
  | basis eq => exact (q.rebase eq).weaken (by omega)
  | step h _ ih => simpa [Nat.succ_add] using Path.step h (ih q)

theorem Path.post {a b c : Term s} {k} (p : Path R k a b) (eq : EquivB b c) : Path R k a c := by
  simpa using p.append (Path.basis (k := 0) eq)

theorem Path.reduces {a b : Term s} {k} (p : Path R k a b) : Reduces R a b := by
  induction p with
  | basis e => exact .basis e
  | step h _ ih => exact (Reduces.step h).trans ih

theorem Path.subst {a b : Term s} {k} (p : Path (ruleRoot rs) k a b) (ρ : Substitution s) :
    Path (ruleRoot rs) k (ρ.apply a) (ρ.apply b) := by
  induction p with
  | basis e => exact .basis (e.subst ρ.image)
  | step h _ ih => exact .step (SpecializedFresh.stepModulo_subst rs ρ h) ih

private theorem Path.ctx (F : Term s → Term s) (eq : ∀ {a b}, EquivB a b → EquivB (F a) (F b))
    (step : ∀ {a b}, Step R a b → Step R (F a) (F b)) {a b k} (p : Path R k a b) : Path R k (F a) (F b) := by
  induction p with
  | basis h => exact .basis (eq h)
  | step h _ ih =>
    obtain ⟨x,y,l,st,r⟩ := h
    exact .step ⟨_,_,eq l,step st,eq r⟩ ih

private theorem Path.binary (F : Term s → Term s → Term s)
    (eq : ∀ {a b c d}, EquivB a c → EquivB b d → EquivB (F a b) (F c d))
    (left : ∀ b {a c}, Step R a c → Step R (F a b) (F c b))
    (right : ∀ a {b d}, Step R b d → Step R (F a b) (F a d))
    {a b c d k m} (p : Path R k a c) (q : Path R m b d) : Path R (k+m) (F a b) (F c d) :=
  (p.ctx (fun x => F x b) (fun h => eq h (.refl _)) (left b)).append
    (q.ctx (F c) (fun h => eq (.refl _) h) (right c))

theorem Path.ac (f : s.ACSym) {a b c d k m} (p : Path R k a c) (q : Path R m b d) :
    Path R (k+m) (.ac f a b) (.ac f c d) :=
  Path.binary (.ac f) (.ac_congr f) (fun _ {_ _} h => .ac_left _ _ h) (fun _ {_ _} h => .ac_right _ _ h) p q

theorem Path.comm (f : s.CSym) {a b c d k m} (p : Path R k a c) (q : Path R m b d) :
    Path R (k+m) (.comm f a b) (.comm f c d) :=
  Path.binary (.comm f) (.comm_congr f) (fun _ {_ _} h => .comm_left _ _ h) (fun _ {_ _} h => .comm_right _ _ h) p q

theorem Path.free (f : s.FreeSym) (a b : Fin (s.arity f) → Term s) (k : Nat)
    (p : ∀ i, Path R k (a i) (b i)) : Path R (s.arity f * k) (.free f a) (.free f b) := by
  let mix (n : Nat) (j : Fin (s.arity f)) := if j.val < n then b j else a j
  have traverse (n) (bound : n ≤ s.arity f) : Path R (n*k) (.free f a) (.free f (mix n)) := by
    induction n with
    | zero => exact .basis (.free f _ _ fun j => by simp [mix]; exact .refl _)
    | succ n ih =>
      let i : Fin (s.arity f) := ⟨n,by omega⟩
      let args (t : Term s) (j : Fin (s.arity f)) := if j=i then t else mix n j
      let F (t : Term s) := Term.free f (args t)
      have eq {x y : Term s} (e : EquivB x y) : EquivB (F x) (F y) := by
        apply EquivB.free; intro j; by_cases h : j=i <;> simp [args,h] <;> first | exact e | exact .refl _
      have st {x y : Term s} (h : Step R x y) : Step R (F x) (F y) := by
        have one := Step.free f (args x) i (u := y) (by simpa [args] using h)
        have id : (fun j => if j=i then y else args x j) = args y := by
          funext j; by_cases h : j=i <;> simp [args,h]
        rw [id] at one; exact one
      have h := (p i).ctx F eq st
      have l : args (a i) = mix n := by funext j; by_cases h : j=i <;> simp [args,h,i,mix]
      have r : args (b i) = mix (n+1) := by
        funext j; by_cases h : j=i
        · simp [args,h,i,mix]
        · have ne : j.val ≠ n := fun e => h (Fin.ext e)
          simp [args,h,mix,show j.val < n+1 ↔ j.val < n by omega]
      change Path R k (.free f (args (a i))) (.free f (args (b i))) at h
      rw [l,r] at h
      simpa [Nat.succ_mul] using (ih (by omega)).append h
  simpa [mix] using traverse _ (Nat.le_refl _)

theorem exists_path {a b : Term s} (red : Reduces R a b) : ∃ k, Path R k a b := by
  apply RootNarrowing.reduction_invariant (fun b => ∃ k, Path R k a b) ?_ ?_ red ⟨0,.basis (.refl _)⟩
  · rintro _ _ ⟨k,p⟩ eq; exact ⟨k,p.post eq⟩
  · rintro _ _ ⟨k,p⟩ st; exact ⟨_,p.append (.step (k := 0) st (.basis (.refl _)))⟩

/-- Every finite covering family gives one uniform path bound for the
normalized instances of the query. Specializing a symbolic derivation replays
its genuine steps and accounts for the value without a final normalization. -/
theorem bounded_paths_of_finite_variants (finite : FiniteVariantProperty (ruleRoot rs)) (t : Term s) :
    ∃ k, ∀ σ : Substitution s, Normalized (ruleRoot rs) σ → ∀ u,
      NormalForm (ruleRoot rs) (σ.apply t) u → Path (ruleRoot rs) k (σ.apply t) u := by
  obtain ⟨rows,sound,complete⟩ := finite [t]
  have row_path (r : {r // r ∈ rows}) : ∃ u k, r.val.values = [u] ∧
      Path (ruleRoot rs) k (r.val.subst.apply t) u := by
    have vals := (sound r.val r.property).2
    cases h : r.val.values with
    | nil => simp [h,Aligned] at vals
    | cons u tail =>
      rw [h] at vals
      cases tail with
      | cons => exact vals.2.elim
      | nil =>
        obtain ⟨k,p⟩ := exists_path vals.1.1
        exact ⟨u,k,rfl,p⟩
  let budget (r : {r // r ∈ rows}) := (row_path r).choose_spec.choose
  refine ⟨(rows.attach.map budget).sum,fun σ hn u form => ?_⟩
  obtain ⟨r,hr,δ,_,fit,values⟩ := complete σ hn [u] ⟨form,trivial⟩
  let a : {r // r ∈ rows} := ⟨r,hr⟩
  obtain ⟨stored,path⟩ := (row_path a).choose_spec.choose_spec
  change r.values = [_] at stored
  rw [stored] at values
  have same : EquivB (σ.apply t) (δ.apply (r.subst.apply t)) := by
    rw [← Substitution.apply_compose]
    exact t.subst_equiv _ _ (fun v hv => fit v ⟨t,List.mem_singleton_self _,hv⟩)
  exact (((path.subst δ).rebase same).post values.1.symm).weaken
    (FiniteOccurs.le_sum _ _ (List.mem_map_of_mem (f := budget) (List.mem_attach rows a)))

/-- A bound for one root with arbitrary already-normal operands. This
quantifies over the term kind, including children lacking the declared sort. -/
structure Operators (R : Root s) : Prop where
  free : ∀ f : s.FreeSym, ∃ k, ∀ xs, (∀ i, Normal R (xs i)) →
    ∃ u, Path R k (.free f xs) u ∧ Normal R u
  comm : ∀ f : s.CSym, ∃ k, ∀ a b, Normal R a → Normal R b →
    ∃ u, Path R k (.comm f a b) u ∧ Normal R u
  ac : ∀ f : s.ACSym, ∃ k, ∀ a b, Normal R a → Normal R b →
    ∃ u, Path R k (.ac f a b) u ∧ Normal R u

private theorem term_bound (operators : Operators R) (atom : ∀ a : s.Atom, ∃ k u, Path R k (.atom a) u ∧ Normal R u)
    (t : Term s) : ∃ k, ∀ ρ : Substitution s, Normalized R ρ → ∃ u, Path R k (ρ.apply t) u ∧ Normal R u := by
  induction t with
  | var v => exact ⟨0,fun ρ hn => ⟨ρ.image v,.basis (.refl _),hn v⟩⟩
  | atom a => obtain ⟨k,u,h⟩ := atom a; exact ⟨k,fun _ _ => ⟨u,h⟩⟩
  | ac f a b l r =>
    obtain ⟨i,l⟩ := l; obtain ⟨j,r⟩ := r
    obtain ⟨m,h⟩ := operators.ac f
    refine ⟨i+j+m,fun ρ hn => ?_⟩
    obtain ⟨a,pa,na⟩ := l ρ hn; obtain ⟨b,pb,nb⟩ := r ρ hn
    obtain ⟨u,p,nn⟩ := h a b na nb
    exact ⟨u,(Path.ac f pa pb).append p,nn⟩
  | comm f a b l r =>
    obtain ⟨i,l⟩ := l; obtain ⟨j,r⟩ := r
    obtain ⟨m,h⟩ := operators.comm f
    refine ⟨i+j+m,fun ρ hn => ?_⟩
    obtain ⟨a,pa,na⟩ := l ρ hn; obtain ⟨b,pb,nb⟩ := r ρ hn
    obtain ⟨u,p,nn⟩ := h a b na nb
    exact ⟨u,(Path.comm f pa pb).append p,nn⟩
  | free f xs ih =>
    let k i := (ih i).choose
    let m := (List.ofFn k).sum
    obtain ⟨w,root⟩ := operators.free f
    refine ⟨s.arity f*m+w,fun ρ hn => ?_⟩
    let run i := (ih i).choose_spec ρ hn
    let ys i := (run i).choose
    have children (i) : Path R m (ρ.apply (xs i)) (ys i) := (run i).choose_spec.1.weaken
      (FiniteOccurs.le_sum _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    obtain ⟨u,p,normal⟩ := root ys (fun i => (run i).choose_spec.2)
    exact ⟨u,(Path.free f _ ys m children).append p,normal⟩

/-- Local bounds compose on the full syntax tree regardless of variable
sharing. Each tuple has one finite joint variant family for the original
variables, including repeated occurrences in different observations. -/
theorem finiteVariantProperty_of_operators [DecidableEq s.FreeSym] [DecidableEq s.CSym]
    [DecidableEq s.ACSym] [DecidableEq s.Atom] (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (operators : Operators (ruleRoot rs)) :
    FiniteVariantProperty (ruleRoot rs) := by
  let reducer := ReferenceReduction.reducer rs bound can
  apply finiteVariantProperty bound can
  intro t
  have atom (a : s.Atom) := (reducer.correct (.atom a)).normalForm
  obtain ⟨k,all⟩ := term_bound operators (fun a => by
    obtain ⟨k,p⟩ := exists_path (atom a).1
    exact ⟨k,_,p,(atom a).2.1⟩) t
  refine ⟨k,fun ρ hn y form => ?_⟩
  obtain ⟨u,path,normal⟩ := all ρ hn
  obtain ⟨v,hu,hy⟩ := can.confluent path.reduces form.1
  exact path.post ((normal_reduces_equiv hu normal).trans (normal_reduces_equiv hy form.2.1).symm)

end Tamarin.ShortVariantPaths
