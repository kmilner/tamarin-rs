import Tamarin.RootNarrowing
import Tamarin.VariantJoinLeaf

/-! A finite narrowing frontier is complete only after every relevant
specialized rewrite stays in its denotation. This proof follows a finite
derivation of each requested normal form, without assuming termination or
confluence of the equational theory. -/
namespace Tamarin.Rewriting.RootNarrowing
open VariantJoin
variable {sig : Signature} {R : Root sig}

private inductive Path (R : Root sig) : Term sig → Term sig → Prop where
  | basis {a b} : EquivB a b → Path R a b
  | next {a b c} : StepModulo R a b → Path R b c → Path R a c

private theorem Path.rebase {a b c : Term sig} (e : EquivB a b) (h : Path R b c) : Path R a c := by
  cases h with
  | basis eq => exact .basis (e.trans eq)
  | next step tail =>
    obtain ⟨s,t,eq,r,out⟩ := step
    exact .next ⟨s,t,e.trans eq,r,out⟩ tail

private theorem Path.trans {a b c : Term sig} (h : Path R a b) (k : Path R b c) : Path R a c := by
  induction h with
  | basis e => exact k.rebase e
  | next st _ ih => exact .next st (ih k)

private theorem Path.context (F : Term sig → Term sig) (basis : ∀ {a b}, EquivB a b → EquivB (F a) (F b))
    (step : ∀ {a b}, Step R a b → Step R (F a) (F b)) {a b} (h : Path R a b) : Path R (F a) (F b) := by
  induction h with
  | basis eq => exact .basis (basis eq)
  | next st _ ih =>
    obtain ⟨s,t,eq,hs,out⟩ := st
    exact .next ⟨F s,F t,basis eq,step hs,basis out⟩ ih

private theorem Path.free (f : sig.FreeSym) (a b : Fin (sig.arity f) → Term sig)
    (h : ∀ i, Path R (a i) (b i)) : Path R (.free f a) (.free f b) := by
  let mix (k : Nat) (i : Fin (sig.arity f)) := if i.val < k then b i else a i
  have reach (k) (bound : k ≤ sig.arity f) : Path R (.free f a) (.free f (mix k)) := by
    induction k with
    | zero => exact .basis (.free f _ _ fun i => by simp [mix]; exact .refl _)
    | succ k ih =>
      let i : Fin (sig.arity f) := ⟨k,by omega⟩
      let args (t : Term sig) (j : Fin (sig.arity f)) := if j = i then t else mix k j
      let F (t : Term sig) := Term.free f (args t)
      have basis {x y : Term sig} (e : EquivB x y) : EquivB (F x) (F y) := by
        apply EquivB.free; intro j; by_cases eq : j = i
        · simpa [args,eq] using e
        · simp [args,eq]; exact .refl _
      have step {x y : Term sig} (st : Step R x y) : Step R (F x) (F y) := by
        have one := Step.free f (args x) i (u := y) (by simpa [args] using st)
        have same : (fun j => if j = i then y else args x j) = args y := by
          funext j; by_cases eq : j = i <;> simp [args,eq]
        rw [same] at one; exact one
      have patch := (h i).context F basis step
      have left : args (a i) = mix k := by
        funext j; by_cases eq : j = i <;> simp [args,eq,i,mix]
      have right : args (b i) = mix (k+1) := by
        funext j; by_cases eq : j = i
        · simp [args,eq,i,mix]
        · have ne : j.val ≠ k := fun e => eq (Fin.ext e)
          simp [args,eq,mix,show j.val < k+1 ↔ j.val < k by omega]
      change Path R (.free f (args (a i))) (.free f (args (b i))) at patch
      rw [left,right] at patch
      exact (ih (by omega)).trans patch
  simpa [mix] using reach _ (Nat.le_refl (sig.arity f))

/-- Congruence in the reference relation permits several independently
reduced children. Each such derivation serializes in argument order. -/
private theorem path_of_reduces {a b : Term sig} (h : Reduces R a b) : Path R a b := by
  induction h with
  | basis e => exact .basis e
  | step st => exact .next st (.basis (.refl _))
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b _ ih => exact Path.free f a b ih
  | @ac f a c b d _ _ ih ik =>
    exact (ih.context (fun x => .ac f x c) (fun e => .ac_congr f e (.refl _)) (Step.ac_left f c)).trans
      (ik.context (fun x => .ac f b x) (fun e => .ac_congr f (.refl _) e) (Step.ac_right f b))
  | @comm f a c b d _ _ ih ik =>
    exact (ih.context (fun x => .comm f x c) (fun e => .comm_congr f e (.refl _)) (Step.comm_left f c)).trans
      (ik.context (fun x => .comm f b x) (fun e => .comm_congr f (.refl _) e) (Step.comm_right f b))

/-- A state retains one result and all input images. Closure can use any
state in the finite family (including an older more general state). Each
new factor substitution must still explain all input images together. -/
def Closed {I : Type} (R : Root sig) (rows : List (Row sig I Unit)) : Prop :=
  ∀ q ∈ rows, ∀ δ : Substitution sig, (∀ i, Normal R (δ.apply (q.input i))) → ∀ u,
    StepModulo R (δ.apply (q.value ())) u →
    ∃ r ∈ rows, ∃ η : Substitution sig, (∀ i, EquivB (δ.apply (q.input i)) (η.apply (r.input i))) ∧
      EquivB u (η.apply (r.value ()))

/-- Root narrowing or a finite-theory theorem must establish `Closed`
independently. A well-typed CSU for one rule supplies only one transition.
Discarded terminal rows may be covered by another retained answer. -/
theorem frontier_covers {I : Type} {rules : List (Equation sig)}
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (rows kept : List (Row sig I Unit)) (closed : Closed (ruleRoot rules) rows)
    (terminal : ∀ q ∈ rows, q.IsNormal (ruleRoot rules) → ∃ r ∈ kept,
      ∃ σ : Substitution sig, VariantJoin.Fits r q.input q.value σ)
    (input : I → Term sig) (ni : ∀ i, Normal (ruleRoot rules) (input i))
    (start out : Term sig) (red : Reduces (ruleRoot rules) start out) (normal : Normal (ruleRoot rules) out)
    (seed : ∃ q ∈ rows, ∃ δ : Substitution sig, (∀ i, EquivB (input i) (δ.apply (q.input i))) ∧
      EquivB start (δ.apply (q.value ()))) :
    ∃ q ∈ kept, Denotes (ruleRoot rules) q input (fun _ => out) := by
  have path := path_of_reduces red
  clear red
  induction path with
  | @basis _ out e =>
    obtain ⟨q,mem,δ,ins,value⟩ := seed
    have fit : VariantJoin.Fits q input (fun _ => out) δ :=
      ⟨ins,fun _ => e.symm.trans value⟩
    have norm := normal_witness vars ni (fun _ => normal) fit
    obtain ⟨r,rm,τ,cover⟩ := terminal q mem norm.1
    have hit : VariantJoin.Fits r input (fun _ => out) (δ.compose τ) := by
      constructor
      · intro i; rw [Substitution.apply_compose]; exact (ins i).trans ((cover.inputs i).subst δ.image)
      · intro a; rw [Substitution.apply_compose]; exact (fit.values a).trans ((cover.values a).subst δ.image)
    exact ⟨r,rm,(normal_witness vars ni (fun _ => normal) hit).2⟩
  | next st tail ih =>
    obtain ⟨q,mem,δ,ins,value⟩ := seed
    obtain ⟨s,t,eq,hs,finish⟩ := st
    obtain ⟨r,rm,η,more,hit⟩ := closed q mem δ (fun i => (normal_equiv _ (ins i)).mp (ni i)) _
      ⟨s,t,value.symm.trans eq,hs,finish⟩
    exact ih normal ⟨r,rm,η,fun i => (ins i).trans (more i),hit⟩

def initial (t : Term sig) : Row sig (LocalKey t) Unit := ⟨fun i => .var i.val,fun _ => t⟩

/-- Closure and terminal coverage establish the completeness half. Returning
an arm separately requires its own sort-preserving normalized replay. There
is no assertion that a finite closed frontier exists for every rule table. -/
structure Certificate (rules : List (Equation sig)) (t : Term sig)
    (states kept : List (Row sig (LocalKey t) Unit)) (answers : List (Variant sig)) : Prop where
  seed : initial t ∈ states
  closed : Closed (ruleRoot rules) states
  terminal : ∀ q ∈ states, q.IsNormal (ruleRoot rules) → ∃ r ∈ kept,
    ∃ σ : Substitution sig, VariantJoin.Fits r q.input q.value σ
  returned : ∀ r ∈ kept, ∃ a ∈ answers, ∃ u, a.values = [u] ∧
    (∀ i : LocalKey t, EquivB (r.input i) (a.subst.image i.val)) ∧ EquivB (r.value ()) u
  sound : ∀ a ∈ answers, a.Sound (ruleRoot rules) [t]

theorem Certificate.complete {rules : List (Equation sig)} {t : Term sig} {states kept answers}
    (frontier : Certificate rules t states kept answers)
    (vars : Normalized (ruleRoot rules) Substitution.identity) : CompleteVariants (ruleRoot rules) [t] answers := by
  refine ⟨frontier.sound,?_⟩
  intro ρ hn vs forms
  cases vs with
  | nil => exact False.elim forms
  | cons out tail => cases tail with
    | cons => exact False.elim forms.2
    | nil =>
      obtain ⟨r,mem,δ,nd,fit⟩ := frontier_covers vars states kept frontier.closed frontier.terminal
        (fun i => ρ.image i.val) (fun i => hn i.val) _ out forms.1.1 forms.1.2.1
        ⟨initial t,frontier.seed,ρ,fun _ => .refl _,.refl _⟩
      obtain ⟨a,am,u,vals,images,value⟩ := frontier.returned r mem
      refine ⟨a,am,δ,nd,?_,?_⟩
      · rintro v ⟨_,hm,occ⟩; obtain rfl := List.mem_singleton.mp hm
        exact (fit.inputs ⟨v,occ⟩).trans ((images ⟨v,occ⟩).subst δ.image)
      · rw [vals]; exact ⟨(fit.values ()).trans (value.subst δ.image),trivial⟩

end Tamarin.Rewriting.RootNarrowing
