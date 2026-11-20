import Tamarin.DestructorTable
import Tamarin.SubtermVariants

/-! Constructor-pattern projections inside an arbitrary active table. For one
free head, all matching equations select a common path through free symbols.
Other heads may have their own rewrite theories. -/
namespace Tamarin.ConstructorRows
open Rewriting ConstructorVariants DestructorTable ContextualReduction
variable {s : Signature} {rs : Problem s} {r : Equation s}

/-- An argument pattern can inspect any free, C or AC constructors absent
from the heads of the whole table. Repeated pattern variables are allowed. -/
def Inert (rs : Problem s) (t : Term s) := ∀ f ∈ operators t, f ∉ ruleHeads rs

def Pattern (rs : Problem s) : Term s → Prop
  | .free _ xs => ∀ i, Inert rs (xs i)
  | .comm _ a b => Inert rs a ∧ Inert rs b
  | _ => False

theorem root_of_pattern (apps : ∀ r ∈ rs, Application r.lhs)
    (σ : Substitution s) (hn : Normalized (ruleRoot rs) σ) {t u}
    (pat : Pattern rs t) (st : StepModulo (ruleRoot rs) (σ.apply t) u) : AtRoot (ruleRoot rs) (σ.apply t) u := by
  cases t with
  | var | atom | ac => contradiction
  | free f xs =>
    have nf i := (constructor_normal rs apps).2 (xs i) (pat i) σ hn
    obtain ⟨ys,v,eq,root,out⟩ := (stepModulo_free_iff nf).mp st
    exact ⟨_,_,.free _ _ _ eq,root,out⟩
  | comm f a b =>
    rcases (comm_iff ..).mp st with root | ⟨_,step,_⟩ | ⟨_,step,_⟩
    · exact root
    · exact ((constructor_normal rs apps).2 a pat.1 σ hn _ step).elim
    · exact ((constructor_normal rs apps).2 b pat.2 σ hn _ step).elim

structure ProjectionRow (rs : Problem s) (r : Equation s) : Prop where
  pattern : ∃ f xs, r.lhs = .free f xs ∧ ∀ i, Inert rs (xs i)
  path : ∃ p : List Nat, p ≠ [] ∧ ∀ q ∈ rs, head q.lhs = head r.lhs → atPath q.lhs p = some q.rhs

private theorem atPath_normal {R : Root s} {a b : Term s} {p} (pos : atPath a p = some b)
    (nf : Normal R a) : Normal R b := by
  induction p generalizing a with
  | nil => simp_all [atPath]
  | cons i p ih =>
    cases a <;> simp only [atPath] at pos <;> try contradiction
    split at pos <;> try contradiction
    next f xs hi => exact ih pos (normal_free_child f xs nf ⟨i,hi⟩)

private theorem atPath_mem {a b : Term s} {p} (pos : atPath a p = some b) :
    b ∈ MixedUnification.subterms a := by
  induction p generalizing a with
  | nil =>
    simp only [atPath,Option.some.injEq] at pos
    subst b; cases a <;> simp [MixedUnification.subterms]
  | cons i p ih =>
    cases a <;> simp only [atPath] at pos <;> try contradiction
    split at pos <;> try contradiction
    next f xs hi =>
      exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩,ih pos⟩)

theorem ProjectionRow.subterm (ok : ProjectionRow rs r) (mem : r ∈ rs) : SubtermVariants.Row r := by
  obtain ⟨f,xs,src,_⟩ := ok.pattern
  obtain ⟨p,ne,path⟩ := ok.path
  have pos := path r mem rfl
  rw [src] at pos
  cases p with
  | nil => contradiction
  | cons i p =>
    simp only [atPath] at pos
    split at pos <;> try contradiction
    next hi =>
      simp only [SubtermVariants.Row,src]
      exact .inr ⟨⟨i,hi⟩,atPath_mem pos⟩

/-- Every normalized instance fires, and every reduction to a normal form
returns this very projection modulo the declared structural axioms. -/
theorem ProjectionRow.result (ok : ProjectionRow rs r) (mem : r ∈ rs)
    (apps : ∀ q ∈ rs, Application q.lhs) (σ : Substitution s) (norm : Normalized (ruleRoot rs) σ)
    {u} (nf : NormalForm (ruleRoot rs) (σ.apply r.lhs) u) : EquivB u (σ.apply r.rhs) := by
  obtain ⟨f,xs,src,absent⟩ := ok.pattern
  obtain ⟨p,ne,path⟩ := ok.path
  have kids := fun i => (constructor_normal rs apps).2 (xs i) (absent i) σ norm
  have pos := apply_path σ (path r mem rfl)
  have target : Normal (ruleRoot rs) (σ.apply r.rhs) := by
    rw [src] at pos
    cases p with
    | nil => contradiction
    | cons i p =>
      simp only [Substitution.apply,Term.subst,atPath] at pos
      split at pos <;> try contradiction
      next hi => exact atPath_normal pos (kids ⟨i,hi⟩)
  have fire : ruleRoot rs (σ.apply r.lhs) (σ.apply r.rhs) := ⟨r,mem,σ,rfl,rfl⟩
  rw [src] at nf fire
  apply normalForm_free_root_unique kids target ⟨_,_,.refl _,.root fire,.refl _⟩ _ nf
  intro ys eq b root
  obtain ⟨q,hq,τ,hl,rfl⟩ := root
  have base : EquivB (σ.apply r.lhs) (τ.apply q.lhs) := by rw [src,← hl]; exact .free f _ _ eq
  have same : head q.lhs = head r.lhs :=
    (instance_head q (apps q hq) τ).symm.trans (base.head_eq.symm.trans (instance_head r (apps r mem) σ))
  exact (path_congr base pos (apply_path τ (path q hq same))).symm

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

def headEq : Head s → Head s → Bool
  | .var a, .var b => a == b
  | .atom a, .atom b => a == b
  | .free a, .free b => a == b
  | .comm a, .comm b => a == b
  | .ac a, .ac b => a == b
  | _, _ => false

theorem headEq_iff (a b : Head s) : headEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [headEq]

theorem headEq_false (a b : Head s) : headEq a b = false ↔ a ≠ b :=
  Bool.eq_false_iff.trans (not_congr (headEq_iff a b))

def constructorPattern (rs : Problem s) (t : Term s) : Bool :=
  (operators t).all fun h => (ruleHeads rs).all fun k => !(headEq k h)

theorem constructorPattern_iff (rs : Problem s) (t : Term s) : constructorPattern rs t ↔ Inert rs t := by
  simp only [constructorPattern,List.all_eq_true,Bool.not_eq_true',Inert]
  constructor
  · exact fun ok h used present => (headEq_false h h).mp (ok h used h present) rfl
  · exact fun ok h used k present => (headEq_false k h).mpr (fun eq => ok h used (eq ▸ present))

def pattern (rs : Problem s) : Term s → Bool
  | .free _ xs => (List.finRange _).all fun i => constructorPattern rs (xs i)
  | .comm _ a b => constructorPattern rs a && constructorPattern rs b
  | _ => false

theorem pattern_iff (rs : Problem s) (t : Term s) : pattern rs t ↔ Pattern rs t := by
  cases t <;> simp [pattern,Pattern,constructorPattern_iff]

def projectionRow (rs : Problem s) (r : Equation s) : Bool :=
  (match r.lhs with | .free _ xs => (List.finRange _).all fun i => constructorPattern rs (xs i) | _ => false) &&
    (paths r.lhs).any fun p => !p.isEmpty && rs.all fun q =>
      !(headEq (head q.lhs) (head r.lhs)) || atPath q.lhs p == some q.rhs

theorem projectionRow_iff (rs : Problem s) (r : Equation s) (mem : r ∈ rs) :
    projectionRow rs r ↔ ProjectionRow rs r := by
  simp only [projectionRow,Bool.and_eq_true,List.any_eq_true,List.all_eq_true,Bool.not_eq_true',
    List.isEmpty_eq_false_iff,Bool.or_eq_true,beq_iff_eq]
  classical
  constructor
  · rintro ⟨h,⟨p,_,ne,all⟩⟩
    refine ⟨?_,p,ne,fun q hq same => (all q hq).resolve_left (fun off => (headEq_false ..).mp off same)⟩
    cases src : r.lhs <;> simp [src] at h
    next f xs => exact ⟨f,xs,rfl,fun i => (constructorPattern_iff ..).mp (h i)⟩
  · rintro ⟨⟨f,xs,src,kids⟩,p,ne,all⟩
    exact ⟨by simp [src,constructorPattern_iff,kids],p,path_mem (all r mem rfl),ne,
      fun q hq => if e : _ = _ then .inr (all q hq e) else .inl ((headEq_false ..).mpr e)⟩

end Tamarin.ConstructorRows
