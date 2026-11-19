import Tamarin.RootNormalForms
import Tamarin.SortCheck
import Tamarin.VariableElimination

/-! The three builtin XOR rules are considered modulo AC in the active table.
For two Fresh operands, a unit or a nested XOR cannot match either operand.
Only equality of those operands can expose a root rewrite. -/
namespace Tamarin.Rewriting.FreshXor
open ConstructorVariants
variable {sig : Signature}

def Leaf : Term sig → Prop
  | .atom _ | .var _ => True
  | _ => False

private theorem leaf_eq {a b : Term sig} (l : Leaf a) (h : EquivB a b) : a = b := by
  cases a <;> cases b <;> first | contradiction | (cases h.head_eq <;> rfl)

private theorem pair_view (f : sig.ACSym) {a b : Term sig} (la : Leaf a) (lb : Leaf b)
    {s t : Term sig} (h : EquivB s t) :
    (s = .ac f a b ∨ s = .ac f b a) ↔ (t = .ac f a b ∨ t = .ac f b a) := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free | comm_congr | comm_swap => simp
  | ac_congr g e d =>
    constructor
    · rintro (he|he) <;> cases he <;>
        first | exact Or.inl (by rw [← leaf_eq la e, ← leaf_eq lb d])
              | exact Or.inr (by rw [← leaf_eq lb e, ← leaf_eq la d])
    · rintro (he|he) <;> cases he <;>
        first | exact Or.inl (by rw [← leaf_eq la e.symm, ← leaf_eq lb d.symm])
              | exact Or.inr (by rw [← leaf_eq lb e.symm, ← leaf_eq la d.symm])
  | ac_swap => simp only [Term.ac.injEq]; grind
  | ac_assoc => cases a <;> cases b <;> simp_all [Leaf]

structure Table (sig : Signature) where
  rules : List (Equation sig)
  f : sig.ACSym
  fSort : sig.acSort f = .msg
  zero : Term sig
  zeroFree : ∃ g args, zero = .free g args
  zeroGround : ∀ v, ¬ zero.Occurs v
  zeroSort : HasSort zero .msg
  zeroAbsent : ∀ h ∈ operators zero, h ∉ ruleHeads rules
  apps : ∀ r ∈ rules, Application r.lhs
  param : Variable
  paramSort : param.sort = .msg
  duplicate : (⟨.ac f (.var param) (.var param), zero⟩ : Equation sig) ∈ rules
  bucket : ∀ r ∈ rules, head r.lhs = .ac f →
    r = ⟨.ac f (.var param) (.var param), zero⟩ ∨
    (∃ v, r.lhs = .ac f (.var v) zero) ∨
    (∃ u v, r.lhs = .ac f (.var u) (.ac f (.var u) (.var v))) ∨
    (∃ u v, r.lhs = .ac f (.ac f (.var u) (.var u)) (.var v))
  freeSort : ∀ g, sig.outputSort g ≠ .fresh
  commSort : ∀ g, sig.cSort g ≠ .fresh
  acSort : ∀ g, sig.acSort g ≠ .fresh

namespace Table
variable (T : Table sig)
abbrev R := ruleRoot T.rules

theorem fixes_zero (σ : Substitution sig) : σ.apply T.zero = T.zero := by
  exact (Term.subst_eq_of_agree σ.image Term.var T.zero (fun v h => False.elim (T.zeroGround v h))).trans T.zero.subst_id

theorem zero_normal : Normal T.R T.zero := by
  obtain ⟨vars, hn⟩ := constructor_normal T.rules T.apps
  simpa using hn T.zero T.zeroAbsent Substitution.identity vars

include T in
theorem fresh_leaf {a : Term sig} (ha : HasSort a .fresh) : Leaf a := by
  have h := Term.rootSort_le ha
  have only {s : SortId} (hs : Subsort s .fresh) : s = .fresh := by cases hs; rfl
  have e := only h
  cases a with
  | var | atom => trivial
  | free f => exact False.elim (T.freeSort f e)
  | comm f => exact False.elim (T.commSort f e)
  | ac f => exact False.elim (T.acSort f e)

theorem at_pair {a b u : Term sig} (ha : HasSort a .fresh) (hb : HasSort b .fresh) :
    T.R (.ac T.f a b) u ↔ a = b ∧ u = T.zero := by
  constructor
  · rintro ⟨r,hm,σ,e,eu⟩
    have hhead : head r.lhs = .ac T.f := by
      rw [← instance_head r (T.apps r hm) σ, ← e]; rfl
    rcases T.bucket r hm hhead with hd | ⟨v,hu⟩ | ⟨v,w,ht⟩ | ⟨v,w,ht⟩
    · subst r; simp only [Substitution.apply, Term.subst, Term.ac.injEq] at e
      exact ⟨e.2.1.trans e.2.2.symm, eu.trans (T.fixes_zero σ)⟩
    · rw [hu] at e
      have h : b = σ.apply T.zero := (Term.ac.inj e).2.2
      rw [T.fixes_zero] at h
      obtain ⟨g,args,hz⟩ := T.zeroFree
      have l := T.fresh_leaf hb; rw [h,hz] at l; exact False.elim l
    · rw [ht] at e
      have l := T.fresh_leaf hb; rw [(Term.ac.inj e).2.2] at l; exact False.elim l
    · rw [ht] at e
      have l := T.fresh_leaf ha; rw [(Term.ac.inj e).2.1] at l; exact False.elim l
  · rintro ⟨rfl,rfl⟩
    let σ := Substitution.binding T.param a (T.paramSort ▸ HasSort.widen ha Subsort.fresh_msg)
    refine ⟨_,T.duplicate,σ,?_,(T.fixes_zero σ).symm⟩
    simp [σ,Substitution.binding,Substitution.apply,Term.subst]

private theorem step_pair {a b u : Term sig} (ha : HasSort a .fresh) (hb : HasSort b .fresh)
    (na : Normal T.R a) (nb : Normal T.R b) (h : StepModulo T.R (.ac T.f a b) u) :
    a = b ∧ EquivB T.zero u := by
  obtain ⟨s,t,e,hs,et⟩ := h
  have vs := (pair_view T.f (T.fresh_leaf ha) (T.fresh_leaf hb) e).mp (Or.inl rfl)
  rcases vs with rfl | rfl <;> cases hs with
  | root hr =>
    first | obtain ⟨he,rfl⟩ := (T.at_pair ha hb).mp hr; exact ⟨he,et⟩
          | obtain ⟨he,rfl⟩ := (T.at_pair hb ha).mp hr; exact ⟨he.symm,et⟩
  | ac_left _ _ h | ac_right _ _ h =>
    first | exact False.elim (na _ ⟨_,_,.refl _,h,.refl _⟩)
          | exact False.elim (nb _ ⟨_,_,.refl _,h,.refl _⟩)

theorem distinct_normal {a b : Term sig} (ha : HasSort a .fresh) (hb : HasSort b .fresh)
    (na : Normal T.R a) (nb : Normal T.R b) (ne : a ≠ b) : Normal T.R (.ac T.f a b) :=
  fun _ h => ne (T.step_pair ha hb na nb h).1

theorem duplicate_nf {a : Term sig} (ha : HasSort a .fresh) : NormalForm T.R (.ac T.f a a) T.zero := by
  exact ⟨.step ⟨_,_,.refl _,.root ((T.at_pair ha ha).mpr ⟨rfl,rfl⟩),.refl _⟩, T.zero_normal,
    fun _ hs => .widen T.zeroSort (T.fSort ▸ Term.rootSort_le hs)⟩

theorem duplicate_unique {a u : Term sig} (ha : HasSort a .fresh) (na : Normal T.R a)
    (nf : NormalForm T.R (.ac T.f a a) u) : EquivB u T.zero := by
  have go {s t : Term sig} (red : Reduces T.R s t) : s = .ac T.f a a →
      t = .ac T.f a a ∨ EquivB t T.zero := by
    induction red with
    | basis e =>
      rintro rfl
      exact Or.inl (((pair_view T.f (T.fresh_leaf ha) (T.fresh_leaf ha) e).mp (Or.inl rfl)).elim id id)
    | step h => rintro rfl; exact Or.inr (T.step_pair ha ha na na h).2.symm
    | trans r t ih ik =>
      rintro rfl
      rcases ih rfl with he|he
      · exact ik he
      · exact Or.inr ((normal_reduces_equiv t ((normal_equiv _ he).mpr T.zero_normal)).symm.trans he)
    | ac g r s _ _ =>
      rintro e; cases e
      rw [← leaf_eq (T.fresh_leaf ha) (normal_reduces_equiv r na),
          ← leaf_eq (T.fresh_leaf ha) (normal_reduces_equiv s na)]
      exact Or.inl rfl
    | free | comm => intro h; cases h
  rcases go nf.1 rfl with rfl | he
  · exact False.elim (nf.2.1 T.zero ⟨_,_,.refl _,.root ((T.at_pair ha ha).mpr ⟨rfl,rfl⟩),.refl _⟩)
  · exact he

end Table
end Tamarin.Rewriting.FreshXor
