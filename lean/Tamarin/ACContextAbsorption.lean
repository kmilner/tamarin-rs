import Tamarin.SymbolicNarrowing
import Tamarin.VariantPresentation

/-! An AC rule may already carry its own context. A bare schema can cover
its extension when one sorted substitution reproduces both sides of the
extended rule modulo B. This decision is independent of the query, the
narrowing unifier and the search strategy. -/
namespace Tamarin.Rewriting.RootNarrowing
open ACSubproductReduction ConstructorVariants
variable {s : Signature}

/-- One simultaneous substitution witnesses both the redex and its actual
successor. This can be checked on the symbolic rule alone. -/
def Absorbs (f : s.ACSym) (z : Variable) (r : Equation s) : Prop :=
  ∃ α : Substitution s, EquivB (α.apply r.lhs) (.ac f r.lhs (.var z)) ∧
    EquivB (α.apply r.rhs) (.ac f r.rhs (.var z))

/-- Every instance of the extended equation has the same subject and result
as an instance of the bare equation. The two concrete terms are compared
modulo B without rewriting or renormalizing them. -/
theorem Absorbs.instance {f : s.ACSym} {z : Variable} {r : Equation s} (h : Absorbs f z r)
    (τ : Substitution s) :
    ∃ η : Substitution s, EquivB (η.apply r.lhs) (τ.apply (pattern f z r true).lhs) ∧
      EquivB (η.apply r.rhs) (τ.apply (pattern f z r true).rhs) := by
  obtain ⟨α,lhs,rhs⟩ := h
  exact ⟨τ.compose α,Substitution.apply_compose .. ▸ lhs.subst τ.image,
    Substitution.apply_compose .. ▸ rhs.subst τ.image⟩

/-- Symbolic replay characterizes inclusion of all concrete rule instances.
The identity assignment exposes the most general extended instance. -/
theorem absorbs_iff_instances (f : s.ACSym) (z : Variable) (r : Equation s) :
    Absorbs f z r ↔ ∀ τ : Substitution s, ∃ η : Substitution s,
      EquivB (η.apply r.lhs) (τ.apply (pattern f z r true).lhs) ∧
      EquivB (η.apply r.rhs) (τ.apply (pattern f z r true).rhs) := by
  refine ⟨fun h => h.instance,fun h => ?_⟩
  obtain ⟨α,lhs,rhs⟩ := h Substitution.identity
  exact ⟨α,by simpa only [Substitution.apply_identity,pattern] using lhs,
    by simpa only [Substitution.apply_identity,pattern] using rhs⟩

/-- The bare successor has exactly the same normal results, including when
a table is nonconfluent or the rule assignment contains reducible images. -/
theorem Absorbs.normalForms {f : s.ACSym} {z : Variable} {r : Equation s} (h : Absorbs f z r)
    (τ : Substitution s) (R : Root s) :
    ∃ η : Substitution s, EquivB (η.apply r.lhs) (τ.apply (pattern f z r true).lhs) ∧
      ∀ n, NormalForm R (η.apply r.rhs) n ↔ NormalForm R (τ.apply (pattern f z r true).rhs) n := by
  obtain ⟨η,lhs,rhs⟩ := h.instance τ
  exact ⟨η,lhs,fun _ => ⟨NormalForm.equiv_input rhs,NormalForm.equiv_input rhs.symm⟩⟩

/-- A variable occurs exactly once, as a factor at the selected AC head.
The lone variable is the degenerate one-factor side, allowed on the RHS. -/
inductive ContextFactor (f : s.ACSym) (v : Variable) : Term s → Prop where
  | var : ContextFactor f v (.var v)
  | left {a b} : ContextFactor f v a → ¬b.Occurs v → ContextFactor f v (.ac f a b)
  | right {a b} : ¬a.Occurs v → ContextFactor f v b → ContextFactor f v (.ac f a b)

private theorem ContextFactor.extends {f : s.ACSym} {v z : Variable} {t : Term s}
    (factor : ContextFactor f v t) (typed : HasSort (.ac f (.var v) (.var z)) v.sort) :
    EquivB ((Substitution.binding v _ typed).apply t) (.ac f t (.var z)) := by
  induction factor with
  | var =>
    change EquivB ((Substitution.binding v _ typed).image v) _
    rw [Substitution.binding_image_self]; exact .refl _
  | @left a b _ absent ih =>
    have keep := Substitution.binding_apply_of_not_occurs v _ b typed absent
    change EquivB (.ac f _ ((Substitution.binding v _ typed).apply b)) _
    rw [keep]
    exact (EquivB.ac_congr f ih (.refl b)).trans ((EquivB.ac_assoc f a _ b).trans
      ((EquivB.ac_congr f (.refl a) (.ac_swap f _ b)).trans (EquivB.ac_assoc f a b _).symm))
  | @right a b absent _ ih =>
    have keep := Substitution.binding_apply_of_not_occurs v _ a typed absent
    change EquivB (.ac f ((Substitution.binding v _ typed).apply a) _) _
    rw [keep]
    exact (EquivB.ac_congr f (.refl a) ih).trans (EquivB.ac_assoc f a b _).symm

/-- A linear context variable on both sides absorbs any nonempty remainder.
The proposed symbolic assignment may contain its own variable because its
application is simultaneous. -/
theorem absorbs_of_contextFactor {f : s.ACSym} {v z : Variable} {r : Equation s}
    (left : ContextFactor f v r.lhs) (right : ContextFactor f v r.rhs)
    (varSort : v.sort = s.acSort f) (restSort : z.sort = s.acSort f) : Absorbs f z r := by
  have typed : HasSort (.ac f (.var v) (.var z)) v.sort := varSort ▸
    HasSort.ac f _ _ (varSort ▸ HasSort.var v) (restSort ▸ HasSort.var z)
  exact ⟨Substitution.binding v _ typed,left.extends typed,right.extends typed⟩

/-- The actual bucket may omit an absorbed extension independently for each
rule. All remaining extensions and every bare rule are still covered, so
every concrete AC occurrence gives a narrowing instance with its original
successor and a single shared assignment on both sides. -/
theorem instances_at_ac_of_absorbs (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (a u : Term s) (typed : HasSort a (s.acSort f))
    (bound : ∀ r ∈ rules, head r.lhs = .ac f → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (z : Equation s → Variable) (sort : ∀ r ∈ rules, (z r).sort = s.acSort f)
    (fresh : ∀ r ∈ rules, ¬r.lhs.Occurs (z r)) (schemas : List (Schema (ruleRoot rules)))
    (bare : ∀ r ∈ rules, head r.lhs = .ac f → ∃ p ∈ schemas, p.Presents r)
    (extended : ∀ r ∈ rules, head r.lhs = .ac f →
      Absorbs f (z r) r ∨ ∃ p ∈ schemas, p.Presents (pattern f (z r) r true))
    (step : Occurrence (ruleRoot rules) f a u) : HasInstance schemas a u := by
  have lift {r : Equation s} (presents : ∃ p ∈ schemas, p.Presents r) (τ : Substitution s)
      (inEq : EquivB a (τ.apply r.lhs)) (outEq : EquivB (τ.apply r.rhs) u) :
      HasInstance schemas a u := by
    obtain ⟨p,hp,h⟩ := presents
    obtain ⟨η,l,r⟩ := h.instance τ
    exact ⟨p,hp,η,l ▸ inEq,r ▸ outEq.symm⟩
  obtain ⟨r,hr,hd,ext,τ,l,out⟩ :=
    (occurrence_iff_instances f rules apps bound a u typed z sort fresh).mp step
  cases ext with
  | false => exact lift (bare r hr hd) τ l out
  | true =>
    rcases extended r hr hd with absorbed|presents
    · obtain ⟨η,lhs,rhs⟩ := absorbed.instance τ
      exact lift (bare r hr hd) η (l.trans lhs.symm) (rhs.trans out)
    · exact lift presents τ l out

end Tamarin.Rewriting.RootNarrowing
