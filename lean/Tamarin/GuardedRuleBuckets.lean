import Tamarin.VariantFrontier
import Tamarin.LocalConvergence
import Tamarin.SpecializedRule
import Tamarin.HereditaryConvergence
import Tamarin.StableVariants

/-! A finite family of rules at a free head may overlap. On normal operands
the different matching assignments must yield the same normal result. While
a child is still changing, its fixed outer head can rule out an early parent
rewrite. This local criterion does not depend on rules at unrelated heads. -/
namespace Tamarin.Rewriting.GuardedRuleBuckets
open ConstructorVariants RootNarrowing VariantJoin
variable {s : Signature} {R : Root s} {d : s.FreeSym}

structure Bucket (R : Root s) (d : s.FreeSym) : Prop where
  normal : ∀ xs, (∀ i, Normal R (xs i)) → ∀ u, R (.free d xs) u → Normal R u
  agrees : ∀ xs ys, (∀ i, Normal R (xs i)) → (∀ i, EquivB (xs i) (ys i)) →
    ∀ a b, R (.free d xs) a → R (.free d ys) b → EquivB a b

abbrev RuleRow (s : Signature) (d : s.FreeSym) := State s (Fin (s.arity d))

/-- Every rule in the actual bucket is represented with all its arguments
and its return value under one simultaneous assignment. -/
def Covers (R : Root s) (d : s.FreeSym) (rows : List (RuleRow s d)) :=
  ∀ xs out, R (.free d xs) out → ∃ r ∈ rows, ∃ σ : Substitution s,
    (∀ i, EquivB (xs i) (σ.apply (r.input i))) ∧ EquivB out (σ.apply (r.value ()))

theorem covers_of_bucket (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (rows : List (RuleRow s d))
    (complete : ∀ r ∈ rules, head r.lhs = .free d → ∃ p ∈ rows,
      EquivB r.lhs (.free d p.input) ∧ EquivB r.rhs (p.value ())) : Covers (ruleRoot rules) d rows := by
  rintro xs out ⟨r,mem,σ,l,rfl⟩
  have hd := (instance_head r (apps r mem) σ).symm.trans (congrArg head l.symm)
  obtain ⟨p,hp,pl,pr⟩ := complete r mem hd
  have shape := pl.subst σ.image
  change EquivB (σ.apply r.lhs) (.free d (fun i => σ.apply (p.input i))) at shape
  rw [← l] at shape
  exact ⟨p,hp,σ,(Matching.free_equiv_iff ..).mp shape,pr.subst σ.image⟩

/-- Only one orientation of each pair is needed. The diagonal compares
independent matching assignments to the very same rule. -/
theorem compatible_triangle {rows : List (RuleRow s d)}
    (checked : ∀ i j : Fin rows.length, j ≤ i → CompatibleValues R rows[i] rows[j]) :
    ∀ p ∈ rows, ∀ q ∈ rows, CompatibleValues R p q := by
  intro p hp q hq
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hp
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hq
  by_cases le : j ≤ i
  · exact checked ⟨i,hi⟩ ⟨j,hj⟩ le
  · intro x a b nx na nb left right
    exact (checked ⟨j,hj⟩ ⟨i,hi⟩ (by change i ≤ j; omega) x b a nx nb na right left).symm

theorem of_compatible {rules : List (Equation s)} (vars : Normalized (ruleRoot rules) Substitution.identity)
    (rows : List (RuleRow s d)) (covers : Covers (ruleRoot rules) d rows)
    (returns : ∀ r ∈ rows, ∀ σ : Substitution s, (∀ i, Normal (ruleRoot rules) (σ.apply (r.input i))) →
      Normal (ruleRoot rules) (σ.apply (r.value ())))
    (agree : ∀ p ∈ rows, ∀ q ∈ rows, CompatibleValues (ruleRoot rules) p q) : Bucket (ruleRoot rules) d := by
  have normal xs (hn : ∀ i, Normal (ruleRoot rules) (xs i)) u (hit : ruleRoot rules (.free d xs) u) :
      Normal (ruleRoot rules) u := by
    obtain ⟨r,hr,σ,eq,val⟩ := covers _ _ hit
    exact (normal_equiv _ val).mpr (returns r hr σ (fun i => (normal_equiv _ (eq i)).mp (hn i)))
  refine ⟨normal,?_⟩
  intro x y nx eq a b l r
  have na := normal _ nx _ l
  have nb := normal _ (fun i => (normal_equiv _ (eq i)).mp (nx i)) _ r
  obtain ⟨p,hp,σ,lhs,lv⟩ := covers _ _ l
  obtain ⟨q,hq,τ,rhs,rv⟩ := covers _ _ r
  apply agree p hp q hq x _ _ nx na nb
  · exact (normal_witness vars nx (fun _ => na) (δ := σ)
      (q := p) ⟨lhs,fun _ => lv⟩).2
  · exact (normal_witness vars nx (fun _ => nb) (δ := τ)
      (q := q) ⟨fun i => (eq i).trans (rhs i),fun _ => rv⟩).2

/-- Normalizing a child either gives its final value or keeps its pending
head. A stable leaf has no pending head at all. -/
structure Stage (R : Root s) (mark : Option s.FreeSym) (t n : Term s) : Prop where
  normal : Normal R n
  converges : Converges R t n
  positions : ∀ u, Reduces R t u → EquivB u n ∨ ∃ f, mark = some f ∧ head u = .free f

theorem Stage.leaf {t : Term s} (normal : Normal R t) : Stage R none t t :=
  ⟨normal,Converges.normal normal,fun _ red => .inl (normal_reduces_equiv red normal).symm⟩

/-- Before the children normalize, every root instance must exclude their
pending heads. It is enough to inspect that slot in each original rule. -/
def Guard (R : Root s) (d : s.FreeSym) (mark : Fin (s.arity d) → Option s.FreeSym) :=
  ∀ ys out, R (.free d ys) out → ∀ i f, mark i = some f → head (ys i) ≠ .free f

private theorem result (B : Bucket R d) (ns : Fin (s.arity d) → Term s) (hn : ∀ i, Normal R (ns i)) :
    ∃ n, Normal R n ∧ Reduces R (.free d ns) n ∧
      ∀ ys, (∀ i, EquivB (ys i) (ns i)) → ∀ u, R (.free d ys) u → EquivB u n := by
  by_cases yes : ∃ ys, (∀ i, EquivB (ys i) (ns i)) ∧ ∃ u, R (.free d ys) u
  · obtain ⟨ys,ey,v,fire⟩ := yes
    have ny i := (normal_equiv R (ey i)).mpr (hn i)
    refine ⟨v,B.normal _ ny _ fire,.step ⟨_,_,.free d _ _ (fun i => (ey i).symm),.root fire,.refl _⟩,?_⟩
    intro zs ez u hit
    exact B.agrees zs ys (fun i => (normal_equiv R (ez i)).mpr (hn i))
      (fun i => (ez i).trans (ey i).symm) u v hit fire
  · refine ⟨_,normal_free_no_root hn (fun ys e u hit => yes ⟨ys,fun i => (e i).symm,u,hit⟩),.basis (.refl _),?_⟩
    exact fun ys e u hit => False.elim (yes ⟨ys,e,u,hit⟩)

theorem Stage.free (B : Bucket R d) (xs ns : Fin (s.arity d) → Term s) (marks)
    (kids : ∀ i, Stage R (marks i) (xs i) (ns i)) (guarded : Guard R d marks) :
    ∃ n, Stage R (some d) (.free d xs) n := by
  obtain ⟨n,norm,final,unique⟩ := result B ns (fun i => (kids i).normal)
  have early ys (rs : ∀ i, Reduces R (xs i) (ys i)) out (hit : R (.free d ys) out) : EquivB out n := by
    apply unique ys _ out hit
    intro i
    rcases (kids i).positions _ (rs i) with e|⟨f,mark,h⟩
    · exact e
    · exact False.elim (guarded ys out hit i f mark h)
  have closed {t u : Term s} (eq : EquivB t n) (red : Reduces R t u) : EquivB u n :=
    (normal_reduces_equiv red ((normal_equiv R eq).mpr norm)).symm.trans eq
  have split u := @reduces_free_until s R d xs (fun t => EquivB t n) closed early u
  refine ⟨n,norm,?_,?_⟩
  · intro u red
    rcases split u red with ⟨ys,rfl,rs⟩|e
    · exact (.free d ys ns (fun i => (kids i).converges _ (rs i)) : Reduces R _ _).trans final
    · exact .basis e
  · intro u red
    rcases split u red with ⟨ys,rfl,_⟩|e
    · exact .inr ⟨d,rfl,rfl⟩
    · exact .inl e

theorem Stage.unique {m} {x n a b : Term s} (stage : Stage R m x n)
    (l : NormalForm R x a) (r : NormalForm R x b) : EquivB a b :=
  (normal_reduces_equiv (stage.converges _ l.1) l.2.1).trans
    (normal_reduces_equiv (stage.converges _ r.1) r.2.1).symm

/-- A projected result follows zero or more ordinary child slots. -/
inductive Projection : Term s → Term s → Prop where
  | here (t) : Projection t t
  | child {t c v} : Immediate t c → Projection c v → Projection t v

theorem Projection.normal {t v : Term s} (path : Projection t v) (σ : Substitution s)
    (nt : Normal R (σ.apply t)) : Normal R (σ.apply v) := by
  induction path with
  | here => exact nt
  | child arg _ ih =>
    apply ih
    cases arg with
    | free _ _ i => exact normal_free_child _ _ nt i
    | comm_left => exact (normal_comm_children _ nt).1
    | comm_right => exact (normal_comm_children _ nt).2
    | ac_left => exact (normal_ac_children _ nt).1
    | ac_right => exact (normal_ac_children _ nt).2

theorem normal_return (r : RuleRow s d)
    (shape : (∃ i, Projection (r.input i) (r.value ())) ∨
      ((∀ v, ¬ (r.value ()).Occurs v) ∧ Normal R (r.value ())))
    (σ : Substitution s) (hn : ∀ i, Normal R (σ.apply (r.input i))) : Normal R (σ.apply (r.value ())) := by
  rcases shape with ⟨i,h⟩ | ⟨ground,n⟩
  · exact h.normal σ (hn i)
  · rwa [SpecializedRule.apply_ground ground]

theorem guard_of_heads {rows : List (RuleRow s d)} (covers : Covers R d rows) (marks)
    (heads : ∀ r ∈ rows, ∀ i f, marks i = some f →
      (∀ v, r.input i ≠ .var v) ∧ head (r.input i) ≠ .free f) : Guard R d marks := by
  intro ys out hit i f mark
  obtain ⟨r,hr,σ,args,_⟩ := covers _ _ hit
  obtain ⟨rigid,other⟩ := heads r hr i f mark
  have hd : head (ys i) = head (σ.apply (r.input i)) := (args i).head_eq
  rw [hd]
  generalize eq : r.input i = t at *
  cases t with
  | var v => exact (rigid v rfl).elim
  | atom | free | comm | ac => exact other

inductive Query (R : Root s) : Option s.FreeSym → Term s → Prop where
  | stable {t} : StableVariants.Stable R t → Query R none t
  | free (d : s.FreeSym) (xs : Fin (s.arity d) → Term s) (marks)
    (bucket : Bucket R d) (guarded : Guard R d marks) (children : ∀ i, Query R (marks i) (xs i)) :
    Query R (some d) (.free d xs)

/-- All stages share the original substitution, including occurrences of a
variable in different argument slots or different observations. -/
theorem Query.stage {m t} (q : Query R m t) (σ : Substitution s) (hn : Normalized R σ) :
    ∃ n, Stage R m (σ.apply t) n := by
  induction q with
  | stable h => exact ⟨_,Stage.leaf (h σ hn)⟩
  | free d xs marks b g _ ih => exact Stage.free b _ (fun i => (ih i).choose) marks (fun i => (ih i).choose_spec) g

theorem Query.caller_unique {m t} (q : Query R m t) {σ : Substitution s} (hn : Normalized R σ)
    {a b} (l : NormalForm R (σ.apply t) a) (r : NormalForm R (σ.apply t) b) : EquivB a b :=
  (q.stage σ hn).choose_spec.unique l r

end Tamarin.Rewriting.GuardedRuleBuckets
