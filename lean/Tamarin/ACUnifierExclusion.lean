import Tamarin.AtomicACPair
import Tamarin.ACPivot
import Tamarin.ACSubgroups
import Tamarin.StableVariants
import Tamarin.VariantJoinRenaming

/-! An AC root may be exposed by reassociation. With two indivisible,
normal factors, every rewrite is at the root of a representative of the
whole pair. An ordinary sorted unifier can refute the possibility of this
rewrite under every caller substitution, including ones identifying names. -/
namespace Tamarin.Rewriting.ACUnifierExclusion
open ConstructorVariants Cancellation
variable {s : Signature} {R : Root s}

/-- Operands of every B-equivalent binary representative can only have
exchanged places, up to equivalence within the operands. -/
private theorem aligned_normal {f : s.ACSym} {a b c d : Term s}
    (ha : flatten f a = [classOf a]) (hb : flatten f b = [classOf b])
    (na : Normal R a) (nb : Normal R b) (e : EquivB (.ac f a b) (.ac f c d)) :
    Normal R c ∧ Normal R d := by
  rcases (AtomicACPair.equiv_iff f a b c d ha hb).mp e with ⟨ac,bd⟩|⟨ad,bc⟩
  · exact ⟨(normal_equiv _ ac).mp na,(normal_equiv _ bd).mp nb⟩
  · exact ⟨(normal_equiv _ bc).mp nb,(normal_equiv _ ad).mp na⟩

theorem pair_step_iff {f : s.ACSym} {a b u : Term s}
    (ha : flatten f a = [classOf a]) (hb : flatten f b = [classOf b])
    (na : Normal R a) (nb : Normal R b) :
    StepModulo R (.ac f a b) u ↔ ∃ v w, EquivB (.ac f a b) v ∧ R v w ∧ EquivB w u := by
  constructor
  · rintro ⟨v,w,eq,step,out⟩
    cases step with
    | root r => exact ⟨_,_,eq,r,out⟩
    | free | comm_left | comm_right => cases eq.head_eq
    | ac_left g c st =>
      obtain rfl := Head.ac.inj eq.head_eq
      exact False.elim ((aligned_normal ha hb na nb eq).1 _ ⟨_,_,.refl _,st,.refl _⟩)
    | ac_right g c st =>
      obtain rfl := Head.ac.inj eq.head_eq
      exact False.elim ((aligned_normal ha hb na nb eq).2 _ ⟨_,_,.refl _,st,.refl _⟩)
  · rintro ⟨v,w,e,r,h⟩
    exact ⟨v,w,e,.root r,h⟩

/-- Once a root rewrite is available, checking all possible root outputs
against a common normal result also proves uniqueness for arbitrary
reduction derivations. This allows overlapping active rules. -/
theorem normalForm_pair_root_unique {f : s.ACSym} {a b v u : Term s}
    (ha : flatten f a = [classOf a]) (hb : flatten f b = [classOf b])
    (na : Normal R a) (nb : Normal R b) (nv : Normal R v)
    (fires : StepModulo R (.ac f a b) v)
    (outputs : ∀ x y, EquivB (.ac f a b) x → R x y → EquivB y v)
    (form : NormalForm R (.ac f a b) u) : EquivB u v := by
  have go {x y} (red : Reduces R x y) : EquivB (.ac f a b) x → EquivB (.ac f a b) y ∨ EquivB y v := by
    induction red with
    | basis e => exact fun q => .inl (q.trans e)
    | step hs =>
      rintro q
      obtain ⟨s,t,e,step,out⟩ := hs
      obtain ⟨s',t',eq,root,finish⟩ := (pair_step_iff ha hb na nb).mp ⟨s,t,q.trans e,step,out⟩
      exact .inr (finish.symm.trans (outputs s' t' eq root))
    | trans first second ih ik =>
      intro q
      rcases ih q with e|e
      · exact ik e
      · exact .inr ((normal_reduces_equiv second ((normal_equiv _ e).mpr nv)).symm.trans e)
    | free | comm => intro q; cases q.head_eq
    | ac g rx ry _ _ =>
      intro q; obtain rfl := Head.ac.inj q.head_eq
      have normals := aligned_normal ha hb na nb q
      exact .inl (q.trans (.ac_congr _ (normal_reduces_equiv rx normals.1) (normal_reduces_equiv ry normals.2)))
  rcases go form.1 (.refl _) with e|e
  · exact False.elim (((normal_equiv _ e).mpr form.2.1) v fires)
  · exact e

/-- A rule and a subject have independent scopes. Freshen all occurrences
of each local rule variable together; an implementation may also rebuild
and reorder either term modulo B before ordinary unification. -/
structure Refuted (subject lhs : Term s) : Prop where
  certified : ∃ (π : VariablePermutation) (l r : Term s),
    (∀ v, ((π.subst s).apply lhs).Occurs v → ¬subject.Occurs v) ∧
    EquivB subject l ∧ EquivB ((π.subst s).apply lhs) r ∧ CompleteSet [⟨l,r⟩] []

/-- Rust only allocates names that occur in the left side. A local sorted
injection avoiding the query suffices, including overlapping old/new ranges. -/
theorem Refuted.of_allocation (subject lhs l r : Term s)
    (alloc : CallerFreshening.Allocation lhs.variables)
    (fresh : ∀ v ∈ lhs.variables, ¬subject.Occurs (alloc.assign v))
    (ql : EquivB subject l) (pattern : EquivB (lhs.subst (fun w => .var (alloc.assign w))) r)
    (none : CompleteSet [⟨l,r⟩] []) : Refuted subject lhs := by
  obtain ⟨π,assigned⟩ := VariantJoin.extendAllocation _ _ alloc.sorted alloc.injective
  have same : (π.subst s).apply lhs = lhs.subst (fun w => .var (alloc.assign w)) :=
    Term.subst_eq_of_agree _ _ _ fun w hw =>
      congrArg Term.var (assigned w ((lhs.mem_variables w).mpr hw))
  refine ⟨π,l,r,?_,ql,same ▸ pattern,none⟩
  intro v hv
  obtain ⟨w,hw,image⟩ := (π.subst s).occurs_in_image lhs v hv
  change v = π.forward w at image
  have hm := (lhs.mem_variables w).mpr hw
  rw [image,assigned w hm]
  exact fresh w hm

theorem Refuted.incompatible {subject lhs : Term s} (miss : Refuted subject lhs)
    (ρ τ : Substitution s) : ¬EquivB (ρ.apply subject) (τ.apply lhs) := by
  obtain ⟨π,l,r,apart,ql,pr,no⟩ := miss.certified
  let η := τ.compose (π.inverse.subst s)
  let joint := VariantJoin.choose subject.Occurs ρ η
  have query : joint.apply subject = ρ.apply subject :=
    (VariantJoin.choose_apply _ _ _ _).1 (fun _ h => h)
  have rule : joint.apply ((π.subst s).apply lhs) = τ.apply lhs := by
    rw [(VariantJoin.choose_apply _ _ _ _).2 apart]
    simp only [η,Substitution.apply_compose,π.inverse_apply]
  intro same
  apply (complete_empty_iff _).mp no
  refine ⟨joint,?_⟩
  intro e h; obtain rfl := List.mem_singleton.mp h
  exact (ql.subst joint.image).symm.trans ((query ▸ rule ▸ same).trans (pr.subst joint.image))

/-- The solver enters the standardized rule on the left of the equations.
Empty completeness transfers through exchange of sides. -/
theorem Refuted.of_pattern_first (subject lhs l r : Term s)
    (alloc : CallerFreshening.Allocation lhs.variables)
    (fresh : ∀ v ∈ lhs.variables, ¬subject.Occurs (alloc.assign v))
    (ql : EquivB subject l) (pattern : EquivB (lhs.subst (fun w => .var (alloc.assign w))) r)
    (none : CompleteSet [⟨r,l⟩] []) : Refuted subject lhs := by
  apply Refuted.of_allocation subject lhs l r alloc fresh ql pattern
  apply (complete_empty_iff _).mpr
  rintro ⟨σ,sol⟩
  apply (complete_empty_iff _).mp none
  refine ⟨σ,?_⟩
  intro e h; obtain rfl := List.mem_singleton.mp h
  exact (sol _ List.mem_cons_self).symm

/-- With two indivisible caller operands, the two ordinary *conjunctions*
tested by Rust exhaust AC alignment. Repeated names in either side receive
one binding across both equations in each conjunction. -/
theorem Refuted.of_orientations (subject lhs : Term s) (f : s.ACSym) (a b x y : Term s)
    (alloc : CallerFreshening.Allocation lhs.variables)
    (fresh : ∀ v ∈ lhs.variables, ¬subject.Occurs (alloc.assign v))
    (ql : EquivB subject (.ac f a b))
    (pattern : EquivB (lhs.subst (fun w => .var (alloc.assign w))) (.ac f x y))
    (ha : AtomicACPair.Atomic f a) (hb : AtomicACPair.Atomic f b)
    (direct : CompleteSet [⟨x,a⟩,⟨y,b⟩] []) (crossed : CompleteSet [⟨x,b⟩,⟨y,a⟩] []) :
    Refuted subject lhs := by
  apply Refuted.of_pattern_first subject lhs _ _ alloc fresh ql pattern
  let q : AtomicACPair.Query s := ⟨f,x,y,a,b,[]⟩
  apply (complete_empty_iff _).mpr
  rintro ⟨σ,sol⟩
  rcases (q.solves_iff (.inr ⟨ha,hb⟩) σ).mp sol with d|c
  · exact (complete_empty_iff _).mp direct ⟨σ,d⟩
  · exact (complete_empty_iff _).mp crossed ⟨σ,c⟩

private theorem positive (f : s.ACSym) (a : Term s) : 0 < (flatten f a).length := by
  have fold := fold_flatten f a
  cases eq : flatten f a with
  | nil => rw [eq] at fold; contradiction
  | cons => simp

/-- AC has no unit, so substitution cannot lower the top-level factor count. -/
theorem factor_lower_bound (f : s.ACSym) (t : Term s) (τ : Substitution s) :
    (flatten f t).length ≤ (flatten f (τ.apply t)).length := by
  induction t with
  | ac g a b ia ib =>
    by_cases e : f = g
    · subst g
      change _ ≤ (flatten f (.ac f (τ.apply a) (τ.apply b))).length
      simp only [flatten_ac,List.length_append]; exact Nat.add_le_add ia ib
    · simp [Substitution.apply,Term.subst,flatten,e]
  | var v => exact positive f (τ.image v)
  | atom | free | comm => exact Nat.le_refl _

/-- The subject of an ordinary match stays rigid, so an individual conjunct
can refute the full search using just the widths of its two AC normalizations
modulo B. Additional rewrite equations never participate in this comparison. -/
theorem refute_directional_width (f : s.ACSym) {p t : Term s}
    (smaller : (flatten f t).length < (flatten f p).length) (σ : Substitution s) :
    ¬ EquivB (σ.apply p) t := by
  intro eq
  have width := (flatten_equiv f eq).length_eq
  have bound := factor_lower_bound f p σ
  omega

/-- Each operand position is visible separately even when two positions
carry the same term. Reordering or reassociating the packed term is allowed. -/
def Represents (f : s.ACSym) (actual : Term s) (positions : List (Term s)) : Prop :=
  ∃ decoded, ACRepresentation.decode f positions = some decoded ∧ EquivB actual decoded

theorem Represents.specializes {f : s.ACSym} {actual : Term s} {ts : List (Term s)}
    (rep : Represents f actual ts) (ρ : Substitution s)
    (atomic : ∀ t ∈ ts, flatten f (ρ.apply t) = [classOf (ρ.apply t)]) :
    (flatten f (ρ.apply actual)).Perm (ts.map (fun t => classOf (ρ.apply t))) := by
  obtain ⟨d,dec,eq⟩ := rep
  cases ts with
  | nil => cases dec
  | cons a xs =>
    cases dec
    apply (flatten_equiv f (eq.subst ρ.image)).trans
    change (flatten f (ρ.apply (ACRepresentation.fold f a xs))).Perm _
    rw [ACPivot.fold_factors]
    have images (ts : List (Term s)) (all : ∀ t ∈ ts, flatten f (ρ.apply t) = [classOf (ρ.apply t)]) :
        ACPivot.factors f ρ ts = ts.map (fun t => classOf (ρ.apply t)) := by
      induction ts with
      | nil => rfl
      | cons t tail ih =>
        change flatten f (ρ.apply t) ++ ACPivot.factors f ρ tail = _
        rw [all t List.mem_cons_self, ih (fun k hk => all k (List.mem_cons_of_mem _ hk))]
        rfl
    rw [images _ atomic]

/-- Certify all subbags at once, for every normalized specialization of the
caller. A single numeral per operand position suffices even when positions
share variables. Refuting only the complete product does not meet this contract. -/
def StableSubgroups (select : ACSubgroups.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (rules : List (Equation s))
    (_ : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (whole : Term s)
    {width : UInt64} {rows} (_ : select width = some rows) (read : UInt64 → Term s)
    (piece : List UInt64 → Term s),
    let ids := (List.range width.toNat).map Nat.toUInt64
    Represents f whole (ids.map read) →
    (∀ i ∈ ids, AtomicACPair.Atomic f (read i) ∧ StableVariants.Stable (ruleRoot rules) (read i)) →
    (∀ row : List UInt64, row.toArray ∈ rows → Represents f (piece row) (row.map read)) →
    (∀ row : List UInt64, row.toArray ∈ rows → ∀ r ∈ rules, head r.lhs = .ac f →
      row.length < (flatten f r.lhs).length ∨ Refuted (piece row) r.lhs) →
    StableVariants.Stable (ruleRoot rules) whole

/-- At a single specialization only the actual operands need to be
indivisible and normal. This includes concrete reduction at the identity. -/
def PointwiseSubgroups (select : ACSubgroups.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (rules : List (Equation s))
    (_ : ∀ r ∈ rules, Application r.lhs) (f : s.ACSym) (whole : Term s)
    {width : UInt64} {rows} (_ : select width = some rows) (read : UInt64 → Term s)
    (piece : List UInt64 → Term s) (ρ : Substitution s),
    let ids := (List.range width.toNat).map Nat.toUInt64
    Represents f whole (ids.map read) →
    (∀ i ∈ ids, flatten f (ρ.apply (read i)) = [classOf (ρ.apply (read i))] ∧
      Normal (ruleRoot rules) (ρ.apply (read i))) →
    (∀ row : List UInt64, row.toArray ∈ rows → Represents f (piece row) (row.map read)) →
    (∀ row : List UInt64, row.toArray ∈ rows → ∀ r ∈ rules, head r.lhs = .ac f →
      row.length < (flatten f r.lhs).length ∨ Refuted (piece row) r.lhs) →
    Normal (ruleRoot rules) (ρ.apply whole)

theorem pointwiseSubgroups {select : ACSubgroups.Kernel} (ok : ACSubgroups.Correct select) :
    PointwiseSubgroups select := by
  intro s inst rules apps f whole width rows ran read piece ρ
  dsimp only
  intro packed children parts bucket
  let ids := (List.range width.toNat).map Nat.toUInt64
  let value := fun i => classOf (ρ.apply (read i))
  have layout : (flatten f (ρ.apply whole)).Perm (ids.map value) := by
    simpa only [ids,value,List.map_map,Function.comp_def] using packed.specializes ρ (by
      rintro t h; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h; exact (children i hi).1)
  refine DHProduct.subgroup_normal f _ ?_ ?_
  · intro t ht
    have h : classOf t ∈ flatten f (ρ.apply whole) := by
      rw [DHProduct.classes]; exact List.mem_map_of_mem ht
    obtain ⟨i,hi,same⟩ := List.mem_map.mp (layout.mem_iff.mp h)
    exact (normal_equiv _ (Quotient.exact same)).mp (children i hi).2
  · rintro p q headP ⟨rest,occ⟩ ⟨r,hr,τ,rfl,_⟩
    have two : 2 ≤ (flatten f (τ.apply r.lhs)).length := by
      generalize h : τ.apply r.lhs = v at headP ⊢
      cases v with
      | ac g a b =>
        cases headP; rw [flatten_ac,List.length_append]
        have := positive f a; have := positive f b; omega
      | _ => cases headP
    obtain ⟨row,mem,perm⟩ := ACSubgroups.covers ok ran value (occ.symm.trans layout) two
    have inside (i) (hi : i ∈ row) : i ∈ ids := by
      obtain ⟨sub,hs,_,hp⟩ := ((ok width).2 rows ran row).mp ⟨row,mem,.refl _⟩
      exact hs.subset (hp.mem_iff.mpr hi)
    have specialized : (flatten f (ρ.apply (piece row))).Perm (row.map value) := by
      simpa only [value,List.map_map,Function.comp_def] using (parts row mem).specializes ρ (by
        rintro t h; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h; exact (children i (inside i hi)).1)
    rcases bucket row mem r hr ((instance_head r (apps r hr) τ).symm.trans headP) with big|no
    · have len := perm.length_eq
      rw [List.length_map] at len
      have := factor_lower_bound f r.lhs τ
      omega
    · exact no.incompatible ρ τ (equiv_of_flatten_perm f (specialized.trans perm))

theorem stableSubgroups {select : ACSubgroups.Kernel} (ok : ACSubgroups.Correct select) :
    StableSubgroups select := by
  intro s inst rules apps f whole width rows ran read piece
  dsimp only
  intro packed children parts bucket ρ hn
  exact pointwiseSubgroups ok rules apps f whole ran read piece ρ packed
    (fun i hi => ⟨(children i hi).1 ρ,(children i hi).2 ρ hn⟩) parts bucket

theorem pairAt (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (a b : Term s) (ρ : Substitution s)
    (ha : flatten f (ρ.apply a) = [classOf (ρ.apply a)])
    (hb : flatten f (ρ.apply b) = [classOf (ρ.apply b)])
    (na : Normal (ruleRoot rules) (ρ.apply a)) (nb : Normal (ruleRoot rules) (ρ.apply b))
    (bucket : ∀ r ∈ rules, head r.lhs = .ac f →
      2 < (flatten f r.lhs).length ∨ Refuted (.ac f a b) r.lhs) :
    Normal (ruleRoot rules) (ρ.apply (.ac f a b)) := by
  intro u step
  obtain ⟨v,w,e,⟨r,mem,τ,rfl,_⟩,_⟩ := (pair_step_iff ha hb na nb).mp step
  rcases bucket r mem ((instance_head r (apps r mem) τ).symm.trans e.head_eq.symm) with large|no
  · have size := (flatten_equiv f e).length_eq
    rw [flatten_ac,ha,hb] at size
    simp only [List.singleton_append,List.length_cons,List.length_nil] at size
    have := factor_lower_bound f r.lhs τ
    omega
  · exact no.incompatible ρ τ e

theorem pairStable (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (a b : Term s) (ha : AtomicACPair.Atomic f a) (hb : AtomicACPair.Atomic f b)
    (na : StableVariants.Stable (ruleRoot rules) a) (nb : StableVariants.Stable (ruleRoot rules) b)
    (bucket : ∀ r ∈ rules, head r.lhs = .ac f →
      2 < (flatten f r.lhs).length ∨ Refuted (.ac f a b) r.lhs) :
    StableVariants.Stable (ruleRoot rules) (.ac f a b) :=
  fun ρ hn => pairAt rules apps f a b ρ (ha ρ) (hb ρ) (na ρ hn) (nb ρ hn) bucket

end Tamarin.Rewriting.ACUnifierExclusion
