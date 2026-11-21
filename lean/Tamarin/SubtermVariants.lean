import Tamarin.OperatorVariantBounds
import Tamarin.ContextualReduction
import Tamarin.MixedReconstruction
import Tamarin.SignatureExtension
import Tamarin.VariantJoin

/-! Finite variants for subterm, ground and constructor results modulo C/AC.
The rule head can be free or commutative. A proper subterm may lie below any
operators, including AC. A ground result may itself need further rewriting.
A constructor result rebuilds normal captures using operators inert in the combined table. -/
namespace Tamarin.SubtermVariants
open Rewriting MaudeOperations MixedUnification ShortVariantPaths ConstructorVariants
variable {s : Signature}

/-- The row's result is ground or comes from inside one of its arguments. -/
def Row (r : Equation s) : Prop := match r.lhs with
  | .free _ xs => r.rhs.Ground ∨ ∃ i, r.rhs ∈ subterms (xs i)
  | .comm _ a b => r.rhs.Ground ∨ r.rhs ∈ subterms a ∨ r.rhs ∈ subterms b
  | _ => False

/-- A constructor result may rebuild any number of captured variables. Every
operator in that result must be inert in the complete table. Range restriction
is supplied independently when deriving a bound. -/
def ResultRow (rs : Problem s) (r : Equation s) : Prop :=
  Row r ∨ ((match r.lhs with | .free .. | .comm .. => True | _ => False) ∧
    ∀ h ∈ operators r.rhs, h ∉ ruleHeads rs)

theorem ResultRow.application {rs : Problem s} {r : Equation s} (row : ResultRow rs r) :
    Application r.lhs := by
  cases src : r.lhs <;> simp_all [ResultRow,Row,Application]

theorem ResultRow.not_ac {rs : Problem s} {r : Equation s} (row : ResultRow rs r) (f : s.ACSym) :
    head r.lhs ≠ .ac f := by
  cases src : r.lhs <;> simp_all [ResultRow,Row,head,headModel,Model.eval]

def Presentation (rs : Problem s) := ∀ r ∈ rs, Row r

private theorem subterm_inherit {P : Term s → Prop} (t : Term s)
    (free : ∀ f xs i, P (xs i) → P (.free f xs))
    (comm : ∀ f a b, P a ∨ P b → P (.comm f a b))
    (ac : ∀ f a b, P a ∨ P b → P (.ac f a b)) :
    ∀ u ∈ subterms t, P u → P t := by
  induction t with
  | var | atom => intro u hu; cases List.mem_singleton.mp hu; exact id
  | free f xs ih =>
    intro u hu h
    rcases List.mem_cons.mp hu with rfl | sub
    · exact h
    · obtain ⟨l,hl,hu⟩ := List.mem_flatten.mp sub
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact free _ _ i (ih i _ hu h)
  | comm f a b l r | ac f a b l r =>
    intro u hu h
    rcases List.mem_cons.mp hu with rfl | sub
    · exact h
    · rcases List.mem_append.mp sub with ha | hb
      · first | exact comm _ _ _ (.inl (l _ ha h)) | exact ac _ _ _ (.inl (l _ ha h))
      · first | exact comm _ _ _ (.inr (r _ hb h)) | exact ac _ _ _ (.inr (r _ hb h))

theorem bound {rs : Problem s} (cls : Presentation rs) : ReferenceReduction.Bound rs := by
  intro r hr v hv
  have inside (t u : Term s) (hu : u ∈ subterms t) (occ : u.Occurs v) : t.Occurs v :=
    subterm_inherit (P := fun z => z.Occurs v) t (fun _ _ i h => ⟨i,h⟩)
      (fun _ _ _ => id) (fun _ _ _ => id) u hu occ
  have row := cls r hr
  cases h : r.lhs <;> simp only [Row,h] at row <;> try contradiction
  case free f xs =>
    rcases row with g | ⟨i,sub⟩
    · exact (g v hv).elim
    · exact ⟨i,inside _ _ sub hv⟩
  case comm f a b =>
    rcases row with g | sub | sub
    · exact (g v hv).elim
    · exact Or.inl (inside _ _ sub hv)
    · exact Or.inr (inside _ _ sub hv)

/-- Adding the caller's extra names or symbols preserves every eligible row. -/
theorem extend {rs : Problem s} (cls : Presentation rs) (extra : Signature) :
    Presentation (SignatureExtension.query extra rs) := by
  let embed := SignatureExtension.embed (s := s) extra
  have sub {u t : Term s} (mem : u ∈ subterms t) : embed u ∈ subterms (embed t) := by
    apply subterm_inherit (P := fun t => embed u ∈ subterms (embed t)) t _ _ _ u mem
    · cases u <;> simp [embed,SignatureExtension.embed,subterms]
    · intro f xs i h
      exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,h⟩)
    · intro f a b h; exact List.mem_cons_of_mem _ (List.mem_append.mpr h)
    · intro f a b h; exact List.mem_cons_of_mem _ (List.mem_append.mpr h)
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  have ground (g : e.rhs.Ground) : (embed e.rhs).Ground :=
    fun v h => g v ((SignatureExtension.embed_occurs ..).mp h)
  have row := cls e he
  cases h : e.lhs <;> simp only [Row,h] at row <;> try contradiction
  case free f xs =>
    simp only [Row,SignatureExtension.embed]
    exact row.imp ground (fun ⟨i,hi⟩ => ⟨i,sub hi⟩)
  case comm f a b =>
    simp only [Row,SignatureExtension.embed]
    exact row.imp ground (fun h => h.imp sub sub)

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]
variable {rs : Problem s} (scope : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs))

/-- This syntactic check needs neither a normalizer nor a search budget. -/
def accepts (rules : Problem s) : Bool := rules.all fun r =>
  let ground := r.rhs.variables.isEmpty
  match r.lhs with
  | .free _ xs => ground || (List.finRange _).any fun i => (subterms (xs i)).contains r.rhs
  | .comm _ a b => ground || ((subterms a).contains r.rhs || (subterms b).contains r.rhs)
  | _ => false

theorem accepts_iff (rules : Problem s) : accepts rules ↔ Presentation rules := by
  have ground (t : Term s) : t.variables.isEmpty ↔ t.Ground := by
    simp [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,Term.Ground,Term.mem_variables]
  unfold accepts Presentation
  rw [List.all_eq_true]
  apply forall_congr'; intro r
  apply forall_congr'; intro _
  cases src : r.lhs <;> simp [Row,src,ground]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- A subterm of a normal argument remains normal after the same substitution
has been applied to both. This includes paths through C and AC nodes. -/
theorem subnormal {R : Root s} (σ : Substitution s) {t u : Term s}
    (sub : u ∈ subterms t) (nf : Normal R (σ.apply t)) : Normal R (σ.apply u) := by
  apply Classical.byContradiction
  intro bad
  apply subterm_inherit (P := fun t => ¬ Normal R (σ.apply t)) t _ _ _ u sub bad nf
  · exact fun f xs i no yes => no (normal_free_child f _ yes i)
  · exact fun f a b no yes => no.elim (fun h => h (normal_comm_children f yes).1)
      (fun h => h (normal_comm_children f yes).2)
  · exact fun f a b no yes => no.elim (fun h => h (normal_ac_children f yes).1)
      (fun h => h (normal_ac_children f yes).2)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
/-- A rule substitution can have reducible images away from the pattern.
It suffices that the variables used by the result have normal images. -/
private theorem constructor_result_normal (apps : ∀ r ∈ rs, Application r.lhs) (t : Term s)
    (inert : ∀ h ∈ operators t, h ∉ ruleHeads rs) (σ : Substitution s)
    (used : ∀ v, t.Occurs v → Normal (ruleRoot rs) (σ.image v)) : Normal (ruleRoot rs) (σ.apply t) := by
  classical
  let τ := VariantJoin.choose t.Occurs σ Substitution.identity
  have eq : τ.apply t = σ.apply t := (VariantJoin.choose_apply ..).1 (fun _ => id)
  rw [← eq]
  apply (constructor_normal rs apps).2 t inert τ
  intro v
  by_cases occ : t.Occurs v
  · simpa [τ,VariantJoin.choose,occ] using used v occ
  · simpa [τ,VariantJoin.choose,occ] using (constructor_normal rs apps).1 v

include scope can

/-- A fixed finite table has a common finite normalization budget for all its
ground results, even if one of them uses equations owned by another operator. -/
private theorem ground_budget : ∃ k, ∀ r ∈ rs, r.rhs.Ground → ∀ σ : Substitution s,
    ∃ u, Path (ruleRoot rs) k (σ.apply r.rhs) u ∧ Normal (ruleRoot rs) u := by
  let red := ReferenceReduction.reducer rs scope can
  have run (r : Equation s) := exists_path (red.correct r.rhs).normalForm.1
  refine ⟨(rs.map fun r => (run r).choose).sum,fun r hr g σ => ?_⟩
  rw [g.apply_eq]
  exact ⟨_,(run r).choose_spec.weaken (FiniteOccurs.le_sum _ _ (List.mem_map_of_mem hr)),
    (red.correct r.rhs).normalForm.2.1⟩

/-- The bound at a free head uses only the shapes of rules for that head.
All hypotheses about normalization refer to the *whole* mixed table. -/
theorem free_result_bound (apps : ∀ r ∈ rs, Application r.lhs) (f : s.FreeSym)
    (rows : ∀ r ∈ rs, head r.lhs = .free f → ResultRow rs r) :
    ∃ k, ∀ xs, (∀ i, Normal (ruleRoot rs) (xs i)) → ∃ u,
      Path (ruleRoot rs) k (.free f xs) u ∧ Normal (ruleRoot rs) u := by
  obtain ⟨k,ground⟩ := ground_budget scope can
  refine ⟨k+1,fun xs normals => ?_⟩
  by_cases normal : Normal (ruleRoot rs) (.free f xs)
  · exact ⟨_,.basis (.refl _),normal⟩
  obtain ⟨u,st⟩ := Classical.not_forall.mp normal
  obtain ⟨ys,v,eq,⟨r,hr,σ,src,dst⟩,out⟩ := (stepModulo_free_iff normals).mp (Classical.not_not.mp st)
  have atRoot : head r.lhs = .free f :=
    (instance_head r (apps r hr) σ).symm.trans (congrArg head src.symm)
  have shape := rows r hr atRoot
  cases h : r.lhs <;> simp only [h,head] at atRoot <;> try contradiction
  case free g as =>
    cases atRoot
    simp only [ResultRow,Row,h,true_and] at shape
    rw [h] at src
    have kids : ys = (fun i => σ.apply (as i)) := Term.free.inj src |>.2 |> eq_of_heq
    have step : StepModulo (ruleRoot rs) (.free f xs) (σ.apply r.rhs) :=
      ⟨_,_,.free f _ _ eq,.root ⟨r,hr,σ,h ▸ src,rfl⟩,.refl _⟩
    have normalArg i : Normal (ruleRoot rs) (σ.apply (as i)) := by
      simpa only [kids] using (normal_equiv _ (eq i)).mp (normals i)
    rcases shape with (clean | ⟨i,sub⟩) | inert
    · obtain ⟨u,p,nf⟩ := ground r hr clean σ; exact ⟨u,.step step p,nf⟩
    · exact ⟨_,.step step (.basis (.refl _)),subnormal σ sub (normalArg i)⟩
    · refine ⟨_,.step step (.basis (.refl _)),constructor_result_normal apps _ inert σ ?_⟩
      intro v hv
      obtain ⟨i,occ⟩ : ∃ i, (as i).Occurs v := by simpa only [h,Term.Occurs] using scope r hr v hv
      exact RulePattern.image_normal (normalArg i) occ

theorem comm_result_bound (apps : ∀ r ∈ rs, Application r.lhs) (f : s.CSym)
    (rows : ∀ r ∈ rs, head r.lhs = .comm f → ResultRow rs r) :
    ∃ k, ∀ a b, Normal (ruleRoot rs) a → Normal (ruleRoot rs) b → ∃ u,
      Path (ruleRoot rs) k (.comm f a b) u ∧ Normal (ruleRoot rs) u := by
  obtain ⟨k,ground⟩ := ground_budget scope can
  refine ⟨k+1,fun a b na nb => ?_⟩
  by_cases normal : Normal (ruleRoot rs) (.comm f a b)
  · exact ⟨_,.basis (.refl _),normal⟩
  obtain ⟨u,st⟩ := Classical.not_forall.mp normal
  rcases (ContextualReduction.comm_iff ..).mp (Classical.not_not.mp st) with
    ⟨p,q,eq,⟨r,hr,σ,src,dst⟩,out⟩ | ⟨_,step,_⟩ | ⟨_,step,_⟩
  · subst p q
    have atRoot := (instance_head r (apps r hr) σ).symm.trans eq.head_eq.symm
    have shape := rows r hr atRoot
    have step : StepModulo (ruleRoot rs) (.comm f a b) (σ.apply r.rhs) :=
      ⟨_,_,eq,.root ⟨r,hr,σ,rfl,rfl⟩,.refl _⟩
    cases h : r.lhs <;> simp only [h,head] at atRoot <;> try contradiction
    case comm g x y =>
      cases atRoot
      simp only [ResultRow,Row,h,true_and] at shape
      rw [h] at eq
      have kids : Normal (ruleRoot rs) (σ.apply x) ∧ Normal (ruleRoot rs) (σ.apply y) := by
        rcases (Commutative.equiv_iff ..).mp eq with ⟨l,r⟩ | ⟨l,r⟩
        · exact ⟨(normal_equiv _ l).mp na,(normal_equiv _ r).mp nb⟩
        · exact ⟨(normal_equiv _ r).mp nb,(normal_equiv _ l).mp na⟩
      rcases shape with (clean | sub | sub) | inert
      · obtain ⟨u,p,nf⟩ := ground r hr clean σ; exact ⟨u,.step step p,nf⟩
      · exact ⟨_,.step step (.basis (.refl _)),subnormal σ sub kids.1⟩
      · exact ⟨_,.step step (.basis (.refl _)),subnormal σ sub kids.2⟩
      · refine ⟨_,.step step (.basis (.refl _)),constructor_result_normal apps _ inert σ ?_⟩
        intro v hv
        have occ : x.Occurs v ∨ y.Occurs v := by simpa only [h,Term.Occurs] using scope r hr v hv
        exact occ.elim (RulePattern.image_normal kids.1) (RulePattern.image_normal kids.2)
  · exact (na _ step).elim
  · exact (nb _ step).elim

theorem free_bound (apps : ∀ r ∈ rs, Application r.lhs) (f : s.FreeSym)
    (rows : ∀ r ∈ rs, head r.lhs = .free f → Row r) :
    ∃ k, ∀ xs, (∀ i, Normal (ruleRoot rs) (xs i)) → ∃ u,
      Path (ruleRoot rs) k (.free f xs) u ∧ Normal (ruleRoot rs) u :=
  free_result_bound scope can apps f (fun r hr hd => .inl (rows r hr hd))

theorem comm_bound (apps : ∀ r ∈ rs, Application r.lhs) (f : s.CSym)
    (rows : ∀ r ∈ rs, head r.lhs = .comm f → Row r) :
    ∃ k, ∀ a b, Normal (ruleRoot rs) a → Normal (ruleRoot rs) b → ∃ u,
      Path (ruleRoot rs) k (.comm f a b) u ∧ Normal (ruleRoot rs) u :=
  comm_result_bound scope can apps f (fun r hr hd => .inl (rows r hr hd))

/-- A canonical table of free/C rules with subterm, ground or constructor
results has finite variants on all tuples, including open kind-level inputs. -/
theorem finiteResultVariants (cls : ∀ r ∈ rs, ResultRow rs r) :
    FiniteVariantProperty (ruleRoot rs) := by
  have apps := fun r hr => (cls r hr).application
  apply finiteVariantProperty_of_operators scope can
  refine ⟨fun f => free_result_bound scope can apps f (fun r hr _ => cls r hr),
    fun f => comm_result_bound scope can apps f (fun r hr _ => cls r hr),?_⟩
  intro f
  have inert : Head.ac f ∉ ruleHeads rs := by
    rintro member
    obtain ⟨r,hr,hd⟩ := List.mem_map.mp member
    exact (cls r hr).not_ac f hd
  exact ⟨0,fun a b na nb => ⟨_,.basis (.refl _),constructor_node_normal rs apps (.ac f a b) inert ⟨na,nb⟩⟩⟩

omit scope can

theorem finiteVariants (can : CanonicalPresentation (ruleRoot rs)) (cls : Presentation rs) :
    FiniteVariantProperty (ruleRoot rs) :=
  finiteResultVariants (bound cls) can (fun r hr => .inl (cls r hr))

end Tamarin.SubtermVariants
