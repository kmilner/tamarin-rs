import Tamarin.HereditaryConvergence
import Tamarin.OpenNarrowing

/-! Staging for an active free head with positional constructor patterns.
A rule may use a variable repeatedly in different arguments. Even when an
early root rewrite discards other arguments, every match projects to one
shared assignment on the normalized children. -/
namespace Tamarin.Rewriting.PositionalConvergence
open ConstructorVariants
variable {s : Signature} {R : Root s}

/-- The dispatcher compiles variable leaves of sort Msg and declared free
constructors with Msg argument slots. Nullary constants are included. -/
inductive Pattern (R : Root s) : Term s → Prop where
  | var (v : Variable) : v.sort = .msg → Pattern R (.var v)
  | free (f : s.FreeSym) (inert : ∀ ys t, ¬R (.free f ys) t)
      (slots : ∀ i, s.inputSort f i = .msg) (xs : Fin (s.arity f) → Term s)
      (children : ∀ i, Pattern R (xs i)) : Pattern R (.free f xs)

private def Witness (R : Root s) (σ : Substitution s) (v : Variable) (n : Term s) :=
  HasSort n v.sort ∧ Normal R n ∧ Converges R (σ.image v) n

noncomputable section
open Classical

private noncomputable def settled (R : Root s) (σ : Substitution s) (keys : List Variable) : Substitution s where
  image v := if v ∈ keys then if h : ∃ n, Witness R σ v n then h.choose else .var v else .var v
  support := keys
  outside v off := by simp [off]
  sorted v := by
    split
    · split
      · next ex => exact ex.choose_spec.1
      · exact .var _
    · exact .var _

private theorem settled_agrees {σ : Substitution s} {keys : List Variable} {v n}
    (localKey : v ∈ keys) (w : Witness R σ v n) :
    EquivB ((settled R σ keys).image v) n ∧ Converges R (σ.image v) ((settled R σ keys).image v) := by
  have ex : ∃ m, Witness R σ v m := ⟨n,w⟩
  simp only [settled,ite_eq_left localKey,dite_eq_left ex]
  exact ⟨Converges.agree ex.choose_spec.2.2 w.2.2 ex.choose_spec.2.1,ex.choose_spec.2.2⟩

/-- Normalize the assignment once for the whole rule. Its occurrences under
all positional constructors converge to the same value modulo B. -/
private theorem liftPattern {p : Term s} (pat : Pattern R p) {n : Term s} (hn : Normal R n)
    (typed : HasSort n .msg) (σ : Substitution s) (keys : List Variable)
    (scope : ∀ v, p.Occurs v → v ∈ keys) (conv : Converges R (σ.apply p) n) :
    EquivB ((settled R σ keys).apply p) n ∧
    ∀ v, p.Occurs v → Converges R (σ.image v) ((settled R σ keys).image v) := by
  induction pat generalizing n with
  | var v sort =>
    have hit := settled_agrees (scope v rfl) (show Witness R σ v n from ⟨sort ▸ typed,hn,conv⟩)
    exact ⟨hit.1,fun w eq => eq ▸ hit.2⟩
  | free f inert slots xs _ ih =>
    obtain ⟨ns,rfl,children⟩ := Converges.free_view f inert conv
    have check := Term.checkSort_complete typed
    simp only [Term.checkSort,Bool.and_eq_true,List.all_eq_true] at check
    have child i := ih i (normal_free_child f ns hn i)
      (slots i ▸ Term.checkSort_sound _ _ (check.2 i (List.mem_finRange i)))
      (fun v hv => scope v ⟨i,hv⟩) (children i)
    exact ⟨.free f _ ns (fun i => (child i).1),fun v ⟨i,occ⟩ => (child i).2 v occ⟩

private theorem Pattern.free_shape {p : Term s} (h : Pattern R p) : RulePattern.Free p := by
  induction h with
  | var => exact .var _
  | free f _ _ xs _ ih => exact .free f xs ih

/-- A rule can return a selected variable or a fixed normal constant. Only
a root match at the fully normalized children needs to be evaluated. -/
inductive Result (R : Root s) {m : Nat} (p : Fin m → Term s) : Term s → Prop where
  | selected (v : Variable) (occurs : ∃ i, (p i).Occurs v) : Result R p (.var v)
  | fixed (n : Term s) (ground : ∀ v, ¬n.Occurs v)
      (normal : Normal R n) : Result R p n

theorem staged (d : s.FreeSym) (p : Fin (s.arity d) → Term s) (rhs : Term s)
    (patterns : ∀ i, Pattern R (p i)) (ret : Result R p rhs)
    (table : ∀ ys t, R (.free d ys) t ↔ ∃ σ : Substitution s,
      (∀ i, ys i = σ.apply (p i)) ∧ t = σ.apply rhs)
    (xs ns : Fin (s.arity d) → Term s) (kids : ∀ i, Converges R (xs i) (ns i))
    (normal : ∀ i, Normal R (ns i)) (typed : ∀ i, HasSort (ns i) .msg)
    {n : Term s} (endPoint : Converges R (.free d ns) n) : Converges R (.free d xs) n := by
  apply Converges.active_free d xs n
  · intro ys rs
    exact (.free d ys ns (fun i => kids i _ (rs i)) : Reduces R _ _).trans
      (endPoint _ (.basis (.refl _)))
  intro ys rs t fired
  obtain ⟨σ,hit,rfl⟩ := (table ys t).mp fired
  let keys := (List.ofFn p).flatMap Term.variables
  have scope i v (hv : (p i).Occurs v) : v ∈ keys :=
    List.mem_flatMap.mpr ⟨p i,List.mem_ofFn.mpr ⟨i,rfl⟩,((p i).mem_variables v).mpr hv⟩
  have lift i := liftPattern (patterns i) (normal i) (typed i) σ keys (scope i)
    ((hit i) ▸ (kids i).follow (rs i))
  let τ := settled R σ keys
  have root := (table (fun i => τ.apply (p i)) (τ.apply rhs)).mpr ⟨τ,fun _ => rfl,rfl⟩
  have red : Reduces R (.free d ns) (τ.apply rhs) :=
    .step ⟨_,_,.free d _ _ (fun i => (lift i).1.symm),.root root,.refl _⟩
  have after := endPoint _ red
  cases ret with
  | selected z mem =>
    obtain ⟨i,occ⟩ := mem
    intro u ru
    exact ((lift i).2 z occ u ru).trans after
  | fixed c ground norm =>
    rw [SpecializedRule.apply_ground ground] at after ⊢
    exact fun _ r => (Converges.normal norm _ r).trans after

/-- The normalized children either have no root match, or every root match
returns the same normal value. This proof also supplies the endpoint needed
for staging, for the entire declared pattern class. -/
theorem endpoint (d : s.FreeSym) (p : Fin (s.arity d) → Term s) (rhs : Term s)
    (patterns : ∀ i, Pattern R (p i)) (ret : Result R p rhs)
    (table : ∀ ys t, R (.free d ys) t ↔ ∃ σ : Substitution s,
      (∀ i, ys i = σ.apply (p i)) ∧ t = σ.apply rhs)
    (ns : Fin (s.arity d) → Term s) (normal : ∀ i, Normal R (ns i)) :
    ∃ n, Normal R n ∧ Converges R (.free d ns) n := by
  by_cases h : ∃ σ : Substitution s, ∀ i, EquivB (ns i) (σ.apply (p i))
  · obtain ⟨σ,matched⟩ := h
    have nv : Normal R (σ.apply rhs) := by
      cases ret with
      | selected z occurs =>
        obtain ⟨i,occ⟩ := occurs
        exact RulePattern.image_normal ((normal_equiv R (matched i)).mp (normal i)) occ
      | fixed c ground n => rw [SpecializedRule.apply_ground ground]; exact n
    refine ⟨σ.apply rhs,nv,?_⟩
    have fire : StepModulo R (.free d ns) (σ.apply rhs) :=
      ⟨_,_,.free d _ _ matched,.root ((table _ _).mpr ⟨σ,fun _ => rfl,rfl⟩),.refl _⟩
    have results ys (basis : ∀ i, EquivB (ns i) (ys i)) b (hit : R (.free d ys) b) :
        EquivB b (σ.apply rhs) := by
      obtain ⟨τ,eq,rfl⟩ := (table _ _).mp hit
      cases ret with
      | selected z occurs =>
        obtain ⟨i,occ⟩ := occurs
        exact RulePattern.image_equiv (patterns i).free_shape
          (((eq i ▸ basis i).symm).trans (matched i)) occ
      | fixed c ground _ => rw [SpecializedRule.apply_ground ground,SpecializedRule.apply_ground ground]; exact .refl _
    intro u red
    rcases reduces_free_root_cases normal nv results red with e|e
    · exact (.basis e.symm : Reduces R _ _).trans (.step fire)
    · exact .basis e
  · have irreducible := normal_free_no_root normal (fun ys basis b root => by
      obtain ⟨σ,eq,_⟩ := (table ys b).mp root
      exact h ⟨σ,fun i => eq i ▸ basis i⟩)
    exact ⟨_,irreducible,Converges.normal irreducible⟩

theorem unique_value (d : s.FreeSym) (p : Fin (s.arity d) → Term s) (rhs : Term s)
    (patterns : ∀ i, Pattern R (p i)) (ret : Result R p rhs)
    (table : ∀ ys t, R (.free d ys) t ↔ ∃ σ : Substitution s,
      (∀ i, ys i = σ.apply (p i)) ∧ t = σ.apply rhs)
    (xs ns : Fin (s.arity d) → Term s) (kids : ∀ i, Converges R (xs i) (ns i))
    (normal : ∀ i, Normal R (ns i)) (typed : ∀ i, HasSort (ns i) .msg) :
    ∃ n, Normal R n ∧ Converges R (.free d xs) n ∧ Converges R (.free d ns) n := by
  obtain ⟨n,hn,endPoint⟩ := endpoint d p rhs patterns ret table ns normal
  exact ⟨n,hn,staged d p rhs patterns ret table xs ns kids normal typed endPoint,endPoint⟩

/-- Replacing the caller's changing arguments by their convergent normal
values preserves the full, sort-respecting normal-form relation at this
defined head. This is the operation-specific law for the variant row join. -/
theorem normalForm_iff (d : s.FreeSym) (p : Fin (s.arity d) → Term s) (rhs : Term s)
    (patterns : ∀ i, Pattern R (p i)) (ret : Result R p rhs)
    (table : ∀ ys t, R (.free d ys) t ↔ ∃ σ : Substitution s,
      (∀ i, ys i = σ.apply (p i)) ∧ t = σ.apply rhs)
    (xs ns : Fin (s.arity d) → Term s) (kids : ∀ i, Converges R (xs i) (ns i))
    (normal : ∀ i, Normal R (ns i)) (typed : ∀ i, HasSort (ns i) .msg)
    (tx : ∀ i, HasSort (xs i) (s.inputSort d i)) (tn : ∀ i, HasSort (ns i) (s.inputSort d i)) (u) :
    NormalForm R (.free d xs) u ↔ NormalForm R (.free d ns) u := by
  obtain ⟨n,_,c1,c2⟩ := unique_value d p rhs patterns ret table xs ns kids normal typed
  constructor
  · intro nf
    have eq := normal_reduces_equiv (c1 _ nf.1) nf.2.1
    exact ⟨(c2 _ (.basis (.refl _))).trans (.basis eq.symm),nf.2.1,fun _ hs =>
      .widen (nf.2.2 _ (.free d xs tx)) (Term.rootSort_le hs)⟩
  · intro nf
    exact ⟨(.free d xs ns (fun i => kids i _ (.basis (.refl _))) : Reduces R _ _).trans nf.1,
      nf.2.1,fun _ hs => .widen (nf.2.2 _ (.free d ns tn)) (Term.rootSort_le hs)⟩

private theorem argument_access (σ : Substitution s) {p : Term s} (pat : Pattern R p)
    {v : Variable} (occ : p.Occurs v) : Access R (σ.apply p) (σ.image v) := by
  induction pat with
  | var _ _ => obtain rfl := occ; exact .refl _
  | free f _ _ xs _ ih =>
    obtain ⟨i,h⟩ := occ
    exact (Access.child (Immediate.free f (fun j => σ.apply (xs j)) i)).trans (ih i h)

/-- A positional destructor preserves hereditary convergence even when its
selected variable becomes a product or another changing destructor. -/
theorem hereditary (d : s.FreeSym) (p : Fin (s.arity d) → Term s) (rhs : Term s)
    (patterns : ∀ i, Pattern R (p i)) (ret : Result R p rhs)
    (table : ∀ ys t, R (.free d ys) t ↔ ∃ σ : Substitution s,
      (∀ i, ys i = σ.apply (p i)) ∧ t = σ.apply rhs)
    (slots : ∀ i, s.inputSort d i = .msg) (out : Subsort (s.outputSort d) .msg)
    (groundRhs : (∀ v, ¬rhs.Occurs v) → Hereditary R rhs)
    (xs : Fin (s.arity d) → Term s) (kids : ∀ i, Hereditary R (xs i)) : Hereditary R (.free d xs) := by
  have result ys (hy : ∀ i, Hereditary R (ys i)) t (root : R (.free d ys) t) : Hereditary R t := by
    obtain ⟨σ,eq,rfl⟩ := (table _ _).mp root
    cases ret with
    | selected z occ =>
      obtain ⟨i,mem⟩ := occ
      exact (eq i ▸ hy i : Hereditary R (σ.apply (p i))).follow (argument_access σ (patterns i) mem)
    | fixed c ground norm =>
      rw [SpecializedRule.apply_ground ground]; exact groundRhs ground
  apply Hereditary.free_active d _ result xs kids
  intro ys hy
  let ns i := (hy i).settles.choose
  have spec i := (hy i).settles.choose_spec
  have normals i : Normal R (ns i) := (spec i).1
  have typed i : HasSort (ns i) .msg := (spec i).2.1
  have conv i : Converges R (ys i) (ns i) := (spec i).2.2
  obtain ⟨n,hn,cy,cn⟩ := unique_value d p rhs patterns ret table ys ns conv normals typed
  refine ⟨n,hn,?_,cy⟩
  have rs := cn _ (.basis (.refl _))
  rcases reduces_free_until d ns (Hereditary R) (fun h r => h.follow (.reduces r))
    (fun zs rz => result zs (fun i => (hy i).follow (.reduces (((conv i) _ (.basis (.refl _))).trans (rz i))))) rs with
    ⟨zs,rfl,rz⟩|known
  · apply HasSort.widen _ out
    apply HasSort.free
    intro i
    have eq := normal_reduces_equiv (rz i) (normals i)
    exact slots i ▸ Term.checkSort_sound _ _ (SortClash.check_equiv eq _ ▸ Term.checkSort_complete (typed i))
  · obtain ⟨v,_,tv,hv⟩ := known.settles
    have eq := normal_reduces_equiv (hv _ (.basis (.refl _))) hn
    exact Term.checkSort_sound _ _ (SortClash.check_equiv eq _ ▸ Term.checkSort_complete tv)

end
end Tamarin.Rewriting.PositionalConvergence
