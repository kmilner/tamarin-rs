import Tamarin.RecursiveACMatch
import Tamarin.VariablePermutation
import Tamarin.GroundACEquality

/-! Reduce ordinary directional matching on open subjects to ground-subject
matching. Subject variables become rigid atoms disjoint from every original
atom. The very same variable can remain bindable on the pattern side. -/
namespace Tamarin.Matching.RigidSubject

variable (s : Signature)

/-- A clash in any conjunct refutes the entire directional match before
partition search. A bare subject variable still has its own rigid head. -/
theorem head_clash {p t : Term s} (rigid : ∀ v, p ≠ .var v)
    (clash : (headModel s).eval Head.var p ≠ (headModel s).eval Head.var t) (σ : Substitution s) : ¬EquivB (σ.apply p) t := by
  intro eq
  apply clash
  cases p with
  | var v => exact (rigid v rfl).elim
  | atom | free | comm | ac => exact eq.head_eq

/-- Extending the atom namespace preserves all operator declarations. -/
abbrev withAtoms (α : Type) (sort : α → SortId) : Signature := { s with Atom := α, atomSort := sort }
abbrev frozenSig := withAtoms s (s.Atom ⊕ Variable) (Sum.elim s.atomSort Variable.sort)

private def leaves {α : Type} {sort : α → SortId}
    (v : Variable → Term (withAtoms s α sort)) (a : s.Atom → Term (withAtoms s α sort)) :
    Term s → Term (withAtoms s α sort)
  | .var w => v w
  | .atom b => a b
  | .free f xs => .free f (fun i => leaves v a (xs i))
  | .comm f x y => .comm f (leaves v a x) (leaves v a y)
  | .ac f x y => .ac f (leaves v a x) (leaves v a y)

private theorem leaves_equiv {α : Type} {sort : α → SortId}
    (v : Variable → Term (withAtoms s α sort)) (a : s.Atom → Term (withAtoms s α sort))
    {x y : Term s} (e : EquivB x y) : EquivB (leaves s v a x) (leaves s v a y) := by
  induction e with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ h k => exact h.trans k
  | free f _ _ _ ih => exact EquivB.free (sig := withAtoms s α sort) f _ _ ih
  | comm_congr f _ _ h k => exact EquivB.comm_congr (sig := withAtoms s α sort) f h k
  | ac_congr f _ _ h k => exact EquivB.ac_congr (sig := withAtoms s α sort) f h k
  | comm_swap => exact .comm_swap ..
  | ac_swap => exact .ac_swap ..
  | ac_assoc => exact .ac_assoc ..

private theorem leaves_sorted {α : Type} {sort : α → SortId}
    (v : Variable → Term (withAtoms s α sort)) (a : s.Atom → Term (withAtoms s α sort))
    (vs : ∀ w, HasSort (v w) w.sort) (ats : ∀ b, HasSort (a b) (s.atomSort b))
    {x : Term s} {k} (h : HasSort x k) : HasSort (leaves s v a x) k := by
  induction h with
  | var w => exact vs w
  | atom b => exact ats b
  | free f _ _ ih => exact HasSort.free (sig := withAtoms s α sort) f _ ih
  | comm f _ _ _ _ l r => exact HasSort.comm (sig := withAtoms s α sort) f _ _ l r
  | ac f _ _ _ _ l r => exact HasSort.ac (sig := withAtoms s α sort) f _ _ l r
  | widen _ h ih => exact .widen ih h

def pattern := leaves s (α := s.Atom ⊕ Variable) (sort := Sum.elim s.atomSort Variable.sort)
  Term.var (fun b => .atom (.inl b))
def freeze := leaves s (α := s.Atom ⊕ Variable) (sort := Sum.elim s.atomSort Variable.sort)
  (fun w => .atom (.inr w)) (fun b => .atom (.inl b))
def thaw : Term (frozenSig s) → Term s :=
  leaves (frozenSig s) (α := s.Atom) (sort := s.atomSort) Term.var (Sum.elim Term.atom Term.var)

theorem freeze_sorted {t : Term s} {k} (h : HasSort t k) : HasSort (freeze s t) k :=
  leaves_sorted s (α := s.Atom ⊕ Variable) (sort := Sum.elim s.atomSort Variable.sort) _ _
    (fun v => HasSort.atom (sig := frozenSig s) (Sum.inr v))
    (fun a => HasSort.atom (sig := frozenSig s) (Sum.inl a)) h

theorem freeze_ground (t : Term s) : (freeze s t).Ground := by
  induction t with
  | var | atom => intro _; exact id
  | free f xs ih => intro w ⟨i,h⟩; exact ih i w h
  | comm _ _ _ l r | ac _ _ _ l r => intro w h; exact h.elim (l w) (r w)

private theorem thaw_freeze (t : Term s) : thaw s (freeze s t) = t := by
  induction t with
  | var | atom => rfl
  | free f xs ih => exact congrArg (Term.free (sig := s) f) (funext ih)
  | comm f _ _ l r => exact congr (congrArg (Term.comm (sig := s) f) l) r
  | ac f _ _ l r => exact congr (congrArg (Term.ac (sig := s) f) l) r

theorem freeze_equiv {a b : Term s} (eq : EquivB a b) : EquivB (freeze s a) (freeze s b) :=
  leaves_equiv s _ _ eq

theorem freeze_inj {a b : Term s} (eq : freeze s a = freeze s b) : a = b := by
  simpa only [thaw_freeze] using congrArg (thaw s) eq

private theorem occurs_pattern (t : Term s) (w : Variable) : (pattern s t).Occurs w ↔ t.Occurs w := by
  induction t with
  | var | atom => rfl
  | free f xs ih => exact exists_congr ih
  | comm _ _ _ l r | ac _ _ _ l r => exact or_congr l r

/-- The C orientation shortcut compares across sides. An identical open
subtree is different syntax once its subject variables become rigid. -/
theorem same_across (a b : Term s) : pattern s a = freeze s b ↔ a = b ∧ a.Ground := by
  have back (t : Term s) : thaw s (pattern s t) = t := by
    induction t with
    | var | atom => rfl
    | free f xs ih => exact congrArg (Term.free (sig := s) f) (funext ih)
    | comm f _ _ l r => exact congr (congrArg (Term.comm (sig := s) f) l) r
    | ac f _ _ l r => exact congr (congrArg (Term.ac (sig := s) f) l) r
  constructor
  · intro eq
    refine ⟨(back a).symm.trans ((congrArg (thaw s) eq).trans (thaw_freeze s b)),?_⟩
    intro v occ
    exact freeze_ground s b v (eq ▸ (occurs_pattern s a v).mpr occ)
  · rintro ⟨rfl, ground⟩
    induction a with
    | var v => exact False.elim (ground v rfl)
    | atom => rfl
    | free f xs ih =>
      exact congrArg (Term.free (sig := frozenSig s) f) (funext fun i => ih i fun v h => ground v ⟨i,h⟩)
    | comm f _ _ l r =>
      change Term.comm (sig := frozenSig s) f _ _ = Term.comm (sig := frozenSig s) f _ _
      exact congr (congrArg (Term.comm (sig := frozenSig s) f) (l fun v h => ground v (.inl h)))
        (r fun v h => ground v (.inr h))
    | ac f _ _ l r =>
      change Term.ac (sig := frozenSig s) f _ _ = Term.ac (sig := frozenSig s) f _ _
      exact congr (congrArg (Term.ac (sig := frozenSig s) f) (l fun v h => ground v (.inl h)))
        (r fun v h => ground v (.inr h))

def query (p : Problem s) : Problem (frozenSig s) :=
  p.map fun e => ⟨pattern s e.lhs, freeze s e.rhs⟩

private theorem observed (p : Problem s) (v) : Observed (query s p) v ↔ Observed p v := by
  constructor
  · rintro ⟨_,mem,hv⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp mem
    exact ⟨e,he,(occurs_pattern s e.lhs v).mp hv⟩
  · rintro ⟨e,he,hv⟩
    exact ⟨_,List.mem_map_of_mem he,(occurs_pattern s e.lhs v).mpr hv⟩

def decode (σ : Substitution (frozenSig s)) : Substitution s where
  image v := thaw s (σ.image v)
  support := σ.support
  outside v hv := by rw [σ.outside v hv]; rfl
  sorted v := leaves_sorted (frozenSig s) (α := s.Atom) (sort := s.atomSort) _ _ HasSort.var
    (fun b => by cases b with | inl a => exact .atom a | inr w => exact .var w) (σ.sorted v)

private theorem thaw_apply (σ : Substitution (frozenSig s)) (t : Term s) :
    thaw s (σ.apply (pattern s t)) = (decode s σ).apply t := by
  induction t with
  | var | atom => rfl
  | free f xs ih => exact congrArg (Term.free (sig := s) f) (funext ih)
  | comm f _ _ l r => exact congr (congrArg (Term.comm (sig := s) f) l) r
  | ac f _ _ l r => exact congr (congrArg (Term.ac (sig := s) f) l) r

private noncomputable def lift (p : Problem s) (ρ : Substitution s) : Substitution (frozenSig s) := by
  classical
  exact {
    image := fun w => if Observed p w then freeze s (ρ.image w) else .var w
    support := p.variables
    outside := fun w hw => ite_eq_right (fun ⟨e,he,h⟩ => hw ((p.mem_variables w).mpr ⟨e,he,Or.inl h⟩))
    sorted := fun w => by
      split
      · exact freeze_sorted s (ρ.sorted w)
      · exact .var _ }

private theorem lift_apply (p : Problem s) (ρ : Substitution s) (t : Term s)
    (seen : ∀ v, t.Occurs v → Observed p v) :
    (lift s p ρ).apply (pattern s t) = freeze s (ρ.apply t) := by
  induction t with
  | var w => classical exact ite_eq_left (seen w rfl)
  | atom => rfl
  | free f xs ih => exact congrArg (Term.free (sig := frozenSig s) f) (funext fun i => ih i fun v h => seen v ⟨i,h⟩)
  | comm f _ _ l r =>
    change Term.comm (sig := frozenSig s) f _ _ = Term.comm (sig := frozenSig s) f _ _
    exact congr (congrArg (Term.comm (sig := frozenSig s) f) (l fun v h => seen v (.inl h))) (r fun v h => seen v (.inr h))
  | ac f _ _ l r =>
    change Term.ac (sig := frozenSig s) f _ _ = Term.ac (sig := frozenSig s) f _ _
    exact congr (congrArg (Term.ac (sig := frozenSig s) f) (l fun v h => seen v (.inl h))) (r fun v h => seen v (.inr h))

/-- Soundness, exact coverage on pattern variables and preservation of scope
survive freezing the subjects of an entire conjunction. No occurs check or
disjointness condition on caller variables is needed. -/
theorem complete (p : Problem s) (arms : List (Substitution (frozenSig s)))
    (h : Complete (query s p) (fun _ => True) arms) :
    Complete p (fun _ => True) (arms.map (decode s)) := by
  classical
  constructor
  · intro a ha
    obtain ⟨σ,mem,rfl⟩ := List.mem_map.mp ha
    obtain ⟨matchQ,scope⟩ := h.sound σ mem
    constructor
    · intro e he
      have eq := matchQ _ (List.mem_map_of_mem (f := fun e : Equation s => (⟨pattern s e.lhs,freeze s e.rhs⟩ : Equation _)) he)
      have back := leaves_equiv (frozenSig s) (α := s.Atom) (sort := s.atomSort)
        Term.var (Sum.elim Term.atom Term.var) eq
      change EquivB (thaw s (σ.apply (pattern s e.lhs))) (thaw s (freeze s e.rhs)) at back
      simpa only [thaw_apply,thaw_freeze] using back
    · intro v hv
      change thaw s (σ.image v) = _
      rw [scope v (fun hv' => hv ⟨(observed s p v).mp hv'.1,trivial⟩)]
      rfl
  · intro ρ matchP _
    have matched : Matches (query s p) (lift s p ρ) := by
      intro e he
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
      change EquivB ((lift s p ρ).apply (pattern s q.lhs)) (freeze s q.rhs)
      rw [lift_apply s p ρ q.lhs (fun _ hv => ⟨q,hq,hv⟩)]
      exact leaves_equiv s _ _ (matchP q hq)
    obtain ⟨σ,mem,agrees⟩ := h.covers _ matched (fun v hv =>
      ite_eq_right (fun obs => hv ⟨(observed s p v).mpr obs,trivial⟩))
    refine ⟨_,List.mem_map_of_mem mem,fun v hv => ?_⟩
    have eq := agrees v ((observed s p v).mpr hv)
    change EquivB (if Observed p v then _ else _) (σ.image v) at eq
    rw [ite_eq_left hv] at eq
    have back := leaves_equiv (frozenSig s) (α := s.Atom) (sort := s.atomSort)
      Term.var (Sum.elim Term.atom Term.var) eq
    change EquivB (thaw s (freeze s (ρ.image v))) (thaw s (σ.image v)) at back
    rw [thaw_freeze] at back
    exact back

/-- Completed recursive kernel calls read all equations under one substitution.
The sets represented by the Rust worklist and the returned binding maps must
agree on those joint readings, including empty results. -/
def SearchCorrect (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : NestedTreeMatch.Orient) (cancel : RecursiveACMatch.Cancellation) : Prop :=
  ∀ (sig : Signature) [DecidableEq sig.ACSym] (p : Problem sig),
    let q := query sig p
    ∀ (arms : List (Substitution (frozenSig sig)))
      (read : Equation (frozenSig sig) → Substitution (frozenSig sig) → Prop),
    (∀ e ∈ q, ∃ enc l r, EquivB l e.lhs ∧ EquivB r e.rhs ∧
      RecursiveACMatch.Search select flat orient cancel enc l r (read e)) →
    (∀ a ∈ arms, Scoped q (fun _ => True) a) →
    (∀ σ, Scoped q (fun _ => True) σ → ((∀ e ∈ q, read e σ) ↔
      ∃ a ∈ arms, Substitution.AgreesOn (Observed q) σ a)) →
    Complete p (fun _ => True) (arms.map (decode sig))

theorem of_recursive {select flat orient cancel} (checked : RecursiveACMatch.Correct select flat orient cancel) :
    SearchCorrect select flat orient cancel := by
  intro sig _ p q arms read runs domains replies
  have eq (σ) : Matches q σ ↔ ∀ e ∈ q, read e σ := by
    apply forall_congr'; intro e
    apply forall_congr'; intro he
    obtain ⟨enc,l,r,hl,hr,tree⟩ := runs e he
    simpa [Matches] using checked tree e.lhs e.rhs hl hr [] σ
  apply complete
  constructor
  · intro a ha
    exact ⟨(eq a).mpr ((replies a (domains a ha)).mpr ⟨a,ha,fun _ _ => .refl _⟩),domains a ha⟩
  · intro σ hσ hs
    exact (replies σ hs).mp ((eq σ).mp hσ)

end Tamarin.Matching.RigidSubject
