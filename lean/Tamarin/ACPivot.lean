import Tamarin.AtomicACPair

/-! Select one indivisible occurrence in a sorted AC equation. Its owner on
the opposite side either equals it or contains a nonempty, sorted remainder.
The one-open-operand specialization emits a finite set of ordinary equation
systems and keeps the entire caller problem in every continuation. -/
namespace Tamarin.ACPivot
open Cancellation AtomicACPair
variable {sig : Signature}

/-- Expanded occurrences under one simultaneous substitution. -/
noncomputable def factors (f : sig.ACSym) (σ : Substitution sig) (xs : List (Term sig)) :=
  xs.flatMap fun x => flatten f (σ.apply x)

theorem fold_factors (f : sig.ACSym) (σ : Substitution sig) (u : Term sig) (us : List (Term sig)) :
    flatten f (σ.apply (ACRepresentation.fold f u us)) = factors f σ (u :: us) := by
  induction us generalizing u with
  | nil => simp [ACRepresentation.fold,factors]
  | cons y ys ih =>
    change flatten f (.ac f (σ.apply u) (σ.apply (ACRepresentation.fold f y ys))) = _
    rw [flatten_ac,ih]; rfl

/-- General pivot inversion. No grouping assumption or linearity restriction
on the right operands is needed. The empty-fringe case is ordinary equality. -/
theorem locate (f : sig.ACSym) (σ : Substitution sig) (a : Term sig) (left right : List (Term sig))
    (atomic : Atomic f a) (typed : ∀ t ∈ right, HasSort t (sig.acSort f))
    (eq : (factors f σ (a :: left)).Perm (factors f σ right)) :
    ∃ b ∈ right, classOf (σ.apply a) ∈ flatten f (σ.apply b) ∧
      RigidAllocation.Split f (σ.apply a) (σ.apply b) := by
  have here : classOf (σ.apply a) ∈ factors f σ (a :: left) := by
    simp [factors,atomic σ]
  obtain ⟨b,hb,mem⟩ := List.mem_flatMap.mp (eq.mem_iff.mp here)
  exact ⟨b,hb,mem,RigidAllocation.split_factor f _ _ ((typed b hb).subst _ σ.sorted) mem⟩

theorem fixed_owner {f : sig.ACSym} {b : Term sig} (atom : Atomic f b) (σ : Substitution sig)
    {a : Term sig} (mem : classOf a ∈ flatten f (σ.apply b)) : EquivB a (σ.apply b) :=
  Quotient.exact (List.mem_singleton.mp (atom σ ▸ mem))

private theorem selected {α : Type} (xs : List α) (i : Fin xs.length) :
    xs.Perm (xs[i] :: xs.eraseIdx i.val) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i using Fin.cases with
    | zero => exact .refl _
    | succ i => exact ((ih i).cons x).trans (.swap ..)

structure Query (sig : Signature) where
  f : sig.ACSym
  x : Variable
  y : Variable
  a : Term sig
  b : Term sig
  bs : List (Term sig)
  tail : Problem sig

namespace Query
variable (q : Query sig)

def operands := q.b :: q.bs
def product := ACRepresentation.fold q.f q.b q.bs
def remainder (i : Fin q.operands.length) := ACRepresentation.fold q.f (.var q.y) (q.operands.eraseIdx i.val)
def lhs : Term sig := .ac q.f (.var q.x) q.a
def rhs : Term sig := .ac q.f (.var q.y) q.product
def problem : Problem sig := ⟨q.lhs,q.rhs⟩ :: q.tail

inductive Choice (n : Nat) where
  | matchAt (i : Fin n)
  | whole
  | shared

def choices : List (Choice q.operands.length) :=
  (List.finRange q.operands.length).map .matchAt ++ [.whole,.shared]

theorem choice_mem (c : Choice q.operands.length) : c ∈ q.choices := by cases c <;> simp [choices]

/-- In the last branch the same fresh W denotes the nonempty surplus on
both sides. The first branch deletes one indexed occurrence, preserving all
other occurrences even when two original operands were identical. -/
def branch (w : Variable) : Choice q.operands.length → Problem sig
  | .matchAt i => ⟨q.a,q.operands[i]⟩ :: ⟨.var q.x,q.remainder i⟩ :: q.tail
  | .whole => ⟨.var q.y,q.a⟩ :: ⟨.var q.x,q.product⟩ :: q.tail
  | .shared => ⟨.var q.y,.ac q.f q.a (.var w)⟩ :: ⟨.var q.x,.ac q.f q.product (.var w)⟩ :: q.tail

private theorem regroup (i : Fin q.operands.length) :
    EquivB q.rhs (.ac q.f (q.remainder i) q.operands[i]) := by
  have perm := ((selected q.operands i).cons (.var q.y)).trans (.swap ..)
  exact (ACRepresentation.decode_perm q.f perm q.rhs (.ac q.f q.operands[i] (q.remainder i)) rfl rfl).trans (.ac_swap ..)

private theorem rotate (f : sig.ACSym) (a r p : Term sig) :
    EquivB (.ac f (.ac f a r) p) (.ac f (.ac f p r) a) :=
  (RigidAllocation.rotate f a r p).trans (.ac_congr f (.ac_swap ..) (.refl _))

inductive View (q : Query sig) (σ : Substitution sig) : Prop where
  | matchAt (i : Fin q.operands.length) (ha : EquivB (σ.apply q.a) (σ.apply q.operands[i]))
      (hx : EquivB (σ.image q.x) (σ.apply (q.remainder i))) : q.View σ
  | whole (hy : EquivB (σ.image q.y) (σ.apply q.a)) (hx : EquivB (σ.image q.x) (σ.apply q.product)) : q.View σ
  | shared (r : Term sig) (typed : HasSort r (sig.acSort q.f))
      (hy : EquivB (σ.image q.y) (.ac q.f (σ.apply q.a) r))
      (hx : EquivB (σ.image q.x) (.ac q.f (σ.apply q.product) r)) : q.View σ

/-- Algebraic core for X*A = Y*B₀*…*Bₙ. This covers substitutions that
narrow a variable's sort, that contain AC terms or that identify operands. -/
theorem view_iff (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (σ : Substitution sig) :
    EquivB (σ.apply q.lhs) (σ.apply q.rhs) ↔ q.View σ := by
  constructor
  · intro he
    have flat := flatten_equiv q.f he
    change (flatten q.f (.ac q.f (σ.image q.x) (σ.apply q.a))).Perm
      (flatten q.f (.ac q.f (σ.image q.y) (σ.apply q.product))) at flat
    rw [flatten_ac,flatten_ac,atom σ] at flat
    have mem := flat.mem_iff.mp (List.mem_append_right _ (List.mem_singleton_self _))
    rcases List.mem_append.mp mem with inY|inB
    · rcases RigidAllocation.split_factor q.f _ _ (sy ▸ σ.sorted q.y) inY with hy|⟨r,typed,hy⟩
      · exact .whole hy (EquivB.ac_cancel_right q.f
          (he.trans ((EquivB.ac_congr q.f hy (.refl _)).trans (.ac_swap ..))))
      · exact .shared r typed hy (EquivB.ac_cancel_right q.f
          (he.trans ((EquivB.ac_congr q.f hy (.refl _)).trans (rotate q.f _ _ _))))
    · change _ ∈ flatten q.f (σ.apply (ACRepresentation.fold q.f q.b q.bs)) at inB
      rw [fold_factors] at inB
      obtain ⟨b,hb,occ⟩ := List.mem_flatMap.mp inB
      obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hb
      let i : Fin q.operands.length := ⟨j,hj⟩
      have ha : EquivB (σ.apply q.a) (σ.apply q.operands[i]) := eq ▸ fixed_owner (each b hb) σ occ
      exact .matchAt i ha (EquivB.ac_cancel_right q.f
        ((he.trans ((q.regroup i).subst σ.image)).trans (.ac_congr q.f (.refl _) ha.symm)))
  · intro view
    cases view with
    | matchAt i ha hx => exact (EquivB.ac_congr q.f hx ha).trans ((q.regroup i).subst σ.image).symm
    | whole hy hx => exact (EquivB.ac_congr q.f hx hy.symm).trans (.ac_swap ..)
    | shared r _ hy hx =>
      exact (EquivB.ac_congr q.f hx (.refl _)).trans
        ((rotate q.f _ _ _).symm.trans (.ac_congr q.f hy.symm (.refl _)))


theorem solves_cons (l r : Term sig) (tail : Problem sig) (σ : Substitution sig) :
    Problem.Solves (⟨l,r⟩ :: tail) σ ↔ EquivB (σ.apply l) (σ.apply r) ∧ tail.Solves σ := by
  simp [Problem.Solves]

theorem occurs_cons (l r : Term sig) (tail : Problem sig) (v : Variable) :
    Problem.Occurs (⟨l,r⟩ :: tail) v ↔ (l.Occurs v ∨ r.Occurs v) ∨ tail.Occurs v := by
  simp [Problem.Occurs]

theorem input_in_branch (w : Variable) (k : Choice q.operands.length) (v : Variable) :
    q.problem.Occurs v → (q.branch w k).Occurs v := by
  cases k with
  | matchAt i =>
    have h := (q.regroup i).occurs_iff v
    simp only [problem,branch,occurs_cons,lhs,Term.Occurs] at *
    grind
  | whole | shared =>
    simp only [problem,branch,occurs_cons,lhs,rhs,Term.Occurs]
    grind

theorem branch_sound (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (k : Choice q.operands.length) (σ : Substitution sig) :
    (q.branch w k).Solves σ → q.problem.Solves σ := by
  rw [problem,solves_cons,q.view_iff atom each sy]
  cases k with
  | matchAt i =>
    rw [branch,solves_cons,solves_cons]
    exact fun ⟨ha,hx,tail⟩ => ⟨.matchAt i ha hx,tail⟩
  | whole =>
    rw [branch,solves_cons,solves_cons]
    exact fun ⟨hy,hx,tail⟩ => ⟨.whole hy hx,tail⟩
  | shared =>
    rw [branch,solves_cons,solves_cons]
    exact fun ⟨hy,hx,tail⟩ => ⟨.shared (σ.image w) (hw ▸ σ.sorted w) hy hx,tail⟩

/-- Every source solution has an extension solving one continuation. All
images except the fresh witness's image are literally unchanged, including
variables in the tail and variables outside the entire problem. -/
theorem extend (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (fresh : ¬ q.problem.Occurs w) (ρ : Substitution sig) (solves : q.problem.Solves ρ) :
    ∃ k δ, (∀ v, v ≠ w → δ.image v = ρ.image v) ∧ (q.branch w k).Solves δ := by
  obtain ⟨main,tail⟩ := (solves_cons ..).mp solves
  cases (q.view_iff atom each sy ρ).mp main with
  | matchAt i ha hx =>
    exact ⟨.matchAt i,ρ,fun _ _ => rfl,(solves_cons ..).mpr ⟨ha,(solves_cons ..).mpr ⟨hx,tail⟩⟩⟩
  | whole hy hx =>
    exact ⟨.whole,ρ,fun _ _ => rfl,(solves_cons ..).mpr ⟨hy,(solves_cons ..).mpr ⟨hx,tail⟩⟩⟩
  | shared r typed hy hx =>
    let δ := RigidAllocation.Query.override ρ w r (hw ▸ typed)
    have dw : δ.image w = r := by simp [δ,RigidAllocation.Query.override]
    have same (v : Variable) (ne : v ≠ w) : δ.image v = ρ.image v := by
      simp [δ,RigidAllocation.Query.override,ne]
    have sameInput (v : Variable) (hv : q.problem.Occurs v) : δ.image v = ρ.image v :=
      same v (fun h => fresh (h ▸ hv))
    have agree (t : Term sig) (h : ∀ v, t.Occurs v → q.problem.Occurs v) : δ.apply t = ρ.apply t :=
      Term.subst_eq_of_agree _ _ _ fun v hv => sameInput v (h v hv)
    have da := agree q.a fun _ h => (occurs_cons ..).mpr (.inl (.inl (.inr h)))
    have db := agree q.product fun _ h => (occurs_cons ..).mpr (.inl (.inr (.inr h)))
    have dx := sameInput q.x ((occurs_cons ..).mpr (.inl (.inl (.inl rfl))))
    have dy := sameInput q.y ((occurs_cons ..).mpr (.inl (.inr (.inl rfl))))
    refine ⟨.shared,δ,same,(solves_cons ..).mpr ⟨?_,(solves_cons ..).mpr ⟨?_,?_⟩⟩⟩
    · change EquivB (δ.image q.y) (.ac q.f (δ.apply q.a) (δ.image w))
      rwa [dy,da,dw]
    · change EquivB (δ.image q.x) (.ac q.f (δ.apply q.product) (δ.image w))
      rwa [dx,db,dw]
    · intro e mem
      rw [agree e.lhs fun _ hv => (occurs_cons ..).mpr (.inr ⟨e,mem,.inl hv⟩),
          agree e.rhs fun _ hv => (occurs_cons ..).mpr (.inr ⟨e,mem,.inr hv⟩)]
      exact tail e mem

/-- Complete unifiers for the continuations cover every original solution
with a single factorization on the variables of the whole caller problem. -/
theorem complete (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (fresh : ¬ q.problem.Occurs w) (answers : Choice q.operands.length → List (Substitution sig))
    (branches : ∀ k, CompleteSet (q.branch w k) (answers k)) :
    CompleteSet q.problem (q.choices.flatMap answers) := by
  constructor
  · intro σ hs
    obtain ⟨k,_,h⟩ := List.mem_flatMap.mp hs
    exact q.branch_sound atom each sy w hw k σ ((branches k).sound _ h)
  · intro ρ hs
    obtain ⟨k,δ,same,hδ⟩ := q.extend atom each sy w hw fresh ρ hs
    obtain ⟨σ,hs,η,hη⟩ := (branches k).covers _ hδ
    refine ⟨σ,List.mem_flatMap.mpr ⟨k,q.choice_mem k,hs⟩,η,fun v hv => ?_⟩
    rw [← same v (fun h => fresh (h ▸ hv))]
    exact hη v (q.input_in_branch w k v hv)


private theorem branch_scope (w : Variable) (k : Choice q.operands.length) (v : Variable) :
    (q.branch w k).Occurs v → q.problem.Occurs v ∨ v = w := by
  cases k with
  | matchAt i =>
    have h := (q.regroup i).occurs_iff v
    simp only [problem,branch,occurs_cons,lhs,Term.Occurs] at *
    grind
  | whole | shared =>
    simp only [problem,branch,occurs_cons,lhs,rhs,Term.Occurs]
    grind

/-- Hide the branch-local domain entry while retaining the one shared name
where it occurs in ranges. Substitution application is simultaneous. -/
def hide (w : Variable) (σ : Substitution sig) :=
  RigidAllocation.Query.override σ w (.var w) (.var w)

private theorem hide_at (w : Variable) (σ : Substitution sig) (v : Variable) :
    (hide w σ).image v = if v = w then .var w else σ.image v := rfl

/-- Scoped composition for the caller. A fresh name can occur in the
ranges of several answer bindings. Its own binding is private to the branch. -/
theorem scopedComplete (atom : Atomic q.f q.a) (each : ∀ b ∈ q.operands, Atomic q.f b)
    (sy : q.y.sort = sig.acSort q.f) (w : Variable) (hw : w.sort = sig.acSort q.f)
    (fresh : ¬ q.problem.Occurs w) (avoid : List Variable) (away : w ∉ avoid)
    (answers : Choice q.operands.length → List (Substitution sig))
    (branches : ∀ k, (Outcome.complete (answers k)).CorrectIn (q.branch w k) avoid) :
    (Outcome.complete ((q.choices.flatMap answers).map (hide w))).CorrectIn q.problem avoid := by
  have complete := q.complete atom each sy w hw fresh answers fun k => (branches k).mathematical
  have same (σ : Substitution sig) (v : Variable) (hv : q.problem.Occurs v) :
      (hide w σ).image v = σ.image v :=
    by simp [hide_at, show v ≠ w from fun h => fresh (h ▸ hv)]
  constructor
  · constructor
    · intro θ hθ
      obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hθ
      apply q.problem.solves_instance (complete.sound σ hσ)
      refine ⟨Substitution.identity,fun v hv => ?_⟩
      change EquivB _ (Substitution.identity.apply (σ.image v))
      rw [same σ v hv,Substitution.apply_identity]
      exact .refl _
    · intro ρ hρ
      obtain ⟨σ,hσ,η,hi⟩ := complete.covers ρ hρ
      refine ⟨_,List.mem_map.mpr ⟨σ,hσ,rfl⟩,η,fun v hv => ?_⟩
      change EquivB _ (η.apply ((hide w σ).image v))
      rw [same σ v hv]
      exact hi v hv
  · intro θ hθ v hv
    obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hθ
    obtain ⟨k,_,hs⟩ := List.mem_flatMap.mp hσ
    rw [hide_at]
    split
    · next e => rw [e]
    · next ne =>
        exact (branches k).domain σ hs v fun h => (q.branch_scope w k v h).elim hv ne
  · intro θ hθ v hv z hz hzo
    obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hθ
    obtain ⟨k,_,hs⟩ := List.mem_flatMap.mp hσ
    rw [same σ v hv] at hz
    by_cases he : z = w
    · exact he ▸ away
    · exact (branches k).fresh σ hs v (q.input_in_branch w k v hv) z hz
        fun h => (q.branch_scope w k z h).elim hzo he

end Query
end Tamarin.ACPivot
