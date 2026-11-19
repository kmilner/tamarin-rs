import Tamarin.Cancellation
import Tamarin.GroundACEquality
import Tamarin.ACResidual
import Tamarin.VariablePermutation

/-! Unification at a binary commutative head modulo B. Each orientation
contributes two equations to the *same* residual conjunction. The operands
are unrestricted terms and the statement quantifies over sorted simultaneous
substitutions. Commutativity gives no reassociation or identity law. -/
namespace Tamarin.Commutative
open Cancellation
variable {sig : Signature}

private def children : Term sig → List (Class sig)
  | .comm _ a b => [classOf a, classOf b]
  | _ => []

private theorem children_perm {s t : Term sig} (h : EquivB s t) :
    (children s).Perm (children t) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | comm_congr f ha hb _ _ =>
    simp only [children, Quotient.sound (s := termSetoid sig) ha,
      Quotient.sound (s := termSetoid sig) hb, classOf, List.Perm.refl]
  | comm_swap => exact .swap _ _ []
  | free | ac_swap | ac_assoc | ac_congr => exact .refl _

private theorem pair_perm {α} {a b c d : α} (h : [a,b].Perm [c,d]) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hm := h.mem_iff.mp (List.mem_cons_self ..)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Or.inl ⟨rfl, List.cons.inj (List.perm_singleton.mp h.cons_inv) |>.1⟩
  · have hp := h.trans (List.Perm.swap a c [])
    exact Or.inr ⟨rfl, List.cons.inj (List.perm_singleton.mp hp.cons_inv) |>.1⟩

theorem equiv_iff (f : sig.CSym) (a b c d : Term sig) :
    EquivB (.comm f a b) (.comm f c d) ↔
      (EquivB a c ∧ EquivB b d) ∨ (EquivB a d ∧ EquivB b c) := by
  constructor
  · intro h
    rcases pair_perm (children_perm h) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨Quotient.exact ha, Quotient.exact hb⟩
    · exact Or.inr ⟨Quotient.exact ha, Quotient.exact hb⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact .comm_congr f ha hb
    · exact (EquivB.comm_congr f ha hb).trans (.comm_swap f d c)

structure Query (sig : Signature) where
  f : sig.CSym
  a : Term sig
  b : Term sig
  c : Term sig
  d : Term sig
  rest : Problem sig

namespace Query
variable (q : Query sig)

def problem : Problem sig := ⟨.comm q.f q.a q.b, .comm q.f q.c q.d⟩ :: q.rest

def branch (cross : Bool) : Problem sig :=
  if cross then ⟨q.a,q.d⟩ :: ⟨q.b,q.c⟩ :: q.rest
  else ⟨q.a,q.c⟩ :: ⟨q.b,q.d⟩ :: q.rest

theorem solves_iff (σ : Substitution sig) :
    q.problem.Solves σ ↔ (q.branch false).Solves σ ∨ (q.branch true).Solves σ := by
  simp [problem, branch, Problem.Solves, Substitution.apply, Term.subst, equiv_iff]
  grind

theorem occurs_iff (cross) (v : Variable) : (q.branch cross).Occurs v ↔ q.problem.Occurs v := by
  cases cross <;> simp [problem, branch, Problem.Occurs, Term.Occurs] <;> grind

/-- Well-formed inputs provide the declared operand sort to each branch.
Narrower variables still keep their own sorts during subsequent elimination. -/
theorem branch_wellFormed (hp : q.problem.WellFormed) (cross : Bool) :
    (q.branch cross).WellFormed := by
  have h := hp _ (List.mem_cons_self ..)
  obtain ⟨_, hl⟩ := h.1
  obtain ⟨_, hr⟩ := h.2
  have left := Term.checkSort_complete hl
  have right := Term.checkSort_complete hr
  simp only [Term.checkSort, Bool.and_eq_true] at left right
  have ha := Term.checkSort_sound _ _ left.1.2
  have hb := Term.checkSort_sound _ _ left.2
  have hc := Term.checkSort_sound _ _ right.1.2
  have hd := Term.checkSort_sound _ _ right.2
  intro e he
  cases cross <;> simp [branch] at he <;> rcases he with rfl | rfl | hm
  · exact ⟨⟨_,ha⟩,⟨_,hc⟩⟩
  · exact ⟨⟨_,hb⟩,⟨_,hd⟩⟩
  · exact hp _ (List.mem_cons_of_mem _ hm)
  · exact ⟨⟨_,ha⟩,⟨_,hd⟩⟩
  · exact ⟨⟨_,hb⟩,⟨_,hc⟩⟩
  · exact hp _ (List.mem_cons_of_mem _ hm)

end Query

/-- Bit 0 selects direct alignment and bit 1 crossed alignment. Zero proves
a clash. The two dominance bits in the input describe implications between
orientations, independent of the order of subsequent unification steps. -/
def Selected (mask : UInt8) (cross : Bool) : Prop :=
  mask = (if cross then 2 else 1) ∨ mask = 3

def Viable (a b : UInt64) : Prop := a = 0 ∨ b = 0 ∨ a = b

/-- The kernel may return extra impossible or redundant orientations. For
every interpretation consistent with the head keys and known implications,
the returned orientations must preserve the disjunction exactly. -/
def Correct (run : UInt64 → UInt64 → UInt64 → UInt64 → UInt8 → UInt8) : Prop :=
  ∀ a b c d priority, let mask := run a b c d priority
    mask ≤ 3 ∧ ∀ P Q : Prop,
      (P → Viable a c ∧ Viable b d) → (Q → Viable a d ∧ Viable b c) →
      ((priority = 1 ∨ priority = 3) → Q → P) →
      ((priority = 2 ∨ priority = 3) → P → Q) →
      (P ∨ Q ↔ (Selected mask false ∧ P) ∨ (Selected mask true ∧ Q))

/-- Protect bounded native search from unnecessary exponential fan-out.
A rigid clash must not enqueue a continuation; a known implication needs
at most one continuation. Either representative of an equivalence is valid. -/
def BranchBound (run : UInt64 → UInt64 → UInt64 → UInt64 → UInt8 → UInt8) : Prop :=
  ∀ a b c d priority, let mask := run a b c d priority
    (Selected mask false → Viable a c ∧ Viable b d) ∧
    (Selected mask true → Viable a d ∧ Viable b c) ∧
    ((priority = 1 ∨ priority = 2 ∨ priority = 3) → mask ≠ 3)

/-- A head code uses zero for a variable. Any consistent function on full
rigid head identities suffices: collisions merely admit more branches. -/
def headCode (key : Head sig → UInt64) (t : Term sig) : UInt64 :=
  match t with
  | .var _ => 0
  | _ => key ((headModel sig).eval Head.var t)

private theorem viable_of_equiv (key : Head sig → UInt64) (σ : Substitution sig)
    (a b : Term sig) (he : EquivB (σ.apply a) (σ.apply b)) :
    Viable (headCode key a) (headCode key b) := by
  have hh := congrArg key he.head_eq
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr hh)

/-- Facts the encoder can establish with child identity. The semantic
implications hold under every substitution, even in a larger system. -/
structure Priority (q : Query sig) (p : UInt8) : Prop where
  direct : (p = 1 ∨ p = 3) → q.a = q.b ∨ q.c = q.d ∨ q.a = q.c ∨ q.b = q.d
  crossed : (p = 2 ∨ p = 3) → q.a = q.b ∨ q.c = q.d ∨ q.a = q.d ∨ q.b = q.c

private theorem dominates (q : Query sig) (p : UInt8) (h : Priority q p)
    (σ : Substitution sig) :
    ((p = 1 ∨ p = 3) → (q.branch true).Solves σ → (q.branch false).Solves σ) ∧
    ((p = 2 ∨ p = 3) → (q.branch false).Solves σ → (q.branch true).Solves σ) := by
  have align {a b c d : Term sig} (eq : a = b ∨ c = d ∨ a = c ∨ b = d)
      (ad : EquivB a d) (bc : EquivB b c) : EquivB a c ∧ EquivB b d := by
    rcases eq with rfl | rfl | rfl | rfl
    · exact ⟨bc, ad⟩
    · exact ⟨ad, bc⟩
    · exact ⟨.refl _, bc.trans ad⟩
    · exact ⟨ad.trans bc, .refl _⟩
  constructor
  · intro hp hm; have eq := h.direct hp
    simp [Query.branch, Problem.Solves] at hm ⊢
    exact ⟨(align (by grind) hm.1 hm.2.1).1, (align (by grind) hm.1 hm.2.1).2, hm.2.2⟩
  · intro hp hm; have eq := h.crossed hp
    simp [Query.branch, Problem.Solves] at hm ⊢
    exact ⟨(align (by grind) hm.1 hm.2.1).1, (align (by grind) hm.1 hm.2.1).2, hm.2.2⟩

def orientations (mask : UInt8) : List Bool :=
  [false,true].filter fun b => mask == (if b then 2 else 1) || mask == 3

theorem mem_orientations (mask : UInt8) (b : Bool) : b ∈ orientations mask ↔ Selected mask b := by
  cases b <;> simp [orientations, Selected]

theorem run_solves {run} (hc : Correct run) (q : Query sig) (key : Head sig → UInt64)
    (p : UInt8) (hp : Priority q p) (σ : Substitution sig) :
    let mask := run (headCode key q.a) (headCode key q.b) (headCode key q.c) (headCode key q.d) p
    q.problem.Solves σ ↔ ∃ b ∈ orientations mask, (q.branch b).Solves σ := by
  dsimp only
  rw [q.solves_iff]
  let mask := run (headCode key q.a) (headCode key q.b) (headCode key q.c) (headCode key q.d) p
  have allowed := (hc (headCode key q.a) (headCode key q.b) (headCode key q.c) (headCode key q.d) p).2
    ((q.branch false).Solves σ) ((q.branch true).Solves σ)
  have eq := allowed (fun h => by
      simp [Query.branch, Problem.Solves] at h
      exact ⟨viable_of_equiv key σ _ _ h.1, viable_of_equiv key σ _ _ h.2.1⟩)
    (fun h => by
      simp [Query.branch, Problem.Solves] at h
      exact ⟨viable_of_equiv key σ _ _ h.1, viable_of_equiv key σ _ _ h.2.1⟩)
    (dominates q p hp σ).1 (dominates q p hp σ).2
  refine eq.trans ⟨?_, ?_⟩
  · rintro (⟨hm,hs⟩ | ⟨hm,hs⟩)
    · exact ⟨false,(mem_orientations ..).mpr hm,hs⟩
    · exact ⟨true,(mem_orientations ..).mpr hm,hs⟩
  · rintro ⟨b, hm, hs⟩
    cases b <;> first | exact Or.inl ⟨(mem_orientations ..).mp hm,hs⟩ | exact Or.inr ⟨(mem_orientations ..).mp hm,hs⟩

/-- Every selected branch must finish in the original caller context before
their union can close a search node. Covers uses one instance on *all*
variables of the original system, including variables shared with its tail. -/
theorem assemble (q : Query sig) (bs : List Bool) (answers : Bool → List (Substitution sig))
    (avoid : List Variable) (exactBranches : ∀ σ, q.problem.Solves σ ↔ ∃ b ∈ bs, (q.branch b).Solves σ)
    (complete : ∀ b ∈ bs, (Outcome.complete (answers b)).CorrectIn (q.branch b) avoid) :
    (Outcome.complete (bs.flatMap answers)).CorrectIn q.problem avoid := by
  constructor
  · constructor
    · intro σ hs
      obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
      exact (exactBranches σ).mpr ⟨b,hb,(complete b hb).mathematical.sound σ ha⟩
    · intro ρ hr
      obtain ⟨b,hb,hq⟩ := (exactBranches ρ).mp hr
      obtain ⟨σ,hs,δ,hi⟩ := (complete b hb).mathematical.covers ρ hq
      exact ⟨σ,List.mem_flatMap.mpr ⟨b,hb,hs⟩,δ,fun v hv => hi v ((q.occurs_iff b v).mpr hv)⟩
  · intro σ hs v hn
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
    exact (complete b hb).domain σ ha v (fun h => hn ((q.occurs_iff b v).mp h))
  · intro σ hs v hv w hw hn
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp hs
    exact (complete b hb).fresh σ ha v ((q.occurs_iff b v).mpr hv) w hw (fun h => hn ((q.occurs_iff b w).mp h))

/-- A continuation may erase reflexive child equations. Any variable lost
from the original problem must be reserved while freshening its answers. -/
theorem drop_reflexive (t : Term sig) (rest : Problem sig) (avoid : List Variable)
    (answers : List (Substitution sig))
    (hc : (Outcome.complete answers).CorrectIn rest (t.variables ++ avoid)) :
    (Outcome.complete answers).CorrectIn (⟨t,t⟩ :: rest) avoid := by
  apply ACResidual.lift_complete _ rest avoid t.variables answers _ _ _ hc
  · intro σ
    simp [Problem.Solves, EquivB.refl]
  · rintro v ⟨e, he, hv⟩; exact ⟨e, .tail _ he, hv⟩
  · rintro v ⟨e, he, hv⟩ hn
    rcases List.mem_cons.mp he with rfl | ha
    · exact (Term.mem_variables ..).mpr (hv.elim id id)
    · exact False.elim (hn ⟨e,ha,hv⟩)

end Tamarin.Commutative
