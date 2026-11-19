import Tamarin.ACPivot
import Tamarin.OpenMatchSelect

/-! Unification with one expanding AC operand. The selector enumerates positions
in the opposite product. The chosen position and its entire complement become
two ordinary equations in one continuation, with all other conjuncts retained. -/
namespace Tamarin.OneOpenPivot
open AtomicACPair Cancellation
variable {sig : Signature}

structure Query (sig : Signature) where
  f : sig.ACSym
  loose : Term sig
  rigid : Term sig
  first : Term sig
  second : Term sig
  rest : List (Term sig)
  tail : Problem sig

namespace Query
variable (q : Query sig)

def operands := q.first :: q.second :: q.rest
def operand (i : Nat) := q.operands[i]?.getD q.first
def lhs : Term sig := .ac q.f q.rigid q.loose
def rhs := ACRepresentation.fold q.f q.first (q.second :: q.rest)
def problem : Problem sig := ⟨q.lhs,q.rhs⟩ :: q.tail

private theorem inventory : (List.range q.operands.length).map q.operand = q.operands := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp [operand,hi]

/-- Rust may use its AC smart constructor on the surviving operands and may
move the selected equation to the front. Singleton complements remain terms. -/
inductive Reads : List Nat → Problem sig → Prop where
  | row (i j : Nat) (is : List Nat) (remainder : Term sig) (branch : Problem sig)
      (grouping : EquivB remainder (ACRepresentation.fold q.f (q.operand j) (is.map q.operand)))
      (layout : branch.Perm (⟨q.rigid,q.operand i⟩ :: ⟨q.loose,remainder⟩ :: q.tail)) :
      Reads (i :: j :: is) branch

/-- Rearranging the two sides, their factors, or the surrounding conjunction
does not change the selected problem. -/
structure Presented (caller : Problem sig) : Prop where
  layout : ∃ e : Equation sig, caller.Perm (e :: q.tail) ∧
    ((EquivB e.lhs q.lhs ∧ EquivB e.rhs q.rhs) ∨ (EquivB e.rhs q.lhs ∧ EquivB e.lhs q.rhs))

theorem fromSlots [DecidableEq sig.ACSym] (f : sig.ACSym) {input out : Term sig}
    {slots : List (Term sig)} (perm : (ACRepresentation.flatten f input).Perm slots)
    (decoded : ACRepresentation.decode f slots = some out) : EquivB input out := by
  obtain ⟨t,ht,eq⟩ := ACRepresentation.flatten_correct f input
  exact eq.symm.trans (ACRepresentation.decode_perm f perm _ _ ht decoded)

theorem Presented.of_flatten [DecidableEq sig.ACSym] {caller : Problem sig} (e : Equation sig)
    (placed : caller.Perm (e :: q.tail))
    (sides : ((ACRepresentation.flatten q.f e.lhs).Perm [q.rigid,q.loose] ∧
              (ACRepresentation.flatten q.f e.rhs).Perm q.operands) ∨
             ((ACRepresentation.flatten q.f e.rhs).Perm [q.rigid,q.loose] ∧
              (ACRepresentation.flatten q.f e.lhs).Perm q.operands)) : q.Presented caller := by
  refine ⟨e,placed,?_⟩
  rcases sides with ⟨l,r⟩|⟨l,r⟩
  · exact .inl ⟨fromSlots _ l rfl,fromSlots _ r rfl⟩
  · exact .inr ⟨fromSlots _ l rfl,fromSlots _ r rfl⟩

private theorem perm_solves {p r : Problem sig} (h : p.Perm r) (σ : Substitution sig) :
    p.Solves σ ↔ r.Solves σ := by simp only [Problem.Solves,h.mem_iff]

private theorem perm_occurs {p r : Problem sig} (h : p.Perm r) (v : Variable) :
    p.Occurs v ↔ r.Occurs v := by simp only [Problem.Occurs,h.mem_iff]

private theorem change_sides {a b u v : Term sig} (l : EquivB a u) (r : EquivB b v) (σ : Substitution sig) :
    EquivB (σ.apply a) (σ.apply b) ↔ EquivB (σ.apply u) (σ.apply v) :=
  ⟨fun h => (l.subst σ.image).symm.trans (h.trans (r.subst σ.image)),
   fun h => (l.subst σ.image).trans (h.trans (r.subst σ.image).symm)⟩

theorem Presented.solves {caller : Problem sig} (h : q.Presented caller) (σ : Substitution sig) :
    caller.Solves σ ↔ q.problem.Solves σ := by
  obtain ⟨e,move,sides⟩ := h.layout
  rw [perm_solves move,problem,ACPivot.Query.solves_cons,ACPivot.Query.solves_cons]
  apply and_congr_left; intro _
  rcases sides with ⟨l,r⟩|⟨l,r⟩
  · exact change_sides l r σ
  · exact Iff.trans ⟨EquivB.symm,EquivB.symm⟩ (change_sides l r σ)

theorem Presented.occurs {caller : Problem sig} (h : q.Presented caller) (v : Variable) :
    caller.Occurs v ↔ q.problem.Occurs v := by
  obtain ⟨e,move,sides⟩ := h.layout
  rw [perm_occurs move,problem,ACPivot.Query.occurs_cons,ACPivot.Query.occurs_cons]
  rcases sides with ⟨l,r⟩|⟨l,r⟩
  · exact or_congr (or_congr (l.occurs_iff v) (r.occurs_iff v)) Iff.rfl
  · exact or_congr ((or_congr (r.occurs_iff v) (l.occurs_iff v)).trans or_comm) Iff.rfl

theorem regroup {i j : Nat} {is : List Nat}
    (perm : (i :: j :: is).Perm (List.range q.operands.length)) :
    EquivB q.rhs (.ac q.f (q.operand i) (ACRepresentation.fold q.f (q.operand j) (is.map q.operand))) := by
  have p := perm.symm.map q.operand
  rw [q.inventory] at p
  exact ACRepresentation.decode_perm q.f p _ _ rfl rfl

/-- Equal factor occurrences remain distinct positions even if equality
arises only after specializing variables shared by the two sides. -/
private theorem find {σ : Substitution sig} (a : Atomic q.f q.rigid)
    (each : ∀ b ∈ q.operands, Atomic q.f b) (eq : EquivB (σ.apply q.lhs) (σ.apply q.rhs)) :
    ∃ i < q.operands.length, EquivB (σ.apply q.rigid) (σ.apply (q.operand i)) := by
  have flat := flatten_equiv q.f eq
  change (flatten q.f (.ac q.f (σ.apply q.rigid) (σ.apply q.loose))).Perm
    (flatten q.f (σ.apply (ACRepresentation.fold q.f q.first (q.second :: q.rest)))) at flat
  rw [flatten_ac,a σ,ACPivot.fold_factors] at flat
  obtain ⟨b,hb,mem⟩ := List.mem_flatMap.mp (flat.mem_iff.mp List.mem_cons_self)
  obtain ⟨i,hi,atIndex⟩ := List.getElem_of_mem (l := q.operands) hb
  exact ⟨i,hi,by simpa [operand,hi,atIndex] using ACPivot.fixed_owner (each _ hb) σ mem⟩

private theorem view {σ : Substitution sig} {i j is rem}
    (perm : (i :: j :: is).Perm (List.range q.operands.length))
    (grouping : EquivB rem (ACRepresentation.fold q.f (q.operand j) (is.map q.operand)))
    (selected : EquivB (σ.apply q.rigid) (σ.apply (q.operand i))) :
    EquivB (σ.apply q.lhs) (σ.apply q.rhs) ↔ EquivB (σ.apply q.loose) (σ.apply rem) := by
  have target := ((q.regroup perm).trans (.ac_congr q.f (.refl _) grouping.symm)).subst σ.image
  constructor
  · intro h
    exact EquivB.ac_cancel_left q.f ((h.trans target).trans (.ac_congr q.f selected.symm (.refl _)))
  · intro h
    exact (EquivB.ac_congr q.f selected h).trans target.symm

private theorem scope {row branch} (read : q.Reads row branch)
    (perm : row.Perm (List.range q.operands.length)) (v : Variable) : q.problem.Occurs v ↔ branch.Occurs v := by
  cases read with
  | row i j is rem branch grouping layout =>
    have sides := ((q.regroup perm).trans (.ac_congr q.f (.refl _) grouping.symm)).occurs_iff v
    rw [perm_occurs layout,problem,ACPivot.Query.occurs_cons,ACPivot.Query.occurs_cons,ACPivot.Query.occurs_cons]
    simp only [lhs,Term.Occurs] at *
    grind

/-- In the default selection every position is eligible. If a rigid factor
already occurs on the opposite side, keeping any one such position suffices
by cancellativity, including when other positions denote the same term. -/
def CoversPositions (keep : Nat → Prop) : Prop :=
  (∀ i < q.operands.length, keep i) ∨
    ∃ i < q.operands.length, keep i ∧ EquivB q.rigid (q.operand i)


private theorem branch_iff {σ : Substitution sig} {i is work}
    (read : q.Reads (i::is) work) (perm : (i::is).Perm (List.range q.operands.length)) :
    work.Solves σ ↔ q.problem.Solves σ ∧ EquivB (σ.apply q.rigid) (σ.apply (q.operand i)) := by
  cases read with
  | row i j js rem branch grouping layout =>
    rw [perm_solves layout,problem,ACPivot.Query.solves_cons,ACPivot.Query.solves_cons,ACPivot.Query.solves_cons]
    constructor
    · rintro ⟨selected,loose,tail⟩
      exact ⟨⟨(q.view perm grouping selected).mpr loose,tail⟩,selected⟩
    · rintro ⟨⟨full,tail⟩,selected⟩
      exact ⟨selected,(q.view perm grouping selected).mp full,tail⟩

/-- The caller can deduplicate by the value of the selected operand. For
equal selected operands any grouping of the complementary occurrences gives
the same equality modulo B, by cancellation. -/
structure Decoding (packet : OpenMatchSelect.Packet) (keep : Nat → Prop) (work : List (Problem sig)) : Prop where
  valid : ∀ p ∈ work, ∃ i rest, i :: rest ∈ OpenMatchSelect.decoded packet ∧ q.Reads (i :: rest) p
  covers : ∀ i rest, i :: rest ∈ OpenMatchSelect.decoded packet → keep i →
    ∃ p ∈ work, ∃ j tail, j :: tail ∈ OpenMatchSelect.decoded packet ∧
      EquivB (q.operand i) (q.operand j) ∧ q.Reads (j :: tail) p

private theorem resolves {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel)
    {n packet} (size : n.toNat = q.operands.length) (ran : kernel 1 n = some packet)
    (fixed : Atomic q.f q.rigid) (others : ∀ b ∈ q.operands, Atomic q.f b)
    {keep work} (eligible : q.CoversPositions keep) (rows : q.Decoding packet keep work)
    (σ : Substitution sig) : q.problem.Solves σ ↔ ∃ p ∈ work, p.Solves σ := by
  have rowPerm {r} (h : r ∈ OpenMatchSelect.decoded packet) :
      r.Perm (List.range q.operands.length) := size ▸ ok.perm ran h
  constructor
  · intro h
    have selected : ∃ i < q.operands.length, keep i ∧ EquivB (σ.apply q.rigid) (σ.apply (q.operand i)) := by
      rcases eligible with all | ⟨i,hi,allowed,eq⟩
      · obtain ⟨i,hi,eq⟩ := q.find fixed others (h _ List.mem_cons_self)
        exact ⟨i,hi,all i hi,eq⟩
      · exact ⟨i,hi,allowed,eq.subst σ.image⟩
    obtain ⟨i,hi,allowed,eq⟩ := selected
    obtain ⟨rest,mem⟩ := ok.prefixes [i] ran rfl (by simp) (by simpa [size] using hi)
    obtain ⟨p,hp,j,js,hj,same,read⟩ := rows.covers i rest mem allowed
    exact ⟨p,hp,(q.branch_iff read (rowPerm hj)).mpr ⟨h,eq.trans (same.subst σ.image)⟩⟩
  · rintro ⟨p,hp,sol⟩
    obtain ⟨i,is,mem,read⟩ := rows.valid p hp
    exact ((q.branch_iff read (rowPerm mem)).mp sol).1

/-- Interpretation is total on every successful packet at width at least
two. Each row consumes one occurrence and leaves a nonempty AC product. -/
theorem readable {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel)
    {n packet} (size : n.toNat = q.operands.length) (ran : kernel 1 n = some packet) :
    ∀ r ∈ OpenMatchSelect.decoded packet, ∃ p, q.Reads r p := by
  intro r hr
  have len := (ok.perm ran hr).length_eq
  simp only [List.length_range,size,operands,List.length_cons] at len
  cases r with
  | nil => simp at len
  | cons i r => cases r with
    | nil => simp at len
    | cons j is => exact ⟨_,.row i j is _ _ (.refl _) (.refl _)⟩


/-- Interpret the actual prefix and suffix of a selector row. The suffix may
use any order. It must still contain each unselected position exactly once. -/
def read : List Nat → Option (Problem sig)
  | i :: j :: is => some (⟨q.rigid,q.operand i⟩ ::
      ⟨q.loose,ACRepresentation.fold q.f (q.operand j) (is.map q.operand)⟩ :: q.tail)
  | _ => none

def branches (packet : OpenMatchSelect.Packet) :=
  (OpenMatchSelect.decoded packet).filterMap q.read

/-- The full packet itself supplies valid, exhaustive continuations, without
any condition on an external interpretation of its rows. -/
theorem branches_decode {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel)
    {n packet} (size : n.toNat = q.operands.length) (ran : kernel 1 n = some packet) :
    q.Decoding packet (fun _ => True) (q.branches packet) := by
  constructor
  · intro p hp
    obtain ⟨r,hr,read⟩ := List.mem_filterMap.mp hp
    obtain ⟨_,proof⟩ := q.readable ok size ran r hr
    cases proof with
    | row i j is rem branch grouping placement =>
      cases Option.some.inj read
      exact ⟨i,j::is,hr,.row i j is _ _ (.refl _) (.refl _)⟩
  · intro i rest hr _
    obtain ⟨_,proof⟩ := q.readable ok size ran (i :: rest) hr
    cases proof with
    | row i j is rem branch grouping placement =>
      exact ⟨_,List.mem_filterMap.mpr ⟨_,hr,rfl⟩,i,j::is,hr,.refl _,.row i j is _ _ (.refl _) (.refl _)⟩

end Query

/-- The same complete family covers arbitrary caller constraints and keeps
one substitution on every original variable. The allocator can preserve its
existing avoid set because no branch introduces variables. -/
def Semantic (kernel : OpenMatchSelect.Kernel) : Prop :=
  ∀ {s : Signature} (q : Query s) {n packet}, n.toNat = q.operands.length → kernel 1 n = some packet →
    (∀ row ∈ OpenMatchSelect.decoded packet, ∃ p, q.Reads row p) ∧
    q.Decoding packet (fun _ => True) (q.branches packet) ∧
    ∀ (caller : Problem s), q.Presented caller →
    Atomic q.f q.rigid → (∀ b ∈ q.operands, Atomic q.f b) →
    ∀ keep work, q.CoversPositions keep → q.Decoding packet keep work →
      (∀ σ, caller.Solves σ ↔ ∃ p ∈ work, p.Solves σ) ∧
      ∀ avoid (answers : Problem s → List (Substitution s)),
        (∀ p ∈ work, (Outcome.complete (answers p)).CorrectIn p avoid) →
        (Outcome.complete (work.flatMap answers)).CorrectIn caller avoid

theorem semantic {kernel : OpenMatchSelect.Kernel} (ok : OpenMatchSelect.Correct kernel) : Semantic kernel := by
  intro s q n packet size ran
  refine ⟨q.readable ok size ran,q.branches_decode ok size ran,?_⟩
  intro caller placement fixed others keep work eligible rows
  have solves (σ) := (placement.solves q σ).trans (q.resolves ok size ran fixed others eligible rows σ)
  have scope (p) (hp : p ∈ work) (v) : caller.Occurs v ↔ p.Occurs v := by
    obtain ⟨_,_,mem,read⟩ := rows.valid p hp
    exact (placement.occurs q v).trans (q.scope read (size ▸ ok.perm ran mem) v)
  refine ⟨solves,?_⟩
  intro avoid answers closed
  constructor
  · constructor
    · intro σ mem
      obtain ⟨p,hp,hs⟩ := List.mem_flatMap.mp mem
      exact (solves σ).mpr ⟨p,hp,(closed p hp).mathematical.sound σ hs⟩
    · intro ρ hρ
      obtain ⟨p,hp,sol⟩ := (solves ρ).mp hρ
      obtain ⟨σ,hs,δ,fit⟩ := (closed p hp).mathematical.covers ρ sol
      exact ⟨σ,List.mem_flatMap.mpr ⟨p,hp,hs⟩,δ,fun v hv => fit v ((scope p hp v).mp hv)⟩
  · intro σ mem v absent
    obtain ⟨p,hp,hs⟩ := List.mem_flatMap.mp mem
    exact (closed p hp).domain σ hs v fun h => absent ((scope p hp v).mpr h)
  · intro σ mem v hv w hw outside
    obtain ⟨p,hp,hs⟩ := List.mem_flatMap.mp mem
    exact (closed p hp).fresh σ hs v ((scope p hp v).mp hv) w hw fun h => outside ((scope p hp w).mpr h)

end Tamarin.OneOpenPivot
