import Tamarin.ACLinearConsequence
import Tamarin.ACSpanCertificate
import Tamarin.ResidualSearch
import Tamarin.ACPivot

namespace Tamarin.ACForcedEquations
open ACBasis
variable {s : Signature} {n : Nat}

/-- A preprocessing step may add consequences about caller operands.
Its equality certificates never introduce an unrelated caller variable. -/
structure Forced (p added : Problem s) : Prop where
  follows : ∀ σ, p.Solves σ → added.Solves σ
  scope : ∀ v, added.Occurs v → p.Occurs v

theorem Forced.of_each {p added : Problem s} (each : ∀ e ∈ added, Forced p [e]) : Forced p added where
  follows σ sol e he := (each e he).follows σ sol e List.mem_cons_self
  scope v := fun ⟨e,he,occ⟩ => (each e he).scope v ⟨e,List.mem_cons_self,occ⟩

private theorem decoded_occurs (f : s.ACSym) (get : Fin n → Term s) (ids : List (Fin n))
    {t : Term s} (encoded : ACRepresentation.decode f (ids.map get) = some t) {i : Fin n}
    (present : i ∈ ids) {v : Variable} (occ : (get i).Occurs v) : t.Occurs v := by
  cases ids with
  | nil => cases present
  | cons j js =>
    obtain rfl : t = ACRepresentation.fold f (get j) (js.map get) := (Option.some.inj encoded).symm
    clear encoded
    induction js generalizing j with
    | nil => obtain rfl := List.mem_singleton.mp present; exact occ
    | cons a as ih =>
      rcases List.mem_cons.mp present with rfl|tail
      · exact Or.inl occ
      · exact Or.inr (ih a tail)

private theorem factor_scope (f : s.ACSym) (get : Fin n → Term s) (p : Problem s)
    {rs : List (ACRowElimination.Row (Fin n))}
    (sources : ∀ r ∈ rs, ∃ e ∈ p, ACRowElimination.Represents r f get e)
    {i : Fin n} (used : ∃ r ∈ rs, i ∈ r.lhs ++ r.rhs) {v : Variable} (occ : (get i).Occurs v) :
    p.Occurs v := by
  obtain ⟨r,hr,mem⟩ := used
  obtain ⟨e,he,rep⟩ := sources r hr
  refine ⟨e,he,?_⟩
  rcases List.mem_append.mp mem with l|r'
  · obtain ⟨_,formed,eq⟩ := rep.lhs
    exact .inl ((eq.occurs_iff v).mpr (decoded_occurs f get _ formed l occ))
  · obtain ⟨_,formed,eq⟩ := rep.rhs
    exact .inr ((eq.occurs_iff v).mpr (decoded_occurs f get _ formed r' occ))

/-- A certified equality between two coordinate values is an equality of
the original operands, including when an operand contains other variables
or expands to another product under substitution. -/
theorem forced_pair_of_holds (f : s.ACSym) (get : Fin n → Term s) (p : Problem s)
    (rs : List (ACRowElimination.Row (Fin n)))
    (sources : ∀ r ∈ rs, ∃ e ∈ p, ACRowElimination.Represents r f get e) (i j : Fin n)
    (used : ∀ k ∈ [i,j], ∃ r ∈ rs, k ∈ r.lhs ++ r.rhs)
    (equal : ∀ x, (∀ r ∈ rs.map ACLinearConsequence.incidence, r.Holds x) → x i = x j) :
    Forced p [⟨get i,get j⟩] := by
  let singleton : ACRowElimination.Row (Fin n) := ⟨[i],[j]⟩
  constructor
  · intro σ pos e he
    obtain rfl := List.mem_singleton.mp he
    exact ACLinearConsequence.equation f get p _ rs singleton sources (ACRowElimination.singleton f get i j)
      (fun x common => (ACLinearConsequence.incidence_holds singleton x).mpr (by
        simpa [singleton,ACRowElimination.Balanced,ACRowElimination.weight] using equal x common)) σ pos
  · rintro v ⟨e,he,h⟩
    obtain rfl := List.mem_singleton.mp he
    rcases h with l|r
    · exact factor_scope f get p sources (used i (by simp)) l
    · exact factor_scope f get p sources (used j (by simp)) r

theorem forced_pair (f : s.ACSym) (get : Fin n → Term s) (p : Problem s)
    (rs : List (ACRowElimination.Row (Fin n)))
    (sources : ∀ r ∈ rs, ∃ e ∈ p, ACRowElimination.Represents r f get e) (i j : Fin n)
    (used : ∀ k ∈ [i,j], ∃ r ∈ rs, k ∈ r.lhs ++ r.rhs)
    (certificate : ∃ c, SpanCertificate.Valid (rs.map ACLinearConsequence.incidence)
      (Row.ofWeights (spike i 1) (spike j 1)) c) : Forced p [⟨get i,get j⟩] := by
  apply forced_pair_of_holds f get p rs sources i j used
  intro x common
  obtain ⟨cert,nonzero,_,span⟩ := certificate
  have h := ACLinearConsequence.holds_of_combination _ _ cert.weights cert.scale nonzero span x common
  have swap (v w : Vec n) : dot v w = dot w v := by simp only [dot,Nat.mul_comm]
  simpa only [Row.ofWeights_holds,swap (spike _ _) x,dot_spike,Nat.mul_one] using h

/-- A factor may be replaced as a whole, under any constructor, in either
direction and at any number of sites. Basis equivalence allows alternative
AC associations to expose different occurrences of the same operand. -/
inductive Replace (added : Problem s) : Term s → Term s → Prop where
  | equation {e} (h : e ∈ added) : Replace added e.lhs e.rhs
  | basis {a b} (h : EquivB a b) : Replace added a b
  | symm {a b} : Replace added a b → Replace added b a
  | trans {a b c} : Replace added a b → Replace added b c → Replace added a c
  | free (f : s.FreeSym) (xs ys : Fin (s.arity f) → Term s) :
      (∀ i, Replace added (xs i) (ys i)) → Replace added (.free f xs) (.free f ys)
  | comm (f : s.CSym) {a b c d} : Replace added a c → Replace added b d →
      Replace added (.comm f a b) (.comm f c d)
  | ac (f : s.ACSym) {a b c d} : Replace added a c → Replace added b d →
      Replace added (.ac f a b) (.ac f c d)

theorem Replace.valid {added : Problem s} {a b} (h : Replace added a b)
    (σ : Substitution s) (sol : added.Solves σ) : EquivB (σ.apply a) (σ.apply b) := by
  induction h with
  | equation h => exact sol _ h
  | basis h => exact h.subst σ.image
  | symm _ ih => exact ih.symm
  | trans _ _ ih jk => exact ih.trans jk
  | free f _ _ _ ih => exact .free f _ _ ih
  | comm f _ _ ih jk => exact .comm_congr f ih jk
  | ac f _ _ ih jk => exact .ac_congr f ih jk

theorem Replace.outside {added : Problem s} {a b} (h : Replace added a b)
    (v : Variable) (external : ¬added.Occurs v) : a.Occurs v ↔ b.Occurs v := by
  induction h with
  | equation h => exact ⟨fun l => False.elim (external ⟨_,h,.inl l⟩),fun r => False.elim (external ⟨_,h,.inr r⟩)⟩
  | basis h => exact h.occurs_iff v
  | symm _ ih => exact ih.symm
  | trans _ _ ih jk => exact ih.trans jk
  | free f _ _ _ ih => exact exists_congr ih
  | comm f _ _ ih jk | ac f _ _ ih jk => exact or_congr ih jk

/-- Apply the replacements simultaneously on both sides of every equation.
The same assumptions and the same specialization apply across the list. -/
inductive Refactors (added : Problem s) : Problem s → Problem s → Prop where
  | nil : Refactors added [] []
  | cons {a b a' b' : Term s} {ps qs : Problem s}
      (lhs : Replace added a a') (rhs : Replace added b b') (tail : Refactors added ps qs) :
      Refactors added (⟨a,b⟩ :: ps) (⟨a',b'⟩ :: qs)

theorem Refactors.refl (added p : Problem s) : Refactors added p p := by
  induction p with
  | nil => exact .nil
  | cons e _ ih => exact .cons (.basis (.refl e.lhs)) (.basis (.refl e.rhs)) ih

/-- A simultaneous replacement can use a single term transformation for
the entire input. It only needs evidence at the actual equation sites. -/
theorem Refactors.map {added : Problem s} (p : Problem s) (replace : Term s → Term s)
    (sites : ∀ e ∈ p, Replace added e.lhs (replace e.lhs) ∧ Replace added e.rhs (replace e.rhs)) :
    Refactors added p (p.map fun e => ⟨replace e.lhs,replace e.rhs⟩) := by
  induction p with
  | nil => exact .nil
  | cons e p ih =>
    obtain ⟨l,r⟩ := sites e List.mem_cons_self
    exact .cons l r (ih (fun x hx => sites x (List.mem_cons_of_mem _ hx)))

private theorem Refactors.under {added p q : Problem s} (h : Refactors added p q)
    (σ : Substitution s) (sol : added.Solves σ) : p.Solves σ ↔ q.Solves σ := by
  induction h with
  | nil => rfl
  | cons a b _ ih =>
    simp only [Problem.Solves,List.forall_mem_cons] at ih ⊢
    have l := a.valid σ sol
    have r := b.valid σ sol
    exact and_congr ⟨fun e => l.symm.trans (e.trans r),fun e => l.trans (e.trans r.symm)⟩ ih

private theorem Refactors.outside {added p q : Problem s} (h : Refactors added p q)
    (v : Variable) (absent : ¬added.Occurs v) : p.Occurs v ↔ q.Occurs v := by
  induction h with
  | nil => rfl
  | cons a b _ ih =>
    rw [ACPivot.Query.occurs_cons,ACPivot.Query.occurs_cons]
    exact or_congr (or_congr (a.outside v absent) (b.outside v absent)) ih

/-- Both directions refer to the same substitution, including open inputs
and variables shared between equations. The caller-visible domain is
unchanged even if a replacement erases variables from the residual rows. -/
structure Equivalent (p q : Problem s) : Prop where
  solutions : ∀ σ, p.Solves σ ↔ q.Solves σ
  variables : ∀ v, p.Occurs v ↔ q.Occurs v

theorem Forced.refactor {p added q : Problem s} (forced : Forced p added) (rewrite : Refactors added p q) :
    Equivalent p (added ++ q) where
  solutions σ := by
    have both : (added ++ q).Solves σ ↔ added.Solves σ ∧ q.Solves σ := by
      simp [Problem.Solves,or_imp,forall_and]
    rw [both]
    exact ⟨fun hp => ⟨forced.follows σ hp,(rewrite.under σ (forced.follows σ hp)).mp hp⟩,
      fun h => (rewrite.under σ h.1).mpr h.2⟩
  variables v := by
    have obs : (added ++ q).Occurs v ↔ added.Occurs v ∨ q.Occurs v := by
      simp [Problem.Occurs,or_and_right,exists_or]
    rw [obs]
    by_cases seen : added.Occurs v
    · exact ⟨fun _ => .inl seen,fun _ => forced.scope v seen⟩
    · simpa [seen] using rewrite.outside v seen

theorem Forced.prepend {p added : Problem s} (forced : Forced p added) : Equivalent p (added ++ p) :=
  forced.refactor (.refl added p)

theorem Equivalent.complete {p q : Problem s} (h : Equivalent p q) (answers : List (Substitution s)) :
    CompleteSet q answers ↔ CompleteSet p answers := by
  exact ⟨ACRowElimination.complete_of_equivalent h.solutions (fun v => (h.variables v).mp),
    ACRowElimination.complete_of_equivalent (fun σ => (h.solutions σ).symm) (fun v => (h.variables v).mpr)⟩

/-- Both finished and interrupted outcomes retain soundness, domain and
freshness relative to the original caller and its unchanged avoid list. -/
theorem Equivalent.correctIn {p q : Problem s} (h : Equivalent p q) (avoid : List Variable)
    (out : Outcome s) (answer : out.CorrectIn q avoid) : out.CorrectIn p avoid := by
  have scope : p.Occurs = q.Occurs := funext (fun v => propext (h.variables v))
  constructor
  · cases out with
    | complete answers => exact (h.complete answers).mp answer.mathematical
    | stopped why partials => exact fun σ hs => (h.solutions σ).mpr (answer.mathematical σ hs)
  · simpa only [DomainRestricted,scope] using answer.domain
  · simpa only [FreshFor,scope] using answer.fresh

/-- Replacing factors during a residual search preserves the accumulated
substitution on every observed variable, including those already removed
from the pending worklist. -/
theorem Equivalent.residual {p q : Problem s} (h : Equivalent p q) (observed : Variable → Prop)
    (θ ρ : Substitution s) : Residual.Denotes observed p θ ρ ↔ Residual.Denotes observed q θ ρ :=
  Residual.equivalent observed h.solutions θ ρ

end Tamarin.ACForcedEquations
