import Tamarin.FlatACVariable
import Tamarin.FreshSubstitution
import Tamarin.SortCheck

/-! Unifiers of x+a = y+b for distinct variables of the operator sort and
distinct rigid atoms. The empty common remainder and the nonempty remainder
are separate branches, since an AC operator has no unit. -/
namespace Tamarin.SharedOffset
open Cancellation
variable {sig : Signature}

private theorem exchange (f : sig.ACSym) (r u v : Term sig) :
    EquivB (.ac f (.ac f r u) v) (.ac f (.ac f r v) u) :=
  (EquivB.ac_assoc f _ _ _).trans
    ((EquivB.ac_congr f (.refl r) (.ac_swap f _ _)).trans (EquivB.ac_assoc f _ _ _).symm)

private def Split (f : sig.ACSym) (b : sig.Atom) (t : Term sig) : Prop :=
  EquivB t (.atom b) ∨ ∃ r, HasSort r (sig.acSort f) ∧ EquivB t (.ac f r (.atom b))

private theorem split_left (f : sig.ACSym) (b : sig.Atom) {u v : Term sig}
    (hu : Split f b u) (hv : HasSort v (sig.acSort f)) : Split f b (.ac f u v) := by
  right
  rcases hu with h | ⟨r, hr, h⟩
  · exact ⟨v, hv, (EquivB.ac_congr f h (.refl v)).trans (.ac_swap f _ _)⟩
  · exact ⟨.ac f r v, .ac f _ _ hr hv,
      (EquivB.ac_congr f h (.refl v)).trans (exchange f _ _ _)⟩

private theorem split_atom (f : sig.ACSym) (b : sig.Atom) (t : Term sig)
    (ht : HasSort t (sig.acSort f)) (hm : classOf (.atom b) ∈ flatten f t) : Split f b t := by
  induction t with
  | ac g u v iu iv =>
    by_cases he : f = g
    · subst g
      rw [flatten_ac] at hm
      have hc := Term.checkSort_complete ht
      simp only [Term.checkSort, Bool.and_eq_true] at hc
      have hu := Term.checkSort_sound _ _ hc.1.2
      have hv := Term.checkSort_sound _ _ hc.2
      rcases List.mem_append.mp hm with h | h
      · exact split_left f b (iu hu h) hv
      · obtain h | ⟨r, hr, h⟩ := split_left f b (iv hv h) hu
        · exact Or.inl ((EquivB.ac_swap f u v).trans h)
        · exact Or.inr ⟨r, hr, (EquivB.ac_swap f u v).trans h⟩
    · simp only [flatten, ite_eq_right he, List.mem_singleton] at hm
      exact Or.inl (Quotient.exact hm.symm)
  | var | atom | free | comm =>
    exact Or.inl (Quotient.exact (List.mem_singleton.mp hm).symm)

private theorem decompose (f : sig.ACSym) (a b : sig.Atom) (hab : a ≠ b)
    (u v : Term sig) (hu : HasSort u (sig.acSort f))
    (h : EquivB (.ac f u (.atom a)) (.ac f v (.atom b))) :
    (EquivB u (.atom b) ∧ EquivB v (.atom a)) ∨
      ∃ r, HasSort r (sig.acSort f) ∧ EquivB u (.ac f r (.atom b)) ∧
        EquivB v (.ac f r (.atom a)) := by
  classical
  have hp := flatten_equiv f h
  rw [flatten_ac, flatten_ac] at hp
  have hm := hp.symm.subset (a := classOf (.atom b))
    (List.mem_append_right _ (List.mem_singleton_self _))
  rcases List.mem_append.mp hm with hm | hm
  · rcases split_atom f b u hu hm with hb | ⟨r, hr, hb⟩
    · exact Or.inl ⟨hb, EquivB.ac_cancel_right f
        (h.symm.trans ((EquivB.ac_congr _ hb (.refl _)).trans (.ac_swap f _ _)))⟩
    · exact Or.inr ⟨r, hr, hb, EquivB.ac_cancel_right f
        (h.symm.trans ((EquivB.ac_congr _ hb (.refl _)).trans (exchange f _ _ _)))⟩
  · have eq : EquivB (Term.atom (sig := sig) b) (.atom a) :=
      Quotient.exact (List.mem_singleton.mp hm)
    have count := eq.eval_eq (FlatAC.atomCountModel b) (fun _ => 0)
    simp [Model.eval, FlatAC.atomCountModel, hab] at count

def problem (f : sig.ACSym) (x y : Variable) (a b : sig.Atom) : Problem sig :=
  [⟨.ac f (.var x) (.atom a), .ac f (.var y) (.atom b)⟩]

theorem occurs (f : sig.ACSym) (x y : Variable) (a b : sig.Atom) (v : Variable) :
    (problem f x y a b).Occurs v ↔ v = x ∨ v = y := by
  simp [Problem.Occurs, problem, Term.Occurs]

/-- The only range variable in the open branch is the single slot z, shared
by both images. The compact branch uses the opposite atom alone. -/
def image (f : sig.ACSym) (z : Variable) (shared : Bool) (b : sig.Atom) : Term sig :=
  if shared then .ac f (.var z) (.atom b) else .atom b

private theorem image_sorted (f : sig.ACSym) (z : Variable) (shared : Bool) (b : sig.Atom)
    (hz : z.sort = sig.acSort f) (hb : HasSort (.atom b) (sig.acSort f)) :
    HasSort (image f z shared b) (sig.acSort f) := by
  cases shared
  · exact hb
  · exact .ac f _ _ (hz ▸ HasSort.var z) hb

structure Query (sig : Signature) where
  f : sig.ACSym
  x : Variable
  y : Variable
  a : sig.Atom
  b : sig.Atom
  xy : x ≠ y
  ab : a ≠ b
  sx : x.sort = sig.acSort f
  sy : y.sort = sig.acSort f
  sa : HasSort (.atom a) (sig.acSort f)
  sb : HasSort (.atom b) (sig.acSort f)

variable (q : Query sig) (z : Variable) (hz : z.sort = sig.acSort q.f)

def answer (shared : Bool) : Substitution sig where
  image v := if v = q.x then image q.f z shared q.b
    else if v = q.y then image q.f z shared q.a else .var v
  support := [q.x, q.y]
  outside v hv := by simp_all
  sorted v := by
    split
    · next h => subst v; rw [q.sx]; exact image_sorted _ _ _ _ hz q.sb
    · split
      · next h => subst v; rw [q.sy]; exact image_sorted _ _ _ _ hz q.sa
      · exact .var v

theorem complete : CompleteSet (problem q.f q.x q.y q.a q.b)
    [answer q z hz false, answer q z hz true] := by
  constructor
  · intro σ hs e he
    obtain rfl := List.mem_singleton.mp he
    rcases List.mem_cons.mp hs with h | h
    · subst σ
      simpa [Substitution.apply, Term.subst, answer, image, Ne.symm q.xy] using
        (EquivB.ac_swap q.f (.atom q.b) (.atom q.a))
    · obtain rfl := List.mem_singleton.mp h
      simpa [Substitution.apply, Term.subst, answer, image, Ne.symm q.xy] using
        (exchange q.f (.var z) (.atom q.b) (.atom q.a))
  · intro ρ hρ
    have h := hρ _ (List.mem_singleton_self _)
    have sorted := ρ.sorted q.x
    rw [q.sx] at sorted
    rcases decompose q.f q.a q.b q.ab (ρ.image q.x) (ρ.image q.y) sorted h with ⟨hx, hy⟩ | ⟨r, hr, hx, hy⟩
    · refine ⟨_, List.mem_cons_self, Substitution.identity, ?_⟩
      intro v hv
      rcases (occurs _ _ _ _ _ _).mp hv with rfl | rfl
      · simpa [Substitution.compose, answer, image] using hx
      · simpa [Substitution.compose, answer, image, Ne.symm q.xy] using hy
    · let δ := Substitution.binding z r (hz ▸ hr)
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), δ, ?_⟩
      intro v hv
      rcases (occurs _ _ _ _ _ _).mp hv with rfl | rfl
      · simpa [Substitution.compose, Substitution.apply, answer, image, Term.subst, δ,
          Substitution.binding] using hx
      · simpa [Substitution.compose, Substitution.apply, answer, image, Term.subst, δ,
          Substitution.binding, Ne.symm q.xy] using hy

theorem correctIn (avoid : List Variable) (fresh : z ∉ avoid) :
    (Outcome.complete [answer q z hz false, answer q z hz true]).CorrectIn
      (problem q.f q.x q.y q.a q.b) avoid := by
  have domain (s : Bool) : DomainRestricted (problem q.f q.x q.y q.a q.b) (answer q z hz s) := by
    intro v hv
    have hn := mt ((occurs q.f q.x q.y q.a q.b v).mpr) hv
    simp_all [answer]
  have hscope (s : Bool) : FreshFor (problem q.f q.x q.y q.a q.b) avoid (answer q z hz s) := by
    intro v hv w hw _
    rcases (occurs _ _ _ _ _ _).mp hv with rfl | rfl <;> cases s <;>
      simp [answer, image, Term.Occurs, Ne.symm q.xy] at hw
    all_goals exact hw ▸ fresh
  constructor
  · exact complete q z hz
  · simpa only [Outcome.answers, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true] using And.intro (domain false) (domain true)
  · simpa only [Outcome.answers, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true] using And.intro (hscope false) (hscope true)

/-- A row stores its rigid atom ID followed by an optional branch-local witness ID.
The two namespaces are independent, even when their words coincide. -/
def decodeRow (f : sig.ACSym) (atom : UInt64 → sig.Atom) (slot : UInt64 → Variable)
    (row : Array UInt64) : Option (Term sig) :=
  match row.toList with
  | [a] => some (.atom (atom a))
  | [a, w] => some (.ac f (.var (slot w)) (.atom (atom a)))
  | _ => none

def decodeArm (q : Query sig) (atom : UInt64 → sig.Atom) (slot : UInt64 → Variable)
    (arm : Array (Array UInt64)) : Option (List (Variable × Term sig)) := do
  let [l, r] := arm.toList | none
  return [(q.x, ← decodeRow q.f atom slot l), (q.y, ← decodeRow q.f atom slot r)]

abbrev Packet := Array (Array (Array UInt64))

/-- The contract permits different branch order and any choice of witness ID.
A disagreement between its two occurrences would change the represented answer. -/
def PacketCorrect (run : UInt64 → UInt64 → Packet) : Prop :=
  ∀ a b, a ≠ b → ∃ w, (run a b).toList.Perm
    [#[#[b], #[a]], #[#[b, w], #[a, w]]]

/-- Every stored range variable is outside both input keys and the caller's
context, as required when reinterpreting a packet as a fresh-range substitution. -/
def ClosedRanges (q : Query sig) (avoid : List Variable) (σ : Substitution sig) : Prop :=
  ∀ v ∈ [q.x, q.y], ∀ w, (σ.image v).Occurs w → w ∉ avoid ++ [q.x, q.y]

private theorem closedRanges (s : Bool) (avoid : List Variable)
    (fresh : z ∉ avoid ++ [q.x, q.y]) : ClosedRanges q avoid (answer q z hz s) := by
  intro v hv w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> cases s <;>
    simp [answer, image, Term.Occurs, Ne.symm q.xy] at hw
  all_goals exact hw ▸ fresh

theorem packet_correctIn {run : UInt64 → UInt64 → Packet} (hc : PacketCorrect run)
    (q : Query sig) (a b : UInt64) (atom : UInt64 → sig.Atom)
    (ha : atom a = q.a) (hb : atom b = q.b)
    (slot : UInt64 → Variable) (typed : ∀ w, (slot w).sort = sig.acSort q.f)
    (avoid : List Variable) (fresh : ∀ w, slot w ∉ avoid ++ [q.x, q.y]) :
    ∃ answers : List (Substitution sig),
      ((run a b).toList.map (decodeArm q atom slot)).Perm
        (answers.map fun σ => some (FreshAnswer.encode [q.x, q.y] σ).bindings) ∧
      (Outcome.complete answers).CorrectIn (problem q.f q.x q.y q.a q.b) avoid ∧
      ∀ σ ∈ answers, ClosedRanges q avoid σ := by
  have hab : a ≠ b := fun he => q.ab (ha.symm.trans ((congrArg atom he).trans hb))
  obtain ⟨w, hp⟩ := hc a b hab
  refine ⟨[answer q (slot w) (typed w) false, answer q (slot w) (typed w) true], ?_,
    correctIn q (slot w) (typed w) avoid (fun h => fresh w (List.mem_append_left _ h)), ?_⟩
  · simpa [decodeArm, decodeRow, FreshAnswer.encode, answer, image, ha, hb, Ne.symm q.xy]
      using hp.map (decodeArm q atom slot)
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨closedRanges q _ _ false avoid (fresh w), closedRanges q _ _ true avoid (fresh w)⟩

end Tamarin.SharedOffset
