import Tamarin.CompoundOffsetRefinement

/-! Distinct atoms are persistent factors with no variables to retain.
Specialize the general shared-offset decoder using the identity permutation. -/
namespace Tamarin.SharedOffset
variable {sig : Signature}

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

def problem (f : sig.ACSym) (x y : Variable) (a b : sig.Atom) : Problem sig :=
  [⟨.ac f (.var x) (.atom a), .ac f (.var y) (.atom b)⟩]

private def Query.compound (q : Query sig) : CompoundOffset.Query sig where
  f := q.f
  x := q.x
  y := q.y
  a := .atom q.a
  b := .atom q.b
  xy := q.xy
  sx := q.sx
  sy := q.sy
  sa := q.sa
  sb := q.sb
  outside := by simp [Term.Occurs]
  factorA := fun _ => rfl
  factorB := fun _ => rfl
  distinct := fun _ h => q.ab (Head.atom.inj h.head_eq)

private def Query.decoder (q : Query sig) (avoid : List Variable)
    (slot : UInt64 → Variable) (typed : ∀ w, (slot w).sort = sig.acSort q.f)
    (fresh : ∀ w, slot w ∉ avoid ++ [q.x, q.y]) : CompoundOffset.Decoder q.compound avoid where
  retained := []
  inventory := by simp [Query.compound, Term.Occurs]
  π := fun _ => ⟨id, id, [], by simp, by simp, by simp, by simp⟩
  renamed := by simp
  slot := slot
  typed := typed
  fresh := by
    intro w
    simpa [CompoundOffset.Query.occurs, Query.compound, Term.Occurs, not_or, and_assoc, and_comm, and_left_comm] using fresh w
  fixed := by simp

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

/-- Every stored range variable is outside both input keys and the caller's
context, as required when reinterpreting a packet as a fresh-range substitution. -/
def ClosedRanges (q : Query sig) (avoid : List Variable) (σ : Substitution sig) : Prop :=
  ∀ v ∈ [q.x, q.y], ∀ w, (σ.image v).Occurs w → w ∉ avoid ++ [q.x, q.y]

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
  let d := q.decoder avoid slot typed fresh
  have rows (r) : d.decodeRow (fun i => .atom (atom i)) r = decodeRow q.f atom slot r := by
    simp only [CompoundOffset.Decoder.decodeRow, decodeRow]
    generalize r.toList = row
    match row with
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl
  have arms (r) : d.decodeArm (fun i => .atom (atom i)) r = decodeArm q atom slot r := by
    simp only [CompoundOffset.Decoder.decodeArm, decodeArm, rows]
    generalize r.toList = arm
    match arm with
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl
  obtain ⟨answers, packet, correct, closed⟩ := CompoundOffset.packet_correctIn hc q.compound avoid d
    a b (fun i => .atom (atom i)) (congrArg Term.atom ha) (congrArg Term.atom hb)
  refine ⟨answers, ?_, correct, ?_⟩
  · rw [funext arms] at packet
    exact packet
  · intro σ hσ v hv w hw
    have hh := closed σ hσ v hv w hw
    simpa [CompoundOffset.Query.occurs, Query.compound, Term.Occurs, not_or, and_comm,
      and_left_comm] using hh

end Tamarin.SharedOffset
