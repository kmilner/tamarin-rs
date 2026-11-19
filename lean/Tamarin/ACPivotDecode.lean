import Tamarin.ACPivotPacket

/-! Interpret a pivot program against the caller's term vector. The length
word splits two ordinary equations, each with a singleton LHS and a nonempty
AC fold on the RHS. Bad slots, short headers and empty folds fail. -/
namespace Tamarin.ACPivot.Packet
variable {sig : Signature}

def parse : List UInt64 → Option Fields
  | x :: n :: xs =>
    match xs.drop n.toNat with
    | y :: rest => some (x, xs.take n.toNat, y, rest)
    | [] => none
  | _ => none

/-- The Rust operand vector has these four reserved entries followed by
the original fixed operands, in occurrence order. -/
def slot (q : Query sig) (w : Variable) (word : UInt64) : Option (Term sig) :=
  match word.toNat with
  | 0 => some (.var q.x)
  | 1 => some q.a
  | 2 => some (.var q.y)
  | 3 => some (.var w)
  | i + 4 => q.operands[i]?

private def collect {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | h :: t => return (← h) :: (← collect t)

private theorem collect_some {α : Type} (xs : List α) : collect (xs.map some) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collect,ih]

def interpret (q : Query sig) (w : Variable) (row : Array UInt64) : Option (Problem sig) := do
  let (x,l,y,r) ← parse row.toList
  let lhs ← slot q w x
  let first ← ACRepresentation.decode q.f (← collect (l.map (slot q w)))
  let lhs' ← slot q w y
  let second ← ACRepresentation.decode q.f (← collect (r.map (slot q w)))
  return ⟨lhs,first⟩ :: ⟨lhs',second⟩ :: q.tail

private theorem parse_words {n : Nat} (c : Query.Choice n) :
    parse (words c).toList = some (fields c) := by cases c <;> rfl

private theorem slot_offset (q : Query sig) (w : Variable) (bound : q.operands.length ≤ 32)
    (i : Nat) (hi : i < q.operands.length) :
    slot q w (4+i).toUInt64 = some q.operands[i] := by
  have fits : 4 + i < UInt64.size := by change 4+i < 18446744073709551616; omega
  unfold slot
  rw [show (4+i).toUInt64.toNat = 4+i from UInt64.toNat_ofNat_of_lt' fits,Nat.add_comm 4 i]
  exact List.getElem?_eq_getElem hi

private theorem all_slots (q : Query sig) (w : Variable) (bound : q.operands.length ≤ 32) :
    (offsets q.operands.length).map (slot q w) = q.operands.map some := by
  apply List.ext_getElem
  · simp [offsets]
  · intro i hi hj
    simp only [offsets,List.length_map,List.length_range] at hi
    simpa [offsets] using slot_offset q w bound i hi

private theorem erase_map {α β : Type} (g : α → β) (xs : List α) (i : Nat) :
    (xs.eraseIdx i).map g = (xs.map g).eraseIdx i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (g x :: ·) (ih i)

/-- The packet prepends W to the RHS operand vector in the shared branch. -/
def decodedBranch (q : Query sig) (w : Variable) : Query.Choice q.operands.length → Problem sig
  | .shared => ⟨.var q.y,.ac q.f q.a (.var w)⟩ :: ⟨.var q.x,.ac q.f (.var w) q.product⟩ :: q.tail
  | c => q.branch w c

theorem interpret_words (q : Query sig) (w : Variable) (bound : q.operands.length ≤ 32)
    (c : Query.Choice q.operands.length) :
    interpret q w (words c) = some (decodedBranch q w c) := by
  have all := all_slots q w bound
  have slot0 : slot q w 0 = some (.var q.x) := rfl
  have slot1 : slot q w 1 = some q.a := rfl
  have slot2 : slot q w 2 = some (.var q.y) := rfl
  have slot3 : slot q w 3 = some (.var w) := rfl
  cases c with
  | matchAt i =>
    have he : ((offsets q.operands.length).eraseIdx i.val).map (slot q w) =
        (q.operands.eraseIdx i.val).map some := by rw [erase_map, all, erase_map]
    have si := slot_offset q w bound i.val i.isLt
    simp at si
    simp [interpret,parse_words,fields,slot0,slot1,slot2,he,si,
      collect,collect_some,ACRepresentation.decode,decodedBranch,Query.branch,Query.remainder,ACRepresentation.fold]
  | whole =>
    simp [Query.operands] at all
    simp [interpret,parse_words,fields,slot0,slot1,slot2,all,collect,collect_some,
      ACRepresentation.decode,decodedBranch,Query.branch,ACRepresentation.fold,Query.product,Query.operands]
  | shared =>
    simp [Query.operands] at all
    simp [interpret,parse_words,fields,slot0,slot1,slot2,slot3,all,collect,collect_some,
      ACRepresentation.decode,decodedBranch,ACRepresentation.fold,Query.product,Query.operands]

theorem decoded_solves (q : Query sig) (w : Variable) (c : Query.Choice q.operands.length)
    (σ : Substitution sig) : (decodedBranch q w c).Solves σ ↔ (q.branch w c).Solves σ := by
  cases c with
  | matchAt | whole => rfl
  | shared =>
    simp [decodedBranch, Query.branch,Problem.Solves,Substitution.apply,Term.subst]
    intro _ _; constructor <;> intro h <;> exact h.trans (.ac_swap ..)

theorem decoded_occurs (q : Query sig) (w : Variable) (c : Query.Choice q.operands.length)
    (v : Variable) : (decodedBranch q w c).Occurs v ↔ (q.branch w c).Occurs v := by
  cases c with
  | matchAt | whole => rfl
  | shared => simp [decodedBranch,Query.branch,Problem.Occurs,Term.Occurs,or_comm]

/-- An ordinary complete set for the equations actually decoded from this
row supplies exactly the continuation required by the pivot proof. -/
theorem interpreted_complete (q : Query sig) (w : Variable) (bound : q.operands.length ≤ 32)
    (c : Query.Choice q.operands.length) (p : Problem sig) (answers : List (Substitution sig))
    (ran : interpret q w (words c) = some p) (cs : CompleteSet p answers) :
    CompleteSet (q.branch w c) answers := by
  rw [interpret_words q w bound c] at ran
  cases Option.some.inj ran
  refine ⟨fun σ h => (decoded_solves q w c σ).mp (cs.sound _ h),?_⟩
  intro ρ hρ
  obtain ⟨σ,hs,δ,agrees⟩ := cs.covers _ ((decoded_solves q w c ρ).mpr hρ)
  exact ⟨σ,hs,δ,fun v hv => agrees v ((decoded_occurs q w c v).mpr hv)⟩

end Tamarin.ACPivot.Packet
