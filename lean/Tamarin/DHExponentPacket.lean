import Tamarin.DHPeer

namespace Tamarin.Rewriting.DHExponent
open DHPeer

/-- The unconstrained old exponent can be the unit or have a negative
occurrence of the added factor. In a cancellation both residual products
are optional, and any nonempty remainder occupies a single Msg slot. -/
inductive Branch where
  | unchanged | unit | cancelPositive | cancelAll | cancelMixed | cancelNegative
  deriving DecidableEq, Repr

def Branch.image : Branch → Expr Slot
  | .unchanged => peer
  | .unit => .one
  | .cancelPositive => .mul p (.inv r)
  | .cancelAll => .inv r
  | .cancelMixed => .mul p (.inv (.mul n r))
  | .cancelNegative => .inv (.mul n r)

def Branch.result : Branch → Expr Slot
  | .unchanged => .mul peer r
  | .unit => r
  | .cancelPositive => p
  | .cancelAll => .one
  | .cancelMixed => .mul p (.inv n)
  | .cancelNegative => .inv n

namespace Packet

def step (stack : List (Expr Slot)) (word : UInt64) : Option (List (Expr Slot)) :=
  match word, stack with
  | 0, xs => some (peer :: xs)
  | 1, xs => some (r :: xs)
  | 3, xs => some (p :: xs)
  | 4, xs => some (n :: xs)
  | 6, x :: xs => some (.inv x :: xs)
  | 7, y :: x :: xs => some (.mul x y :: xs)
  | 9, xs => some (.one :: xs)
  | _, _ => none

def decode (row : Array UInt64) : Option (Expr Slot) := do
  let [e] ← row.toList.foldlM step [] | none
  return e

def branches : List Branch := [.unchanged,.unit,.cancelPositive,.cancelAll,.cancelMixed,.cancelNegative]

/-- Every actual program decodes and every semantic arm is available.
The kernel can change its enumeration order or repeat an equivalent row. -/
structure Correct (rows : Array (Array UInt64)) : Prop where
  valid : ∀ row ∈ rows.toList, ∃ k : Branch, decode row = some k.image
  covers : ∀ k : Branch, ∃ row ∈ rows.toList, decode row = some k.image

/-- The export is input-independent, so the kernel can discharge the full
packet obligation by evaluation even after its implementation changes. -/
def accepts (rows : Array (Array UInt64)) : Bool :=
  let images := rows.toList.map decode
  images.all (fun e => branches.any fun k => e == some k.image) &&
    branches.all (fun k => images.contains (some k.image))

theorem of_accepts {rows} (ok : accepts rows = true) : Correct rows := by
  simp only [accepts,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,
    beq_iff_eq,List.contains_iff_mem] at ok
  constructor
  · intro r m
    obtain ⟨k,_,h⟩ := ok.1 _ (List.mem_map_of_mem (f := decode) m)
    exact ⟨k,h⟩
  · intro k
    exact List.mem_map.mp (ok.2 k (by cases k <;> decide))

def emitted (rows : Array (Array UInt64)) : List Branch :=
  rows.toList.flatMap fun row => branches.filter fun k => decode row = some k.image

theorem mem_emitted {rows : Array (Array UInt64)} (ok : Correct rows) (k : Branch) : k ∈ emitted rows := by
  obtain ⟨row,hr,hd⟩ := ok.covers k
  have mem : k ∈ branches := by cases k <;> decide
  exact List.mem_flatMap.mpr ⟨row,hr,List.mem_filter.mpr ⟨mem,by simp [hd]⟩⟩

theorem interpreted {rows : Array (Array UInt64)} (ok : Correct rows) {row} (hr : row ∈ rows) :
    ∃ k ∈ emitted rows, decode row = some k.image := by
  obtain ⟨k,hd⟩ := ok.valid row (Array.mem_toList_iff.mpr hr)
  exact ⟨k,mem_emitted ok k,hd⟩

end Packet
end Tamarin.Rewriting.DHExponent
