import Tamarin.BinaryXorVariants
import TamarinRuntime.BinaryCancellation

/-! A single namespace of three message witnesses is used for both
caller images and the normal value. Membership permits any enumeration order. -/
namespace Tamarin.Rewriting.BinaryXor

def Shape.packet : Shape → Array UInt64
  | .disjoint => #[2,4,6]
  | .unitLeft => #[0,4,4]
  | .unitRight => #[2,0,2]
  | .same => #[1,1,0]
  | .leftContains => #[3,1,2]
  | .rightContains => #[1,5,4]
  | .overlap => #[3,5,6]

def RowsCorrect (rows : Array (Array UInt64)) :=
  ∀ row, row ∈ rows ↔ ∃ sh : Shape, row = sh.packet

theorem candidate_rows : RowsCorrect BinaryCancellationCandidate.rows := by
  let shapes : List Shape := [.disjoint,.unitLeft,.unitRight,.same,.leftContains,.rightContains,.overlap]
  have covered (sh : Shape) : sh ∈ shapes := by cases sh <;> decide
  have all : ∀ sh ∈ shapes, sh.packet ∈ BinaryCancellationCandidate.rows.toList := by decide
  have only : ∀ row ∈ BinaryCancellationCandidate.rows.toList, row ∈ shapes.map Shape.packet := by decide
  intro row
  constructor
  · intro mem
    obtain ⟨sh,_,eq⟩ := List.mem_map.mp (only row (Array.mem_def.mp mem))
    exact ⟨sh,eq.symm⟩
  · rintro ⟨sh,rfl⟩
    exact Array.mem_def.mpr (all sh (covered sh))

variable {sig : Signature}

def decodeMask (T : Table sig) (w : Names) (mask : UInt64) : Option (Term sig) :=
  match mask with
  | 0 => some T.zero
  | 1 => some (.var w.h)
  | 2 => some (.var w.i)
  | 3 => some (.ac T.f (.var w.h) (.var w.i))
  | 4 => some (.var w.j)
  | 5 => some (.ac T.f (.var w.h) (.var w.j))
  | 6 => some (.ac T.f (.var w.i) (.var w.j))
  | _ => none

structure PacketArm (q : Query sig) (row : Array UInt64) (a : Variant sig) : Prop where
  outside : ∀ v, v ≠ q.x → v ≠ q.y → a.subst.image v = .var v
  terms : ∃ (w : Names) (left right value : Term sig) (l r o : UInt64),
    row = #[l,r,o] ∧ decodeMask q.table w l = some left ∧
    decodeMask q.table w r = some right ∧ decodeMask q.table w o = some value ∧
    EquivB (a.subst.image q.x) left ∧ EquivB (a.subst.image q.y) right ∧
    ∃ actual, a.values = [actual] ∧ EquivB actual value

theorem PacketArm.decodes {q : Query sig} {sh : Shape} {arm : Variant sig}
    (a : PacketArm q sh.packet arm) : Decodes q sh arm := by
  obtain ⟨w,l,r,o,ml,mr,mo,e,el,er,eo,hl,hr,v,hv,ho⟩ := a.terms
  refine ⟨a.outside,w,v,hv,?_⟩
  cases sh <;> simp [Shape.packet] at e <;> obtain ⟨rfl,rfl,rfl⟩ := e <;>
    simp_all [decodeMask,Names.images,Shape.images]

theorem packetFamily_complete (q : Query sig) (rows : Array (Array UInt64)) (ok : RowsCorrect rows)
    (arms : List (Variant sig)) (all : ∀ row ∈ rows, ∃ a ∈ arms, PacketArm q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ rows, PacketArm q row a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] := by
  apply complete q arms
  · intro sh
    obtain ⟨a,ha,decoded⟩ := all sh.packet ((ok _).mpr ⟨sh,rfl⟩)
    exact ⟨a,ha,decoded.decodes⟩
  · intro a ha
    obtain ⟨row,mem,decoded⟩ := only a ha
    obtain ⟨sh,rfl⟩ := (ok _).mp mem
    exact ⟨sh,decoded.decodes⟩

end Tamarin.Rewriting.BinaryXor
