import Tamarin.TermEncoding

/-! Identity tables preserve values, not just hashes, printed names, or numeric
variable indices. This is the mathematical model of the Rust request-local
bidirectional interner; validation of the Rust implementation remains separate.
-/
namespace Tamarin

structure IdentityTable (α : Type) where
  entries : List α
  unique : entries.Nodup

namespace IdentityTable
variable {α : Type} [DecidableEq α]

def encode (t : IdentityTable α) (a : α) : Option Nat :=
  if a ∈ t.entries then some (t.entries.idxOf a) else none

def decode (t : IdentityTable α) (id : Nat) : Option α := t.entries[id]?

theorem decode_encode (t : IdentityTable α) (a : α) (h : a ∈ t.entries) :
    t.decode (t.entries.idxOf a) = some a := by
  simp only [decode, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h), List.getElem_idxOf]

theorem encode_injective (t : IdentityTable α) {a b : α} {id : Nat}
    (ha : t.encode a = some id) (hb : t.encode b = some id) : a = b := by
  have ea : a ∈ t.entries ∧ t.entries.idxOf a = id := by
    by_cases hm : a ∈ t.entries <;> simp_all [encode]
  have eb : b ∈ t.entries ∧ t.entries.idxOf b = id := by
    by_cases hm : b ∈ t.entries <;> simp_all [encode]
  have da := t.decode_encode a ea.1
  have db := t.decode_encode b eb.1
  rw [ea.2] at da
  rw [eb.2] at db
  exact Option.some.inj (da.symm.trans db)

/-- The executable reference transition mirrors request-local Rust interning:
existing IDs are retained; new values append one row, without truncation. -/
def intern (t : IdentityTable α) (a : α) : IdentityTable α × Nat :=
  if h : a ∈ t.entries then (t, t.entries.idxOf a)
  else (⟨t.entries ++ [a], by
    simp [List.nodup_append, t.unique]
    intro b hb he; subst b; exact h hb⟩, t.entries.length)

theorem intern_decode (t : IdentityTable α) (a : α) :
    (t.intern a).1.decode (t.intern a).2 = some a := by
  unfold intern
  split
  · exact t.decode_encode a ‹_›
  · simp [decode]

theorem intern_preserves (t : IdentityTable α) (a : α) (id : Nat)
    (h : id < t.entries.length) : (t.intern a).1.decode id = t.decode id := by
  unfold intern
  split
  · rfl
  · simp [decode, List.getElem?_append, h]

/-- Checked word allocation; no wraparound can turn a new identity into an
old row. Failure is a representation error, never an empty solver result. -/
def internWord (t : IdentityTable α) (a : α) : Option (IdentityTable α × UInt64) :=
  let next := t.intern a
  if next.2 < UInt64.size then some (next.1, UInt64.ofNat next.2) else none

theorem internWord_sound (t : IdentityTable α) (a : α) (next : IdentityTable α) (id : UInt64)
    (h : t.internWord a = some (next, id)) : next.decode id.toNat = some a := by
  dsimp only [internWord] at h
  split at h
  · rename_i hf
    have he := Option.some.inj h
    cases he
    rw [UInt64.toNat_ofNat_of_lt' hf]
    exact t.intern_decode a
  · cases h

/-- The table supplies the codec required by the generic term representation;
only registered full identities inhabit its semantic symbol type. -/
def codec (t : IdentityTable α) : SymbolEncoding {a : α // a ∈ t.entries} where
  encode := fun a => t.entries.idxOf a.val
  decode := fun id => if h : id < t.entries.length then
    some ⟨t.entries[id], List.getElem_mem h⟩ else none
  decode_encode := by
    intro a
    simp only [List.idxOf_lt_length_of_mem a.property, ↓reduceDIte]
    congr 1
    exact Subtype.ext (List.getElem_idxOf _)
  encode_decode := by
    intro id a h
    split at h
    · cases h
      apply t.unique.eq_of_getElem_eq (List.idxOf_lt_length_of_mem (List.getElem_mem ‹_›)) ‹_›
      exact List.getElem_idxOf _
    · cases h

/-- Total interpretation for semantic statements over lists of words. Its
fallback is irrelevant once every input word is known to be registered. -/
def wordAtom (t : IdentityTable α) (fallback : α) (id : UInt64) : α :=
  (t.decode id.toNat).getD fallback

def atomWord (t : IdentityTable α) (a : α) : Option UInt64 := do
  let i ← t.encode a
  if i < UInt64.size then some (UInt64.ofNat i) else none

theorem live_word_roundtrip (t : IdentityTable α) (fallback : α) (id : UInt64)
    (hi : id.toNat < t.entries.length) : t.atomWord (t.wordAtom fallback id) = some id := by
  have hm := List.getElem_mem hi
  have he := t.unique.eq_of_getElem_eq (List.idxOf_lt_length_of_mem hm) hi
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem hm))
  simp [wordAtom, decode, List.getElem?_eq_getElem hi, atomWord, encode, hm, he, id.toNat_lt_size]

/-- Concrete variable identity includes the name and sort as well as the
index. Names are bytes here, matching Rust string/byte equality exactly. -/
structure VariableKey where
  name : List UInt8
  sort : SortId
  index : UInt64
  deriving DecidableEq, Repr

structure NameKey where
  tag : Nat
  name : List UInt8
  deriving DecidableEq, Repr

structure FreeKey where
  name : List UInt8
  arity : Nat
  privacy : Nat
  constructability : Nat
  ndc : Nat
  deriving DecidableEq, Repr

/-- Converting a full registered variable identity retains its declared sort.
The numeric ID is a table row, never the caller's raw variable index. -/
def encodeVariable (t : IdentityTable VariableKey) (v : {a // a ∈ t.entries}) : Variable :=
  ⟨t.codec.encode v, v.val.sort⟩

theorem variable_injective (t : IdentityTable VariableKey) : Function.Injective t.encodeVariable := by
  intro a b h
  exact t.codec.injective (congrArg Variable.id h)

end IdentityTable
end Tamarin
