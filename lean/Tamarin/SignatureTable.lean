import Tamarin.WordEncoding

/-!
Finite, executable signature tables. Identity is the namespace and row index,
not equality of declaration metadata. The Rust producer must intern full
identities consistently and supply the declarations for the active theory.
These round-trip proofs concern the supplied table. They do not establish
solver completeness under an enlarged ambient signature; a solver must retain
the generic semantic contract or separately prove that extension property.
-/
namespace Tamarin

structure FreeDeclaration where
  inputs : Array SortId
  output : SortId
  deriving DecidableEq, Repr

structure SignatureTable where
  free : Array FreeDeclaration
  comm : Array SortId
  ac : Array SortId
  atoms : Array SortId
  deriving Repr

namespace SignatureTable

def signature (table : SignatureTable) : Signature where
  FreeSym := Fin table.free.size
  CSym := Fin table.comm.size
  ACSym := Fin table.ac.size
  Atom := Fin table.atoms.size
  arity := fun f => table.free[f].inputs.size
  inputSort := fun f i => table.free[f].inputs[i]
  outputSort := fun f => table.free[f].output
  cSort := fun f => table.comm[f]
  acSort := fun f => table.ac[f]
  atomSort := fun a => table.atoms[a]

/-- No assumptions about the table contents are needed for ID round trips.
In particular, repeated declaration metadata does not alias two row IDs. -/
def indexEncoding (size : Nat) : SymbolEncoding (Fin size) where
  encode := Fin.val
  decode := fun id => if h : id < size then some ⟨id, h⟩ else none
  decode_encode := fun a => by simp [a.isLt]
  encode_decode := by
    intro id a h
    split at h
    · cases h; rfl
    · cases h

def encoding (table : SignatureTable) : SignatureEncoding table.signature where
  free := indexEncoding table.free.size
  comm := indexEncoding table.comm.size
  ac := indexEncoding table.ac.size
  atom := indexEncoding table.atoms.size

theorem decode_encode (table : SignatureTable) (t : Term table.signature) :
    TermEncoding.decode table.encoding (TermEncoding.encode table.encoding t) = some t :=
  TermEncoding.decode_encode table.encoding t

theorem checked_roundTrip (table : SignatureTable) (t : Term table.signature)
    (s : SortId) (h : HasSort t s) :
    TermEncoding.decodeChecked table.encoding s (TermEncoding.encode table.encoding t) = some t :=
  TermEncoding.decodeChecked_encode table.encoding t s h

/-- Row counts may use every UInt64 identity, but an encoded free arity must
itself fit in UInt64. Memory and platform usize limits are additional checks. -/
structure Fits (table : SignatureTable) : Prop where
  free : table.free.size ≤ UInt64.size
  comm : table.comm.size ≤ UInt64.size
  ac : table.ac.size ≤ UInt64.size
  atoms : table.atoms.size ≤ UInt64.size
  arities : ∀ f : Fin table.free.size, table.free[f].inputs.size < UInt64.size

def checkFits (table : SignatureTable) : Bool :=
  decide (table.free.size ≤ UInt64.size ∧ table.comm.size ≤ UInt64.size ∧
    table.ac.size ≤ UInt64.size ∧ table.atoms.size ≤ UInt64.size) &&
    table.free.all (fun f => decide (f.inputs.size < UInt64.size))

theorem checkFits_iff (table : SignatureTable) : table.checkFits = true ↔ table.Fits := by
  simp only [checkFits, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true]
  constructor
  · rintro ⟨⟨hf, hc, ha, hn⟩, har⟩
    exact ⟨hf, hc, ha, hn, fun f => har f.val f.isLt⟩
  · intro h
    exact ⟨⟨h.free, h.comm, h.ac, h.atoms⟩, fun i hi => h.arities ⟨i, hi⟩⟩

theorem encoded_fits (table : SignatureTable) (ht : table.Fits)
    (t : Term table.signature)
    (hv : ∀ v, t.Occurs v → v.id < UInt64.size) :
    WordEncoding.Fits (TermEncoding.encode table.encoding t) := by
  induction t with
  | var v => exact hv v rfl
  | atom a => exact Nat.lt_of_lt_of_le a.isLt ht.atoms
  | free f args ih =>
    exact ⟨Nat.lt_of_lt_of_le f.isLt ht.free, ht.arities f,
      fun i => ih i (fun v h => hv v ⟨i, h⟩)⟩
  | comm f a b ia ib =>
    exact ⟨Nat.lt_of_lt_of_le f.isLt ht.comm,
      ia (fun v h => hv v (Or.inl h)), ib (fun v h => hv v (Or.inr h))⟩
  | ac f a b ia ib =>
    exact ⟨Nat.lt_of_lt_of_le f.isLt ht.ac,
      ia (fun v h => hv v (Or.inl h)), ib (fun v h => hv v (Or.inr h))⟩

theorem word_roundTrip (table : SignatureTable) (ht : table.Fits)
    (t : Term table.signature) (s : SortId) (hs : HasSort t s)
    (hv : ∀ v, t.Occurs v → v.id < UInt64.size) :
    ∃ w, WordEncoding.encode table.encoding t = some w ∧
      WordEncoding.decode table.encoding s w = some t := by
  obtain ⟨w, hw⟩ := WordEncoding.term_complete _ (encoded_fits table ht t hv)
  exact ⟨w, hw, WordEncoding.checked_roundTrip table.encoding t s hs w hw⟩

end SignatureTable
end Tamarin
