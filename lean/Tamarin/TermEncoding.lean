import Tamarin.SortCheck

/-!
Numeric syntax at the representation boundary. This is a reference format,
not a C memory layout. Symbol namespaces are separate and tied to a fixed
signature. Rust must still supply an injective encoding of full symbol/name
identities and full variable identities; numeric indices alone do not prove
that correspondence. Transport-only lists are not algebraic function symbols.
-/
namespace Tamarin

/-- An encoding cannot collapse distinct semantic identities. Unknown numeric
IDs may be rejected; no default symbol is substituted for an unknown ID. -/
structure SymbolEncoding (α : Type) where
  encode : α → Nat
  decode : Nat → Option α
  decode_encode : ∀ a, decode (encode a) = some a
  encode_decode : ∀ id a, decode id = some a → encode a = id

theorem SymbolEncoding.injective {α : Type} (c : SymbolEncoding α) :
    Function.Injective c.encode := by
  intro a b h
  have := congrArg c.decode h
  simpa only [c.decode_encode, Option.some.injEq] using this

theorem SymbolEncoding.rejects_unassigned {α : Type} (c : SymbolEncoding α)
    (id : Nat) (h : ∀ a, c.encode a ≠ id) : c.decode id = none := by
  cases hd : c.decode id with
  | none => rfl
  | some a => exact False.elim (h a (c.encode_decode id a hd))

structure SignatureEncoding (sig : Signature) where
  free : SymbolEncoding sig.FreeSym
  comm : SymbolEncoding sig.CSym
  ac : SymbolEncoding sig.ACSym
  atom : SymbolEncoding sig.Atom

/-- Free applications carry an explicit vector length. This makes the
reference decoder executable without any unchecked array indexing. A later
flat-buffer adapter must validate lengths and indices before constructing it.
C/AC are binary here; flattened AC arrays are interpreted separately. -/
inductive NumericTerm where
  | var : Nat → SortId → NumericTerm
  | atom : Nat → NumericTerm
  | free : Nat → (arity : Nat) → (Fin arity → NumericTerm) → NumericTerm
  | comm : Nat → NumericTerm → NumericTerm → NumericTerm
  | ac : Nat → NumericTerm → NumericTerm → NumericTerm

namespace TermEncoding
variable {sig : Signature}

/-- Traverse a finite vector with failure propagation. -/
def vector {α : Type} : (n : Nat) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← vector n (fun i => f i.succ)
    pure (Fin.cases a rest)

theorem vector_some {α : Type} (n : Nat) (f : Fin n → α) :
    vector n (fun i => some (f i)) = some f := by
  induction n with
  | zero =>
    change some Fin.elim0 = some f
    congr; funext i; exact Fin.elim0 i
  | succ n ih =>
    simp [vector, ih]
    congr; funext i; exact Fin.cases (by rfl) (fun _ => rfl) i

theorem vector_sound {α : Type} (n : Nat) (f : Fin n → Option α) (g : Fin n → α)
    (h : vector n f = some g) : ∀ i, f i = some (g i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    cases h0 : f 0 with
    | none => simp [vector, h0] at h
    | some a =>
      cases hr : vector n (fun i => f i.succ) with
      | none => simp [vector, h0, hr] at h
      | some rest =>
        have hg : Fin.cases a rest = g := by simpa [vector, h0, hr] using h
        subst g
        intro i
        exact Fin.cases h0 (fun j => ih _ rest hr j) i

theorem vector_complete {α : Type} (n : Nat) (f : Fin n → Option α)
    (h : ∀ i, ∃ a, f i = some a) : ∃ g, vector n f = some g := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := h 0
    obtain ⟨rest, hr⟩ := ih (fun i => f i.succ) (fun i => h i.succ)
    exact ⟨Fin.cases a rest, by simp [vector, ha, hr]⟩

def encode (c : SignatureEncoding sig) : Term sig → NumericTerm
  | .var v => .var v.id v.sort
  | .atom a => .atom (c.atom.encode a)
  | .free f args => .free (c.free.encode f) (sig.arity f) (fun i => encode c (args i))
  | .comm f a b => .comm (c.comm.encode f) (encode c a) (encode c b)
  | .ac f a b => .ac (c.ac.encode f) (encode c a) (encode c b)

/-- Structural decoding: unknown symbols and wrong free arities are rejected.
Sort validation is a separate step; this function does not certify typing. -/
def decode (c : SignatureEncoding sig) : NumericTerm → Option (Term sig)
  | .var id sort => some (.var ⟨id, sort⟩)
  | .atom id => (c.atom.decode id).map Term.atom
  | .free id n args => do
    let f ← c.free.decode id
    if h : n = sig.arity f then
      let children ← vector n (fun i => decode c (args i))
      pure (.free f (fun i => children (h.symm ▸ i)))
    else none
  | .comm id a b => do
    let f ← c.comm.decode id
    let a ← decode c a
    let b ← decode c b
    pure (.comm f a b)
  | .ac id a b => do
    let f ← c.ac.decode id
    let a ← decode c a
    let b ← decode c b
    pure (.ac f a b)

theorem decode_encode (c : SignatureEncoding sig) (t : Term sig) :
    decode c (encode c t) = some t := by
  induction t with
  | var v => rfl
  | atom a => simp [encode, decode, c.atom.decode_encode]
  | free f args ih =>
    simp [encode, decode, c.free.decode_encode, ih, vector_some]
  | comm f a b ha hb => simp [encode, decode, c.comm.decode_encode, ha, hb]
  | ac f a b ha hb => simp [encode, decode, c.ac.decode_encode, ha, hb]

theorem encode_injective (c : SignatureEncoding sig) : Function.Injective (encode c) := by
  intro a b h
  have := congrArg (decode c) h
  simpa only [decode_encode, Option.some.injEq] using this

/-- Checked decoding for a caller-declared sort. Failure is a representation
error, never a proof that a unification problem has no solutions. -/
def decodeChecked (c : SignatureEncoding sig) (s : SortId) (raw : NumericTerm) :
    Option (Term sig) := do
  let t ← decode c raw
  if t.checkSort s then some t else none

theorem decodeChecked_iff (c : SignatureEncoding sig) (s : SortId)
    (raw : NumericTerm) (t : Term sig) :
    decodeChecked c s raw = some t ↔ decode c raw = some t ∧ HasSort t s := by
  simp only [decodeChecked]
  cases h : decode c raw with
  | none => simp
  | some u =>
    change (if u.checkSort s then some u else none) = some t ↔
      some u = some t ∧ HasSort t s
    split <;> simp_all [Term.checkSort_iff] <;> rintro rfl <;> assumption

theorem decodeChecked_encode (c : SignatureEncoding sig) (t : Term sig)
    (s : SortId) (h : HasSort t s) :
    decodeChecked c s (encode c t) = some t :=
  (decodeChecked_iff c s _ t).mpr ⟨decode_encode c t, h⟩

end TermEncoding
end Tamarin
