import Tamarin.TermEncoding

/-!
Checked fixed-width conversion for the reference syntax. Overflow is failure,
never modular arithmetic on identities. This is still typed reference syntax,
not a specification of C pointers, buffer lengths, or allocation lifetimes.
-/
namespace Tamarin

namespace WordEncoding

def pack (n : Nat) : Option UInt64 :=
  if n < UInt64.size then some (UInt64.ofNat n) else none

theorem pack_iff (n : Nat) (w : UInt64) : pack n = some w ↔ w.toNat = n := by
  unfold pack
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact UInt64.toNat_ofNat_of_lt' h
    · intro hw
      rw [← hw, UInt64.ofNat_toNat]
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hw
    exact h (hw ▸ w.toNat_lt_size)

theorem pack_none_iff (n : Nat) : pack n = none ↔ UInt64.size ≤ n := by
  simp [pack]

theorem pack_toNat (w : UInt64) : pack w.toNat = some w :=
  (pack_iff _ _).mpr rfl

end WordEncoding

/-- IDs and free arities are fixed-width. Finite vectors and checked SortId
values remain reference-level structures, awaiting a validated buffer adapter. -/
inductive WordTerm where
  | var : UInt64 → SortId → WordTerm
  | atom : UInt64 → WordTerm
  | free : UInt64 → (arity : UInt64) → (Fin arity.toNat → WordTerm) → WordTerm
  | comm : UInt64 → WordTerm → WordTerm → WordTerm
  | ac : UInt64 → WordTerm → WordTerm → WordTerm

namespace WordTerm

def toNumeric : WordTerm → NumericTerm
  | .var v s => .var v.toNat s
  | .atom a => .atom a.toNat
  | .free f n args => .free f.toNat n.toNat (fun i => toNumeric (args i))
  | .comm f a b => .comm f.toNat a.toNumeric b.toNumeric
  | .ac f a b => .ac f.toNat a.toNumeric b.toNumeric

end WordTerm

namespace WordEncoding

def term : NumericTerm → Option WordTerm
  | .var v s => (pack v).map (fun w => .var w s)
  | .atom a => (pack a).map WordTerm.atom
  | .free f n args => do
    let f ← pack f
    if h : n < UInt64.size then
      let children ← TermEncoding.vector n (fun i => term (args i))
      pure (.free f (UInt64.ofNatLT n h) children)
    else none
  | .comm f a b => do
    let f ← pack f
    let a ← term a
    let b ← term b
    pure (.comm f a b)
  | .ac f a b => do
    let f ← pack f
    let a ← term a
    let b ← term b
    pure (.ac f a b)

/-- Every fixed-width tree has a lossless reference interpretation. -/
theorem term_toNumeric (t : WordTerm) : term t.toNumeric = some t := by
  induction t with
  | var v s => simp [WordTerm.toNumeric, term, pack_toNat]
  | atom a => simp [WordTerm.toNumeric, term, pack_toNat]
  | free f n args ih =>
    simp [WordTerm.toNumeric, term, pack_toNat, n.toNat_lt_size, ih,
      TermEncoding.vector_some]
  | comm f a b ha hb => simp [WordTerm.toNumeric, term, pack_toNat, ha, hb]
  | ac f a b ha hb => simp [WordTerm.toNumeric, term, pack_toNat, ha, hb]

/-- A successful conversion cannot wrap, collapse, or replace any subtree. -/
theorem term_sound (t : NumericTerm) (w : WordTerm) (h : term t = some w) :
    w.toNumeric = t := by
  induction t generalizing w with
  | var v s =>
    obtain ⟨id, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [WordTerm.toNumeric, (pack_iff v id).mp hi]
  | atom a =>
    obtain ⟨id, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [WordTerm.toNumeric, (pack_iff a id).mp hi]
  | free f n args ih =>
    obtain ⟨id, hi, hr⟩ := Option.bind_eq_some_iff.mp h
    split at hr
    · obtain ⟨children, hc, hw⟩ := Option.bind_eq_some_iff.mp hr
      cases hw
      simp only [WordTerm.toNumeric, (pack_iff f id).mp hi]
      congr; funext i
      exact ih i _ (TermEncoding.vector_sound n _ children hc i)
    · cases hr
  | comm f a b ia ib =>
    obtain ⟨id, hi, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a', ha, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨b', hb, hw⟩ := Option.bind_eq_some_iff.mp rest
    cases hw
    simp only [WordTerm.toNumeric, (pack_iff f id).mp hi, ia _ ha, ib _ hb]
  | ac f a b ia ib =>
    obtain ⟨id, hi, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a', ha, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨b', hb, hw⟩ := Option.bind_eq_some_iff.mp rest
    cases hw
    simp only [WordTerm.toNumeric, (pack_iff f id).mp hi, ia _ ha, ib _ hb]

theorem term_iff (t : NumericTerm) (w : WordTerm) :
    term t = some w ↔ w.toNumeric = t := by
  constructor
  · exact term_sound t w
  · rintro rfl; exact term_toNumeric w

/-- Exact representability, including every nested ID and free arity. -/
def Fits : NumericTerm → Prop
  | .var v _ => v < UInt64.size
  | .atom a => a < UInt64.size
  | .free f n args => f < UInt64.size ∧ n < UInt64.size ∧ ∀ i, Fits (args i)
  | .comm f a b | .ac f a b => f < UInt64.size ∧ Fits a ∧ Fits b

theorem toNumeric_fits (w : WordTerm) : Fits w.toNumeric := by
  induction w with
  | var v s => exact v.toNat_lt_size
  | atom a => exact a.toNat_lt_size
  | free f n args ih => exact ⟨f.toNat_lt_size, n.toNat_lt_size, ih⟩
  | comm f a b ha hb => exact ⟨f.toNat_lt_size, ha, hb⟩
  | ac f a b ha hb => exact ⟨f.toNat_lt_size, ha, hb⟩

theorem term_complete (t : NumericTerm) (h : Fits t) : ∃ w, term t = some w := by
  induction t with
  | var v s => exact ⟨.var (UInt64.ofNat v) s, by simp [term, pack, show v < UInt64.size from h]⟩
  | atom a => exact ⟨.atom (UInt64.ofNat a), by simp [term, pack, show a < UInt64.size from h]⟩
  | free f n args ih =>
    obtain ⟨hf, hn, hs⟩ := h
    obtain ⟨children, hc⟩ := TermEncoding.vector_complete n _ (fun i => ih i (hs i))
    exact ⟨.free (UInt64.ofNat f) (UInt64.ofNatLT n hn) children,
      by simp [term, pack, hf, hn, hc]⟩
  | comm f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := h
    obtain ⟨a', ha⟩ := ia ha
    obtain ⟨b', hb⟩ := ib hb
    exact ⟨.comm (UInt64.ofNat f) a' b', by simp [term, pack, hf, ha, hb]⟩
  | ac f a b ia ib =>
    obtain ⟨hf, ha, hb⟩ := h
    obtain ⟨a', ha⟩ := ia ha
    obtain ⟨b', hb⟩ := ib hb
    exact ⟨.ac (UInt64.ofNat f) a' b', by simp [term, pack, hf, ha, hb]⟩

theorem term_none_iff (t : NumericTerm) : term t = none ↔ ¬ Fits t := by
  constructor
  · intro hn hf
    obtain ⟨w, hw⟩ := term_complete t hf
    simp [hn] at hw
  · intro h
    cases hw : term t with
    | none => rfl
    | some w => exact False.elim (h ((term_sound t w hw) ▸ toNumeric_fits w))

def encode {sig : Signature} (c : SignatureEncoding sig) (t : Term sig) : Option WordTerm :=
  term (TermEncoding.encode c t)

def decode {sig : Signature} (c : SignatureEncoding sig) (s : SortId) (w : WordTerm) :
    Option (Term sig) := TermEncoding.decodeChecked c s w.toNumeric

theorem checked_roundTrip {sig : Signature} (c : SignatureEncoding sig)
    (t : Term sig) (s : SortId) (h : HasSort t s)
    (w : WordTerm) (hw : encode c t = some w) : decode c s w = some t := by
  unfold decode
  rw [term_sound _ _ hw]
  exact TermEncoding.decodeChecked_encode c t s h

end WordEncoding
end Tamarin
