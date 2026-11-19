import Tamarin.SignatureTable
import Tamarin.VariablePermutation

namespace Tamarin.WordEncodingChecks

-- Boundary cases are small computations, not large allocations.
example : WordEncoding.pack 0 = some 0 := rfl
example : WordEncoding.pack 18446744073709551615 = some 18446744073709551615 := rfl
example : WordEncoding.pack 18446744073709551616 = none := rfl
example : WordEncoding.pack 18446744073709551617 = none := rfl

-- Overflow cannot silently turn an identity into a different representable one.
example (a b : Nat) (w : UInt64)
    (ha : WordEncoding.pack a = some w) (hb : WordEncoding.pack b = some w) : a = b :=
  ((WordEncoding.pack_iff a w).mp ha).symm.trans ((WordEncoding.pack_iff b w).mp hb)

example : WordEncoding.term (.var 18446744073709551616 .msg) = none := rfl
example : WordEncoding.term (.atom 18446744073709551616) = none := rfl
example : WordEncoding.term (.comm 18446744073709551616 (.atom 0) (.atom 1)) = none := rfl
example : WordEncoding.term (.ac 18446744073709551616 (.atom 0) (.atom 1)) = none := rfl
example : WordEncoding.term (.ac 0 (.atom 0) (.var 18446744073709551616 .pub)) = none := rfl
example : WordEncoding.term (.free 18446744073709551616 0 Fin.elim0) = none := rfl
example : WordEncoding.term (.free 0 1 (fun _ => .atom 18446744073709551616)) = none := rfl

-- An overflowing arity fails before the reference decoder traverses children.
example : WordEncoding.term (.free 0 18446744073709551616 (fun _ => .atom 0)) = none := rfl

-- Existing freshness semantics stay unbounded. Packing detects an exhausted
-- or too-sparse shifted supply; a future allocator can compact it with proof.
example : WordEncoding.pack
    (VariablePermutation.freshBound [⟨18446744073709551615, .msg⟩]) = none := rfl

private def table : SignatureTable where
  free := #[⟨#[.nat, .msg], .msg⟩, ⟨#[.nat, .msg], .msg⟩, ⟨#[], .nat⟩]
  comm := #[.msg]
  ac := #[.msg, .nat]
  atoms := #[.pub, .fresh, .node, .nat]

private theorem fits : table.Fits := (table.checkFits_iff).mp (by
  simp only [SignatureTable.checkFits, ← Array.all_toList]
  decide)

-- Duplicate metadata denotes distinct free symbols. Namespace IDs likewise
-- do not alias free, C, AC, and atom identities.
example : table.free[0] = table.free[1] := rfl
example : table.encoding.free.encode ⟨0, by decide⟩ ≠
    table.encoding.free.encode ⟨1, by decide⟩ := by decide
example : WordEncoding.decode table.encoding .msg (.comm 1 (.atom 0) (.atom 1)) = none := rfl
example : WordEncoding.decode table.encoding .msg (.atom 4) = none := rfl
example : WordEncoding.decode table.encoding .msg (.atom 18446744073709551615) = none := rfl
example : WordEncoding.decode table.encoding .msg (.free 0 0 Fin.elim0) = none := rfl
example : WordEncoding.decode table.encoding .nat (.free 2 0 Fin.elim0) =
    some (.free ⟨2, by decide⟩ Fin.elim0) := rfl
example : WordEncoding.decode table.encoding .msg (.comm 0 (.atom 0) (.atom 2)) = none := rfl
example : (WordEncoding.decode table.encoding .msg
    (.free 0 2 (Fin.cases (.atom 3) (fun _ => .atom 0)))).isSome = true := rfl

-- Zero-sized namespaces have no default inhabitant.
private def emptyTable : SignatureTable := ⟨#[], #[], #[], #[]⟩
example : WordEncoding.decode emptyTable.encoding .msg (.atom 0) = none := rfl
example : WordEncoding.decode emptyTable.encoding .msg (.var 0 .msg) =
    some (.var ⟨0, .msg⟩) := rfl

example (t : Term table.signature) (s : SortId) (hs : HasSort t s)
    (hv : ∀ v, t.Occurs v → v.id < UInt64.size) :
    ∃ w, WordEncoding.encode table.encoding t = some w ∧
      WordEncoding.decode table.encoding s w = some t :=
  table.word_roundTrip fits t s hs hv

end Tamarin.WordEncodingChecks
